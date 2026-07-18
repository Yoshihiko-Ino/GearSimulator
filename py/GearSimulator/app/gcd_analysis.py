from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from math import ceil, isfinite
from statistics import median
from typing import Dict, Iterable, List, Mapping, Optional, Sequence, Tuple


GCD_ACTION_TYPES = {"spell", "weaponskill"}
MIN_GCD_INTERVAL_MS = 750
MAX_GCD_INTERVAL_MS = 3500
CAST_PAIR_WINDOW_MS = 10_000
CLUSTER_TOLERANCE_MS = 35


@dataclass(frozen=True)
class LogGcdEstimate:
    seconds: Optional[float]
    sample_count: int
    cluster_share: float
    spread_ms: float
    confidence: str
    reason: str = ""
    raw_median_ms: Optional[float] = None
    tier_share: float = 0.0

    @property
    def usable(self) -> bool:
        return self.seconds is not None and self.confidence in {"high", "medium"}


@dataclass(frozen=True)
class LogGcdConstraint:
    observed_seconds: float
    baseline_formula_seconds: float
    confidence: str
    sample_count: int

    def candidate_effective_seconds(self, candidate_formula_seconds: float) -> float:
        if self.baseline_formula_seconds <= 0:
            return float(candidate_formula_seconds)
        return self.observed_seconds * float(candidate_formula_seconds) / self.baseline_formula_seconds

    def accepts(self, candidate_formula_seconds: float) -> bool:
        candidate = self.candidate_effective_seconds(candidate_formula_seconds)
        return round(candidate + 1e-9, 2) == round(self.observed_seconds + 1e-9, 2)


def _event_timestamp(event: Mapping[str, object]) -> Optional[int]:
    value = event.get("timestamp")
    if value is None:
        value = event.get("time")
    try:
        return int(value) if value is not None else None
    except (TypeError, ValueError):
        return None


def _event_source_id(event: Mapping[str, object]) -> Optional[int]:
    value = event.get("sourceID")
    if value is None:
        value = event.get("sourceId")
    if value is None:
        value = event.get("sourceid")
    try:
        return int(value) if value is not None else None
    except (TypeError, ValueError):
        return None


def _event_action_id(event: Mapping[str, object]) -> Optional[int]:
    ability = event.get("ability")
    values: List[object] = []
    if isinstance(ability, Mapping):
        values.extend((ability.get("gameID"), ability.get("guid"), ability.get("id")))
    values.extend((event.get("abilityGameID"), event.get("abilityGuid"), event.get("actionID")))
    for value in values:
        try:
            action_id = int(value)
        except (TypeError, ValueError):
            continue
        if action_id > 0:
            return action_id
    return None


def _action_type(action: object) -> str:
    if isinstance(action, Mapping):
        value = action.get("attack_type") or action.get("attackType")
    else:
        value = getattr(action, "attack_type", None)
    return str(value or "").strip().lower().replace("-", "")


def _gcd_start_timestamps(
    events: Iterable[Mapping[str, object]],
    action_data: Mapping[int, object],
    actor_id: Optional[int],
) -> List[int]:
    normalized: List[Tuple[int, str, int]] = []
    for event in events:
        source_id = _event_source_id(event)
        if actor_id is not None and source_id is not None and source_id != actor_id:
            continue
        timestamp = _event_timestamp(event)
        action_id = _event_action_id(event)
        event_type = str(event.get("type") or "").lower()
        if timestamp is None or action_id is None or event_type not in {"begincast", "cast"}:
            continue
        if _action_type(action_data.get(action_id)) not in GCD_ACTION_TYPES:
            continue
        normalized.append((timestamp, event_type, action_id))
    normalized.sort(key=lambda entry: (entry[0], 0 if entry[1] == "begincast" else 1))

    starts: List[int] = []
    pending: Dict[int, List[int]] = {}
    for timestamp, event_type, action_id in normalized:
        if event_type == "begincast":
            pending.setdefault(action_id, []).append(timestamp)
            continue
        entries = pending.get(action_id, [])
        match_index: Optional[int] = None
        for idx in range(len(entries) - 1, -1, -1):
            begin_ts = entries[idx]
            if timestamp - begin_ts > CAST_PAIR_WINDOW_MS:
                break
            match_index = idx
            break
        if match_index is not None:
            begin_ts = entries.pop(match_index)
            starts.append(begin_ts)
        else:
            starts.append(timestamp)

    for entries in pending.values():
        starts.extend(entries)
    return sorted(set(starts))


def _dominant_cluster(intervals: Sequence[int]) -> Tuple[List[int], float]:
    if not intervals:
        return [], 0.0
    ordered = sorted(intervals)
    clusters: List[List[int]] = []
    for interval in ordered:
        best: Optional[List[int]] = None
        best_distance: Optional[float] = None
        for cluster in clusters:
            distance = abs(interval - median(cluster))
            if distance <= CLUSTER_TOLERANCE_MS and (best_distance is None or distance < best_distance):
                best = cluster
                best_distance = distance
        if best is None:
            clusters.append([interval])
        else:
            best.append(interval)
    minimum_reference_samples = max(3, ceil(len(intervals) * 0.20))
    reference_clusters = [
        values for values in clusters if len(values) >= minimum_reference_samples
    ]
    if reference_clusters:
        # The slower stable cluster represents the normal rotation. This avoids
        # treating fixed short burst GCDs (steps, transformed actions, etc.) as
        # the gear-sensitive reference GCD.
        selected = max(reference_clusters, key=lambda values: median(values))
    else:
        selected = max(clusters, key=len)
    return selected, len(selected) / len(intervals)


def _gcd_tier_seconds(cluster: Sequence[int]) -> Tuple[float, float]:
    center = float(median(cluster))
    tier_counts = Counter((int(value) + 5) // 10 for value in cluster)
    tier, tier_count = min(
        tier_counts.items(),
        key=lambda entry: (
            -entry[1],
            abs((entry[0] * 10) - center),
            -entry[0],
        ),
    )
    tier_share = tier_count / len(cluster)
    if tier_count < max(3, ceil(len(cluster) * 0.20)):
        tier = (int(round(center)) + 5) // 10
    return tier / 100.0, tier_share


def estimate_log_gcd(
    events: Iterable[Mapping[str, object]],
    action_data: Mapping[int, object],
    *,
    actor_id: Optional[int] = None,
) -> LogGcdEstimate:
    starts = _gcd_start_timestamps(events, action_data, actor_id)
    if len(starts) < 2:
        return LogGcdEstimate(None, 0, 0.0, 0.0, "unavailable", "GCDアクションが不足しています")
    intervals = [
        current - previous
        for previous, current in zip(starts, starts[1:])
        if MIN_GCD_INTERVAL_MS <= current - previous <= MAX_GCD_INTERVAL_MS
    ]
    if not intervals:
        return LogGcdEstimate(None, 0, 0.0, 0.0, "unavailable", "有効なGCD間隔がありません")
    cluster, share = _dominant_cluster(intervals)
    center = float(median(cluster))
    deviations = [abs(value - center) for value in cluster]
    spread = float(median(deviations)) if deviations else 0.0
    sample_count = len(cluster)
    if sample_count >= 20 and share >= 0.70 and spread <= 30:
        confidence = "high"
    elif sample_count >= 8 and share >= 0.50 and spread <= 60:
        confidence = "medium"
    else:
        confidence = "low"
    seconds, tier_share = _gcd_tier_seconds(cluster)
    if not isfinite(seconds) or seconds <= 0:
        return LogGcdEstimate(None, 0, 0.0, 0.0, "unavailable", "GCD推定値が不正です")
    reason = "" if confidence != "low" else "サンプル数またはクラスタの信頼度が不足しています"
    return LogGcdEstimate(
        seconds,
        sample_count,
        share,
        spread,
        confidence,
        reason,
        center,
        tier_share,
    )


def build_log_gcd_constraint(
    estimate: LogGcdEstimate,
    baseline_formula_seconds: Optional[float],
) -> Optional[LogGcdConstraint]:
    if not estimate.usable or baseline_formula_seconds is None or baseline_formula_seconds <= 0:
        return None
    ratio = float(estimate.seconds) / float(baseline_formula_seconds)
    if ratio < 0.50 or ratio > 1.10:
        return None
    return LogGcdConstraint(
        observed_seconds=float(estimate.seconds),
        baseline_formula_seconds=float(baseline_formula_seconds),
        confidence=estimate.confidence,
        sample_count=estimate.sample_count,
    )
