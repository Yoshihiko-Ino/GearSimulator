from __future__ import annotations

import heapq
import logging
import ctypes
import math
import multiprocessing
import os
import time
from bisect import bisect_right
from collections import defaultdict
from dataclasses import dataclass, replace
from functools import lru_cache
from typing import Any, Callable, Dict, List, Optional, Sequence, Tuple

from .models import (
    FoodRecord,
    GEAR_SLOTS,
    Gearset,
    ItemRecord,
    ItemSelection,
    MateriaCategory,
    MateriaGrade,
    MateriaSlotSelection,
    SPELL_SPEED_JOBS,
)
from . import xivmath
from .gcd_analysis import LogGcdConstraint
from .utils import encode_progress_message, sim_log, sim_debug_enabled

logger = logging.getLogger(__name__)

# Stats that can be melded.
MELDABLE_STATS = {6, 19, 22, 27, 44, 45, 46}
COMBAT_FOOD_BONUS_STATS = {1, 2, 3, 4, 5, 6, 19, 22, 27, 44, 45, 46}
MAX_OPTIMIZATION_WORKERS = 16
AUTO_OPTIMIZATION_WORKERS_MAX = 8
PREVIEW_BATCH_SIZE = 32
UPPER_BOUND_BATCH_SIZE = 4
UPPER_BOUND_MAX_COMPOSITIONS = 250000
GEAR_SEARCH_REQUIRED_RESULTS = 2
SCORE_MODEL_VERSIONS = {
    "dmg100p": 1,
    "simdps": 1,
    "simdps_self": 1,
}

# Match XIVGear materia rules.
MATERIA_LEVEL_MAX_NORMAL = 12
MATERIA_LEVEL_MAX_OVERMELD = 11
MATERIA_ACCEPTABLE_OVERCAP_LOSS = 2


def score_tie_tolerance(mode: str) -> float:
    return 0.005 if str(mode or "") == "dmg100p" else 0.05

JOB_MELD_PARAM_INDEX = {
    "PLD": 1,
    "WAR": 1,
    "DRK": 1,
    "GNB": 1,
    "WHM": 6,
    "SCH": 6,
    "AST": 6,
    "SGE": 6,
    "BLM": 5,
    "SMN": 5,
    "RDM": 5,
    "PCT": 5,
    "MNK": 3,
    "SAM": 3,
    "DRG": 2,
    "RPR": 2,
    "NIN": 4,
    "VPR": 4,
    "BRD": 4,
    "MCH": 4,
    "DNC": 4,
}

STAT_ID_TO_ITEMLEVEL_FIELD = {
    1: "strength",
    2: "dexterity",
    3: "vitality",
    4: "intelligence",
    5: "mind",
    6: "piety",
    19: "tenacity",
    22: "directHitRate",
    27: "criticalHit",
    44: "determination",
    45: "skillSpeed",
    46: "spellSpeed",
}

MAIN_STAT_BY_JOB = {
    "PLD": 1,
    "WAR": 1,
    "DRK": 1,
    "GNB": 1,
    "MNK": 1,
    "DRG": 1,
    "SAM": 1,
    "RPR": 1,
    "VPR": 2,
    "BRD": 2,
    "MCH": 2,
    "DNC": 2,
    "NIN": 2,
    "WHM": 5,
    "SCH": 5,
    "AST": 5,
    "SGE": 5,
    "BLM": 4,
    "SMN": 4,
    "RDM": 4,
    "PCT": 4,
}
MAIN_STAT_LABELS = {
    1: "str",
    2: "dex",
    4: "int",
    5: "mnd",
}
SLOT_LABELS = {
    "weapon": "武器",
    "offhand": "サブ武器",
    "head": "頭",
    "body": "胴",
    "hands": "手",
    "legs": "脚",
    "feet": "足",
    "earrings": "耳",
    "necklace": "首",
    "bracelet": "腕",
    "ring1": "指輪1",
    "ring2": "指輪2",
    "ring": "指輪",
}


@dataclass(frozen=True)
class OptimizationWorkerContext:
    """Immutable inputs shared by all exact-optimization worker processes."""

    items_by_id: Dict[int, ItemRecord]
    materia_catalog: Dict[int, MateriaCategory]
    foods: List[Optional[FoodRecord]]
    casts: List[dict]
    fight_duration_ms: int
    cap_table: Dict[Tuple, int]
    damage_summary: Optional[Dict[str, object]] = None
    baseline_raw_stats: Optional[Dict[int, int]] = None
    baseline_items: Optional[Dict[str, ItemRecord]] = None
    baseline_gcd: Optional[float] = None
    gcd_constraint: Optional[LogGcdConstraint] = None
    job_mods: Optional[Dict[str, int]] = None
    baseline_food: Optional[FoodRecord] = None
    party_bonus: int = 0
    baseline_party_bonus: Optional[int] = None
    mode: str = "simdps"
    baseline_race: Optional[str] = None
    party_synergies: Optional[Dict[str, bool]] = None
    crit_rate_offset: float = 0.0
    dhit_rate_offset: float = 0.0


@dataclass(frozen=True)
class OptimizationRequest:
    request_id: int
    cache_key: Tuple
    gearset: Gearset
    selected_items: Dict[str, ItemRecord]
    no_meld_slots: set


@dataclass(frozen=True)
class PreviewCandidate:
    request_id: int
    selected_items: Dict[str, ItemRecord]
    raw_stats: Dict[int, int]


@dataclass(frozen=True)
class PreviewBatchRequest:
    request_id: int
    job: str
    target_gcd: Optional[float]
    race: Optional[str]
    level: int
    foods: Tuple[Optional[FoodRecord], ...]
    candidates: Tuple[PreviewCandidate, ...]


@dataclass(frozen=True)
class UpperBoundBatchRequest:
    request_id: int
    requests: Tuple[OptimizationRequest, ...]


def optimization_request_key(
    gearset: Gearset,
    selected_items: Optional[Dict[str, ItemRecord]] = None,
    no_meld_slots: Optional[set] = None,
) -> Tuple:
    key_slots = []
    for slot_name in GEAR_SLOTS:
        selection = (gearset.items or {}).get(slot_name)
        materia = (
            tuple((m.base_param, m.grade) for m in (selection.materia or []))
            if selection
            else tuple()
        )
        relic = (
            tuple(
                sorted(
                    (int(stat_id), int(value))
                    for stat_id, value in dict(
                        getattr(selection, "relic_stats", {}) or {}
                    ).items()
                    if int(value or 0) > 0
                )
            )
            if selection
            else tuple()
        )
        key_slots.append(
            (
                slot_name,
                selection.item_id if selection else None,
                materia,
                relic,
                bool(getattr(selection, "lock_item", False)) if selection else False,
                bool(getattr(selection, "lock_materia", False)) if selection else False,
            )
        )
    selected_signature = tuple(
        (
            slot_name,
            int(item.item_id),
            int(item.ilvl or 0),
            tuple(
                sorted(
                    (int(stat_id), int(value))
                    for stat_id, value in (item.base_params_hq or {}).items()
                )
            ),
            int(item.damage_phys or 0),
            int(item.damage_mag or 0),
            int(item.delay_ms or 0),
            int(item.materia_slots or 0),
            bool(item.overmeld),
        )
        for slot_name, item in sorted((selected_items or {}).items())
    )
    return (
        gearset.job,
        gearset.food_id,
        bool(getattr(gearset, "food_simulation", False)),
        float(gearset.target_gcd or 0.0),
        int(gearset.level or 0),
        tuple(key_slots),
        selected_signature,
        tuple(sorted(str(slot) for slot in (no_meld_slots or set()))),
    )


_PROCESS_OPTIMIZATION_CONTEXT: Optional[OptimizationWorkerContext] = None
_PROCESS_OPTIMIZATION_CANCEL_EVENT = None
_PROCESS_PREVIEW_EVAL_CONTEXTS: Dict[Tuple[int, str, str, int], object] = {}


def _init_optimization_process(
    context: OptimizationWorkerContext,
    cancel_event,
) -> None:
    global _PROCESS_OPTIMIZATION_CONTEXT, _PROCESS_OPTIMIZATION_CANCEL_EVENT
    _PROCESS_OPTIMIZATION_CONTEXT = context
    _PROCESS_OPTIMIZATION_CANCEL_EVENT = cancel_event
    _PROCESS_PREVIEW_EVAL_CONTEXTS.clear()


def _execute_optimization_request(
    request: OptimizationRequest,
    context: OptimizationWorkerContext,
    stop_event,
) -> Tuple[int, List[Tuple[Gearset, float, float]]]:
    if stop_event is not None and stop_event.is_set():
        return request.request_id, []
    results = optimize(
        request.gearset,
        context.items_by_id,
        context.materia_catalog,
        context.foods,
        context.casts,
        context.fight_duration_ms,
        context.cap_table,
        damage_summary=context.damage_summary,
        baseline_raw_stats=context.baseline_raw_stats,
        baseline_items=context.baseline_items,
        baseline_gcd=context.baseline_gcd,
        gcd_constraint=context.gcd_constraint,
        job_mods=context.job_mods,
        baseline_food=context.baseline_food,
        party_bonus=context.party_bonus,
        baseline_party_bonus=context.baseline_party_bonus,
        mode=context.mode,
        baseline_race=context.baseline_race,
        party_synergies=context.party_synergies,
        crit_rate_offset=context.crit_rate_offset,
        dhit_rate_offset=context.dhit_rate_offset,
        selected_items_override=request.selected_items,
        no_meld_slots=request.no_meld_slots,
        progress=None,
        stop_event=stop_event,
    )
    return request.request_id, results


def _run_optimization_process_request(
    request: OptimizationRequest,
) -> Tuple[int, List[Tuple[Gearset, float, float]]]:
    context = _PROCESS_OPTIMIZATION_CONTEXT
    if context is None:
        raise RuntimeError("Optimization worker context is not initialized")
    return _execute_optimization_request(
        request,
        context,
        _PROCESS_OPTIMIZATION_CANCEL_EVENT,
    )


def _preview_eval_context(
    request: PreviewBatchRequest,
    context: OptimizationWorkerContext,
):
    key = (
        id(context),
        request.job,
        str(request.race or ""),
        int(request.level),
    )
    cached = _PROCESS_PREVIEW_EVAL_CONTEXTS.get(key)
    if cached is not None:
        return cached
    prepared = prepare_score_eval_context(
        request.job,
        context.damage_summary,
        context.baseline_raw_stats,
        context.baseline_items,
        context.baseline_food,
        context.baseline_gcd,
        context.job_mods,
        context.party_bonus,
        context.baseline_party_bonus,
        request.race,
        context.baseline_race,
        context.party_synergies,
        context.mode,
        request.level,
    )
    _PROCESS_PREVIEW_EVAL_CONTEXTS[key] = prepared
    return prepared


def _execute_preview_batch_request(
    request: PreviewBatchRequest,
    context: OptimizationWorkerContext,
    stop_event,
) -> Tuple[int, List[Tuple[int, float, float, int]]]:
    eval_ctx = _preview_eval_context(request, context)
    results: List[Tuple[int, float, float, int]] = []
    for candidate in request.candidates:
        if stop_event is not None and stop_event.is_set():
            break
        best_score = float("-inf")
        best_gcd = 99.0
        best_food_index = -1
        for food_index, food in enumerate(request.foods):
            try:
                score, gcd = evaluate_score(
                    candidate.raw_stats,
                    request.job,
                    context.casts,
                    context.fight_duration_ms,
                    request.target_gcd,
                    damage_summary=context.damage_summary,
                    job_mods=context.job_mods,
                    food=food,
                    party_bonus=context.party_bonus,
                    baseline_raw_stats=context.baseline_raw_stats,
                    baseline_items=context.baseline_items,
                    selected_items=candidate.selected_items,
                    baseline_food=context.baseline_food,
                    mode=context.mode,
                    race=request.race,
                    baseline_party_bonus=context.baseline_party_bonus,
                    baseline_race=context.baseline_race,
                    party_synergies=context.party_synergies,
                    debug=False,
                    level=request.level,
                    crit_rate_offset=context.crit_rate_offset,
                    dhit_rate_offset=context.dhit_rate_offset,
                    eval_ctx=eval_ctx,
                )
            except Exception:
                logger.exception(
                    "Failed to evaluate gear-search preview candidate "
                    "(food_id=%s, items=%s)",
                    int(food.food_id or 0) if food else 0,
                    {
                        slot: int(item.item_id)
                        for slot, item in candidate.selected_items.items()
                    },
                )
                score, gcd = 0.0, 99.0
            if score > best_score + 1e-9 or (
                abs(score - best_score) <= 1e-9 and gcd < best_gcd
            ):
                best_score = float(score)
                best_gcd = float(gcd)
                best_food_index = food_index
        if best_score == float("-inf"):
            best_score, best_gcd = 0.0, 99.0
        results.append(
            (candidate.request_id, best_score, best_gcd, best_food_index)
        )
    return request.request_id, results


def _run_preview_process_request(
    request: PreviewBatchRequest,
) -> Tuple[int, List[Tuple[int, float, float, int]]]:
    context = _PROCESS_OPTIMIZATION_CONTEXT
    if context is None:
        raise RuntimeError("Optimization worker context is not initialized")
    return _execute_preview_batch_request(
        request,
        context,
        _PROCESS_OPTIMIZATION_CANCEL_EVENT,
    )


def _execute_upper_bound_batch_request(
    request: UpperBoundBatchRequest,
    context: OptimizationWorkerContext,
    stop_event,
) -> Tuple[int, List[Tuple[Tuple, float]]]:
    values: List[Tuple[Tuple, float]] = []
    for candidate in request.requests:
        if stop_event is not None and stop_event.is_set():
            break
        try:
            bound = optimization_score_upper_bound(
                candidate.gearset,
                candidate.selected_items,
                candidate.no_meld_slots,
                context,
                stop_event=stop_event,
            )
        except Exception:
            logger.exception(
                "Failed to calculate optimization upper bound (request_id=%s)",
                candidate.request_id,
            )
            bound = math.inf
        values.append((candidate.cache_key, float(bound)))
    return request.request_id, values


def _run_upper_bound_process_request(
    request: UpperBoundBatchRequest,
) -> Tuple[int, List[Tuple[Tuple, float]]]:
    context = _PROCESS_OPTIMIZATION_CONTEXT
    if context is None:
        raise RuntimeError("Optimization worker context is not initialized")
    return _execute_upper_bound_batch_request(
        request,
        context,
        _PROCESS_OPTIMIZATION_CANCEL_EVENT,
    )


def _windows_memory_gb() -> Tuple[Optional[float], Optional[float]]:
    if os.name != "nt":
        return None, None

    class MemoryStatusEx(ctypes.Structure):
        _fields_ = [
            ("dwLength", ctypes.c_ulong),
            ("dwMemoryLoad", ctypes.c_ulong),
            ("ullTotalPhys", ctypes.c_ulonglong),
            ("ullAvailPhys", ctypes.c_ulonglong),
            ("ullTotalPageFile", ctypes.c_ulonglong),
            ("ullAvailPageFile", ctypes.c_ulonglong),
            ("ullTotalVirtual", ctypes.c_ulonglong),
            ("ullAvailVirtual", ctypes.c_ulonglong),
            ("ullAvailExtendedVirtual", ctypes.c_ulonglong),
        ]

    status = MemoryStatusEx()
    status.dwLength = ctypes.sizeof(status)
    try:
        if not ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(status)):
            return None, None
    except Exception:
        return None, None
    gb = float(1024**3)
    return status.ullTotalPhys / gb, status.ullAvailPhys / gb


def recommended_optimization_workers() -> int:
    """Return a conservative CPU-process count without adding a psutil dependency."""

    override = str(os.environ.get("GEARSIM_WORKERS", "")).strip()
    if override:
        try:
            return max(1, min(MAX_OPTIMIZATION_WORKERS, int(override)))
        except ValueError:
            logger.warning("Ignored invalid GEARSIM_WORKERS=%r", override)

    logical = max(1, int(os.cpu_count() or 1))
    estimated_physical = max(1, logical // 2) if logical >= 4 else logical
    cpu_limit = min(AUTO_OPTIMIZATION_WORKERS_MAX, estimated_physical)
    total_gb, available_gb = _windows_memory_gb()
    if total_gb is not None and available_gb is not None:
        if total_gb < 12.0 or available_gb < 4.0:
            return 1
        if total_gb < 24.0 or available_gb < 8.0:
            return min(cpu_limit, 4)
        if available_gb < 14.0:
            return min(cpu_limit, 6)
    return max(1, cpu_limit)


def _process_safe_value(value):
    if isinstance(value, dict):
        return {
            _process_safe_value(key): _process_safe_value(item)
            for key, item in value.items()
        }
    if isinstance(value, list):
        return [_process_safe_value(item) for item in value]
    if isinstance(value, tuple):
        return tuple(_process_safe_value(item) for item in value)
    if isinstance(value, set):
        return {_process_safe_value(item) for item in value}
    return value


class OptimizationSession:
    """Own one spawn process pool and an exact-result cache for a full GUI run."""

    def __init__(
        self,
        context: OptimizationWorkerContext,
        *,
        worker_count: Optional[int] = None,
    ) -> None:
        self.context = replace(
            context,
            damage_summary=_process_safe_value(context.damage_summary),
        )
        self.worker_count = max(
            1,
            min(
                MAX_OPTIMIZATION_WORKERS,
                int(worker_count or recommended_optimization_workers()),
            ),
        )
        self._mp_context = multiprocessing.get_context("spawn")
        self._cancel_event = None
        self._pool = None
        self._cache: Dict[Tuple, Optional[Tuple[Gearset, float, float]]] = {}
        self._variant_cache: Dict[Tuple, Tuple[Tuple[Gearset, float, float], ...]] = {}
        self._upper_bound_cache: Dict[Tuple, float] = {}
        self._parallel_failed = False

    @property
    def parallel_enabled(self) -> bool:
        return self.worker_count > 1 and not self._parallel_failed

    def __enter__(self) -> "OptimizationSession":
        if self.worker_count <= 1:
            return self
        try:
            self._cancel_event = self._mp_context.Event()
            self._pool = self._mp_context.Pool(
                processes=self.worker_count,
                initializer=_init_optimization_process,
                initargs=(self.context, self._cancel_event),
            )
        except Exception:
            logger.exception("Failed to start optimization process pool; using serial fallback")
            self._parallel_failed = True
            self._terminate_pool()
        return self

    def __exit__(self, exc_type, exc, traceback) -> None:
        if exc_type is not None:
            self.cancel()
        else:
            self.close()

    def _terminate_pool(self) -> None:
        pool = self._pool
        self._pool = None
        if pool is None:
            return
        try:
            pool.terminate()
        finally:
            pool.join()

    def close(self) -> None:
        pool = self._pool
        self._pool = None
        if pool is None:
            return
        pool.close()
        pool.join()

    def cancel(self) -> None:
        if self._cancel_event is not None:
            self._cancel_event.set()
        self._terminate_pool()

    def cached_variants(
        self,
        cache_key: Tuple,
    ) -> Tuple[Tuple[Gearset, float, float], ...]:
        return self._variant_cache.get(cache_key, ())

    def _store_optimization_results(
        self,
        request: OptimizationRequest,
        variants: Sequence[Tuple[Gearset, float, float]],
        results: Dict[Tuple, Optional[Tuple[Gearset, float, float]]],
    ) -> None:
        stored_variants = tuple(variants)
        best = stored_variants[0] if stored_variants else None
        self._variant_cache[request.cache_key] = stored_variants
        self._cache[request.cache_key] = best
        results[request.cache_key] = best

    def optimize_batch(
        self,
        requests: Sequence[OptimizationRequest],
        *,
        stop_event=None,
        progress: Optional[Callable[[int, int, float, Optional[float]], None]] = None,
    ) -> Dict[Tuple, Optional[Tuple[Gearset, float, float]]]:
        if not requests:
            return {}

        results: Dict[Tuple, Optional[Tuple[Gearset, float, float]]] = {}
        unique_pending: List[OptimizationRequest] = []
        seen_pending: set = set()
        for request in requests:
            if request.cache_key in self._cache:
                results[request.cache_key] = self._cache[request.cache_key]
            elif request.cache_key not in seen_pending:
                seen_pending.add(request.cache_key)
                unique_pending.append(request)

        total = len(unique_pending)
        cache_hits = max(0, len(requests) - total)
        if total == 0:
            if progress:
                progress(0, 0, 0.0, 0.0)
            return results

        started = time.perf_counter()

        def report(completed: int) -> None:
            if not progress:
                return
            elapsed = max(0.0, time.perf_counter() - started)
            eta = None
            if completed > 0:
                eta = max(0.0, elapsed * (total - completed) / completed)
            progress(completed, total, elapsed, eta)

        if not self.parallel_enabled or self._pool is None:
            for completed, request in enumerate(unique_pending, 1):
                if stop_event is not None and stop_event.is_set():
                    break
                _request_id, variants = _execute_optimization_request(
                    request,
                    self.context,
                    stop_event,
                )
                self._store_optimization_results(request, variants, results)
                report(completed)
            if sim_debug_enabled():
                sim_log(
                    f"[parallel-opt] mode=serial workers=1 requests={len(requests)} "
                    f"evaluated={total} cache_hits={cache_hits} "
                    f"elapsed={time.perf_counter() - started:.3f}s"
                )
            return results

        async_results = {
            request.request_id: (request, self._pool.apply_async(_run_optimization_process_request, (request,)))
            for request in unique_pending
        }
        completed = 0
        last_report = 0.0
        parallel_error: Optional[BaseException] = None
        while async_results:
            if stop_event is not None and stop_event.is_set():
                self.cancel()
                return results
            made_progress = False
            for request_id, (request, async_result) in list(async_results.items()):
                if not async_result.ready():
                    continue
                try:
                    _result_id, variants = async_result.get()
                except BaseException as exc:
                    parallel_error = exc
                    break
                self._store_optimization_results(request, variants, results)
                async_results.pop(request_id, None)
                completed += 1
                made_progress = True
            if parallel_error is not None:
                break
            now = time.perf_counter()
            if made_progress or now - last_report >= 1.0:
                report(completed)
                last_report = now
            if async_results and not made_progress:
                time.sleep(0.02)

        if parallel_error is None:
            report(completed)
            if sim_debug_enabled():
                sim_log(
                    f"[parallel-opt] mode=process workers={self.worker_count} "
                    f"requests={len(requests)} evaluated={total} cache_hits={cache_hits} "
                    f"elapsed={time.perf_counter() - started:.3f}s"
                )
            return results

        logger.error(
            "Optimization process pool failed; retrying unfinished candidates serially: %s",
            parallel_error,
            exc_info=(
                type(parallel_error),
                parallel_error,
                parallel_error.__traceback__,
            ),
        )
        unresolved = [request for request, _result in async_results.values()]
        self._parallel_failed = True
        self._terminate_pool()
        for request in unresolved:
            if stop_event is not None and stop_event.is_set():
                break
            _request_id, variants = _execute_optimization_request(
                request,
                self.context,
                stop_event,
            )
            self._store_optimization_results(request, variants, results)
            completed += 1
            report(completed)
        return results

    def evaluate_preview_batch(
        self,
        candidates: Sequence[PreviewCandidate],
        *,
        job: str,
        target_gcd: Optional[float],
        race: Optional[str],
        level: int,
        foods: Sequence[Optional[FoodRecord]],
        stop_event=None,
        progress: Optional[Callable[[int, int, float, Optional[float]], None]] = None,
    ) -> Dict[int, Tuple[float, float, int]]:
        if not candidates:
            return {}
        batches = [
            PreviewBatchRequest(
                request_id=batch_id,
                job=job,
                target_gcd=target_gcd,
                race=race,
                level=level,
                foods=tuple(foods),
                candidates=tuple(candidates[offset : offset + PREVIEW_BATCH_SIZE]),
            )
            for batch_id, offset in enumerate(
                range(0, len(candidates), PREVIEW_BATCH_SIZE)
            )
        ]
        total = len(candidates)
        results: Dict[int, Tuple[float, float, int]] = {}
        started = time.perf_counter()

        def report(completed: int) -> None:
            if not progress:
                return
            elapsed = max(0.0, time.perf_counter() - started)
            eta = None
            if completed > 0:
                eta = max(0.0, elapsed * (total - completed) / completed)
            progress(completed, total, elapsed, eta)

        def consume(
            values: Sequence[Tuple[int, float, float, int]],
        ) -> None:
            for request_id, score, gcd, food_index in values:
                results[request_id] = (score, gcd, food_index)

        if not self.parallel_enabled or self._pool is None:
            completed = 0
            for batch in batches:
                if stop_event is not None and stop_event.is_set():
                    break
                _batch_id, values = _execute_preview_batch_request(
                    batch,
                    self.context,
                    stop_event,
                )
                consume(values)
                completed += len(values)
                report(completed)
            return results

        async_results = {
            batch.request_id: (
                batch,
                self._pool.apply_async(_run_preview_process_request, (batch,)),
            )
            for batch in batches
        }
        completed = 0
        last_report = 0.0
        parallel_error: Optional[BaseException] = None
        while async_results:
            if stop_event is not None and stop_event.is_set():
                self.cancel()
                return results
            made_progress = False
            for batch_id, (batch, async_result) in list(async_results.items()):
                if not async_result.ready():
                    continue
                try:
                    _result_id, values = async_result.get()
                except BaseException as exc:
                    parallel_error = exc
                    break
                consume(values)
                async_results.pop(batch_id, None)
                completed += len(values)
                made_progress = True
            if parallel_error is not None:
                break
            now = time.perf_counter()
            if made_progress or now - last_report >= 1.0:
                report(completed)
                last_report = now
            if async_results and not made_progress:
                time.sleep(0.02)

        if parallel_error is None:
            report(completed)
            if sim_debug_enabled():
                sim_log(
                    f"[parallel-preview] workers={self.worker_count} "
                    f"candidates={total} batches={len(batches)} "
                    f"elapsed={time.perf_counter() - started:.3f}s"
                )
            return results

        logger.error(
            "Preview process pool failed; retrying unfinished batches serially: %s",
            parallel_error,
            exc_info=(
                type(parallel_error),
                parallel_error,
                parallel_error.__traceback__,
            ),
        )
        unresolved = [batch for batch, _result in async_results.values()]
        self._parallel_failed = True
        self._terminate_pool()
        for batch in unresolved:
            if stop_event is not None and stop_event.is_set():
                break
            _batch_id, values = _execute_preview_batch_request(
                batch,
                self.context,
                stop_event,
            )
            consume(values)
            completed += len(values)
            report(completed)
        return results

    def evaluate_upper_bounds(
        self,
        requests: Sequence[OptimizationRequest],
        *,
        stop_event=None,
        progress: Optional[Callable[[int, int, float, Optional[float]], None]] = None,
    ) -> Dict[Tuple, float]:
        if not requests:
            return {}

        results: Dict[Tuple, float] = {}
        pending: List[OptimizationRequest] = []
        seen: set = set()
        for request in requests:
            cached = self._upper_bound_cache.get(request.cache_key)
            if cached is not None:
                results[request.cache_key] = cached
            elif request.cache_key not in seen:
                seen.add(request.cache_key)
                pending.append(request)
        if not pending:
            return results

        batches = [
            UpperBoundBatchRequest(
                request_id=batch_id,
                requests=tuple(pending[offset : offset + UPPER_BOUND_BATCH_SIZE]),
            )
            for batch_id, offset in enumerate(
                range(0, len(pending), UPPER_BOUND_BATCH_SIZE)
            )
        ]
        total = len(pending)
        completed = 0
        started = time.perf_counter()

        def report() -> None:
            if not progress:
                return
            elapsed = max(0.0, time.perf_counter() - started)
            eta = None
            if completed > 0:
                eta = max(0.0, elapsed * (total - completed) / completed)
            progress(completed, total, elapsed, eta)

        def consume(values: Sequence[Tuple[Tuple, float]]) -> None:
            nonlocal completed
            for cache_key, bound in values:
                safe_bound = float(bound)
                self._upper_bound_cache[cache_key] = safe_bound
                results[cache_key] = safe_bound
                completed += 1

        if not self.parallel_enabled or self._pool is None:
            for batch in batches:
                if stop_event is not None and stop_event.is_set():
                    break
                _batch_id, values = _execute_upper_bound_batch_request(
                    batch,
                    self.context,
                    stop_event,
                )
                consume(values)
                report()
            return results

        async_results = {
            batch.request_id: (
                batch,
                self._pool.apply_async(
                    _run_upper_bound_process_request,
                    (batch,),
                ),
            )
            for batch in batches
        }
        parallel_error: Optional[BaseException] = None
        last_report = 0.0
        while async_results:
            if stop_event is not None and stop_event.is_set():
                self.cancel()
                return results
            made_progress = False
            for batch_id, (_batch, async_result) in list(async_results.items()):
                if not async_result.ready():
                    continue
                try:
                    _result_id, values = async_result.get()
                except BaseException as exc:
                    parallel_error = exc
                    break
                consume(values)
                async_results.pop(batch_id, None)
                made_progress = True
            if parallel_error is not None:
                break
            now = time.perf_counter()
            if made_progress or now - last_report >= 1.0:
                report()
                last_report = now
            if async_results and not made_progress:
                time.sleep(0.02)

        if parallel_error is None:
            report()
            if sim_debug_enabled():
                sim_log(
                    f"[parallel-bound] workers={self.worker_count} "
                    f"candidates={total} elapsed={time.perf_counter() - started:.3f}s"
                )
            return results

        logger.error(
            "Upper-bound process pool failed; retrying unfinished batches serially: %s",
            parallel_error,
            exc_info=(
                type(parallel_error),
                parallel_error,
                parallel_error.__traceback__,
            ),
        )
        unresolved = [batch for batch, _result in async_results.values()]
        self._parallel_failed = True
        self._terminate_pool()
        for batch in unresolved:
            if stop_event is not None and stop_event.is_set():
                break
            _batch_id, values = _execute_upper_bound_batch_request(
                batch,
                self.context,
                stop_event,
            )
            consume(values)
            report()
        return results

@dataclass(frozen=True)
class ActionReplayEntry:
    action_id: int
    bucket_damage: float
    norm_type: str
    is_dot: bool
    base_expected: float
    dmg_mult: float
    crit_bonus: float
    dh_bonus: float
    force_crit: bool
    force_dh: bool
    ext_dmg_mult: float
    ext_crit_bonus: float
    ext_dh_bonus: float
    profile_id: int


@dataclass(frozen=True)
class BucketReplayEntry:
    bucket_damage: float
    norm_type: str
    is_dot: bool
    base_expected: float
    legacy_gcd_adjust: bool


@dataclass
class ScoreEvalContext:
    level_value: int
    level_data: Any
    base_comp: Optional[Any] = None
    baseline_gcd: Optional[float] = None
    action_entries: Optional[List[ActionReplayEntry]] = None
    action_profiles: Optional[List[ActionReplayEntry]] = None
    bucket_entries: Optional[List[BucketReplayEntry]] = None
    ability_names: Optional[Dict[int, str]] = None
    total_damage_all: float = 0.0
    min_ts: Optional[int] = None
    max_ts: Optional[int] = None


@dataclass(frozen=True)
class GearSearchScoreContext:
    main_stat_id: int
    speed_stat_id: int
    target_gcd: Optional[float]
    required_item_speed: Optional[int]
    stat_weights: Optional[Dict[int, float]] = None
    mode: str = "simdps"


class ExactStateNode:
    __slots__ = ("parent", "slot", "melds")

    def __init__(
        self,
        parent: Optional["ExactStateNode"],
        slot: str,
        melds: Tuple[MateriaSlotSelection, ...],
    ) -> None:
        self.parent = parent
        self.slot = slot
        self.melds = melds


def _expand_exact_state_stage(
    exact_states: Dict[Tuple[int, ...], Optional[ExactStateNode]],
    combo_entries: Sequence[
        Tuple[Tuple[int, ...], Tuple[MateriaSlotSelection, ...]]
    ],
    slot: str,
    tuple_length: int,
    *,
    strict_gcd_mode: bool,
    required_speed_stat: int,
    speed_tuple_index: int,
    base_speed_raw: int,
    remaining_speed: int,
    level_base_sub: int,
    max_food_speed_bonus: Callable[[int], int],
    enforce_state_limit: bool,
    state_limit: int,
) -> Tuple[Dict[Tuple[int, ...], ExactStateNode], bool]:
    new_map: Dict[Tuple[int, ...], ExactStateNode] = {}
    limit_hit = False

    if tuple_length == 4:
        for agg_stats, parent_node in exact_states.items():
            left0, left1, left2, left3 = agg_stats
            for add_stats, melds in combo_entries:
                merged_stats = (
                    left0 + add_stats[0],
                    left1 + add_stats[1],
                    left2 + add_stats[2],
                    left3 + add_stats[3],
                )
                if strict_gcd_mode:
                    speed_raw = base_speed_raw + (
                        merged_stats[speed_tuple_index]
                        if speed_tuple_index >= 0
                        else 0
                    )
                    max_raw_speed = speed_raw + remaining_speed
                    max_speed_stat = (
                        max_raw_speed
                        + max_food_speed_bonus(max_raw_speed)
                        + level_base_sub
                    )
                    if max_speed_stat < required_speed_stat:
                        continue
                if merged_stats in new_map:
                    continue
                new_map[merged_stats] = ExactStateNode(parent_node, slot, melds)
                if enforce_state_limit and len(new_map) > state_limit:
                    limit_hit = True
                    break
            if limit_hit:
                break
        return new_map, limit_hit

    if tuple_length == 5:
        for agg_stats, parent_node in exact_states.items():
            left0, left1, left2, left3, left4 = agg_stats
            for add_stats, melds in combo_entries:
                merged_stats = (
                    left0 + add_stats[0],
                    left1 + add_stats[1],
                    left2 + add_stats[2],
                    left3 + add_stats[3],
                    left4 + add_stats[4],
                )
                if strict_gcd_mode:
                    speed_raw = base_speed_raw + (
                        merged_stats[speed_tuple_index]
                        if speed_tuple_index >= 0
                        else 0
                    )
                    max_raw_speed = speed_raw + remaining_speed
                    max_speed_stat = (
                        max_raw_speed
                        + max_food_speed_bonus(max_raw_speed)
                        + level_base_sub
                    )
                    if max_speed_stat < required_speed_stat:
                        continue
                if merged_stats in new_map:
                    continue
                new_map[merged_stats] = ExactStateNode(parent_node, slot, melds)
                if enforce_state_limit and len(new_map) > state_limit:
                    limit_hit = True
                    break
            if limit_hit:
                break
        return new_map, limit_hit

    for agg_stats, parent_node in exact_states.items():
        for add_stats, melds in combo_entries:
            merged_stats = tuple(
                agg_stats[index] + add_stats[index]
                for index in range(tuple_length)
            )
            if strict_gcd_mode:
                speed_raw = base_speed_raw + (
                    merged_stats[speed_tuple_index]
                    if speed_tuple_index >= 0
                    else 0
                )
                max_raw_speed = speed_raw + remaining_speed
                max_speed_stat = (
                    max_raw_speed
                    + max_food_speed_bonus(max_raw_speed)
                    + level_base_sub
                )
                if max_speed_stat < required_speed_stat:
                    continue
            if merged_stats in new_map:
                continue
            new_map[merged_stats] = ExactStateNode(parent_node, slot, melds)
            if enforce_state_limit and len(new_map) > state_limit:
                limit_hit = True
                break
        if limit_hit:
            break
    return new_map, limit_hit


def _expand_packed_exact_state_stage(
    exact_states: Dict[int, Optional[ExactStateNode]],
    combo_entries: Sequence[Tuple[int, Tuple[MateriaSlotSelection, ...]]],
    slot: str,
    *,
    strict_gcd_mode: bool,
    required_speed_stat: int,
    speed_shift: int,
    lane_mask: int,
    base_speed_raw: int,
    remaining_speed: int,
    level_base_sub: int,
    max_food_speed_bonus: Callable[[int], int],
    enforce_state_limit: bool,
    state_limit: int,
) -> Tuple[Dict[int, ExactStateNode], bool]:
    new_map: Dict[int, ExactStateNode] = {}
    limit_hit = False
    state_count = 0
    if not strict_gcd_mode:
        for agg_stats, parent_node in exact_states.items():
            for add_stats, melds in combo_entries:
                merged_stats = agg_stats + add_stats
                if merged_stats in new_map:
                    continue
                new_map[merged_stats] = ExactStateNode(parent_node, slot, melds)
                state_count += 1
                if enforce_state_limit and state_count > state_limit:
                    limit_hit = True
                    break
            if limit_hit:
                break
        return new_map, limit_hit

    for agg_stats, parent_node in exact_states.items():
        for add_stats, melds in combo_entries:
            merged_stats = agg_stats + add_stats
            speed_raw = base_speed_raw + (
                (merged_stats >> speed_shift) & lane_mask
            )
            max_raw_speed = speed_raw + remaining_speed
            max_speed_stat = (
                max_raw_speed
                + max_food_speed_bonus(max_raw_speed)
                + level_base_sub
            )
            if max_speed_stat < required_speed_stat:
                continue
            if merged_stats in new_map:
                continue
            new_map[merged_stats] = ExactStateNode(parent_node, slot, melds)
            state_count += 1
            if enforce_state_limit and state_count > state_limit:
                limit_hit = True
                break
        if limit_hit:
            break
    return new_map, limit_hit

JOB_ALLOWED_STATS = {
    "PLD": {27, 22, 44, 19, 45},
    "WAR": {27, 22, 44, 19, 45},
    "DRK": {27, 22, 44, 19, 45},
    "GNB": {27, 22, 44, 19, 45},
    "WHM": {27, 22, 44, 46, 6},
    "SCH": {27, 22, 44, 46, 6},
    "AST": {27, 22, 44, 46, 6},
    "SGE": {27, 22, 44, 46, 6},
    "BLM": {27, 22, 44, 46},
    "SMN": {27, 22, 44, 46},
    "RDM": {27, 22, 44, 46},
    "PCT": {27, 22, 44, 46},
    "MNK": {27, 22, 44, 45},
    "DRG": {27, 22, 44, 45},
    "NIN": {27, 22, 44, 45},
    "SAM": {27, 22, 44, 45},
    "RPR": {27, 22, 44, 45},
    "VPR": {27, 22, 44, 45},
    "BRD": {27, 22, 44, 45},
    "MCH": {27, 22, 44, 45},
    "DNC": {27, 22, 44, 45},
}

RANGED_HEALER_JOBS = {
    "WHM", "SCH", "AST", "SGE", "BLM", "SMN", "RDM", "PCT", "BRD", "MCH", "DNC",
}

SYNERGY_KEYS = ("dnc", "brd", "drg", "mnk", "rpr", "nin", "rdm", "pct", "ast", "sch")
SYNERGY_JOB_TO_KEY = {
    "DNC": "dnc",
    "BRD": "brd",
    "DRG": "drg",
    "MNK": "mnk",
    "RPR": "rpr",
    "NIN": "nin",
    "RDM": "rdm",
    "PCT": "pct",
    "AST": "ast",
    "SCH": "sch",
}


def allowed_meld_stats(job: str) -> set:
    return JOB_ALLOWED_STATS.get(job, MELDABLE_STATS)


def normalized_level(level: Optional[int]) -> int:
    return xivmath.normalize_supported_level(level)


def level_stats(level: Optional[int]) -> xivmath.LevelStats:
    return xivmath.LEVEL_STATS[normalized_level(level)]


def gearset_level(gearset: Optional[Gearset]) -> int:
    if not gearset:
        return normalized_level(None)
    return normalized_level(getattr(gearset, "level", None))


def _normalize_attack_type_for_job(job: str, attack_type: str) -> str:
    if attack_type in {"Spell", "Weaponskill", "Auto-attack"}:
        return attack_type
    if job in SPELL_SPEED_JOBS:
        return "Spell"
    return "Weaponskill"


def prepare_score_eval_context(
    job: str,
    damage_summary: Optional[Dict[str, object]],
    baseline_raw_stats: Optional[Dict[int, int]],
    baseline_items: Optional[Dict[str, ItemRecord]],
    baseline_food: Optional[FoodRecord],
    baseline_gcd: Optional[float],
    job_mods: Optional[Dict[str, int]],
    party_bonus: int,
    baseline_party_bonus: Optional[int],
    race: Optional[str],
    baseline_race: Optional[str],
    party_synergies: Optional[Dict[str, bool]],
    mode: str,
    level: int,
) -> ScoreEvalContext:
    level_value = normalized_level(level)
    level_data = level_stats(level_value)
    ctx = ScoreEvalContext(
        level_value=level_value,
        level_data=level_data,
        baseline_gcd=baseline_gcd,
    )
    if (
        not damage_summary
        or not baseline_raw_stats
        or baseline_items is None
        or job_mods is None
    ):
        return ctx

    base_wd_phys, base_wd_mag, base_delay = _weapon_params(baseline_items)
    base_party = party_bonus if baseline_party_bonus is None else baseline_party_bonus
    base_race = baseline_race if baseline_race is not None else race
    base_comp = xivmath.build_computed_stats(
        job,
        baseline_raw_stats,
        job_mods,
        baseline_food.bonuses if baseline_food else None,
        base_party,
        base_wd_phys,
        base_wd_mag,
        base_delay,
        race=base_race,
        level=level_value,
    )
    ctx.base_comp = base_comp
    ctx.ability_names = damage_summary.get("ability_names") or {}
    ctx.total_damage_all = float(
        damage_summary.get("total_amount") or damage_summary.get("total_damage") or 0.0
    )
    ctx.min_ts = damage_summary.get("min_ts")
    ctx.max_ts = damage_summary.get("max_ts")

    ability_buckets = damage_summary.get("ability_buckets") or {}
    if mode in {"simdps", "simdps_self"} and ability_buckets:
        ability_buckets = _apply_party_synergy_to_ability_buckets(
            damage_summary,
            job,
            party_synergies,
            debug=False,
        )
    if ability_buckets:
        action_entries: List[ActionReplayEntry] = []
        action_profiles: List[ActionReplayEntry] = []
        action_profile_ids: Dict[Tuple[object, ...], int] = {}
        for key, bucket_damage in ability_buckets.items():
            if not bucket_damage:
                continue
            crit_bonus = 0.0
            dh_bonus = 0.0
            dmg_mult = 1.0
            force_crit = False
            force_dh = False
            ext_dmg_mult = 1.0
            ext_crit_bonus = 0.0
            ext_dh_bonus = 0.0
            if isinstance(key, tuple) and len(key) >= 8:
                action_id, attack_type, is_dot = key[0], key[1], key[2]
                dmg_mult = float(key[3])
                crit_bonus = float(key[4])
                dh_bonus = float(key[5])
                force_crit = bool(key[6])
                force_dh = bool(key[7])
                if len(key) >= 11:
                    ext_dmg_mult = float(key[8])
                    ext_crit_bonus = float(key[9])
                    ext_dh_bonus = float(key[10])
            elif isinstance(key, tuple) and len(key) >= 3:
                action_id, attack_type, is_dot = key[0], key[1], key[2]
            else:
                continue
            norm_type = _normalize_attack_type_for_job(job, attack_type)
            base_expected = xivmath.expected_damage_per_potency(
                base_comp,
                norm_type,
                bool(is_dot),
                auto_dh=force_dh,
                auto_crit=force_crit,
                crit_chance_bonus=crit_bonus,
                dhit_chance_bonus=dh_bonus,
                damage_multiplier=dmg_mult,
            )
            profile_key = (
                norm_type,
                bool(is_dot),
                force_crit,
                force_dh,
                crit_bonus + ext_crit_bonus,
                dh_bonus + ext_dh_bonus,
                dmg_mult * ext_dmg_mult,
            )
            profile_id = action_profile_ids.get(profile_key)
            is_new_profile = profile_id is None
            if profile_id is None:
                profile_id = len(action_profiles)
                action_profile_ids[profile_key] = profile_id
            entry = ActionReplayEntry(
                action_id=int(action_id),
                bucket_damage=float(bucket_damage),
                norm_type=norm_type,
                is_dot=bool(is_dot),
                base_expected=base_expected,
                dmg_mult=dmg_mult,
                crit_bonus=crit_bonus,
                dh_bonus=dh_bonus,
                force_crit=force_crit,
                force_dh=force_dh,
                ext_dmg_mult=ext_dmg_mult,
                ext_crit_bonus=ext_crit_bonus,
                ext_dh_bonus=ext_dh_bonus,
                profile_id=profile_id,
            )
            action_entries.append(entry)
            if is_new_profile:
                action_profiles.append(entry)
        ctx.action_entries = action_entries
        ctx.action_profiles = action_profiles
        return ctx

    bucket_entries: List[BucketReplayEntry] = []
    for key, bucket_damage in (damage_summary.get("buckets") or {}).items():
        if not bucket_damage:
            continue
        attack_type, is_dot = key
        norm_type = _normalize_attack_type_for_job(job, attack_type)
        base_expected = xivmath.expected_damage_per_potency(base_comp, norm_type, bool(is_dot))
        bucket_entries.append(
            BucketReplayEntry(
                bucket_damage=float(bucket_damage),
                norm_type=norm_type,
                is_dot=bool(is_dot),
                base_expected=base_expected,
                legacy_gcd_adjust=bool(
                    attack_type in {"Spell", "Weaponskill"} and not is_dot
                ),
            )
        )
    if bucket_entries and ctx.baseline_gcd is None:
        if job in SPELL_SPEED_JOBS:
            ctx.baseline_gcd = xivmath.sps_to_gcd(2.5, level_data, base_comp.spellspeed)
        else:
            ctx.baseline_gcd = xivmath.sks_to_gcd(2.5, level_data, base_comp.skillspeed)
    ctx.bucket_entries = bucket_entries
    return ctx


def _clone_gearset_with_swapped_item(
    gearset: Gearset,
    slot_name: str,
    item_id: int,
    relic_stats: Optional[Dict[int, int]] = None,
) -> Gearset:
    items = dict(gearset.items or {})
    existing = items.get(slot_name)
    items[slot_name] = ItemSelection(
        item_id=item_id,
        materia=[],
        relic_stats=dict(relic_stats or {}),
        lock_item=bool(getattr(existing, "lock_item", False)),
        lock_materia=bool(getattr(existing, "lock_materia", False)),
        excluded_item_ids=list(getattr(existing, "excluded_item_ids", []) or []),
    )
    return Gearset(
        job=gearset.job,
        items=items,
        food_id=gearset.food_id,
        food_simulation=bool(getattr(gearset, "food_simulation", False)),
        target_gcd=gearset.target_gcd,
        note=gearset.note,
        race=gearset.race,
        level=gearset_level(gearset),
    )


def _reconstruct_exact_meld_map(node: Optional[ExactStateNode]) -> Dict[str, List[MateriaSlotSelection]]:
    meld_map: Dict[str, List[MateriaSlotSelection]] = {}
    current = node
    while current is not None:
        meld_map[current.slot] = list(current.melds)
        current = current.parent
    return meld_map


def _selection_lock_item(selection: Optional[ItemSelection]) -> bool:
    return bool(getattr(selection, "lock_item", False))


def _selection_lock_materia(selection: Optional[ItemSelection]) -> bool:
    return bool(getattr(selection, "lock_materia", False))


def _gear_search_item_score(
    item: ItemRecord,
    job: str,
    target_gcd: Optional[float],
    level: int,
    score_context: Optional[GearSearchScoreContext] = None,
) -> float:
    weapon_damage = max(int(item.damage_phys or 0), int(item.damage_mag or 0))
    meld_slots = total_meld_slots_for_item(item)
    return _gear_search_state_score(
        item.base_params_hq or {},
        job,
        target_gcd,
        level,
        weapon_damage=weapon_damage,
        meld_capacity=meld_slots,
        score_context=score_context,
    )


def _prepare_gear_search_score_context(
    job: str,
    target_gcd: Optional[float],
    level: int,
    *,
    mode: str = "simdps",
    stat_weights: Optional[Dict[int, float]] = None,
) -> GearSearchScoreContext:
    main_stat_id = MAIN_STAT_BY_JOB.get(job, 4)
    speed_stat_id = 46 if job in SPELL_SPEED_JOBS else 45
    required_speed = required_speed_stat_for_target_gcd(job, target_gcd, level=level)
    required_item_speed = None
    if required_speed is not None:
        required_item_speed = max(0, int(required_speed) - int(level_stats(level).base_sub))
    if stat_weights is None:
        stat_weights = {
            27: 1.45,
            22: 1.25,
            44: 1.10,
            45: 1.00,
            46: 1.00,
            19: 0.80 if job in {"PLD", "WAR", "DRK", "GNB"} else 0.05,
            6: 0.10 if job in {"WHM", "SCH", "AST", "SGE"} else 0.0,
        }
        if mode == "dmg100p" and target_gcd is None:
            stat_weights[speed_stat_id] = 0.0
    return GearSearchScoreContext(
        main_stat_id=main_stat_id,
        speed_stat_id=speed_stat_id,
        target_gcd=target_gcd,
        required_item_speed=required_item_speed,
        stat_weights=dict(stat_weights),
        mode=mode,
    )


def _gear_search_speed_score(
    speed_value: int,
    job: str,
    target_gcd: Optional[float],
    level: int,
    score_context: Optional[GearSearchScoreContext] = None,
) -> float:
    context = score_context or _prepare_gear_search_score_context(job, target_gcd, level)
    speed = int(speed_value or 0)
    if speed <= 0:
        return 0.0
    if context.target_gcd is None:
        return float(speed)
    if context.required_item_speed is None:
        return float(speed) * 0.75
    useful_speed = min(speed, context.required_item_speed)
    overspeed = max(0, speed - context.required_item_speed)
    # Search beam should value meeting target GCD, but avoid tunneling on
    # excessive SpS/SkS states that later exact evaluation rejects.
    return float(useful_speed) * 0.9 - float(overspeed) * 0.55


def _gear_search_state_score(
    stats: Dict[int, int],
    job: str,
    target_gcd: Optional[float],
    level: int,
    *,
    weapon_damage: int = 0,
    meld_capacity: int = 0,
    score_context: Optional[GearSearchScoreContext] = None,
) -> float:
    context = score_context or _prepare_gear_search_score_context(job, target_gcd, level)
    stat_weights = context.stat_weights or {}
    speed_weight = float(stat_weights.get(context.speed_stat_id, 1.0))
    if context.target_gcd is not None:
        speed_weight = max(1.0, speed_weight)
    speed_score = _gear_search_speed_score(
        int(stats.get(context.speed_stat_id, 0)),
        job,
        target_gcd,
        level,
        score_context=context,
    )
    return (
        float(int(weapon_damage or 0)) * 10000.0
        + float(int(stats.get(context.main_stat_id, 0))) * 110.0
        + float(int(stats.get(27, 0))) * float(stat_weights.get(27, 1.45))
        + float(int(stats.get(22, 0))) * float(stat_weights.get(22, 1.25))
        + float(int(stats.get(44, 0))) * float(stat_weights.get(44, 1.10))
        + speed_score * speed_weight
        + float(int(stats.get(3, 0))) * 0.20
        + float(int(stats.get(19, 0))) * float(stat_weights.get(19, 0.15))
        + float(int(stats.get(6, 0))) * float(stat_weights.get(6, 0.15))
        + float(int(meld_capacity or 0)) * 85.0
    )


def _gear_search_secondary_score(
    stats: Dict[int, int],
    job: str,
    target_gcd: Optional[float],
    level: int,
    score_context: Optional[GearSearchScoreContext] = None,
) -> float:
    context = score_context or _prepare_gear_search_score_context(job, target_gcd, level)
    stat_weights = context.stat_weights or {}
    speed_weight = float(stat_weights.get(context.speed_stat_id, 1.0))
    if context.target_gcd is not None:
        speed_weight = max(1.0, speed_weight)
    return (
        float(int(stats.get(27, 0))) * float(stat_weights.get(27, 1.50))
        + float(int(stats.get(22, 0))) * float(stat_weights.get(22, 1.65))
        + float(int(stats.get(44, 0))) * float(stat_weights.get(44, 1.25))
        + _gear_search_speed_score(
            int(stats.get(context.speed_stat_id, 0)),
            job,
            target_gcd,
            level,
            score_context=context,
        ) * speed_weight
        + float(int(stats.get(19, 0))) * float(stat_weights.get(19, 0.15))
        + float(int(stats.get(6, 0))) * float(stat_weights.get(6, 0.15))
    )


def _gear_search_diversified_states(
    states: List[Dict[str, object]],
    limit: int,
    job: str,
    target_gcd: Optional[float],
    level: int,
    score_context: Optional[GearSearchScoreContext] = None,
) -> List[Dict[str, object]]:
    if limit <= 0 or not states:
        return []
    if len(states) <= limit:
        return states

    primary_limit = max(1, int(limit * 0.65))
    meld_limit = max(1, int(limit * 0.20))
    secondary_limit = max(1, limit - primary_limit - meld_limit)

    context = score_context or _prepare_gear_search_score_context(job, target_gcd, level)
    decorated = [
        (
            entry,
            float(entry["_gear_search_secondary_score"])
            if entry.get("_gear_search_secondary_score") is not None
            else _gear_search_secondary_score(
                entry.get("stats") or {}, job, target_gcd, level, score_context=context
            ),
        )
        for entry in states
    ]
    ranked_by_score = sorted(
        decorated,
        key=lambda row: (
            -float(row[0].get("score") or 0.0),
            -int(row[0].get("meld_capacity") or 0),
            -row[1],
            int(row[0].get("_search_sequence") or 0),
        ),
    )
    ranked_by_meld = sorted(
        decorated,
        key=lambda row: (
            -int(row[0].get("meld_capacity") or 0),
            -row[1],
            -float(row[0].get("score") or 0.0),
            int(row[0].get("_search_sequence") or 0),
        ),
    )
    ranked_by_secondary = sorted(
        decorated,
        key=lambda row: (
            -row[1],
            -int(row[0].get("meld_capacity") or 0),
            -float(row[0].get("score") or 0.0),
            int(row[0].get("_search_sequence") or 0),
        ),
    )

    selected: List[Dict[str, object]] = []
    seen: set = set()
    signature_cache: Dict[
        int,
        Tuple[Tuple[str, int, Tuple[Tuple[int, int], ...]], ...],
    ] = {}

    def add_from(entries: List[Tuple[Dict[str, object], float]], quota: int) -> None:
        if quota <= 0:
            return
        added = 0
        for entry, _secondary_score in entries:
            entry_id = id(entry)
            signature = signature_cache.get(entry_id)
            if signature is None:
                signature = tuple(
                    sorted(
                        (
                            slot,
                            int(item.item_id),
                            tuple(
                                sorted(
                                    (int(stat_id), int(value))
                                    for stat_id, value in dict(
                                        getattr(item, "_gear_search_relic_stats", {}) or {}
                                    ).items()
                                    if int(value or 0) > 0
                                )
                            ),
                        )
                        for slot, item in (entry.get("items") or {}).items()
                        if item is not None
                    )
                )
                signature_cache[entry_id] = signature
            if signature in seen:
                continue
            seen.add(signature)
            selected.append(entry)
            added += 1
            if added >= quota or len(selected) >= limit:
                break

    add_from(ranked_by_score, primary_limit)
    add_from(ranked_by_meld, meld_limit)
    add_from(ranked_by_secondary, secondary_limit)
    if len(selected) < limit:
        add_from(ranked_by_score, limit - len(selected))
    return selected[:limit]


def _gear_search_ranked_state_union(
    states: List[Dict[str, object]],
    limit: int,
    job: str,
    target_gcd: Optional[float],
    level: int,
    score_context: Optional[GearSearchScoreContext] = None,
) -> List[Dict[str, object]]:
    if limit <= 0 or not states:
        return []
    if len(states) <= limit:
        return states
    context = score_context or _prepare_gear_search_score_context(job, target_gcd, level)
    decorated = [
        (
            entry,
            float(entry["_gear_search_secondary_score"])
            if entry.get("_gear_search_secondary_score") is not None
            else _gear_search_secondary_score(
                entry.get("stats") or {}, job, target_gcd, level, score_context=context
            ),
        )
        for entry in states
    ]
    ranked_lists = (
        sorted(
            decorated,
            key=lambda row: (
                -float(row[0].get("score") or 0.0),
                -int(row[0].get("meld_capacity") or 0),
                -row[1],
                int(row[0].get("_search_sequence") or 0),
            ),
        ),
        sorted(
            decorated,
            key=lambda row: (
                -int(row[0].get("meld_capacity") or 0),
                -row[1],
                -float(row[0].get("score") or 0.0),
                int(row[0].get("_search_sequence") or 0),
            ),
        ),
        sorted(
            decorated,
            key=lambda row: (
                -row[1],
                -int(row[0].get("meld_capacity") or 0),
                -float(row[0].get("score") or 0.0),
                int(row[0].get("_search_sequence") or 0),
            ),
        ),
    )
    retained: List[Dict[str, object]] = []
    seen_ids: set[int] = set()
    for ranked in ranked_lists:
        for entry, _secondary_score in ranked[:limit]:
            entry_id = id(entry)
            if entry_id in seen_ids:
                continue
            seen_ids.add(entry_id)
            retained.append(entry)
    retained.sort(key=lambda entry: int(entry.get("_search_sequence") or 0))
    return retained


def _gear_search_preview_shortlist(
    states: List[Dict[str, object]],
    primary_limit: int,
    diversity_extra_limit: int,
    job: str,
    target_gcd: Optional[float],
    level: int,
    score_context: Optional[GearSearchScoreContext] = None,
) -> List[Dict[str, object]]:
    if primary_limit <= 0 or not states:
        return []
    ranked_by_preview = sorted(
        states,
        key=lambda entry: (
            -float(entry.get("preview_score") or 0.0),
            -int(entry.get("meld_capacity") or 0),
            -float(entry.get("heuristic_score") or 0.0),
            float(entry.get("preview_gcd") or 99.0),
            int(entry.get("_search_sequence") or 0),
        ),
    )
    selected = list(ranked_by_preview[:primary_limit])
    if diversity_extra_limit <= 0 or len(selected) >= len(states):
        return selected
    seen_ids = {id(entry) for entry in selected}
    diversity_pool = _gear_search_diversified_states(
        states,
        min(len(states), primary_limit),
        job,
        target_gcd,
        level,
        score_context=score_context,
    )
    candidate_pools = [diversity_pool]
    if target_gcd is not None:
        best_by_gcd_band: Dict[float, Dict[str, object]] = {}
        for entry in ranked_by_preview:
            gcd_band = round(float(entry.get("preview_gcd") or 99.0), 2)
            best_by_gcd_band.setdefault(gcd_band, entry)
        candidate_pools.append(
            [
                entry
                for _gcd_band, entry in sorted(
                    best_by_gcd_band.items(),
                    key=lambda row: (abs(row[0] - float(target_gcd)), row[0]),
                )
            ]
        )
    pool_indexes = [0] * len(candidate_pools)
    while len(selected) < primary_limit + diversity_extra_limit:
        added = False
        for pool_index, pool in enumerate(candidate_pools):
            while pool_indexes[pool_index] < len(pool):
                entry = pool[pool_indexes[pool_index]]
                pool_indexes[pool_index] += 1
                if id(entry) in seen_ids:
                    continue
                seen_ids.add(id(entry))
                selected.append(entry)
                added = True
                break
            if len(selected) >= primary_limit + diversity_extra_limit:
                break
        if not added:
            break
    selected.sort(
        key=lambda entry: (
            -float(entry.get("preview_score") or 0.0),
            -int(entry.get("meld_capacity") or 0),
            -float(entry.get("heuristic_score") or 0.0),
            float(entry.get("preview_gcd") or 99.0),
            int(entry.get("_search_sequence") or 0),
        )
    )
    return selected


def _normalize_party_synergies(
    party_synergies: Optional[Dict[str, bool]],
    job: Optional[str] = None,
) -> Tuple[str, ...]:
    if not party_synergies:
        return tuple()
    enabled = [k for k in SYNERGY_KEYS if party_synergies.get(k)]
    if job:
        self_key = SYNERGY_JOB_TO_KEY.get(str(job).upper())
        if self_key:
            enabled = [k for k in enabled if k != self_key]
    return tuple(enabled)


def is_combat_food(food: Optional[FoodRecord]) -> bool:
    if not food:
        return False
    bonuses = getattr(food, "bonuses", None) or {}
    for stat_id in bonuses.keys():
        try:
            if int(stat_id) in COMBAT_FOOD_BONUS_STATS:
                return True
        except Exception:
            continue
    return False


def highest_item_level_combat_foods(
    foods: Sequence[Optional[FoodRecord]],
) -> List[FoodRecord]:
    combat_foods = [food for food in foods if is_combat_food(food)]
    known_levels = [int(food.level_item) for food in combat_foods if food.level_item is not None]
    if not known_levels:
        return combat_foods
    highest_il = max(known_levels)
    return [
        food
        for food in combat_foods
        if food.level_item is not None and int(food.level_item) == highest_il
    ]


def non_dominated_combat_foods(
    foods: Sequence[FoodRecord],
    relevant_stats: Sequence[int],
) -> List[FoodRecord]:
    stats = tuple(sorted({int(stat_id) for stat_id in relevant_stats}))
    if not stats:
        return list(foods)

    def bonus_pair(food: FoodRecord, stat_id: int) -> Tuple[int, int]:
        bonus = (food.bonuses or {}).get(stat_id)
        if bonus is None:
            return 0, 0
        return int(bonus.percentage or 0), int(bonus.maximum or 0)

    def dominates(left: FoodRecord, right: FoodRecord) -> bool:
        strictly_better = False
        for stat_id in stats:
            left_pct, left_max = bonus_pair(left, stat_id)
            right_pct, right_max = bonus_pair(right, stat_id)
            if left_pct < right_pct or left_max < right_max:
                return False
            if left_pct > right_pct or left_max > right_max:
                strictly_better = True
        return strictly_better

    candidates = list(foods)
    return [
        food
        for index, food in enumerate(candidates)
        if not any(
            other_index != index and dominates(other, food)
            for other_index, other in enumerate(candidates)
        )
    ]


def _average_party_synergy_effect(
    start_ts: int,
    end_ts: int,
    job: str,
    enabled: Tuple[str, ...],
) -> Tuple[float, float, float]:
    if not enabled:
        return 1.0, 0.0, 0.0
    if end_ts <= start_ts:
        return _party_synergy_effect(start_ts, start_ts, job, enabled)
    # Sample across the whole fight so short burst buffs are averaged by uptime.
    step_ms = 1000
    total_dmg = 0.0
    total_crit = 0.0
    total_dh = 0.0
    samples = 0
    ts = start_ts
    while ts < end_ts:
        sample_ts = min(ts + (step_ms // 2), end_ts - 1)
        dmg, crit, dh = _party_synergy_effect(sample_ts, start_ts, job, enabled)
        total_dmg += dmg
        total_crit += crit
        total_dh += dh
        samples += 1
        ts += step_ms
    if samples <= 0:
        return _party_synergy_effect(start_ts, start_ts, job, enabled)
    return (
        round(total_dmg / samples, 6),
        round(total_crit / samples, 6),
        round(total_dh / samples, 6),
    )


def _synergy_window_active(
    ts: int,
    start_ts: int,
    duration_s: float,
    cycle_s: float,
    offset_s: float = 0.0,
) -> bool:
    if cycle_s <= 0.0 or duration_s <= 0.0:
        return False
    elapsed = (ts - start_ts) / 1000.0 - offset_s
    if elapsed < 0.0:
        return False
    phase = elapsed % cycle_s
    return phase < duration_s


def _party_synergy_effect(
    ts: int,
    start_ts: int,
    job: str,
    enabled: Tuple[str, ...],
) -> Tuple[float, float, float]:
    if not enabled:
        return 1.0, 0.0, 0.0
    dmg_mult = 1.0
    crit_bonus = 0.0
    dh_bonus = 0.0

    if "dnc" in enabled:
        # Standard Finish is effectively near-full uptime for partner.
        dmg_mult *= 1.05
        if _synergy_window_active(ts, start_ts, 20.0, 120.0):
            dmg_mult *= 1.05  # Technical Finish
            crit_bonus += 0.20  # Devilment
            dh_bonus += 0.20

    if "brd" in enabled:
        # Song cycle approximation: 45s * 3 loop.
        if _synergy_window_active(ts, start_ts, 45.0, 135.0, 0.0):
            dmg_mult *= 1.01  # Ballad
        if _synergy_window_active(ts, start_ts, 45.0, 135.0, 45.0):
            dh_bonus += 0.03  # Paeon
        if _synergy_window_active(ts, start_ts, 45.0, 135.0, 90.0):
            crit_bonus += 0.02  # Minuet
        if _synergy_window_active(ts, start_ts, 20.0, 120.0):
            dh_bonus += 0.20  # Battle Voice
        if _synergy_window_active(ts, start_ts, 20.0, 110.0):
            dmg_mult *= 1.06  # Radiant Finale (max coda)

    if "drg" in enabled and _synergy_window_active(ts, start_ts, 20.0, 120.0):
        crit_bonus += 0.10  # Battle Litany
    if "mnk" in enabled and _synergy_window_active(ts, start_ts, 20.0, 120.0):
        dmg_mult *= 1.05  # Brotherhood
    if "rpr" in enabled and _synergy_window_active(ts, start_ts, 20.0, 120.0):
        dmg_mult *= 1.03  # Arcane Circle
    if "nin" in enabled and _synergy_window_active(ts, start_ts, 20.0, 120.0):
        dmg_mult *= 1.05  # Dokumori
    if "rdm" in enabled and _synergy_window_active(ts, start_ts, 20.0, 120.0):
        dmg_mult *= 1.05  # Embolden
    if "pct" in enabled and _synergy_window_active(ts, start_ts, 20.0, 120.0):
        dmg_mult *= 1.05  # Starry Muse
    if "sch" in enabled and _synergy_window_active(ts, start_ts, 20.0, 120.0):
        crit_bonus += 0.10  # Chain Stratagem
    if "ast" in enabled:
        if _synergy_window_active(ts, start_ts, 20.0, 120.0):
            dmg_mult *= 1.06  # Divination
        # Card approximation: 15s buff every 30s, role-adjusted bonus.
        if _synergy_window_active(ts, start_ts, 15.0, 30.0):
            card_bonus = 0.06 if job in RANGED_HEALER_JOBS else 0.03
            dmg_mult *= (1.0 + card_bonus)

    return round(dmg_mult, 6), round(crit_bonus, 6), round(dh_bonus, 6)


def _apply_party_synergy_to_ability_buckets(
    damage_summary: Dict[str, object],
    job: str,
    party_synergies: Optional[Dict[str, bool]],
    debug: bool = False,
) -> Dict[Tuple, float]:
    ability_buckets = damage_summary.get("ability_buckets") or {}
    if not ability_buckets:
        return {}
    enabled = _normalize_party_synergies(party_synergies, job)
    if not enabled:
        return ability_buckets

    cache = damage_summary.setdefault("_party_synergy_cache", {})
    cache_key = (job, enabled)
    cached = cache.get(cache_key)
    if cached is not None:
        return cached

    timeline_entries = damage_summary.get("timeline_entries") or []
    start_ts = int(damage_summary.get("min_ts") or 0)
    if start_ts <= 0 and timeline_entries:
        start_ts = int(min((int(e[1]) for e in timeline_entries), default=0))

    if timeline_entries and start_ts > 0:
        transformed: Dict[Tuple, float] = defaultdict(float)
        for entry in timeline_entries:
            if not isinstance(entry, tuple) or len(entry) < 3:
                continue
            base_key, ts, amount = entry[0], int(entry[1]), float(entry[2])
            if not isinstance(base_key, tuple) or len(base_key) < 8:
                continue
            aid, atk, is_dot, dmg_mult, crit_bonus, dh_bonus, force_crit, force_dh = base_key[:8]
            ext_dmg, ext_crit, ext_dh = _party_synergy_effect(ts, start_ts, job, enabled)
            # Keep original (self-buff) fields and attach external synergy fields.
            # evaluate_score applies ext_* to "new" side only.
            merged = (
                int(aid),
                str(atk),
                bool(is_dot),
                round(float(dmg_mult), 6),
                round(float(crit_bonus), 6),
                round(float(dh_bonus), 6),
                bool(force_crit),
                bool(force_dh),
                round(float(ext_dmg), 6),
                round(float(ext_crit), 6),
                round(float(ext_dh), 6),
            )
            transformed[merged] += amount
        if transformed:
            cache[cache_key] = transformed
            if debug:
                sim_log(
                    f"[simdps] party_synergy enabled={','.join(enabled)} "
                    f"timeline_entries={len(timeline_entries)} buckets={len(transformed)}"
                )
            return transformed

    # Fallback when timeline entries are unavailable: estimate average buffs over fight duration.
    min_ts = int(damage_summary.get("min_ts") or 0)
    max_ts = int(damage_summary.get("max_ts") or 0)
    avg_dmg, avg_crit, avg_dh = _average_party_synergy_effect(
        min_ts,
        max_ts,
        job,
        enabled,
    )
    transformed: Dict[Tuple, float] = defaultdict(float)
    for key, amount in ability_buckets.items():
        if not isinstance(key, tuple) or len(key) < 8:
            continue
        aid, atk, is_dot, dmg_mult, crit_bonus, dh_bonus, force_crit, force_dh = key[:8]
        merged = (
            int(aid),
            str(atk),
            bool(is_dot),
            round(float(dmg_mult), 6),
            round(float(crit_bonus), 6),
            round(float(dh_bonus), 6),
            bool(force_crit),
            bool(force_dh),
            round(float(avg_dmg), 6),
            round(float(avg_crit), 6),
            round(float(avg_dh), 6),
        )
        transformed[merged] += float(amount)
    cache[cache_key] = transformed if transformed else ability_buckets
    if debug:
        sim_log(f"[simdps] party_synergy fallback enabled={','.join(enabled)} buckets={len(transformed)}")
    return cache[cache_key]

def guaranteed_slots_for_item(item: ItemRecord) -> int:
    if item.materia_slots is not None:
        return item.materia_slots
    slot = item.slot
    if slot in {"head", "body", "hands", "legs", "feet", "weapon"}:
        return 2
    if slot in {"offhand", "earrings", "necklace", "bracelet", "ring"}:
        return 1
    return item.materia_slots or 0


def total_meld_slots_for_item(item: ItemRecord) -> int:
    guaranteed = guaranteed_slots_for_item(item)
    if item.overmeld:
        return max(guaranteed, 5)
    return guaranteed


def max_grade_for_slot(item: ItemRecord, slot_index: int) -> int:
    guaranteed = guaranteed_slots_for_item(item)
    if slot_index < guaranteed:
        return MATERIA_LEVEL_MAX_NORMAL
    if not item.overmeld:
        return 0
    if slot_index == guaranteed:
        return MATERIA_LEVEL_MAX_NORMAL
    return MATERIA_LEVEL_MAX_OVERMELD


def allows_high_grade_for_slot(item: ItemRecord, slot_index: int) -> bool:
    guaranteed = guaranteed_slots_for_item(item)
    if slot_index < guaranteed:
        return True
    if not item.overmeld:
        return False
    # First overmeld slot allows high grade; later slots do not.
    return slot_index == guaranteed


def top_grades_by_ilvl(
    item: ItemRecord, grades: List[MateriaGrade], limit: int
) -> List[MateriaGrade]:
    if limit <= 0:
        return []
    available = [
        g
        for g in grades
        if g.value > 0 and (not g.item_ilvl or g.item_ilvl <= item.ilvl)
    ]
    available.sort(key=lambda g: g.grade, reverse=True)
    return available[:limit]


def grades_for_slot(
    item: ItemRecord,
    grades: List[MateriaGrade],
    slot_index: int,
    max_grades: int = 2,
    policy: str = "top",
) -> List[MateriaGrade]:
    max_grade = max_grade_for_slot(item, slot_index)
    if max_grade <= 0 or max_grades <= 0:
        return []
    if policy == "best":
        available = [
            g
            for g in grades
            if g.value > 0
            and (not g.item_ilvl or g.item_ilvl <= item.ilvl)
            and g.grade <= max_grade
        ]
        if not allows_high_grade_for_slot(item, slot_index):
            available = [g for g in available if g.grade % 2 == 1]
        available.sort(key=lambda g: (g.value, g.grade), reverse=True)
        return available[:1]
    available = top_grades_by_ilvl(item, grades, max_grades)
    available = [g for g in available if g.grade <= max_grade]
    if not allows_high_grade_for_slot(item, slot_index):
        available = [g for g in available if g.grade % 2 == 1]
    return available


def allowed_grades_for_slot(
    item: ItemRecord, grades: List[MateriaGrade], slot_index: int
) -> List[MateriaGrade]:
    return grades_for_slot(item, grades, slot_index, max_grades=2, policy="top")


@lru_cache(maxsize=8192)
def _calc_gcd_seconds_cached(speed_stat: int, job: str, base_gcd_ms: int, level: int) -> float:
    level_data = level_stats(level)
    base_gcd = base_gcd_ms / 1000.0
    if job in SPELL_SPEED_JOBS:
        gcd = xivmath.sps_to_gcd(base_gcd, level_data, speed_stat)
    else:
        gcd = xivmath.sks_to_gcd(base_gcd, level_data, speed_stat)
    return round(gcd, 3)


def calc_gcd_seconds(speed_stat: int, job: str, base_gcd_ms: int = 2500, level: int = xivmath.CURRENT_MAX_LEVEL) -> float:
    # Heavy optimize paths call this repeatedly with identical inputs.
    return _calc_gcd_seconds_cached(int(speed_stat), str(job or ""), int(base_gcd_ms), normalized_level(level))


GCD_TARGET_EPSILON = 0.0005


def gcd_meets_target(gcd: float, target_gcd: Optional[float]) -> bool:
    if not target_gcd:
        return True
    return round(float(gcd), 3) <= round(float(target_gcd), 3) + GCD_TARGET_EPSILON


def gcd_meets_constraints(
    gcd: float,
    target_gcd: Optional[float],
    log_constraint: Optional[LogGcdConstraint],
) -> bool:
    if not gcd_meets_target(gcd, target_gcd):
        return False
    return log_constraint is None or log_constraint.accepts(gcd)


@lru_cache(maxsize=1024)
def _required_speed_stat_for_target_gcd_cached(
    job: str,
    target_gcd_milli: int,
    base_gcd_ms: int,
    level: int,
) -> Optional[int]:
    target_gcd = target_gcd_milli / 1000.0
    level_data = level_stats(level)
    low = int(level_data.base_sub)
    high = low + 10000
    answer: Optional[int] = None
    while low <= high:
        mid = (low + high) // 2
        gcd = calc_gcd_seconds(mid, job, base_gcd_ms, level)
        if gcd_meets_target(gcd, target_gcd):
            answer = mid
            high = mid - 1
        else:
            low = mid + 1
    return answer


def required_speed_stat_for_target_gcd(
    job: str,
    target_gcd: Optional[float],
    base_gcd_ms: int = 2500,
    level: int = xivmath.CURRENT_MAX_LEVEL,
) -> Optional[int]:
    """Return minimum speed stat(total, incl. base_sub) needed to satisfy target GCD."""
    if not target_gcd:
        return None
    target_gcd_milli = int(round(float(target_gcd) * 1000))
    return _required_speed_stat_for_target_gcd_cached(
        str(job or ""),
        target_gcd_milli,
        int(base_gcd_ms),
        normalized_level(level),
    )


def _normalize_attack_type_name(raw_type: Optional[str], job: str) -> str:
    if raw_type is None:
        text = ""
    elif isinstance(raw_type, str):
        text = raw_type.strip().lower()
    else:
        text = str(raw_type).strip().lower()
    if not text:
        return "Unknown"
    if "auto" in text or text in {"attack", "melee"}:
        return "Auto-attack"
    if "weaponskill" in text or "weapon" in text:
        return "Weaponskill"
    if "spell" in text or "magic" in text:
        return "Spell"
    if "ability" in text:
        return "Ability"
    if text in {"spell", "weaponskill", "ability"}:
        return text.capitalize()
    return "Unknown"


def summarize_damage(
    events: List[dict],
    job: str,
    action_data: Optional[Dict[int, object]] = None,
) -> Dict[str, object]:
    buckets: Dict[Tuple[str, bool], float] = defaultdict(float)
    bucket_counts: Dict[Tuple[str, bool], int] = defaultdict(int)
    ability_buckets: Dict[Tuple[int, str, bool], float] = defaultdict(float)
    ability_bucket_counts: Dict[Tuple[int, str, bool], int] = defaultdict(int)
    ability_names: Dict[int, str] = {}
    total_damage = 0.0
    total_hits = 0
    total_amount = 0.0
    total_absorbed = 0.0
    total_overkill = 0.0
    min_ts = None
    max_ts = None
    unknown_actions: Dict[Tuple[int, str], Dict[str, float]] = defaultdict(
        lambda: {"damage": 0.0, "count": 0}
    )
    for ev in events or []:
        amount = ev.get("amount")
        if amount is None or amount <= 0:
            continue
        ts = ev.get("timestamp")
        if ts is None:
            ts = ev.get("time")
        if ts is not None:
            min_ts = ts if min_ts is None else min(min_ts, ts)
            max_ts = ts if max_ts is None else max(max_ts, ts)
        absorbed = ev.get("absorbed") or 0
        overkill = ev.get("overkill") or 0
        total_amount += float(amount)
        total_absorbed += float(absorbed)
        total_overkill += float(overkill)
        ability = ev.get("ability") or {}
        action_id = (
            ability.get("gameID")
            or ability.get("guid")
            or ability.get("id")
            or ev.get("abilityGameID")
            or ev.get("abilityGuid")
            or ev.get("actionID")
            or 0
        )
        try:
            action_id_int = int(action_id)
        except Exception:
            action_id_int = 0
        action_record = action_data.get(action_id_int) if action_data else None
        name = str(
            ability.get("name")
            or getattr(action_record, "name_ja", None)
            or getattr(action_record, "name", None)
            or ""
        )
        ability_type = ability.get("type") or getattr(
            action_record,
            "attack_type",
            None,
        )
        is_dot = bool(ev.get("tick") or ev.get("isTick"))
        lower = name.lower()
        is_auto = lower in {"auto attack", "auto-attack", "attack", "攻撃", "オートアタック"}
        if is_auto:
            attack_type = "Auto-attack"
            is_dot = False
        elif ability_type in {"Spell", "Weaponskill", "Ability"}:
            attack_type = ability_type
        else:
            attack_type = _normalize_attack_type_name(ability_type, job)
        if attack_type == "Unknown" and action_record is not None:
            attack_type = _normalize_attack_type_name(
                getattr(action_record, "attack_type", None),
                job,
            )
        if attack_type == "Unknown":
            attack_type = "Spell" if job in SPELL_SPEED_JOBS else "Weaponskill"
        buckets[(attack_type, is_dot)] += float(amount)
        bucket_counts[(attack_type, is_dot)] += 1
        ability_buckets[(action_id_int, attack_type, is_dot)] += float(amount)
        ability_bucket_counts[(action_id_int, attack_type, is_dot)] += 1
        if action_id_int and name:
            ability_names[action_id_int] = name
        if attack_type == "Unknown":
            key = (int(action_id), name)
            unknown_actions[key]["damage"] += float(amount)
            unknown_actions[key]["count"] += 1
        total_damage += float(amount)
        total_hits += 1
    return {
        "total_damage": total_damage,
        "total_hits": total_hits,
        "buckets": buckets,
        "bucket_counts": bucket_counts,
        "ability_buckets": ability_buckets,
        "ability_bucket_counts": ability_bucket_counts,
        "ability_names": ability_names,
        "total_amount": total_amount,
        "total_absorbed": total_absorbed,
        "total_overkill": total_overkill,
        "min_ts": min_ts,
        "max_ts": max_ts,
        "unknown_actions": unknown_actions,
    }


def summarize_timeline_damage(
    casts: List[dict],
    damage_events: List[dict],
    timeline_events: Optional[List[dict]],
    job: str,
    actor_id: Optional[int] = None,
    action_data: Optional[Dict[int, object]] = None,
    status_data: Optional[Dict[int, object]] = None,
    fight_end_ts: Optional[int] = None,
) -> Dict[str, object]:
    """Rebuild damage summary from cast timeline + self-buff timeline.

    This keeps the fight rotation order (cast timeline) and attributes each damage
    event to the most recent matching cast action.
    """

    cast_only = [ev for ev in (casts or []) if (ev.get("type") == "cast")]
    if not cast_only:
        cast_only = [ev for ev in (casts or []) if (ev.get("type") in {"cast", "begincast"})]
    cast_only.sort(key=lambda e: e.get("timestamp") or e.get("time") or 0)

    def _aid(ev: dict) -> int:
        ability = ev.get("ability") or {}
        raw = (
            ability.get("gameID")
            or ability.get("guid")
            or ability.get("id")
            or ev.get("abilityGameID")
            or ev.get("abilityGuid")
            or ev.get("abilityID")
            or 0
        )
        try:
            return int(raw)
        except Exception:
            return 0

    def _ts(ev: dict) -> int:
        ts = ev.get("timestamp")
        if ts is None:
            ts = ev.get("time")
        try:
            return int(ts or 0)
        except Exception:
            return 0

    def _target(ev: dict) -> Optional[int]:
        for key in ("targetID", "targetId", "targetid"):
            if key in ev and ev.get(key) is not None:
                try:
                    return int(ev.get(key))
                except Exception:
                    return None
        return None

    cast_ts = [_ts(ev) for ev in cast_only]
    cast_action_ids = [_aid(ev) for ev in cast_only]
    casts_by_action: Dict[int, List[Tuple[int, int]]] = defaultdict(list)
    for idx, _ev in enumerate(cast_only):
        aid = cast_action_ids[idx]
        if aid > 0:
            casts_by_action[aid].append((cast_ts[idx], idx))

    # Build self-buff intervals from timeline events.
    actor_timeline = sorted((timeline_events or []), key=_ts)
    buff_open: Dict[int, int] = {}
    buff_intervals: Dict[int, List[Tuple[int, int]]] = defaultdict(list)
    for ev in actor_timeline:
        ev_type = ev.get("type")
        if ev_type not in {"applybuff", "refreshbuff", "removebuff", "removebuffstack"}:
            continue
        if actor_id is not None:
            tgt = _target(ev)
            if tgt is not None and tgt != actor_id:
                continue
        aid = _aid(ev)
        if aid <= 0:
            continue
        ts = _ts(ev)
        if ev_type in {"applybuff", "refreshbuff"}:
            if aid not in buff_open:
                buff_open[aid] = ts
        else:
            start = buff_open.pop(aid, None)
            if start is not None and ts >= start:
                buff_intervals[aid].append((start, ts))
    if fight_end_ts is None:
        fight_end_ts = max([_ts(ev) for ev in (damage_events or [])] or [0])
    for aid, start in list(buff_open.items()):
        if fight_end_ts >= start:
            buff_intervals[aid].append((start, fight_end_ts))

    def _active_buff_ids(ts: int) -> List[int]:
        ids: List[int] = []
        for bid, spans in buff_intervals.items():
            for s, e in spans:
                if s <= ts <= e:
                    ids.append(bid)
                    break
        return [i for i in ids if i > 0]

    def _buff_effect(ids: List[int]) -> Tuple[float, float, float, bool, bool]:
        dmg_mult = 1.0
        crit_bonus = 0.0
        dh_bonus = 0.0
        force_crit = False
        force_dh = False
        for bid in ids:
            rec = status_data.get(bid) if status_data else None
            if rec is None:
                continue
            try:
                dmg_up = float(getattr(rec, "damage_up", 0.0) or 0.0)
            except Exception:
                dmg_up = 0.0
            try:
                crit_up = float(getattr(rec, "crit_rate_up", 0.0) or 0.0)
            except Exception:
                crit_up = 0.0
            try:
                dh_up = float(getattr(rec, "dhit_rate_up", 0.0) or 0.0)
            except Exception:
                dh_up = 0.0
            dmg_mult *= (1.0 + dmg_up)
            crit_bonus += crit_up
            dh_bonus += dh_up
            force_crit = force_crit or bool(getattr(rec, "force_crit", False))
            force_dh = force_dh or bool(getattr(rec, "force_dhit", False))
        return (
            round(dmg_mult, 6),
            round(crit_bonus, 6),
            round(dh_bonus, 6),
            force_crit,
            force_dh,
        )

    def _attack_type(ev: dict, aid: int, name: str) -> str:
        ability = ev.get("ability") or {}
        atype = ability.get("type")
        if name.lower() in {"auto attack", "auto-attack", "attack", "攻撃", "オートアタック"}:
            return "Auto-attack"
        if atype in {"Spell", "Weaponskill", "Ability"}:
            return atype
        if action_data and aid in action_data:
            rec = action_data.get(aid)
            if rec is not None:
                mapped = _normalize_attack_type_name(getattr(rec, "attack_type", None), job)
                if mapped != "Unknown":
                    return mapped
        fallback = _normalize_attack_type_name(atype, job)
        if fallback != "Unknown":
            return fallback
        return "Spell" if job in SPELL_SPEED_JOBS else "Weaponskill"

    # DoT snapshot at application time.
    dot_snapshots: Dict[Tuple[Optional[int], int], Tuple[float, float, float, bool, bool]] = {}
    for ev in actor_timeline:
        ev_type = ev.get("type")
        if ev_type not in {"applydebuff", "refreshdebuff", "removedebuff", "removedebuffstack"}:
            continue
        aid = _aid(ev)
        if aid <= 0:
            continue
        tgt = _target(ev)
        key = (tgt, aid)
        if ev_type in {"applydebuff", "refreshdebuff"}:
            ids = _active_buff_ids(_ts(ev))
            dot_snapshots[key] = _buff_effect(ids)
        else:
            dot_snapshots.pop(key, None)

    buckets: Dict[Tuple[str, bool], float] = defaultdict(float)
    bucket_counts: Dict[Tuple[str, bool], int] = defaultdict(int)
    ability_buckets: Dict[Tuple[int, str, bool, float, float, float, bool, bool], float] = defaultdict(float)
    ability_bucket_counts: Dict[Tuple[int, str, bool, float, float, float, bool, bool], int] = defaultdict(int)
    ability_names: Dict[int, str] = {}
    unknown_actions: Dict[Tuple[int, str], Dict[str, float]] = defaultdict(
        lambda: {"damage": 0.0, "count": 0}
    )
    timeline_entries: List[Tuple[Tuple[int, str, bool, float, float, float, bool, bool], int, float]] = []
    total_amount = 0.0
    total_hits = 0
    min_ts = None
    max_ts = None
    match_horizon_ms = 45000

    for ev in sorted((damage_events or []), key=_ts):
        amount = ev.get("amount")
        if amount is None or amount <= 0:
            continue
        ts = _ts(ev)
        aid = _aid(ev)
        ability = ev.get("ability") or {}
        name = str(ability.get("name") or "")
        status_rec = status_data.get(aid) if status_data else None
        is_dot = bool(ev.get("tick") or ev.get("isTick") or bool(getattr(status_rec, "dot_effect", False)))
        atype = _attack_type(ev, aid, name)
        ability_names[aid] = name or ability_names.get(aid, "")

        cast_idx = None
        if aid in casts_by_action:
            rows = casts_by_action[aid]
            timestamps = [r[0] for r in rows]
            pos = bisect_right(timestamps, ts) - 1
            if pos >= 0:
                cts, idx = rows[pos]
                if ts - cts <= match_horizon_ms:
                    cast_idx = idx
        if cast_idx is not None:
            ref_ts = cast_ts[cast_idx]
        else:
            ref_ts = ts
        if is_dot:
            snapshot = dot_snapshots.get((_target(ev), aid))
            if snapshot is None:
                snapshot = _buff_effect(_active_buff_ids(ref_ts))
        else:
            snapshot = _buff_effect(_active_buff_ids(ref_ts))
        dmg_mult, crit_bonus, dh_bonus, force_crit, force_dh = snapshot

        amt = float(amount)
        buckets[(atype, is_dot)] += amt
        bucket_counts[(atype, is_dot)] += 1
        ability_key = (
            aid,
            atype,
            is_dot,
            dmg_mult,
            crit_bonus,
            dh_bonus,
            force_crit,
            force_dh,
        )
        ability_buckets[ability_key] += amt
        ability_bucket_counts[ability_key] += 1
        timeline_entries.append((ability_key, ts, amt))
        if atype == "Unknown":
            key = (aid, name)
            unknown_actions[key]["damage"] += amt
            unknown_actions[key]["count"] += 1

        total_amount += amt
        total_hits += 1
        min_ts = ts if min_ts is None else min(min_ts, ts)
        max_ts = ts if max_ts is None else max(max_ts, ts)

    return {
        "total_damage": total_amount,
        "total_hits": total_hits,
        "buckets": buckets,
        "bucket_counts": bucket_counts,
        "ability_buckets": ability_buckets,
        "ability_bucket_counts": ability_bucket_counts,
        "ability_names": ability_names,
        "total_amount": total_amount,
        "total_absorbed": 0.0,
        "total_overkill": 0.0,
        "min_ts": min_ts,
        "max_ts": max_ts,
        "unknown_actions": unknown_actions,
        "timeline_entries": timeline_entries,
    }


def aggregate_base_stats(selected_items: Dict[str, ItemRecord]) -> Dict[int, int]:
    stats = defaultdict(int)
    for item in selected_items.values():
        for stat_id, value in item.base_params_hq.items():
            stats[stat_id] += value
    return stats


def _js_round(value: float) -> int:
    return int((value + 0.5) // 1)


def _calc_cap_for_slot(base_param, item_level_row: dict, slot: str, meld_index: int) -> Optional[int]:
    if not base_param or not item_level_row:
        return None
    field = STAT_ID_TO_ITEMLEVEL_FIELD.get(base_param["stat_id"])
    if not field:
        return None
    ilvl_modifier = item_level_row.get(field)
    if ilvl_modifier is None:
        return None
    base_param_modifier = base_param["slots"].get(slot, 0)
    base_cap = _js_round(ilvl_modifier * base_param_modifier / 1000)
    meld_param = base_param.get("meld_param") or []
    if meld_index < len(meld_param):
        job_cap = meld_param[meld_index] / 100
        return _js_round(job_cap * _js_round(base_cap))
    return _js_round(base_cap)


def build_cap_table(
    items: List[ItemRecord],
    base_params: Dict[int, object],
    item_levels: Dict[int, dict],
    job: str,
) -> Dict[Tuple[int, int], int]:
    cap: Dict[Tuple[int, int], int] = {}
    meld_index = JOB_MELD_PARAM_INDEX.get(job, 0)
    for item in items:
        ilvl_row = item_levels.get(item.ilvl)
        if not ilvl_row:
            continue
        occ_slot = item.occ_slot or item.slot
        for stat_id in MELDABLE_STATS:
            bp = base_params.get(stat_id)
            if not bp:
                continue
            bp_record = {
                "stat_id": stat_id,
                "slots": getattr(bp, "slots", {}),
                "meld_param": getattr(bp, "meld_param", []),
            }
            if occ_slot == "OffHand":
                cap2h = _calc_cap_for_slot(bp_record, ilvl_row, "Weapon2H", meld_index)
                cap1h = _calc_cap_for_slot(bp_record, ilvl_row, "Weapon1H", meld_index)
                if cap2h is None or cap1h is None:
                    continue
                cap_val = max(0, cap2h - cap1h)
            else:
                cap_val = _calc_cap_for_slot(bp_record, ilvl_row, occ_slot, meld_index)
                if cap_val is None:
                    continue
            cap[(item.item_id, stat_id)] = cap_val
    return cap


def compute_item_stat_caps_for_il(
    item: ItemRecord,
    base_params: Dict[int, object],
    item_levels: Dict[int, dict],
    job: str,
    target_ilvl: int,
) -> Dict[int, int]:
    ilvl_row = item_levels.get(target_ilvl)
    if not ilvl_row:
        return {}
    meld_index = JOB_MELD_PARAM_INDEX.get(job, 0)
    occ_slot = item.occ_slot or item.slot
    caps: Dict[int, int] = {}
    for stat_id in STAT_ID_TO_ITEMLEVEL_FIELD.keys():
        bp = base_params.get(stat_id)
        if not bp:
            continue
        bp_record = {
            "stat_id": stat_id,
            "slots": getattr(bp, "slots", {}),
            "meld_param": getattr(bp, "meld_param", []),
        }
        if occ_slot == "OffHand":
            cap2h = _calc_cap_for_slot(bp_record, ilvl_row, "Weapon2H", meld_index)
            cap1h = _calc_cap_for_slot(bp_record, ilvl_row, "Weapon1H", meld_index)
            if cap2h is None or cap1h is None:
                continue
            cap_val = max(0, cap2h - cap1h)
        else:
            cap_val = _calc_cap_for_slot(bp_record, ilvl_row, occ_slot, meld_index)
            if cap_val is None:
                continue
        caps[stat_id] = int(cap_val)
    return caps


def remaining_cap_for_item(
    item: ItemRecord, stat_id: int, cap_table: Dict[Tuple[int, int], int]
) -> int:
    cap_val = cap_table.get((item.item_id, stat_id))
    if cap_val is None:
        cap_val = max(item.base_params_hq.values()) if item.base_params_hq else 0
    base_val = item.base_params_hq.get(stat_id, 0)
    return max(0, cap_val - base_val)


def _weapon_params(selected_items: Dict[str, ItemRecord]) -> Tuple[int, int, float]:
    weapon = selected_items.get("weapon")
    if not weapon:
        return 0, 0, 3.0
    delay_ms = weapon.delay_ms or 3000
    return weapon.damage_phys or 0, weapon.damage_mag or 0, delay_ms / 1000.0


def evaluate_score_pair(
    raw_stats: Dict[int, int],
    job: str,
    casts: List[dict],
    fight_duration_ms: int,
    target_gcd: Optional[float],
    damage_summary: Optional[Dict[str, object]] = None,
    job_mods: Optional[Dict[str, int]] = None,
    food: Optional[FoodRecord] = None,
    party_bonus: int = 0,
    baseline_raw_stats: Optional[Dict[int, int]] = None,
    baseline_items: Optional[Dict[str, ItemRecord]] = None,
    selected_items: Optional[Dict[str, ItemRecord]] = None,
    baseline_food: Optional[FoodRecord] = None,
    baseline_gcd: Optional[float] = None,
    mode: str = "simdps",
    race: Optional[str] = None,
    baseline_party_bonus: Optional[int] = None,
    baseline_race: Optional[str] = None,
    party_synergies: Optional[Dict[str, bool]] = None,
    debug: bool = False,
    level: int = xivmath.CURRENT_MAX_LEVEL,
    crit_rate_offset: float = 0.0,
    dhit_rate_offset: float = 0.0,
    include_expected: bool = True,
    eval_ctx: Optional[ScoreEvalContext] = None,
) -> Tuple[float, float, float]:
    level_value = eval_ctx.level_value if eval_ctx else normalized_level(level)
    level_data = eval_ctx.level_data if eval_ctx else level_stats(level_value)
    gcd_stat = raw_stats.get(46 if job in SPELL_SPEED_JOBS else 45, 0)
    gcd = calc_gcd_seconds(gcd_stat + level_data.base_sub, job, level=level_value)

    crit = raw_stats.get(27, 0)
    dh = raw_stats.get(22, 0)
    det = raw_stats.get(44, 0)
    ten = raw_stats.get(19, 0)
    pie = raw_stats.get(6, 0)
    speed = gcd_stat

    speed_weight = 0.6
    if target_gcd and gcd > target_gcd:
        speed_weight += min(2.0, (gcd - target_gcd) * 3)

    base_score = (
        crit * 1.0
        + dh * 0.9
        + det * 0.75
        + speed * speed_weight
        + ten * 0.2
        + pie * 0.15
    )

    if mode == "dmg100p":
        if not job_mods or selected_items is None:
            return base_score, base_score, gcd
        wd_phys, wd_mag, delay = _weapon_params(selected_items)
        comp = xivmath.build_computed_stats(
            job,
            raw_stats,
            job_mods,
            food.bonuses if food else None,
            party_bonus,
            wd_phys,
            wd_mag,
            delay,
            race=race,
            level=level_value,
        )
        if job in SPELL_SPEED_JOBS:
            gcd = xivmath.sps_to_gcd(2.5, level_data, comp.spellspeed)
        else:
            gcd = xivmath.sks_to_gcd(2.5, level_data, comp.skillspeed)
        attack_type = "Spell" if job in SPELL_SPEED_JOBS else "Weaponskill"
        dmg100 = xivmath.expected_damage_per_potency(
            comp,
            attack_type,
            False,
            crit_chance_bonus=crit_rate_offset,
            dhit_chance_bonus=dhit_rate_offset,
        )
        expected_dmg100 = (
            xivmath.expected_damage_per_potency(comp, attack_type, False)
            if include_expected and (abs(crit_rate_offset) > 1e-12 or abs(dhit_rate_offset) > 1e-12)
            else dmg100
        )
        return dmg100, expected_dmg100, gcd

    if (
        damage_summary
        and baseline_raw_stats
        and baseline_items is not None
        and selected_items is not None
        and fight_duration_ms > 0
        and job_mods is not None
    ):
        if debug:
            sim_log(
                f"[calc-flow] mode={mode} fight_ms={fight_duration_ms} casts={len(casts or [])} "
                f"target_gcd={target_gcd} party={party_bonus} baseline_party={baseline_party_bonus}"
            )
        new_wd_phys, new_wd_mag, new_delay = _weapon_params(selected_items)
        base_comp = eval_ctx.base_comp if eval_ctx and eval_ctx.base_comp is not None else None
        if base_comp is None:
            base_wd_phys, base_wd_mag, base_delay = _weapon_params(baseline_items)
            base_party = party_bonus if baseline_party_bonus is None else baseline_party_bonus
            base_race = baseline_race if baseline_race is not None else race
            base_comp = xivmath.build_computed_stats(
                job,
                baseline_raw_stats,
                job_mods,
                baseline_food.bonuses if baseline_food else None,
                base_party,
                base_wd_phys,
                base_wd_mag,
                base_delay,
                race=base_race,
                level=level_value,
            )
        new_comp = xivmath.build_computed_stats(
            job,
            raw_stats,
            job_mods,
            food.bonuses if food else None,
            party_bonus,
            new_wd_phys,
            new_wd_mag,
            new_delay,
            race=race,
            level=level_value,
        )
        if debug:
            main_stat_id = MAIN_STAT_BY_JOB.get(job, 4)
            main_stat_label = MAIN_STAT_LABELS.get(main_stat_id, f"stat{main_stat_id}")
            sim_log(
                f"[calc-flow] stats base({main_stat_label}={baseline_raw_stats.get(main_stat_id, 0)} crit={baseline_raw_stats.get(27, 0)} "
                f"dhit={baseline_raw_stats.get(22, 0)} det={baseline_raw_stats.get(44, 0)} "
                f"sks={baseline_raw_stats.get(45, 0)} sps={baseline_raw_stats.get(46, 0)} wd={base_wd_mag}) "
                f"new({main_stat_label}={raw_stats.get(main_stat_id, 0)} crit={raw_stats.get(27, 0)} dhit={raw_stats.get(22, 0)} "
                f"det={raw_stats.get(44, 0)} sks={raw_stats.get(45, 0)} sps={raw_stats.get(46, 0)} wd={new_wd_mag})"
            )
            sim_log(
                f"[calc-flow] multipliers base(main={base_comp.main_stat_multi:.6f} wd={base_comp.wd_multi:.6f} "
                f"det={base_comp.det_multi:.6f} crit_rate={base_comp.crit_chance:.6f} dh_rate={base_comp.dhit_chance:.6f}) "
                f"new(main={new_comp.main_stat_multi:.6f} wd={new_comp.wd_multi:.6f} det={new_comp.det_multi:.6f} "
                f"crit_rate={new_comp.crit_chance:.6f} dh_rate={new_comp.dhit_chance:.6f})"
            )
        if job in SPELL_SPEED_JOBS:
            gcd = xivmath.sps_to_gcd(2.5, level_data, new_comp.spellspeed)
        else:
            gcd = xivmath.sks_to_gcd(2.5, level_data, new_comp.skillspeed)
        buckets = damage_summary.get("buckets") or {}
        bucket_counts = damage_summary.get("bucket_counts") or {}
        action_entries = eval_ctx.action_entries if eval_ctx else None
        bucket_entries = eval_ctx.bucket_entries if eval_ctx else None
        ability_buckets = {} if action_entries is not None else (damage_summary.get("ability_buckets") or {})
        if mode in {"simdps", "simdps_self"} and ability_buckets:
            ability_buckets = _apply_party_synergy_to_ability_buckets(
                damage_summary,
                job,
                party_synergies,
                debug=debug,
            )
        ability_names = (eval_ctx.ability_names if eval_ctx else None) or (damage_summary.get("ability_names") or {})
        total_damage_all = (
            eval_ctx.total_damage_all
            if eval_ctx and eval_ctx.total_damage_all
            else float(damage_summary.get("total_amount") or damage_summary.get("total_damage") or 0.0)
        )
        min_ts = eval_ctx.min_ts if eval_ctx else damage_summary.get("min_ts")
        max_ts = eval_ctx.max_ts if eval_ctx else damage_summary.get("max_ts")
        if debug:
            active_time_ms = None
            if min_ts is not None and max_ts is not None and max_ts >= min_ts:
                active_time_ms = max_ts - min_ts
            raw_dps_fight = total_damage_all / (fight_duration_ms / 1000.0) if fight_duration_ms > 0 else 0.0
            raw_dps_active = (
                total_damage_all / (active_time_ms / 1000.0)
                if active_time_ms and active_time_ms > 0
                else 0.0
            )
            sim_log(
                f"[simdps] total_damage_all={total_damage_all:.1f} fight_ms={fight_duration_ms} "
                f"active_ms={active_time_ms} min_ts={min_ts} max_ts={max_ts} "
                f"raw_dps_fight={raw_dps_fight:.1f} raw_dps_active={raw_dps_active:.1f}"
            )
            total_bucket = sum(buckets.values()) or 1.0
            for (atk, is_dot), dmg in sorted(buckets.items(), key=lambda x: x[1], reverse=True):
                cnt = bucket_counts.get((atk, is_dot), 0)
                pct = dmg / total_bucket * 100.0
                sim_log(f"[simdps] bucket {atk} dot={is_dot} dmg={dmg:.1f} ({pct:.1f}%) count={cnt}")
            unknown = damage_summary.get("unknown_actions") or {}
            if unknown:
                unknown_total = sum(v["damage"] for v in unknown.values()) or 0.0
                sim_log(f"[simdps] unknown_total={unknown_total:.1f} ({unknown_total/total_bucket*100:.1f}%)")
                top = sorted(unknown.items(), key=lambda kv: kv[1]["damage"], reverse=True)[:20]
                for (aid, name), info in top:
                    sim_log(f"[simdps] unknown {aid} {name} dmg={info['damage']:.1f} count={info['count']}")

        sim_damage = 0.0
        expected_sim_damage = 0.0
        contrib_rows: List[Tuple[float, str]] = []
        if action_entries is not None:
            action_profiles = eval_ctx.action_profiles if eval_ctx else None
            profile_expected: Optional[List[float]] = None
            expected_profile_expected: Optional[List[float]] = None
            if action_profiles:
                profile_expected = [
                    xivmath.expected_damage_per_potency(
                        new_comp,
                        entry.norm_type,
                        entry.is_dot,
                        auto_dh=entry.force_dh,
                        auto_crit=entry.force_crit,
                        crit_chance_bonus=(
                            entry.crit_bonus
                            + entry.ext_crit_bonus
                            + crit_rate_offset
                        ),
                        dhit_chance_bonus=(
                            entry.dh_bonus
                            + entry.ext_dh_bonus
                            + dhit_rate_offset
                        ),
                        damage_multiplier=(entry.dmg_mult * entry.ext_dmg_mult),
                    )
                    for entry in action_profiles
                ]
                if include_expected and (
                    abs(crit_rate_offset) > 1e-12
                    or abs(dhit_rate_offset) > 1e-12
                ):
                    expected_profile_expected = [
                        xivmath.expected_damage_per_potency(
                            new_comp,
                            entry.norm_type,
                            entry.is_dot,
                            auto_dh=entry.force_dh,
                            auto_crit=entry.force_crit,
                            crit_chance_bonus=(
                                entry.crit_bonus + entry.ext_crit_bonus
                            ),
                            dhit_chance_bonus=(
                                entry.dh_bonus + entry.ext_dh_bonus
                            ),
                            damage_multiplier=(
                                entry.dmg_mult * entry.ext_dmg_mult
                            ),
                        )
                        for entry in action_profiles
                    ]
            for entry in action_entries:
                bucket_damage = entry.bucket_damage
                if profile_expected is not None:
                    new_expected = profile_expected[entry.profile_id]
                else:
                    new_expected = xivmath.expected_damage_per_potency(
                        new_comp,
                        entry.norm_type,
                        entry.is_dot,
                        auto_dh=entry.force_dh,
                        auto_crit=entry.force_crit,
                        crit_chance_bonus=(
                            entry.crit_bonus
                            + entry.ext_crit_bonus
                            + crit_rate_offset
                        ),
                        dhit_chance_bonus=(
                            entry.dh_bonus
                            + entry.ext_dh_bonus
                            + dhit_rate_offset
                        ),
                        damage_multiplier=(
                            entry.dmg_mult * entry.ext_dmg_mult
                        ),
                    )
                ratio = new_expected / max(1e-6, entry.base_expected)
                sim_part = bucket_damage * ratio
                sim_damage += sim_part
                if include_expected and (abs(crit_rate_offset) > 1e-12 or abs(dhit_rate_offset) > 1e-12):
                    if expected_profile_expected is not None:
                        expected_new = expected_profile_expected[entry.profile_id]
                    else:
                        expected_new = xivmath.expected_damage_per_potency(
                            new_comp,
                            entry.norm_type,
                            entry.is_dot,
                            auto_dh=entry.force_dh,
                            auto_crit=entry.force_crit,
                            crit_chance_bonus=(
                                entry.crit_bonus + entry.ext_crit_bonus
                            ),
                            dhit_chance_bonus=(
                                entry.dh_bonus + entry.ext_dh_bonus
                            ),
                            damage_multiplier=(
                                entry.dmg_mult * entry.ext_dmg_mult
                            ),
                        )
                    expected_ratio = expected_new / max(1e-6, entry.base_expected)
                    expected_sim_damage += bucket_damage * expected_ratio
                else:
                    expected_sim_damage += sim_part
                if debug:
                    action_name = ability_names.get(int(entry.action_id), str(entry.action_id))
                    contrib_rows.append(
                        (
                            float(bucket_damage),
                            f"{action_name} atk={entry.norm_type} dot={entry.is_dot} "
                            f"base={entry.base_expected:.6f} new={new_expected:.6f} ratio={ratio:.6f} "
                            f"dmg_mult={entry.dmg_mult:.4f} ext_dmg={entry.ext_dmg_mult:.4f} "
                            f"crit_bonus={entry.crit_bonus:.4f} ext_crit={entry.ext_crit_bonus:.4f} "
                            f"dh_bonus={entry.dh_bonus:.4f} ext_dh={entry.ext_dh_bonus:.4f} "
                            f"force_crit={entry.force_crit} force_dh={entry.force_dh} log={bucket_damage:.1f} sim={sim_part:.1f}",
                        )
                    )
        elif ability_buckets:
            # Action-level replay model: use per-action damage split from the log.
            for key, bucket_damage in ability_buckets.items():
                if not bucket_damage:
                    continue
                crit_bonus = 0.0
                dh_bonus = 0.0
                dmg_mult = 1.0
                force_crit = False
                force_dh = False
                ext_dmg_mult = 1.0
                ext_crit_bonus = 0.0
                ext_dh_bonus = 0.0
                if isinstance(key, tuple) and len(key) >= 8:
                    _action_id, attack_type, is_dot = key[0], key[1], key[2]
                    dmg_mult = float(key[3])
                    crit_bonus = float(key[4])
                    dh_bonus = float(key[5])
                    force_crit = bool(key[6])
                    force_dh = bool(key[7])
                    if len(key) >= 11:
                        ext_dmg_mult = float(key[8])
                        ext_crit_bonus = float(key[9])
                        ext_dh_bonus = float(key[10])
                elif isinstance(key, tuple) and len(key) >= 3:
                    _action_id, attack_type, is_dot = key[0], key[1], key[2]
                else:
                    continue
                norm_type = _normalize_attack_type_for_job(job, attack_type)
                base_expected = xivmath.expected_damage_per_potency(
                    base_comp,
                    norm_type,
                    is_dot,
                    auto_dh=force_dh,
                    auto_crit=force_crit,
                    crit_chance_bonus=crit_bonus,
                    dhit_chance_bonus=dh_bonus,
                    damage_multiplier=dmg_mult,
                )
                new_expected = xivmath.expected_damage_per_potency(
                    new_comp,
                    norm_type,
                    is_dot,
                    auto_dh=force_dh,
                    auto_crit=force_crit,
                    crit_chance_bonus=(crit_bonus + ext_crit_bonus + crit_rate_offset),
                    dhit_chance_bonus=(dh_bonus + ext_dh_bonus + dhit_rate_offset),
                    damage_multiplier=(dmg_mult * ext_dmg_mult),
                )
                ratio = new_expected / max(1e-6, base_expected)
                sim_part = bucket_damage * ratio
                sim_damage += sim_part
                if include_expected and (abs(crit_rate_offset) > 1e-12 or abs(dhit_rate_offset) > 1e-12):
                    expected_new = xivmath.expected_damage_per_potency(
                        new_comp,
                        norm_type,
                        is_dot,
                        auto_dh=force_dh,
                        auto_crit=force_crit,
                        crit_chance_bonus=(crit_bonus + ext_crit_bonus),
                        dhit_chance_bonus=(dh_bonus + ext_dh_bonus),
                        damage_multiplier=(dmg_mult * ext_dmg_mult),
                    )
                    expected_ratio = expected_new / max(1e-6, base_expected)
                    expected_sim_damage += bucket_damage * expected_ratio
                else:
                    expected_sim_damage += sim_part
                if debug:
                    action_name = ability_names.get(int(_action_id), str(_action_id))
                    contrib_rows.append(
                        (
                            float(bucket_damage),
                            f"{action_name} atk={norm_type} dot={is_dot} "
                            f"base={base_expected:.6f} new={new_expected:.6f} ratio={ratio:.6f} "
                            f"dmg_mult={dmg_mult:.4f} ext_dmg={ext_dmg_mult:.4f} "
                            f"crit_bonus={crit_bonus:.4f} ext_crit={ext_crit_bonus:.4f} "
                            f"dh_bonus={dh_bonus:.4f} ext_dh={ext_dh_bonus:.4f} "
                            f"force_crit={force_crit} force_dh={force_dh} log={bucket_damage:.1f} sim={sim_part:.1f}",
                    )
                    )
        else:
            local_bucket_entries = bucket_entries
            if local_bucket_entries is None:
                local_bucket_entries = []
                for key, bucket_damage in buckets.items():
                    if not bucket_damage:
                        continue
                    attack_type, is_dot = key
                    norm_type = _normalize_attack_type_for_job(job, attack_type)
                    local_bucket_entries.append(
                        BucketReplayEntry(
                            bucket_damage=float(bucket_damage),
                            norm_type=norm_type,
                            is_dot=bool(is_dot),
                            base_expected=xivmath.expected_damage_per_potency(base_comp, norm_type, bool(is_dot)),
                            legacy_gcd_adjust=bool(attack_type in {"Spell", "Weaponskill"} and not is_dot),
                        )
                    )
            baseline_gcd_value = eval_ctx.baseline_gcd if eval_ctx else baseline_gcd
            if baseline_gcd_value is None and local_bucket_entries:
                if job in SPELL_SPEED_JOBS:
                    baseline_gcd_value = xivmath.sps_to_gcd(2.5, level_data, base_comp.spellspeed)
                else:
                    baseline_gcd_value = xivmath.sks_to_gcd(2.5, level_data, base_comp.skillspeed)
            for entry in local_bucket_entries:
                new_expected = xivmath.expected_damage_per_potency(
                    new_comp,
                    entry.norm_type,
                    entry.is_dot,
                    crit_chance_bonus=crit_rate_offset,
                    dhit_chance_bonus=dhit_rate_offset,
                )
                ratio = new_expected / max(1e-6, entry.base_expected)
                bucket_sim = entry.bucket_damage * ratio
                # Keep legacy GCD correction in non-action mode only.
                if baseline_gcd_value and entry.legacy_gcd_adjust and mode == "simdps":
                    bucket_sim *= (baseline_gcd_value / max(0.1, gcd))
                sim_damage += bucket_sim
                if include_expected and (abs(crit_rate_offset) > 1e-12 or abs(dhit_rate_offset) > 1e-12):
                    expected_new = xivmath.expected_damage_per_potency(
                        new_comp,
                        entry.norm_type,
                        entry.is_dot,
                    )
                    expected_ratio = expected_new / max(1e-6, entry.base_expected)
                    expected_bucket = entry.bucket_damage * expected_ratio
                    if baseline_gcd_value and entry.legacy_gcd_adjust and mode == "simdps":
                        expected_bucket *= (baseline_gcd_value / max(0.1, gcd))
                    expected_sim_damage += expected_bucket
                else:
                    expected_sim_damage += bucket_sim
                if debug:
                    contrib_rows.append(
                        (
                            float(entry.bucket_damage),
                            f"bucket atk={entry.norm_type} dot={entry.is_dot} base={entry.base_expected:.6f} "
                            f"new={new_expected:.6f} ratio={ratio:.6f} log={entry.bucket_damage:.1f} sim={bucket_sim:.1f}",
                        )
                    )
        dps = sim_damage / (fight_duration_ms / 1000.0)
        expected_dps = expected_sim_damage / (fight_duration_ms / 1000.0)
        if debug:
            sim_log(
                f"[calc-flow] total log={total_damage_all:.1f} sim={sim_damage:.1f} "
                f"dps={dps:.4f} gcd={gcd:.3f} action_buckets={len(ability_buckets)}"
            )
            for _, line in sorted(contrib_rows, key=lambda x: x[0], reverse=True)[:20]:
                sim_log(f"[calc-flow] top {line}")
        if debug:
            # Check ratio sanity when stats are identical
            same_stats = raw_stats == baseline_raw_stats
            same_food = (food is None and baseline_food is None) or (food and baseline_food and food.food_id == baseline_food.food_id)
            if same_stats and same_food:
                check_keys = [
                    ("crit_chance", base_comp.crit_chance, new_comp.crit_chance),
                    ("crit_multi", base_comp.crit_multi, new_comp.crit_multi),
                    ("dhit_chance", base_comp.dhit_chance, new_comp.dhit_chance),
                    ("det_multi", base_comp.det_multi, new_comp.det_multi),
                    ("wd_multi", base_comp.wd_multi, new_comp.wd_multi),
                    ("main_stat_multi", base_comp.main_stat_multi, new_comp.main_stat_multi),
                ]
                mismatched = [(k, a, b) for k, a, b in check_keys if abs(a - b) > 1e-6]
                if mismatched:
                    sim_log("[simdps] ratio sanity check failed (base!=new) components:")
                    for k, a, b in mismatched:
                        sim_log(f"[simdps] {k}: base={a} new={b}")
        return dps, expected_dps, gcd

    # Fallback: weighted score
    # DPS-like weight using actual casts and fight duration
    cast_ratio = 1.0
    if fight_duration_ms > 0 and casts:
        duration_sec = fight_duration_ms / 1000.0
        cpm = len(casts) / (duration_sec / 60.0)
        expected_cpm = 60.0 / max(0.1, gcd)
        cast_ratio = cpm / expected_cpm
        cast_ratio = max(0.5, min(1.5, cast_ratio))

    score = base_score * cast_ratio

    return score, score, gcd


def evaluate_score(
    raw_stats: Dict[int, int],
    job: str,
    casts: List[dict],
    fight_duration_ms: int,
    target_gcd: Optional[float],
    damage_summary: Optional[Dict[str, object]] = None,
    job_mods: Optional[Dict[str, int]] = None,
    food: Optional[FoodRecord] = None,
    party_bonus: int = 0,
    baseline_raw_stats: Optional[Dict[int, int]] = None,
    baseline_items: Optional[Dict[str, ItemRecord]] = None,
    selected_items: Optional[Dict[str, ItemRecord]] = None,
    baseline_food: Optional[FoodRecord] = None,
    baseline_gcd: Optional[float] = None,
    mode: str = "simdps",
    race: Optional[str] = None,
    baseline_party_bonus: Optional[int] = None,
    baseline_race: Optional[str] = None,
    party_synergies: Optional[Dict[str, bool]] = None,
    debug: bool = False,
    level: int = xivmath.CURRENT_MAX_LEVEL,
    crit_rate_offset: float = 0.0,
    dhit_rate_offset: float = 0.0,
    eval_ctx: Optional[ScoreEvalContext] = None,
) -> Tuple[float, float]:
    score, _expected_score, gcd = evaluate_score_pair(
        raw_stats,
        job,
        casts,
        fight_duration_ms,
        target_gcd,
        damage_summary=damage_summary,
        job_mods=job_mods,
        food=food,
        party_bonus=party_bonus,
        baseline_raw_stats=baseline_raw_stats,
        baseline_items=baseline_items,
        selected_items=selected_items,
        baseline_food=baseline_food,
        baseline_gcd=baseline_gcd,
        mode=mode,
        race=race,
        baseline_party_bonus=baseline_party_bonus,
        baseline_race=baseline_race,
        party_synergies=party_synergies,
        debug=debug,
        level=level,
        crit_rate_offset=crit_rate_offset,
        dhit_rate_offset=dhit_rate_offset,
        include_expected=False,
        eval_ctx=eval_ctx,
    )
    return score, gcd


def apply_food(stats: Dict[int, int], food: Optional[FoodRecord]) -> Dict[int, int]:
    if not food:
        return stats
    new_stats = stats.copy()
    for stat_id, bonus in food.bonuses.items():
        current = stats.get(stat_id, 0)
        add = min(int(current * (bonus.percentage / 100)), bonus.maximum)
        new_stats[stat_id] = current + add
    return new_stats


def materia_value_lookup(category: MateriaCategory, grade: int) -> Optional[MateriaGrade]:
    for g in category.grades:
        if g.grade == grade:
            return g
    return None


def meld_stats_for_item(
    item: ItemRecord,
    melds: List[MateriaSlotSelection],
    materia_catalog: Dict[int, MateriaCategory],
    cap_table: Dict[Tuple[int, int], int],
) -> Dict[int, int]:
    if not melds:
        return {}
    caps = {stat: remaining_cap_for_item(item, stat, cap_table) for stat in MELDABLE_STATS}
    agg: Dict[int, int] = {}
    for meld in melds:
        if not meld or meld.base_param <= 0 or meld.grade <= 0:
            continue
        cat = materia_catalog.get(meld.base_param)
        if not cat:
            continue
        grade = materia_value_lookup(cat, meld.grade)
        if not grade:
            continue
        remain = caps.get(meld.base_param, 0)
        if remain <= 0:
            continue
        value = min(grade.value, remain)
        if value <= 0:
            continue
        caps[meld.base_param] = remain - value
        agg[meld.base_param] = agg.get(meld.base_param, 0) + value
    return agg


@lru_cache(maxsize=128)
def _meld_count_compositions(
    total_slots: int,
    stat_count: int,
) -> Tuple[Tuple[int, ...], ...]:
    if stat_count <= 0:
        return ((),)
    if stat_count == 1:
        return ((max(0, int(total_slots)),),)

    values: List[Tuple[int, ...]] = []

    def append_compositions(remaining: int, remaining_stats: int, prefix: Tuple[int, ...]) -> None:
        if remaining_stats == 1:
            values.append(prefix + (remaining,))
            return
        for count in range(remaining + 1):
            append_compositions(
                remaining - count,
                remaining_stats - 1,
                prefix + (count,),
            )

    append_compositions(max(0, int(total_slots)), int(stat_count), ())
    return tuple(values)


def optimization_score_upper_bound(
    gearset: Gearset,
    selected_items: Dict[str, ItemRecord],
    no_meld_slots: set,
    context: OptimizationWorkerContext,
    *,
    stop_event=None,
) -> float:
    """Return a score upper bound; infinity means the candidate must be evaluated."""

    job = str(gearset.job or "")
    mode = str(context.mode or "")
    if not job or not selected_items or not context.job_mods:
        return math.inf
    if mode in {"simdps", "simdps_self"} and not (
        context.damage_summary
        and context.baseline_raw_stats
        and context.baseline_items is not None
        and context.fight_duration_ms > 0
    ):
        # The fallback weighted score has a target-GCD weight discontinuity and
        # is intentionally not used for mathematical pruning.
        return math.inf
    if mode not in {"dmg100p", "simdps", "simdps_self"}:
        return math.inf

    relevant_stats = tuple(sorted(allowed_meld_stats(job)))
    if not relevant_stats:
        return math.inf
    max_materia_value = max(
        (
            int(grade.value or 0)
            for stat_id in relevant_stats
            for grade in (context.materia_catalog.get(stat_id).grades if context.materia_catalog.get(stat_id) else [])
        ),
        default=0,
    )
    if max_materia_value <= 0:
        return math.inf

    raw_stats = aggregate_base_stats(selected_items)
    free_slots = 0
    global_caps = {stat_id: 0 for stat_id in relevant_stats}
    for slot, item in selected_items.items():
        if slot in no_meld_slots:
            continue
        selection = (gearset.items or {}).get(slot)
        if _selection_lock_item(selection) and _selection_lock_materia(selection):
            fixed_stats = meld_stats_for_item(
                item,
                list(selection.materia or []),
                context.materia_catalog,
                context.cap_table,
            )
            for stat_id, value in fixed_stats.items():
                raw_stats[stat_id] = int(raw_stats.get(stat_id, 0)) + int(value)
            continue
        free_slots += total_meld_slots_for_item(item)
        for stat_id in relevant_stats:
            global_caps[stat_id] += remaining_cap_for_item(
                item,
                stat_id,
                context.cap_table,
            )

    composition_count = math.comb(
        free_slots + len(relevant_stats) - 1,
        len(relevant_stats) - 1,
    )
    if composition_count > UPPER_BOUND_MAX_COMPOSITIONS:
        return math.inf

    foods = list(context.foods or [])
    if not foods:
        return math.inf
    level_value = gearset_level(gearset)
    eval_ctx = prepare_score_eval_context(
        job,
        context.damage_summary,
        context.baseline_raw_stats,
        context.baseline_items,
        context.baseline_food,
        context.baseline_gcd,
        context.job_mods,
        context.party_bonus,
        context.baseline_party_bonus,
        gearset.race,
        context.baseline_race,
        context.party_synergies,
        mode,
        level_value,
    )
    best_score = float("-inf")
    for composition_index, counts in enumerate(
        _meld_count_compositions(free_slots, len(relevant_stats))
    ):
        if (
            stop_event is not None
            and (composition_index % 256) == 0
            and stop_event.is_set()
        ):
            return math.inf
        optimistic_stats = dict(raw_stats)
        for stat_id, count in zip(relevant_stats, counts):
            optimistic_stats[stat_id] = int(optimistic_stats.get(stat_id, 0)) + min(
                int(count) * max_materia_value,
                int(global_caps.get(stat_id, 0)),
            )
        for food in foods:
            score, _gcd = evaluate_score(
                optimistic_stats,
                job,
                context.casts,
                context.fight_duration_ms,
                None,
                damage_summary=context.damage_summary,
                job_mods=context.job_mods,
                food=food,
                party_bonus=context.party_bonus,
                baseline_raw_stats=context.baseline_raw_stats,
                baseline_items=context.baseline_items,
                selected_items=selected_items,
                baseline_food=context.baseline_food,
                baseline_gcd=context.baseline_gcd,
                mode=mode,
                race=gearset.race,
                baseline_party_bonus=context.baseline_party_bonus,
                baseline_race=context.baseline_race,
                party_synergies=context.party_synergies,
                level=level_value,
                crit_rate_offset=context.crit_rate_offset,
                dhit_rate_offset=context.dhit_rate_offset,
                eval_ctx=eval_ctx,
            )
            if not math.isfinite(score):
                return math.inf
            best_score = max(best_score, float(score))
    if best_score == float("-inf"):
        return math.inf
    return math.nextafter(best_score, math.inf)


def compute_dmg100p_weights(
    job: str,
    base_stats: Dict[int, int],
    job_mods: Optional[Dict[str, int]],
    selected_items: Optional[Dict[str, ItemRecord]],
    party_bonus: int = 0,
    food: Optional[FoodRecord] = None,
    race: Optional[str] = None,
    level: int = xivmath.CURRENT_MAX_LEVEL,
    crit_rate_offset: float = 0.0,
    dhit_rate_offset: float = 0.0,
) -> Dict[int, float]:
    default = {27: 1.0, 22: 0.9, 44: 0.75, 45: 0.6, 46: 0.6, 19: 0.2, 6: 0.15}
    if not job_mods or not selected_items:
        return default
    level_value = normalized_level(level)
    wd_phys, wd_mag, delay = _weapon_params(selected_items)
    comp_base = xivmath.build_computed_stats(
        job,
        base_stats,
        job_mods,
        food.bonuses if food else None,
        party_bonus,
        wd_phys,
        wd_mag,
        delay,
        race=race,
        level=level_value,
    )
    attack_type = "Spell" if job in SPELL_SPEED_JOBS else "Weaponskill"
    base_dmg = xivmath.expected_damage_per_potency(
        comp_base,
        attack_type,
        False,
        crit_chance_bonus=crit_rate_offset,
        dhit_chance_bonus=dhit_rate_offset,
    )
    weights: Dict[int, float] = {}
    for stat_id in MELDABLE_STATS:
        test_stats = dict(base_stats)
        test_stats[stat_id] = test_stats.get(stat_id, 0) + 1
        comp = xivmath.build_computed_stats(
            job,
            test_stats,
            job_mods,
            food.bonuses if food else None,
            party_bonus,
            wd_phys,
            wd_mag,
            delay,
            race=race,
            level=level_value,
        )
        dmg = xivmath.expected_damage_per_potency(
            comp,
            attack_type,
            False,
            crit_chance_bonus=crit_rate_offset,
            dhit_chance_bonus=dhit_rate_offset,
        )
        weights[stat_id] = max(0.0, dmg - base_dmg)
    return weights or default


def generate_meld_combos(
    item: ItemRecord,
    materia_catalog: Dict[int, MateriaCategory],
    stat_weights: Dict[int, float],
    cap_table: Dict[Tuple[str, int], int],
    slot_limit: int = 15,
    max_grades: int = 2,
    allowed_stats: Optional[set] = None,
    overcap_loss: int = MATERIA_ACCEPTABLE_OVERCAP_LOSS,
    grade_policy: str = "top",
    candidate_limit: int = 20,
    score_fn: Optional[Callable[[Dict[int, int]], float]] = None,
    base_stats_for_score: Optional[Dict[int, int]] = None,
) -> List[Tuple[Dict[int, int], List[MateriaSlotSelection], float]]:
    if allowed_stats is None:
        allowed_stats = MELDABLE_STATS
    base_caps = {stat: remaining_cap_for_item(item, stat, cap_table) for stat in allowed_stats}
    slots_total = total_meld_slots_for_item(item)
    if slots_total <= 0:
        return [({}, [], 0.0)]

    # candidate materia choices per slot (respecting overmeld restrictions)
    candidates_by_slot: List[List[Tuple[int, MateriaGrade]]] = []
    for slot_idx in range(slots_total):
        slot_candidates: List[Tuple[int, MateriaGrade]] = []
        for stat_id, cat in materia_catalog.items():
            if stat_id not in allowed_stats:
                continue
            slot_candidates.extend(
                (stat_id, grade)
                for grade in grades_for_slot(
                    item,
                    cat.grades,
                    slot_idx,
                    max_grades=max_grades,
                    policy=grade_policy,
                )
            )
        if len(slot_candidates) > candidate_limit:
            slot_candidates.sort(
                key=lambda x: (stat_weights.get(x[0], 0.0) * x[1].value),
                reverse=True,
            )
            slot_candidates = slot_candidates[:candidate_limit]
        candidates_by_slot.append(slot_candidates)
    if any(not slot_candidates for slot_candidates in candidates_by_slot):
        return [({}, [], 0.0)]

    # Beam search per item to avoid exponential explosion (keeps top candidates by score_est).
    beam: List[Tuple[float, Dict[int, int], List[MateriaSlotSelection], Dict[int, int]]] = [
        (0.0, {}, [], base_caps.copy())
    ]
    for slot_idx in range(slots_total):
        new_states: List[
            Tuple[float, Dict[int, int], List[MateriaSlotSelection], Dict[int, int]]
        ] = []
        for score_est, agg, melds, caps in beam:
            for stat_id, grade in candidates_by_slot[slot_idx]:
                remain = caps.get(stat_id, 0)
                if remain <= 0:
                    continue
                if grade.value - remain > overcap_loss:
                    continue
                value = min(grade.value, remain)
                if value <= 0:
                    continue
                new_caps = caps.copy()
                new_caps[stat_id] = remain - value
                new_agg = agg.copy()
                new_agg[stat_id] = new_agg.get(stat_id, 0) + value
                new_melds = melds + [MateriaSlotSelection(base_param=stat_id, grade=grade.grade)]
                new_score = score_est + value * stat_weights.get(stat_id, 0.0)
                new_states.append((new_score, new_agg, new_melds, new_caps))
        if not new_states:
            return [({}, [], 0.0)]
        if len(new_states) > slot_limit:
            new_states = heapq.nlargest(slot_limit, new_states, key=lambda x: x[0])
        beam = new_states

    combos: List[Tuple[Dict[int, int], List[MateriaSlotSelection], float]] = []
    for score_est, stats, melds, _caps in beam:
        if score_fn:
            if base_stats_for_score:
                stats_for_score = base_stats_for_score.copy()
                for stat_id, val in stats.items():
                    stats_for_score[stat_id] = stats_for_score.get(stat_id, 0) + val
            else:
                stats_for_score = stats
            score = score_fn(stats_for_score)
        else:
            score = score_est
        combos.append((stats, melds, score))
    combos.sort(key=lambda x: x[2], reverse=True)
    return combos or [({}, [], 0.0)]


def optimize(
    gearset: Gearset,
    items_by_id: Dict[int, ItemRecord],
    materia_catalog: Dict[int, MateriaCategory],
    foods: List[Optional[FoodRecord]],
    casts: List[dict],
    fight_duration_ms: int,
    cap_table: Dict[Tuple[str, int], int],
    damage_summary: Optional[Dict[str, float]] = None,
    baseline_raw_stats: Optional[Dict[int, int]] = None,
    baseline_items: Optional[Dict[str, ItemRecord]] = None,
    baseline_gcd: Optional[float] = None,
    gcd_constraint: Optional[LogGcdConstraint] = None,
    job_mods: Optional[Dict[str, int]] = None,
    baseline_food: Optional[FoodRecord] = None,
    party_bonus: int = 0,
    baseline_party_bonus: Optional[int] = None,
    mode: str = "simdps",
    baseline_race: Optional[str] = None,
    party_synergies: Optional[Dict[str, bool]] = None,
    crit_rate_offset: float = 0.0,
    dhit_rate_offset: float = 0.0,
    selected_items_override: Optional[Dict[str, ItemRecord]] = None,
    no_meld_slots: Optional[set] = None,
    progress: Optional[Callable[[int, str], None]] = None,
    stop_event=None,
    beam_width: int = 40,
) -> List[Tuple[Gearset, float, float]]:
    debug_enabled = sim_debug_enabled()
    # Validate selected items
    level_value = gearset_level(gearset)
    if selected_items_override is not None:
        selected_items = dict(selected_items_override)
    else:
        selected_items = {}
        seen_unique: Dict[int, bool] = {}
        for slot, selection in gearset.items.items():
            if not selection.item_id:
                continue
            item = items_by_id.get(selection.item_id)
            if not item:
                continue
            if item.unique and item.item_id in seen_unique:
                # duplicate unique item; skip this slot
                continue
            if item.unique:
                seen_unique[item.item_id] = True
            selected_items[slot] = item
    base_stats = aggregate_base_stats(selected_items)
    speed_stat_id = 46 if (gearset.job or "") in SPELL_SPEED_JOBS else 45
    fixed_materia_slots: Dict[str, List[MateriaSlotSelection]] = {}
    for slot, selection in (gearset.items or {}).items():
        if slot not in selected_items:
            continue
        if not (_selection_lock_item(selection) and _selection_lock_materia(selection)):
            continue
        fixed_materia_slots[slot] = list(selection.materia or [])
    total_meld_slots_cache: Dict[int, int] = {}
    meld_stats_cache: Dict[Tuple[int, Tuple[Tuple[int, int], ...]], Dict[int, int]] = {}

    def _total_meld_slots_cached(item: ItemRecord) -> int:
        item_id = int(item.item_id)
        cached = total_meld_slots_cache.get(item_id)
        if cached is not None:
            return cached
        cached = total_meld_slots_for_item(item)
        total_meld_slots_cache[item_id] = cached
        return cached

    def _meld_stats_for_item_cached(
        item: ItemRecord,
        melds: List[MateriaSlotSelection],
    ) -> Dict[int, int]:
        if not melds:
            return {}
        cache_key = (
            int(item.item_id),
            tuple((int(m.base_param), int(m.grade)) for m in melds if m),
        )
        cached = meld_stats_cache.get(cache_key)
        if cached is not None:
            return cached
        computed = meld_stats_for_item(item, melds, materia_catalog, cap_table)
        meld_stats_cache[cache_key] = computed
        return computed

    # Initial pruning weights (neutralized to avoid DH/DET bias in candidate pruning).
    stat_weights = {27: 1.0, 22: 1.0, 44: 1.0, 45: 1.0, 46: 1.0, 19: 1.0, 6: 1.0}

    allowed_stats = allowed_meld_stats(gearset.job or "")
    max_grades = 1 if mode == "dmg100p" else 2
    grade_policy = "best" if mode == "dmg100p" else "top"
    overcap_loss = MATERIA_ACCEPTABLE_OVERCAP_LOSS
    score_fn: Optional[Callable[[Dict[int, int]], float]] = None
    beam_score_fn: Optional[Callable[[Dict[int, int]], float]] = None
    race = getattr(gearset, "race", None)
    eval_ctx = prepare_score_eval_context(
        gearset.job or "",
        damage_summary,
        baseline_raw_stats,
        baseline_items,
        baseline_food,
        baseline_gcd,
        job_mods,
        party_bonus,
        baseline_party_bonus,
        race,
        baseline_race,
        party_synergies,
        mode,
        level_value,
    )
    if mode == "dmg100p":
        per_item_limit = 10000
        candidate_limit = 260
        beam_width = max(beam_width, 2600)
        stat_weights = compute_dmg100p_weights(
            gearset.job or "",
            base_stats,
            job_mods,
            selected_items,
            party_bonus=party_bonus,
            food=baseline_food,
            race=race,
            level=level_value,
            crit_rate_offset=crit_rate_offset,
            dhit_rate_offset=dhit_rate_offset,
        )
        if job_mods and selected_items:
            wd_phys, wd_mag, delay = _weapon_params(selected_items)
            food_bonuses = baseline_food.bonuses if baseline_food else None
            is_spell = gearset.job in SPELL_SPEED_JOBS

            def _score(stats: Dict[int, int]) -> float:
                comp = xivmath.build_computed_stats(
                    gearset.job or "",
                    stats,
                    job_mods,
                    food_bonuses,
                    party_bonus,
                    wd_phys,
                    wd_mag,
                    delay,
                    race=race,
                    level=level_value,
                )
                attack_type = "Spell" if is_spell else "Weaponskill"
                return xivmath.expected_damage_per_potency(
                    comp,
                    attack_type,
                    False,
                    crit_chance_bonus=crit_rate_offset,
                    dhit_chance_bonus=dhit_rate_offset,
                )

            score_fn = _score

            def _beam_score(inc_stats: Dict[int, int]) -> float:
                merged = base_stats.copy()
                for stat_id, val in inc_stats.items():
                    merged[stat_id] = merged.get(stat_id, 0) + val
                return _score(merged)

            beam_score_fn = _beam_score
    else:
        per_item_limit = 80
        candidate_limit = 110
        beam_width = max(beam_width, 640)
        # When target GCD is strict, widen search and prioritize speed-oriented melds.
        target_gcd = gearset.target_gcd
        if target_gcd:
            base_speed = base_stats.get(speed_stat_id, 0) + level_stats(level_value).base_sub
            current_gcd = calc_gcd_seconds(base_speed, gearset.job or "", level=level_value)
            if not gcd_meets_target(current_gcd, target_gcd):
                gcd_gap = current_gcd - target_gcd
                speed_weight = min(4.0, 1.5 + gcd_gap * 10.0)
                stat_weights[speed_stat_id] = max(stat_weights.get(speed_stat_id, 0.6), speed_weight)
                per_item_limit = max(per_item_limit, 180)
                candidate_limit = max(candidate_limit, 180)
                beam_width = max(beam_width, 960)

    if debug_enabled:
        sim_log(
            "[opt] start "
            f"mode={mode} job={gearset.job} slots={len(selected_items)} target_gcd={gearset.target_gcd} "
            "profile=high_precision "
            f"beam_width={beam_width} per_item_limit={per_item_limit} candidate_limit={candidate_limit}"
        )

    per_slot_combos: Dict[str, List[Tuple[Dict[int, int], List[MateriaSlotSelection], float]]] = {}
    slots_to_process = list(selected_items.items())
    total_slots = len(slots_to_process)
    for idx, (slot, item) in enumerate(slots_to_process):
        if stop_event and stop_event.is_set():
            return []
        if no_meld_slots and slot in no_meld_slots:
            per_slot_combos[slot] = [({}, [], 0.0)]
            if progress:
                pct = int(((idx + 1) / max(1, total_slots)) * 25)
                slot_label = SLOT_LABELS.get(slot, slot)
                progress(pct, f"{slot_label} はレベルシンクでマテリア無効")
            continue
        if slot in fixed_materia_slots:
            fixed_melds = list(fixed_materia_slots.get(slot) or [])
            per_slot_combos[slot] = [(_meld_stats_for_item_cached(item, fixed_melds), fixed_melds, 0.0)]
            if progress:
                pct = int(((idx + 1) / max(1, total_slots)) * 25)
                slot_label = SLOT_LABELS.get(slot, slot)
                progress(pct, f"{slot_label} は固定マテリアを使用")
            continue
        combos = generate_meld_combos(
            item,
            materia_catalog,
            stat_weights,
            cap_table,
            slot_limit=per_item_limit,
            max_grades=max_grades,
            allowed_stats=allowed_stats,
            overcap_loss=overcap_loss,
            grade_policy=grade_policy,
            candidate_limit=candidate_limit,
            score_fn=score_fn,
            base_stats_for_score=base_stats,
        )
        per_slot_combos[slot] = combos
        if debug_enabled:
            sim_log(
                f"[opt] slot_candidates slot={slot} item={item.item_id} combos={len(combos)} "
                f"no_meld={bool(no_meld_slots and slot in no_meld_slots)}"
            )
        if progress:
            pct = int(((idx + 1) / max(1, total_slots)) * 25)
            slot_label = SLOT_LABELS.get(slot, slot)
            progress(pct, f"{slot_label} のマテリア候補を準備中")

    exact_mode_requested = mode == "dmg100p" and job_mods and selected_items
    if (
        not exact_mode_requested
        and mode in {"simdps", "simdps_self"}
        and selected_items
    ):
        # High precision simdps: prefer exact DP by stat-vector to avoid
        # beam-pruning misses on near-tie DET/CRT/DH distributions.
        exact_mode_requested = True
        if debug_enabled:
            sim_log("[opt] exact_mode requested reason=high_precision_simdps")

    # A single None explicitly means that no food is fixed for this run.
    no_food_fixed = len(foods) == 1 and foods[0] is None
    combat_foods = highest_item_level_combat_foods(foods)
    combat_foods.sort(key=lambda f: (-(f.level_item or 0), int(f.food_id or 0)))
    if not combat_foods and not no_food_fixed:
        if progress:
            progress(100, "戦闘向け食事が見つかりません")
        return []

    # Candidate foods: include every stat the current job can benefit from.
    # Restricting this to CRT/DH/DET/speed drops TEN-only and PIE-only foods.
    relevant_stats = set(allowed_stats)
    main_stat_id = MAIN_STAT_BY_JOB.get(gearset.job or "")
    if main_stat_id is not None:
        relevant_stats.add(main_stat_id)
    relevant_stats.add(3)  # Keep VIT/HP equivalent when pruning food candidates.
    candidate_foods: List[Optional[FoodRecord]]
    if no_food_fixed:
        candidate_foods = [None]
    else:
        candidate_foods = [
            f for f in combat_foods if any(stat in f.bonuses for stat in relevant_stats)
        ] or combat_foods
        candidate_foods = non_dominated_combat_foods(
            candidate_foods,
            relevant_stats,
        )
        candidate_foods.sort(
            key=lambda f: (-(f.level_item or 0), int(f.food_id or 0))
        )
    foods_by_id = {f.food_id: f for f in foods if f is not None}
    if debug_enabled:
        sim_log(
            f"[opt] food_candidates combat={len(combat_foods)} relevant={len(candidate_foods)} "
            f"speed_stat_id={speed_stat_id}"
        )

    level_base_sub = int(level_stats(level_value).base_sub)
    base_speed_raw = int(base_stats.get(speed_stat_id, 0))
    strict_gcd_mode = bool(gearset.target_gcd)
    required_speed_stat = required_speed_stat_for_target_gcd(
        gearset.job or "",
        gearset.target_gcd,
        level=level_value,
    ) if strict_gcd_mode else None
    speed_foods = [
        f
        for f in candidate_foods
        if f is not None and speed_stat_id in (f.bonuses or {})
    ]
    per_speed_keep = 24
    max_food_speed_bonus_cache: Dict[int, int] = {}

    def _max_food_speed_bonus(raw_speed: int) -> int:
        cached = max_food_speed_bonus_cache.get(raw_speed)
        if cached is not None:
            return cached
        if not speed_foods:
            max_food_speed_bonus_cache[raw_speed] = 0
            return 0
        best = 0
        total_speed = int(raw_speed) + level_base_sub
        for f in speed_foods:
            bonus = (f.bonuses or {}).get(speed_stat_id)
            if not bonus:
                continue
            add = min(int(total_speed * (bonus.percentage / 100)), int(bonus.maximum))
            if add > best:
                best = add
        max_food_speed_bonus_cache[raw_speed] = best
        return best

    if strict_gcd_mode and required_speed_stat is not None:
        # Target GCD already satisfied without meld speed: avoid strict
        # speed-only pruning, which can drop stronger DET/CRT/DH paths.
        base_speed_stat = base_speed_raw + _max_food_speed_bonus(base_speed_raw) + level_base_sub
        if base_speed_stat >= required_speed_stat:
            strict_gcd_mode = False
            if debug_enabled:
                sim_log(
                    f"[opt] strict_gcd disabled reason=already_satisfied "
                    f"required_speed={required_speed_stat} base_speed_stat={base_speed_stat}"
                )

    slot_max_speed: List[int] = []
    for slot, _item in slots_to_process:
        combos = per_slot_combos.get(slot, [])
        slot_max = 0
        for stats_map, _melds, _score in combos:
            slot_max = max(slot_max, int(stats_map.get(speed_stat_id, 0)))
        slot_max_speed.append(slot_max)
    remaining_max_speed: List[int] = [0] * (len(slot_max_speed) + 1)
    for idx in range(len(slot_max_speed) - 1, -1, -1):
        remaining_max_speed[idx] = remaining_max_speed[idx + 1] + slot_max_speed[idx]
    if strict_gcd_mode and required_speed_stat is not None:
        max_raw_speed = base_speed_raw + remaining_max_speed[0]
        max_speed_stat = max_raw_speed + _max_food_speed_bonus(max_raw_speed) + level_base_sub
        if max_speed_stat < required_speed_stat:
            if debug_enabled:
                sim_log(
                    f"[opt] strict_gcd_unreachable required_speed={required_speed_stat} max_speed={max_speed_stat} "
                    f"base_speed={base_speed_raw} remaining_max_speed={remaining_max_speed[0]}"
                )
            if progress:
                progress(100, "目標GCDを満たす速度が不足しています")
            return []
        if debug_enabled:
            sim_log(
                f"[opt] strict_gcd enabled required_speed={required_speed_stat} "
                f"base_speed={base_speed_raw} max_speed={max_speed_stat}"
            )

    # Reuse score evaluations across beam, food, and local refinement loops.
    # Keyed by combat-relevant stats + food id for the current optimize call context.
    eval_cache: Dict[Tuple[Tuple[int, ...], int], Tuple[float, float]] = {}

    def _stats_cache_key(stats: Dict[int, int]) -> Tuple[int, ...]:
        return (
            int(stats.get(1, 0)),
            int(stats.get(2, 0)),
            int(stats.get(3, 0)),
            int(stats.get(4, 0)),
            int(stats.get(5, 0)),
            int(stats.get(6, 0)),
            int(stats.get(19, 0)),
            int(stats.get(22, 0)),
            int(stats.get(27, 0)),
            int(stats.get(44, 0)),
            int(stats.get(45, 0)),
            int(stats.get(46, 0)),
        )

    def _evaluate_direct(
        stats: Dict[int, int],
        food: Optional[FoodRecord],
    ) -> Tuple[float, float]:
        return evaluate_score(
            stats,
            gearset.job or "",
            casts,
            fight_duration_ms,
            gearset.target_gcd,
            damage_summary=damage_summary,
            job_mods=job_mods,
            food=food,
            party_bonus=party_bonus,
            baseline_raw_stats=baseline_raw_stats,
            baseline_items=baseline_items,
            selected_items=selected_items,
            baseline_gcd=baseline_gcd,
            baseline_food=baseline_food,
            baseline_party_bonus=baseline_party_bonus,
            baseline_race=baseline_race,
            party_synergies=party_synergies,
            mode=mode,
            race=race,
            level=level_value,
            crit_rate_offset=crit_rate_offset,
            dhit_rate_offset=dhit_rate_offset,
            eval_ctx=eval_ctx,
        )

    def _evaluate_with_cache(
        stats: Dict[int, int],
        food: Optional[FoodRecord],
    ) -> Tuple[float, float]:
        food_id = int(food.food_id) if food else 0
        key = (_stats_cache_key(stats), food_id)
        cached = eval_cache.get(key)
        if cached is not None:
            return cached
        computed = _evaluate_direct(stats, food)
        eval_cache[key] = computed
        return computed

    def _build_candidate_gearset(
        meld_map: Dict[str, List[MateriaSlotSelection]],
        food: Optional[FoodRecord],
        meld_changes: Optional[int] = None,
    ) -> Gearset:
        candidate = Gearset(
            job=gearset.job,
            items={
                slot: MateriaAwareSelection(
                    sel,
                    [] if (no_meld_slots and slot in no_meld_slots) else meld_map.get(slot, []),
                )
                for slot, sel in gearset.items.items()
            },
            food_id=food.food_id if food else None,
            food_simulation=bool(getattr(gearset, "food_simulation", False)),
            target_gcd=gearset.target_gcd,
            note=gearset.note,
            race=gearset.race,
            level=level_value,
        )
        if meld_changes is None:
            meld_changes = _meld_map_change_count(meld_map)
        setattr(candidate, "_optimizer_meld_change_count", int(meld_changes))
        return candidate

    def _meld_counter(melds) -> Tuple[Dict[Tuple[int, int], int], int]:
        counter: Dict[Tuple[int, int], int] = {}
        total = 0
        for meld in melds or []:
            if not meld:
                continue
            try:
                stat_id = int(meld.base_param)
                grade = int(meld.grade)
            except (TypeError, ValueError, OverflowError):
                continue
            if stat_id <= 0 or grade <= 0:
                continue
            key = (stat_id, grade)
            counter[key] = counter.get(key, 0) + 1
            total += 1
        return counter, total

    baseline_meld_counters: Dict[
        str,
        Tuple[Dict[Tuple[int, int], int], int],
    ] = {
        slot: ({}, 0)
        if (no_meld_slots and slot in no_meld_slots)
        else _meld_counter(sel.materia if sel else [])
        for slot, sel in (gearset.items or {}).items()
    }
    def _meld_map_change_count(
        meld_map: Dict[str, List[MateriaSlotSelection]],
    ) -> int:
        total_changes = 0
        for slot, (base_counter, base_total) in baseline_meld_counters.items():
            cand_counter, cand_total = _meld_counter(meld_map.get(slot))
            unchanged = sum(
                min(base_count, cand_counter.get(key, 0))
                for key, base_count in base_counter.items()
            )
            total_changes += max(base_total, cand_total) - unchanged
        for slot, melds in meld_map.items():
            if slot not in baseline_meld_counters:
                _counter, cand_total = _meld_counter(melds)
                total_changes += cand_total
        return total_changes

    def _meld_node_change_count(meld_node: Optional[ExactStateNode]) -> int:
        total_changes = 0
        seen_slots: set[str] = set()
        current = meld_node
        while current is not None:
            slot = current.slot
            seen_slots.add(slot)
            base_counter, base_total = baseline_meld_counters.get(slot, ({}, 0))
            cand_counter, cand_total = _meld_counter(current.melds)
            unchanged = sum(
                min(base_count, cand_counter.get(key, 0))
                for key, base_count in base_counter.items()
            )
            total_changes += max(base_total, cand_total) - unchanged
            current = current.parent
        for slot, (_base_counter, base_total) in baseline_meld_counters.items():
            if slot not in seen_slots:
                total_changes += base_total
        return total_changes

    def _meld_change_count(gs: Gearset) -> int:
        cached = getattr(gs, "_optimizer_meld_change_count", None)
        if isinstance(cached, int):
            return cached
        total_changes = _meld_map_change_count(
            {
                slot: list(selection.materia or [])
                for slot, selection in (gs.items or {}).items()
                if selection is not None
            }
        )
        setattr(gs, "_optimizer_meld_change_count", total_changes)
        return total_changes

    def _result_sort_key(entry: Tuple[Gearset, float, float]) -> Tuple[float, int, float]:
        gs, score, gcd = entry
        return (-float(score), _meld_change_count(gs), float(gcd))

    def _stats_for_gearset(gs: Gearset) -> Dict[int, int]:
        merged = base_stats.copy()
        for slot, item in selected_items.items():
            if no_meld_slots and slot in no_meld_slots:
                continue
            sel = gs.items.get(slot)
            melds = list(sel.materia) if sel and sel.materia else []
            added = _meld_stats_for_item_cached(item, melds)
            for stat_id, val in added.items():
                merged[stat_id] = merged.get(stat_id, 0) + val
        return merged

    # Fast score used in stage-1 candidate filtering (stage-2 uses evaluate_score).
    coarse_duration_sec = (fight_duration_ms / 1000.0) if fight_duration_ms > 0 else 0.0
    coarse_cpm = (len(casts) / (coarse_duration_sec / 60.0)) if coarse_duration_sec > 0 and casts else 0.0
    coarse_speed_stat_id = 46 if (gearset.job or "") in SPELL_SPEED_JOBS else 45

    def _coarse_candidate_score(
        stats: Dict[int, int],
        food: Optional[FoodRecord],
    ) -> Tuple[float, float]:
        fed_stats = apply_food(stats, food)
        gcd_stat = int(fed_stats.get(coarse_speed_stat_id, 0))
        raw_speed = int(stats.get(coarse_speed_stat_id, 0))
        total_speed = raw_speed + level_base_sub
        speed_bonus = (food.bonuses or {}).get(coarse_speed_stat_id) if food else None
        if speed_bonus:
            total_speed += min(
                int(total_speed * int(speed_bonus.percentage) / 100),
                int(speed_bonus.maximum),
            )
        gcd = calc_gcd_seconds(total_speed, gearset.job or "", level=level_value)

        crit = fed_stats.get(27, 0)
        dh = fed_stats.get(22, 0)
        det = fed_stats.get(44, 0)
        ten = fed_stats.get(19, 0)
        pie = fed_stats.get(6, 0)
        speed = gcd_stat
        speed_weight = float(stat_weights.get(coarse_speed_stat_id, 1.0))
        if gearset.target_gcd and gcd > gearset.target_gcd:
            speed_weight += min(2.0, (gcd - gearset.target_gcd) * 3)

        base_score = (
            crit * float(stat_weights.get(27, 1.0))
            + dh * float(stat_weights.get(22, 1.0))
            + det * float(stat_weights.get(44, 1.0))
            + speed * speed_weight
            + ten * float(stat_weights.get(19, 1.0))
            + pie * float(stat_weights.get(6, 1.0))
        )

        cast_ratio = 1.0
        if coarse_cpm > 0.0:
            expected_cpm = 60.0 / max(0.1, gcd)
            cast_ratio = coarse_cpm / expected_cpm
            cast_ratio = max(0.5, min(1.5, cast_ratio))
        return base_score * cast_ratio, gcd

    results: List[Tuple[Gearset, float, float]] = []

    exact_mode_fallback = False
    exact_states: Dict[Any, Optional[ExactStateNode]] = {}
    relevant_stats_sorted: List[int] = []
    relevant_stat_index: Dict[int, int] = {}
    exact_stat_tuple_len = 0
    exact_pack_bits = 0
    exact_pack_mask = 0
    exact_pack_shifts: List[int] = []
    if exact_mode_requested:
        relevant_stats_sorted = sorted(allowed_stats)
        relevant_stat_index = {
            stat_id: idx for idx, stat_id in enumerate(relevant_stats_sorted)
        }
        exact_stat_tuple_len = len(relevant_stats_sorted)
        if exact_stat_tuple_len in {4, 5}:
            max_totals = [0] * exact_stat_tuple_len
            packable = True
            for slot, _item in slots_to_process:
                combos = per_slot_combos.get(slot, [])
                for stat_index, stat_id in enumerate(relevant_stats_sorted):
                    values = [int(stats.get(stat_id, 0)) for stats, _melds, _score in combos]
                    if any(value < 0 for value in values):
                        packable = False
                        break
                    max_totals[stat_index] += max(values, default=0)
                if not packable:
                    break
            if packable:
                exact_pack_bits = max(1, max(max_totals, default=0).bit_length())
                exact_pack_mask = (1 << exact_pack_bits) - 1
                exact_pack_shifts = [
                    stat_index * exact_pack_bits
                    for stat_index in range(exact_stat_tuple_len)
                ]
        zero_stats_key: Any = 0 if exact_pack_bits else tuple(
            0 for _ in range(exact_stat_tuple_len)
        )
        speed_stat_tuple_index = relevant_stat_index.get(speed_stat_id, -1)
        exact_states = {zero_stats_key: None}
        if debug_enabled:
            sim_log(
                f"[opt] exact_mode enabled packed={bool(exact_pack_bits)} "
                f"lane_bits={exact_pack_bits}"
            )
        exact_state_limit = 600000 if mode in {"simdps", "simdps_self"} else 1200000

        for slot_idx, (slot, _item) in enumerate(slots_to_process):
            if stop_event and stop_event.is_set():
                return []
            combos = per_slot_combos.get(slot, [])
            unique_combo_entries: List[
                Tuple[Any, Tuple[MateriaSlotSelection, ...]]
            ] = []
            seen_combo_tuples: set[Any] = set()
            for add_stats, melds, _score in combos:
                add_stats_tuple = tuple(
                    int(add_stats.get(stat_id, 0))
                    for stat_id in relevant_stats_sorted
                )
                add_stats_key: Any
                if exact_pack_bits:
                    add_stats_key = sum(
                        value << exact_pack_shifts[stat_index]
                        for stat_index, value in enumerate(add_stats_tuple)
                    )
                else:
                    add_stats_key = add_stats_tuple
                if add_stats_key in seen_combo_tuples:
                    continue
                seen_combo_tuples.add(add_stats_key)
                unique_combo_entries.append((add_stats_key, tuple(melds)))
            before_count = len(exact_states)
            if exact_pack_bits:
                new_map, limit_hit = _expand_packed_exact_state_stage(
                    exact_states,
                    unique_combo_entries,
                    slot,
                    strict_gcd_mode=bool(
                        strict_gcd_mode and required_speed_stat is not None
                    ),
                    required_speed_stat=int(required_speed_stat or 0),
                    speed_shift=(
                        exact_pack_shifts[speed_stat_tuple_index]
                        if speed_stat_tuple_index >= 0
                        else 0
                    ),
                    lane_mask=exact_pack_mask,
                    base_speed_raw=base_speed_raw,
                    remaining_speed=remaining_max_speed[slot_idx + 1],
                    level_base_sub=level_base_sub,
                    max_food_speed_bonus=_max_food_speed_bonus,
                    enforce_state_limit=mode in {"simdps", "simdps_self"},
                    state_limit=exact_state_limit,
                )
            else:
                new_map, limit_hit = _expand_exact_state_stage(
                    exact_states,
                    unique_combo_entries,
                    slot,
                    exact_stat_tuple_len,
                    strict_gcd_mode=bool(
                        strict_gcd_mode and required_speed_stat is not None
                    ),
                    required_speed_stat=int(required_speed_stat or 0),
                    speed_tuple_index=speed_stat_tuple_index,
                    base_speed_raw=base_speed_raw,
                    remaining_speed=remaining_max_speed[slot_idx + 1],
                    level_base_sub=level_base_sub,
                    max_food_speed_bonus=_max_food_speed_bonus,
                    enforce_state_limit=mode in {"simdps", "simdps_self"},
                    state_limit=exact_state_limit,
                )
            if limit_hit:
                exact_mode_fallback = True
            if debug_enabled:
                sim_log(
                    f"[opt] exact_stage slot={slot} base_states={before_count} "
                    f"combos={len(combos)} unique_combos={len(unique_combo_entries)} "
                    f"after_states={len(new_map)}"
                )
            exact_states = new_map
            if exact_mode_fallback:
                if debug_enabled:
                    sim_log(
                        f"[opt] exact_mode_fallback reason=state_limit_exceeded "
                        f"limit={exact_state_limit} current={len(exact_states)}"
                    )
                break
            if progress:
                pct = 25 + int(((slot_idx + 1) / max(1, total_slots)) * 25)
                progress(min(50, pct), "マテリアセットを組み合わせ中")

        if not exact_mode_fallback:
            if debug_enabled:
                sim_log(f"[opt] exact_food_eval states={len(exact_states)} foods={len(candidate_foods)}")
            exact_state_count = len(exact_states)
            exact_candidates: Optional[
                List[Tuple[int, Any, Optional[ExactStateNode]]]
            ] = None
            adaptive_fallback_candidates: List[
                Tuple[int, Any, Optional[ExactStateNode]]
            ] = []
            adaptive_shortlist_enabled = False
            adaptive_gap_threshold = 4.0
            crit_idx = relevant_stat_index.get(27)
            dh_idx = relevant_stat_index.get(22)
            det_idx = relevant_stat_index.get(44)
            ten_idx = relevant_stat_index.get(19)
            pie_idx = relevant_stat_index.get(6)
            speed_idx = relevant_stat_index.get(speed_stat_id)

            def _tuple_stat(stats_tuple: Any, stat_idx: Optional[int]) -> int:
                if stat_idx is None:
                    return 0
                if exact_pack_bits:
                    return int(
                        (stats_tuple >> exact_pack_shifts[stat_idx])
                        & exact_pack_mask
                    )
                return int(stats_tuple[stat_idx])

            # Exact evaluation can be very expensive for simdps high-precision.
            # Keep exact state construction, then shortlist by a cheap coarse score
            # with stat-mix diversity before running full evaluate_score.
            if mode in {"simdps", "simdps_self"} and exact_state_count > 12000:
                single_food_mode = len(candidate_foods) == 1 and not strict_gcd_mode
                if single_food_mode:
                    # Single-food + fixed-GCD runs: start with a smaller shortlist,
                    # then expand only when top candidates are near-tie.
                    shortlist_limit = 6000
                    fallback_shortlist_limit = 8000
                    shortlist_per_mix = 6
                    adaptive_shortlist_enabled = True
                else:
                    shortlist_limit = 12000
                    fallback_shortlist_limit = shortlist_limit
                    shortlist_per_mix = 8
                base_crit = int(base_stats.get(27, 0))
                base_dh = int(base_stats.get(22, 0))
                base_det = int(base_stats.get(44, 0))
                base_ten = int(base_stats.get(19, 0))
                base_pie = int(base_stats.get(6, 0))
                base_speed = int(base_stats.get(speed_stat_id, 0))
                # Keep only top entries globally and per-stat-mix while streaming
                # to avoid full materialization+sort of every exact state.
                mix_heaps: Dict[
                    Tuple[int, int, int, int],
                    List[Tuple[float, int, Any, Optional[ExactStateNode]]],
                ] = {}
                global_heap: List[
                    Tuple[float, int, Any, Optional[ExactStateNode]]
                ] = []
                scored_count = 0
                seq = 0
                w_crit = float(stat_weights.get(27, 1.0))
                w_dh = float(stat_weights.get(22, 1.0))
                w_det = float(stat_weights.get(44, 1.0))
                w_ten = float(stat_weights.get(19, 1.0))
                w_pie = float(stat_weights.get(6, 1.0))
                w_speed_base = float(stat_weights.get(speed_stat_id, 1.0))
                coarse_food_profiles = []
                coarse_speed_profiles: List[
                    Dict[int, Tuple[int, float, float, float, bool]]
                ] = []

                def _apply_bonus(val: int, bonus) -> int:
                    if not bonus:
                        return val
                    return val + min((val * int(bonus.percentage)) // 100, int(bonus.maximum))

                if exact_pack_bits and speed_idx is not None:
                    speed_shift = exact_pack_shifts[speed_idx]
                    exact_speed_values = {
                        base_speed
                        + ((int(stats_key) >> speed_shift) & exact_pack_mask)
                        for stats_key in exact_states.keys()
                    }
                else:
                    exact_speed_values = {
                        base_speed + _tuple_stat(stats_key, speed_idx)
                        for stats_key in exact_states.keys()
                    }

                def _bonus_pair(bonus) -> Tuple[int, int]:
                    if not bonus:
                        return 0, 0
                    return int(bonus.percentage), int(bonus.maximum)

                for candidate_food in candidate_foods:
                    bonuses = candidate_food.bonuses if candidate_food else {}
                    coarse_food_profiles.append(
                        (
                            _bonus_pair(bonuses.get(27)),
                            _bonus_pair(bonuses.get(22)),
                            _bonus_pair(bonuses.get(44)),
                            _bonus_pair(bonuses.get(19)),
                            _bonus_pair(bonuses.get(6)),
                        )
                    )
                    bonus_speed = bonuses.get(speed_stat_id)
                    speed_profile: Dict[
                        int,
                        Tuple[int, float, float, float, bool],
                    ] = {}
                    for speed_val in exact_speed_values:
                        fed_speed = _apply_bonus(speed_val, bonus_speed)
                        fed_speed_total = _apply_bonus(
                            speed_val + level_base_sub,
                            bonus_speed,
                        )
                        coarse_gcd = calc_gcd_seconds(
                            fed_speed_total,
                            gearset.job or "",
                            level=level_value,
                        )
                        valid = gcd_meets_constraints(
                            coarse_gcd,
                            gearset.target_gcd,
                            gcd_constraint,
                        )
                        speed_weight_local = w_speed_base
                        if gearset.target_gcd and coarse_gcd > gearset.target_gcd:
                            speed_weight_local += min(
                                2.0,
                                (coarse_gcd - gearset.target_gcd) * 3,
                            )
                        cast_ratio = 1.0
                        if coarse_cpm > 0.0:
                            expected_cpm = 60.0 / max(0.1, coarse_gcd)
                            cast_ratio = coarse_cpm / expected_cpm
                            cast_ratio = max(0.5, min(1.5, cast_ratio))
                        speed_profile[speed_val] = (
                            fed_speed,
                            coarse_gcd,
                            speed_weight_local,
                            cast_ratio,
                            valid,
                        )
                    coarse_speed_profiles.append(speed_profile)

                def _exact_state_rows():
                    if exact_pack_bits:
                        mask = exact_pack_mask
                        crit_shift = exact_pack_shifts[crit_idx] if crit_idx is not None else None
                        dh_shift = exact_pack_shifts[dh_idx] if dh_idx is not None else None
                        det_shift = exact_pack_shifts[det_idx] if det_idx is not None else None
                        ten_shift = exact_pack_shifts[ten_idx] if ten_idx is not None else None
                        pie_shift = exact_pack_shifts[pie_idx] if pie_idx is not None else None
                        speed_shift_local = (
                            exact_pack_shifts[speed_idx]
                            if speed_idx is not None
                            else None
                        )
                        for stats_key, node in exact_states.items():
                            yield (
                                stats_key,
                                node,
                                base_crit
                                + (
                                    (stats_key >> crit_shift) & mask
                                    if crit_shift is not None
                                    else 0
                                ),
                                base_dh
                                + (
                                    (stats_key >> dh_shift) & mask
                                    if dh_shift is not None
                                    else 0
                                ),
                                base_det
                                + (
                                    (stats_key >> det_shift) & mask
                                    if det_shift is not None
                                    else 0
                                ),
                                base_ten
                                + (
                                    (stats_key >> ten_shift) & mask
                                    if ten_shift is not None
                                    else 0
                                ),
                                base_pie
                                + (
                                    (stats_key >> pie_shift) & mask
                                    if pie_shift is not None
                                    else 0
                                ),
                                base_speed
                                + (
                                    (stats_key >> speed_shift_local) & mask
                                    if speed_shift_local is not None
                                    else 0
                                ),
                            )
                        return
                    for stats_key, node in exact_states.items():
                        yield (
                            stats_key,
                            node,
                            base_crit + _tuple_stat(stats_key, crit_idx),
                            base_dh + _tuple_stat(stats_key, dh_idx),
                            base_det + _tuple_stat(stats_key, det_idx),
                            base_ten + _tuple_stat(stats_key, ten_idx),
                            base_pie + _tuple_stat(stats_key, pie_idx),
                            base_speed + _tuple_stat(stats_key, speed_idx),
                        )

                for (
                    meld_stats_tuple,
                    meld_node,
                    crit_val,
                    dh_val,
                    det_val,
                    ten_val,
                    pie_val,
                    speed_val,
                ) in _exact_state_rows():
                    if stop_event and stop_event.is_set():
                        break

                    best_coarse: Optional[float] = None
                    for food_index, (
                        bonus_crit,
                        bonus_dh,
                        bonus_det,
                        bonus_ten,
                        bonus_pie,
                    ) in enumerate(coarse_food_profiles):
                        fed_crit = (
                            crit_val
                            + min(
                                (crit_val * bonus_crit[0]) // 100,
                                bonus_crit[1],
                            )
                            if bonus_crit[0]
                            else crit_val
                        )
                        fed_dh = (
                            dh_val
                            + min(
                                (dh_val * bonus_dh[0]) // 100,
                                bonus_dh[1],
                            )
                            if bonus_dh[0]
                            else dh_val
                        )
                        fed_det = (
                            det_val
                            + min(
                                (det_val * bonus_det[0]) // 100,
                                bonus_det[1],
                            )
                            if bonus_det[0]
                            else det_val
                        )
                        fed_ten = (
                            ten_val
                            + min(
                                (ten_val * bonus_ten[0]) // 100,
                                bonus_ten[1],
                            )
                            if bonus_ten[0]
                            else ten_val
                        )
                        fed_pie = (
                            pie_val
                            + min(
                                (pie_val * bonus_pie[0]) // 100,
                                bonus_pie[1],
                            )
                            if bonus_pie[0]
                            else pie_val
                        )
                        (
                            fed_speed,
                            _coarse_gcd,
                            speed_weight_local,
                            cast_ratio,
                            valid,
                        ) = coarse_speed_profiles[food_index][speed_val]
                        if not valid:
                            continue
                        coarse_score = (
                            fed_crit * w_crit
                            + fed_dh * w_dh
                            + fed_det * w_det
                            + fed_speed * speed_weight_local
                            + fed_ten * w_ten
                            + fed_pie * w_pie
                        )
                        coarse_score *= cast_ratio
                        if best_coarse is None or coarse_score > best_coarse:
                            best_coarse = coarse_score
                    if best_coarse is None:
                        continue
                    scored_count += 1

                    mix_sig = (
                        int(crit_val // 18),
                        int(dh_val // 18),
                        int(det_val // 18),
                        int(speed_val // 18),
                    )
                    mix_heap = mix_heaps.get(mix_sig)
                    if mix_heap is None:
                        mix_heap = []
                        mix_heaps[mix_sig] = mix_heap
                    keep_for_mix = len(mix_heap) < shortlist_per_mix or float(best_coarse) > mix_heap[0][0]
                    keep_for_global = (
                        len(global_heap) < fallback_shortlist_limit
                        or float(best_coarse) > global_heap[0][0]
                    )
                    if not keep_for_mix and not keep_for_global:
                        continue

                    seq += 1
                    packed = (float(best_coarse), seq, meld_stats_tuple, meld_node)

                    if keep_for_mix:
                        if len(mix_heap) < shortlist_per_mix:
                            heapq.heappush(mix_heap, packed)
                        elif packed[0] > mix_heap[0][0]:
                            heapq.heapreplace(mix_heap, packed)

                    if keep_for_global:
                        if len(global_heap) < fallback_shortlist_limit:
                            heapq.heappush(global_heap, packed)
                        elif packed[0] > global_heap[0][0]:
                            heapq.heapreplace(global_heap, packed)

                shortlist_entries: List[
                    Tuple[float, int, Any, Optional[ExactStateNode]]
                ] = []
                for mix_heap in mix_heaps.values():
                    shortlist_entries.extend(sorted(mix_heap, key=lambda x: x[0], reverse=True))
                shortlist_entries.sort(key=lambda x: x[0], reverse=True)
                if len(shortlist_entries) > shortlist_limit:
                    shortlist_entries = shortlist_entries[:shortlist_limit]
                if len(shortlist_entries) < shortlist_limit and global_heap:
                    seen_seq = {entry[1] for entry in shortlist_entries}
                    for entry in sorted(global_heap, key=lambda x: x[0], reverse=True):
                        if entry[1] in seen_seq:
                            continue
                        shortlist_entries.append(entry)
                        seen_seq.add(entry[1])
                        if len(shortlist_entries) >= shortlist_limit:
                            break

                exact_candidates = [
                    (_seq, stats_key_tuple, meld_node)
                    for _c, _seq, stats_key_tuple, meld_node in shortlist_entries
                ]
                if adaptive_shortlist_enabled and len(global_heap) > len(exact_candidates):
                    seen_seq = {_seq for _seq, _stats, _map in exact_candidates}
                    adaptive_fallback_candidates = []
                    for _c, _seq, stats_key_tuple, meld_node in sorted(global_heap, key=lambda x: x[0], reverse=True):
                        if _seq in seen_seq:
                            continue
                        adaptive_fallback_candidates.append((_seq, stats_key_tuple, meld_node))
                        if len(exact_candidates) + len(adaptive_fallback_candidates) >= fallback_shortlist_limit:
                            break
                if debug_enabled:
                    sim_log(
                        f"[opt] exact_shortlist total_states={exact_state_count} "
                        f"scored={scored_count} shortlisted={len(exact_candidates)} "
                        f"per_mix={shortlist_per_mix}"
                    )

            exact_evaluated = 0
            exact_kept = 0
            # Exact mode does not run the later local-refinement path and returns
            # at most eight variants. Keep enough entries for all final checks,
            # but defer Gearset construction until the heap is finalized.
            exact_result_limit = 96
            exact_heap: List[
                Tuple[
                    float,
                    int,
                    float,
                    int,
                    Optional[ExactStateNode],
                    Optional[FoodRecord],
                    float,
                ]
            ] = []
            exact_seq = 0

            def _combined_stats_from_exact_key(stats_key_tuple: Any) -> Dict[int, int]:
                combined_stats = base_stats.copy()
                for stat_idx, stat_id in enumerate(relevant_stats_sorted):
                    val = _tuple_stat(stats_key_tuple, stat_idx)
                    if not val:
                        continue
                    combined_stats[stat_id] = combined_stats.get(stat_id, 0) + int(val)
                return combined_stats

            if exact_candidates is None:
                eval_source = exact_states.items()
                eval_total = exact_state_count
            else:
                eval_source = exact_candidates
                eval_total = len(exact_candidates)
            evaluated_candidate_seqs: set[int] = set()

            for idx, source_entry in enumerate(eval_source):
                if stop_event and stop_event.is_set():
                    break
                if exact_candidates is None:
                    meld_stats_tuple, meld_node = source_entry
                    combined_stats = _combined_stats_from_exact_key(meld_stats_tuple)
                else:
                    candidate_seq, meld_stats_tuple, meld_node = source_entry
                    evaluated_candidate_seqs.add(candidate_seq)
                    combined_stats = _combined_stats_from_exact_key(meld_stats_tuple)
                resolved_meld_changes: Optional[int] = None
                for food in candidate_foods:
                    exact_evaluated += 1
                    score, gcd = _evaluate_with_cache(combined_stats, food)
                    if not gcd_meets_constraints(gcd, gearset.target_gcd, gcd_constraint):
                        continue
                    exact_kept += 1
                    exact_seq += 1
                    score_value = float(score)
                    if (
                        len(exact_heap) >= exact_result_limit
                        and score_value < exact_heap[0][0]
                    ):
                        continue
                    if resolved_meld_changes is None:
                        resolved_meld_changes = _meld_node_change_count(meld_node)
                    rank = (
                        score_value,
                        -int(resolved_meld_changes or 0),
                        -float(gcd),
                    )
                    if len(exact_heap) < exact_result_limit or rank > (
                        exact_heap[0][0],
                        exact_heap[0][1],
                        exact_heap[0][2],
                    ):
                        heap_entry = (
                            rank[0],
                            rank[1],
                            rank[2],
                            exact_seq,
                            meld_node,
                            food,
                            float(gcd),
                        )
                    else:
                        continue
                    if len(exact_heap) < exact_result_limit:
                        heapq.heappush(exact_heap, heap_entry)
                    else:
                        heapq.heapreplace(exact_heap, heap_entry)
                if progress:
                    pct = 50 + int((idx + 1) / max(1, eval_total) * 45)
                    progress(pct, "食事ごとに評価中")
            if (
                adaptive_shortlist_enabled
                and adaptive_fallback_candidates
                and not (stop_event and stop_event.is_set())
            ):
                distinct_scores: List[float] = []
                if exact_heap:
                    for val in sorted((entry[0] for entry in exact_heap), reverse=True):
                        if not distinct_scores or abs(val - distinct_scores[-1]) > 1e-6:
                            distinct_scores.append(val)
                        if len(distinct_scores) >= 2:
                            break
                score_gap = float("inf")
                if len(distinct_scores) >= 2:
                    score_gap = float(distinct_scores[0] - distinct_scores[1])
                should_expand = score_gap <= adaptive_gap_threshold
                if debug_enabled:
                    sim_log(
                        f"[opt] exact_shortlist_adaptive gap={score_gap:.4f} "
                        f"threshold={adaptive_gap_threshold:.4f} "
                        f"expand={'yes' if should_expand else 'no'} "
                        f"extra_pool={len(adaptive_fallback_candidates)}"
                    )
                if should_expand:
                    extra_evaluated = 0
                    extra_kept = 0
                    for extra_idx, (candidate_seq, meld_stats_tuple, meld_node) in enumerate(adaptive_fallback_candidates, 1):
                        if stop_event and stop_event.is_set():
                            break
                        if candidate_seq in evaluated_candidate_seqs:
                            continue
                        evaluated_candidate_seqs.add(candidate_seq)
                        combined_stats = _combined_stats_from_exact_key(meld_stats_tuple)
                        resolved_meld_changes: Optional[int] = None
                        for food in candidate_foods:
                            exact_evaluated += 1
                            extra_evaluated += 1
                            score, gcd = _evaluate_with_cache(combined_stats, food)
                            if not gcd_meets_constraints(gcd, gearset.target_gcd, gcd_constraint):
                                continue
                            exact_kept += 1
                            extra_kept += 1
                            exact_seq += 1
                            score_value = float(score)
                            if (
                                len(exact_heap) >= exact_result_limit
                                and score_value < exact_heap[0][0]
                            ):
                                continue
                            if resolved_meld_changes is None:
                                resolved_meld_changes = _meld_node_change_count(meld_node)
                            rank = (
                                score_value,
                                -int(resolved_meld_changes or 0),
                                -float(gcd),
                            )
                            if len(exact_heap) < exact_result_limit or rank > (
                                exact_heap[0][0],
                                exact_heap[0][1],
                                exact_heap[0][2],
                            ):
                                heap_entry = (
                                    rank[0],
                                    rank[1],
                                    rank[2],
                                    exact_seq,
                                    meld_node,
                                    food,
                                    float(gcd),
                                )
                            else:
                                continue
                            if len(exact_heap) < exact_result_limit:
                                heapq.heappush(exact_heap, heap_entry)
                            else:
                                heapq.heapreplace(exact_heap, heap_entry)
                        if progress:
                            pct = 95 + int((extra_idx / max(1, len(adaptive_fallback_candidates))) * 4)
                            progress(min(99, pct), "上位候補を追加評価中")
                    if debug_enabled:
                        sim_log(
                            f"[opt] exact_shortlist_adaptive_done extra_evaluated={extra_evaluated} "
                            f"extra_accepted={extra_kept}"
                        )
            if exact_heap:
                exact_sorted = sorted(
                    exact_heap,
                    key=lambda entry: (
                        entry[0],
                        entry[1],
                        entry[2],
                        entry[3],
                    ),
                    reverse=True,
                )
                meld_map_cache: Dict[
                    int,
                    Dict[str, List[MateriaSlotSelection]],
                ] = {}
                for score, neg_changes, _neg_gcd, _seq, meld_node, food, gcd in exact_sorted:
                    node_key = id(meld_node)
                    meld_map = meld_map_cache.get(node_key)
                    if meld_map is None:
                        meld_map = _reconstruct_exact_meld_map(meld_node)
                        meld_map_cache[node_key] = meld_map
                    results.append(
                        (
                            _build_candidate_gearset(
                                meld_map,
                                food,
                                -neg_changes,
                            ),
                            score,
                            gcd,
                        )
                    )
            if debug_enabled:
                sim_log(
                    f"[opt] exact_food_eval_done evaluated={exact_evaluated} accepted={exact_kept} "
                    f"kept_top={len(exact_heap)}"
                )
    if not exact_mode_requested or exact_mode_fallback:
        # Beam search across slots
        beam: List[Tuple[Dict[int, int], Dict[str, List[MateriaSlotSelection]], float]] = [
            ({}, {}, 0.0)
        ]
        if debug_enabled:
            sim_log(f"[opt] beam_mode start beam_states={len(beam)}")

        def _state_mix_signature(
            state: Tuple[Dict[int, int], Dict[str, List[MateriaSlotSelection]], float]
        ) -> Tuple[int, int, int, int]:
            agg_stats = state[0]
            # Quantize by one meld tier (18) to keep stat-mix diversity.
            return (
                int(agg_stats.get(27, 0) // 18),
                int(agg_stats.get(22, 0) // 18),
                int(agg_stats.get(44, 0) // 18),
                int(agg_stats.get(speed_stat_id, 0) // 18),
            )

        def _select_diverse(
            states: List[Tuple[Dict[int, int], Dict[str, List[MateriaSlotSelection]], float]],
            limit: int,
            rank_key: Callable[[Tuple[Dict[int, int], Dict[str, List[MateriaSlotSelection]], float]], Tuple],
        ) -> List[Tuple[Dict[int, int], Dict[str, List[MateriaSlotSelection]], float]]:
            if len(states) <= limit:
                return states
            ordered = sorted(states, key=rank_key)
            chosen: List[Tuple[Dict[int, int], Dict[str, List[MateriaSlotSelection]], float]] = []
            seen_mix = set()
            for st in ordered:
                sig = _state_mix_signature(st)
                if sig in seen_mix:
                    continue
                chosen.append(st)
                seen_mix.add(sig)
                if len(chosen) >= limit:
                    return chosen
            if len(chosen) < limit:
                chosen_set = set(id(x) for x in chosen)
                for st in ordered:
                    if id(st) in chosen_set:
                        continue
                    chosen.append(st)
                    if len(chosen) >= limit:
                        break
            return chosen

        for slot_idx, (slot, _item) in enumerate(slots_to_process):
            new_beam = []
            combos = per_slot_combos.get(slot, [])
            for base_stats_contrib, melds, score_est in combos:
                for agg_stats, meld_map, agg_score in beam:
                    merged_stats = agg_stats.copy()
                    for stat_id, val in base_stats_contrib.items():
                        merged_stats[stat_id] = merged_stats.get(stat_id, 0) + val
                    merged_meld_map = dict(meld_map)
                    merged_meld_map[slot] = melds
                    if beam_score_fn:
                        new_score = beam_score_fn(merged_stats)
                    else:
                        new_score = agg_score + score_est
                    new_beam.append((merged_stats, merged_meld_map, new_score))
            pre_prune_count = len(new_beam)
            if strict_gcd_mode and required_speed_stat is not None:
                remain_speed = remaining_max_speed[slot_idx + 1]
                feasible_beam: List[Tuple[Dict[int, int], Dict[str, List[MateriaSlotSelection]], float]] = []
                for state in new_beam:
                    agg_stats, _meld_map, _score = state
                    speed_add = int(agg_stats.get(speed_stat_id, 0))
                    max_raw_speed = base_speed_raw + speed_add + remain_speed
                    max_speed_stat = max_raw_speed + _max_food_speed_bonus(max_raw_speed) + level_base_sub
                    if max_speed_stat >= required_speed_stat:
                        feasible_beam.append(state)
                new_beam = feasible_beam
                if not new_beam:
                    beam = []
                    if debug_enabled:
                        sim_log(
                            f"[opt] beam_stage slot={slot} combos={len(combos)} pre={pre_prune_count} "
                            "post=0 strict_gcd_pruned_all=true"
                        )
                    break

                # Keep diversity by speed tier so target-GCD candidates are not pruned early.
                by_speed: Dict[int, List[Tuple[Dict[int, int], Dict[str, List[MateriaSlotSelection]], float]]] = {}
                for state in new_beam:
                    speed_add = int(state[0].get(speed_stat_id, 0))
                    by_speed.setdefault(speed_add, []).append(state)
                compact: List[Tuple[Dict[int, int], Dict[str, List[MateriaSlotSelection]], float]] = []
                for states in by_speed.values():
                    states.sort(key=lambda x: x[2], reverse=True)
                    compact.extend(states[:per_speed_keep])

                def _beam_rank(
                    state: Tuple[Dict[int, int], Dict[str, List[MateriaSlotSelection]], float]
                ) -> Tuple[int, int, float]:
                    agg_stats, _meld_map, score_est = state
                    speed_add = int(agg_stats.get(speed_stat_id, 0))
                    raw_speed = base_speed_raw + speed_add
                    current_speed_stat = raw_speed + _max_food_speed_bonus(raw_speed) + level_base_sub
                    if current_speed_stat >= required_speed_stat:
                        # Prefer closer-to-target GCD first, then estimated score.
                        return (0, current_speed_stat - required_speed_stat, -score_est)
                    return (1, required_speed_stat - current_speed_stat, -score_est)

                compact.sort(key=_beam_rank)
                beam = _select_diverse(compact, beam_width, _beam_rank)
                if debug_enabled:
                    sim_log(
                        f"[opt] beam_stage slot={slot} combos={len(combos)} pre={pre_prune_count} "
                        f"feasible={len(new_beam)} compact={len(compact)} post={len(beam)} strict_gcd=true"
                    )
            else:
                # keep top beam_width by estimated score
                beam = _select_diverse(
                    new_beam,
                    beam_width,
                    rank_key=lambda x: (-x[2],),
                )
                if debug_enabled:
                    sim_log(
                        f"[opt] beam_stage slot={slot} combos={len(combos)} pre={pre_prune_count} "
                        f"post={len(beam)} strict_gcd=false"
                    )
            if progress:
                pct = 25 + int(((slot_idx + 1) / max(1, total_slots)) * 25)
                progress(min(50, pct), "マテリアセットを組み合わせ中")
            if stop_event and stop_event.is_set():
                return []

        coarse_pool: List[
            Tuple[float, Dict[int, int], Dict[str, List[MateriaSlotSelection]], FoodRecord]
        ] = []
        for meld_stats, meld_map, _ in beam:
            if stop_event and stop_event.is_set():
                break
            combined_stats = base_stats.copy()
            for stat_id, val in meld_stats.items():
                combined_stats[stat_id] = combined_stats.get(stat_id, 0) + val
            for food in candidate_foods:
                coarse_score, coarse_gcd = _coarse_candidate_score(combined_stats, food)
                if not gcd_meets_constraints(coarse_gcd, gearset.target_gcd, gcd_constraint):
                    continue
                coarse_pool.append((coarse_score, combined_stats, meld_map, food))
        if debug_enabled:
            sim_log(
                f"[opt] coarse_pool beam_states={len(beam)} foods={len(candidate_foods)} "
                f"coarse_candidates={len(coarse_pool)}"
            )

        if coarse_pool:
            # Stage-1/2:
            #  1) coarse rank to keep many promising candidates cheaply
            #  2) strict evaluate_score only on shortlisted candidates
            stage2_limit = max(
                beam_width * 5,
                480,
            )
            if mode == "simdps":
                stage2_limit = max(stage2_limit, 960)
            if mode == "simdps_self":
                stage2_limit = max(stage2_limit, 1440)
            if strict_gcd_mode:
                stage2_limit = max(stage2_limit, 1800)
            coarse_pool.sort(key=lambda x: x[0], reverse=True)
            shortlisted = coarse_pool[: min(len(coarse_pool), stage2_limit)]
            sim_log(
                f"[opt] shortlist stage2_limit={stage2_limit} shortlisted={len(shortlisted)} "
                f"coarse_total={len(coarse_pool)}"
            )

            strict_evaluated = 0
            strict_kept = 0
            for idx, (_coarse, combined_stats, meld_map, food) in enumerate(shortlisted):
                if stop_event and stop_event.is_set():
                    break
                strict_evaluated += 1
                score, gcd = _evaluate_with_cache(combined_stats, food)
                if not gcd_meets_constraints(gcd, gearset.target_gcd, gcd_constraint):
                    continue
                new_gearset = _build_candidate_gearset(meld_map, food)
                results.append((new_gearset, score, gcd))
                strict_kept += 1
                if progress:
                    pct = 50 + int((idx + 1) / max(1, len(shortlisted)) * 45)
                    progress(pct, "食事ごとに評価中")
            if debug_enabled:
                sim_log(
                    f"[opt] strict_eval_done evaluated={strict_evaluated} accepted={strict_kept}"
                )

    # Safety net: always include the current meld/food as a valid candidate.
    # This guarantees optimization won't regress below the starting setup.
    current_food = foods_by_id.get(gearset.food_id) if gearset.food_id is not None else None
    current_meld_map: Dict[str, List[MateriaSlotSelection]] = {}
    current_stats = base_stats.copy()
    for slot, item in selected_items.items():
        sel = gearset.items.get(slot)
        melds = [] if (no_meld_slots and slot in no_meld_slots) else list(sel.materia) if sel and sel.materia else []
        current_meld_map[slot] = melds
        if no_meld_slots and slot in no_meld_slots:
            continue
        add_stats = _meld_stats_for_item_cached(item, melds)
        for stat_id, val in add_stats.items():
            current_stats[stat_id] = current_stats.get(stat_id, 0) + val
    current_score, current_gcd = _evaluate_with_cache(current_stats, current_food)
    if gcd_meets_constraints(current_gcd, gearset.target_gcd, gcd_constraint):
        results.append((
            _build_candidate_gearset(current_meld_map, current_food),
            current_score,
            current_gcd,
        ))
        if debug_enabled:
            sim_log(f"[opt] baseline_candidate score={current_score:.4f} gcd={current_gcd:.3f}")

    # keep multiple equivalent best variants available for the UI
    results.sort(key=_result_sort_key)

    if (
        mode in {"dmg100p", "simdps_self"}
        and results
        and job_mods
        and selected_items
        and (not exact_mode_requested or exact_mode_fallback)
    ):
        foods_by_id = {f.food_id: f for f in foods}
        refine_slot_limit = 200000 if mode == "dmg100p" else max(4000, per_item_limit * 20)
        refine_candidate_limit = candidate_limit if mode == "dmg100p" else max(candidate_limit * 3, 80)
        refine_iterations = 2
        if mode != "dmg100p":
            refine_slot_limit = max(refine_slot_limit, per_item_limit * 30)
            refine_candidate_limit = max(refine_candidate_limit, candidate_limit * 5, 160)
            refine_iterations = 3

        def _stats_add(target: Dict[int, int], delta: Dict[int, int], sign: int = 1) -> Dict[int, int]:
            for stat_id, val in delta.items():
                target[stat_id] = target.get(stat_id, 0) + sign * val
                if target[stat_id] == 0:
                    del target[stat_id]
            return target

        refine_slot_combos_cache: Dict[str, List[Tuple[Dict[int, int], List[MateriaSlotSelection], float]]] = {}

        def _refine_slot_combos(slot: str, item: ItemRecord) -> List[Tuple[Dict[int, int], List[MateriaSlotSelection], float]]:
            cached = refine_slot_combos_cache.get(slot)
            if cached is not None:
                return cached
            combos = generate_meld_combos(
                item,
                materia_catalog,
                stat_weights,
                cap_table,
                slot_limit=refine_slot_limit,
                max_grades=max_grades,
                allowed_stats=allowed_stats,
                overcap_loss=overcap_loss,
                grade_policy=grade_policy,
                candidate_limit=refine_candidate_limit,
                score_fn=None,
                base_stats_for_score=None,
            )
            refine_slot_combos_cache[slot] = combos
            return combos

        def _refine_single(
            gs: Gearset, score: float, gcd: float
        ) -> Tuple[Gearset, float, float]:
            food = foods_by_id.get(gs.food_id)
            if not food:
                return gs, score, gcd
            current_melds: Dict[str, List[MateriaSlotSelection]] = {}
            slot_stats: Dict[str, Dict[int, int]] = {}
            for slot, item in selected_items.items():
                sel = gs.items.get(slot)
                melds = [] if (no_meld_slots and slot in no_meld_slots) else list(sel.materia) if sel and sel.materia else []
                current_melds[slot] = melds
                if no_meld_slots and slot in no_meld_slots:
                    slot_stats[slot] = {}
                else:
                    slot_stats[slot] = _meld_stats_for_item_cached(item, melds)

            total_stats = base_stats.copy()
            for stats in slot_stats.values():
                _stats_add(total_stats, stats, 1)

            best_score, best_gcd = _evaluate_with_cache(total_stats, food)

            improved = True
            iterations = 0
            while improved and iterations < refine_iterations:
                improved = False
                iterations += 1
                for slot, item in selected_items.items():
                    if no_meld_slots and slot in no_meld_slots:
                        continue
                    if slot in fixed_materia_slots:
                        continue
                    combos = _refine_slot_combos(slot, item)
                    base_without = total_stats.copy()
                    _stats_add(base_without, slot_stats.get(slot, {}), -1)
                    slot_best_score = best_score
                    slot_best_gcd = best_gcd
                    slot_best_stats = slot_stats.get(slot, {})
                    slot_best_melds = current_melds.get(slot, [])
                    for stats, melds, _score in combos:
                        merged = base_without.copy()
                        _stats_add(merged, stats, 1)
                        cand_score, cand_gcd = _evaluate_with_cache(merged, food)
                        if not gcd_meets_constraints(cand_gcd, gearset.target_gcd, gcd_constraint):
                            continue
                        if cand_score > slot_best_score + 1e-6:
                            slot_best_score = cand_score
                            slot_best_gcd = cand_gcd
                            slot_best_stats = stats
                            slot_best_melds = melds
                    if slot_best_score > best_score + 1e-6:
                        current_melds[slot] = list(slot_best_melds)
                        slot_stats[slot] = slot_best_stats
                        total_stats = base_without.copy()
                        _stats_add(total_stats, slot_best_stats, 1)
                        best_score = slot_best_score
                        best_gcd = slot_best_gcd
                        improved = True

            if best_score > score + 1e-6:
                new_items = {
                    slot: MateriaAwareSelection(sel, current_melds.get(slot, []))
                    for slot, sel in gs.items.items()
                }
                refined = Gearset(
                    job=gs.job,
                    items=new_items,
                    food_id=gs.food_id,
                    food_simulation=bool(getattr(gs, "food_simulation", False)),
                    target_gcd=gs.target_gcd,
                    note=gs.note,
                    race=gs.race,
                    level=gearset_level(gs),
                )
                return refined, best_score, best_gcd
            return gs, score, gcd

        refine_limit = min(5 if mode == "dmg100p" else 12, len(results))
        if debug_enabled:
            sim_log(
                f"[opt] refine_start mode={mode} refine_limit={refine_limit} "
                f"refine_slot_limit={refine_slot_limit} refine_candidate_limit={refine_candidate_limit}"
            )
        for idx in range(refine_limit):
            gs, score, gcd = results[idx]
            results[idx] = _refine_single(gs, score, gcd)
            if results[idx][1] > score + 1e-6:
                if debug_enabled:
                    sim_log(
                        f"[opt] refine_improved index={idx} score={score:.4f}->{results[idx][1]:.4f} "
                        f"gcd={gcd:.3f}->{results[idx][2]:.3f}"
                    )
        results.sort(key=_result_sort_key)

    if results:
        final_check_limit = min(
            len(results),
            12,
        )
        if mode in {"simdps", "simdps_self"}:
            final_check_limit = min(len(results), 24)
        max_final_checks = min(len(results), final_check_limit * 3)
        final_checked = 0
        final_dropped = 0
        verified_head: List[Tuple[Gearset, float, float]] = []
        cursor = 0
        while (
            cursor < len(results)
            and len(verified_head) < final_check_limit
            and final_checked < max_final_checks
        ):
            if stop_event and stop_event.is_set():
                break
            gs, _score, _gcd = results[cursor]
            cursor += 1
            final_checked += 1
            stats = _stats_for_gearset(gs)
            food = foods_by_id.get(gs.food_id) if gs.food_id is not None else None
            checked_score, checked_gcd = _evaluate_direct(stats, food)
            if not gcd_meets_constraints(checked_gcd, gearset.target_gcd, gcd_constraint):
                final_dropped += 1
                continue
            verified_head.append((gs, checked_score, checked_gcd))
        if final_checked > 0:
            results = verified_head + results[cursor:]
            results.sort(key=_result_sort_key)
        if debug_enabled:
            sim_log(
                f"[opt] final_check checked={final_checked} accepted={len(verified_head)} "
                f"dropped={final_dropped} limit={final_check_limit}"
            )

    def gearset_key(gs: Gearset) -> Tuple:
        slots = sorted(gs.items.keys())
        items_key = []
        for slot in slots:
            sel = gs.items.get(slot)
            if not sel:
                items_key.append((slot, None, ()))
                continue
            mats = tuple(sorted((m.base_param, m.grade) for m in (sel.materia or [])))
            items_key.append((slot, sel.item_id, mats))
        return (gs.food_id, round(gs.target_gcd or 0.0, 3), tuple(items_key))

    top_results: List[Tuple[Gearset, float, float]] = []
    seen = set()
    for gs, score, gcd in results:
        key = gearset_key(gs)
        if key in seen:
            continue
        seen.add(key)
        top_results.append((gs, score, gcd))
        if len(top_results) >= 8:
            break
    if debug_enabled:
        sim_log(
            f"[opt] done raw_results={len(results)} deduped={len(top_results)} cache_entries={len(eval_cache)}"
        )
    if progress:
        progress(100, "最適化完了")
    return top_results


def search_gearsets(
    gearset: Gearset,
    candidate_items_by_slot: Dict[str, List[ItemRecord]],
    items_by_id: Dict[int, ItemRecord],
    materia_catalog: Dict[int, MateriaCategory],
    foods: List[Optional[FoodRecord]],
    casts: List[dict],
    fight_duration_ms: int,
    cap_table: Dict[Tuple[int, int], int],
    damage_summary: Optional[Dict[str, object]] = None,
    baseline_raw_stats: Optional[Dict[int, int]] = None,
    baseline_items: Optional[Dict[str, ItemRecord]] = None,
    baseline_gcd: Optional[float] = None,
    gcd_constraint: Optional[LogGcdConstraint] = None,
    job_mods: Optional[Dict[str, int]] = None,
    baseline_food: Optional[FoodRecord] = None,
    party_bonus: int = 0,
    baseline_party_bonus: Optional[int] = None,
    mode: str = "simdps",
    baseline_race: Optional[str] = None,
    party_synergies: Optional[Dict[str, bool]] = None,
    crit_rate_offset: float = 0.0,
    dhit_rate_offset: float = 0.0,
    level_sync_ilvl: Optional[int] = None,
    progress: Optional[Callable[[int, str], None]] = None,
    stop_event=None,
    finalize_progress: bool = True,
    optimization_session: Optional[OptimizationSession] = None,
) -> List[Tuple[Gearset, float, float]]:
    debug_enabled = sim_debug_enabled()
    job = gearset.job or ""
    if not job:
        return []
    if not (len(foods) == 1 and foods[0] is None):
        foods = highest_item_level_combat_foods(foods)
    level_value = gearset_level(gearset)
    search_target_gcd = (
        gcd_constraint.baseline_formula_seconds
        if gcd_constraint is not None
        else gearset.target_gcd
    )
    search_score_context = _prepare_gear_search_score_context(
        job,
        search_target_gcd,
        level_value,
        mode=mode,
    )
    preview_eval_ctx = prepare_score_eval_context(
        job,
        damage_summary,
        baseline_raw_stats,
        baseline_items,
        baseline_food,
        baseline_gcd,
        job_mods,
        party_bonus,
        baseline_party_bonus,
        gearset.race,
        baseline_race,
        party_synergies,
        mode,
        level_value,
    )
    if baseline_raw_stats and baseline_items and job_mods:
        try:
            sensitivity_step = 20
            base_sensitivity_score, _base_sensitivity_gcd = evaluate_score(
                dict(baseline_raw_stats),
                job,
                casts,
                fight_duration_ms,
                gearset.target_gcd,
                damage_summary=damage_summary,
                job_mods=job_mods,
                food=baseline_food,
                party_bonus=party_bonus,
                baseline_raw_stats=baseline_raw_stats,
                baseline_items=baseline_items,
                selected_items=baseline_items,
                baseline_food=baseline_food,
                mode=mode,
                race=gearset.race,
                baseline_party_bonus=baseline_party_bonus,
                baseline_race=baseline_race,
                party_synergies=party_synergies,
                level=level_value,
                crit_rate_offset=crit_rate_offset,
                dhit_rate_offset=dhit_rate_offset,
                eval_ctx=preview_eval_ctx,
            )
            raw_weights: Dict[int, float] = {}
            for stat_id in MELDABLE_STATS:
                test_stats = dict(baseline_raw_stats)
                test_stats[stat_id] = int(test_stats.get(stat_id, 0)) + sensitivity_step
                test_score, _test_gcd = evaluate_score(
                    test_stats,
                    job,
                    casts,
                    fight_duration_ms,
                    gearset.target_gcd,
                    damage_summary=damage_summary,
                    job_mods=job_mods,
                    food=baseline_food,
                    party_bonus=party_bonus,
                    baseline_raw_stats=baseline_raw_stats,
                    baseline_items=baseline_items,
                    selected_items=baseline_items,
                    baseline_food=baseline_food,
                    mode=mode,
                    race=gearset.race,
                    baseline_party_bonus=baseline_party_bonus,
                    baseline_race=baseline_race,
                    party_synergies=party_synergies,
                    level=level_value,
                    crit_rate_offset=crit_rate_offset,
                    dhit_rate_offset=dhit_rate_offset,
                    eval_ctx=preview_eval_ctx,
                )
                raw_weights[stat_id] = max(
                    0.0,
                    (float(test_score) - float(base_sensitivity_score)) / sensitivity_step,
                )
            max_weight = max(raw_weights.values(), default=0.0)
            if max_weight > 0.0:
                scaled_weights = {
                    stat_id: (weight / max_weight) * 1.5
                    for stat_id, weight in raw_weights.items()
                }
                search_score_context = _prepare_gear_search_score_context(
                    job,
                    search_target_gcd,
                    level_value,
                    mode=mode,
                    stat_weights=scaled_weights,
                )
        except Exception:
            logger.exception("Failed to compute mode-aware gear-search stat weights")
    total_meld_slots_cache: Dict[int, int] = {}

    def _total_meld_slots_cached(item: ItemRecord) -> int:
        item_id = int(item.item_id)
        cached = total_meld_slots_cache.get(item_id)
        if cached is not None:
            return cached
        cached = total_meld_slots_for_item(item)
        total_meld_slots_cache[item_id] = cached
        return cached

    def _search_relic_stats(item: Optional[ItemRecord]) -> Dict[int, int]:
        return {
            int(stat_id): int(value)
            for stat_id, value in dict(
                getattr(item, "_gear_search_relic_stats", {}) or {}
            ).items()
            if int(value or 0) > 0
        }

    def _search_item_key(item: ItemRecord) -> Tuple[int, Tuple[Tuple[int, int], ...]]:
        return int(item.item_id), tuple(sorted(_search_relic_stats(item).items()))

    slot_priority = [
        "weapon",
        "offhand",
        "earrings",
        "necklace",
        "bracelet",
        "ring1",
        "ring2",
        "head",
        "hands",
        "feet",
        "body",
        "legs",
    ]
    slot_order = [slot for slot in slot_priority if candidate_items_by_slot.get(slot)]
    if not slot_order:
        return []

    def _emit_progress(
        pct: int,
        message: str,
        *,
        detail_value: Optional[int] = None,
        detail_message: Optional[str] = None,
    ) -> None:
        if not progress:
            return
        progress(
            pct,
            encode_progress_message(
                message,
                detail_value=detail_value,
                detail_message=detail_message,
            ),
        )

    base_slot_limits = {
        "weapon": 20,
        "offhand": 16,
        "body": 20,
        "legs": 20,
        "head": 18,
        "hands": 18,
        "feet": 18,
        "earrings": 18,
        "necklace": 18,
        "bracelet": 18,
        "ring1": 18,
        "ring2": 18,
    }
    if int(level_sync_ilvl or 0) > 0:
        # Synced content collapses many high-IL pieces down to the same capped
        # profile, so the normal slot caps prune too aggressively and can drop
        # exact-score winners before beam search ever sees them.
        base_slot_limits.update(
            {
                "weapon": 40,
                "offhand": 24,
                "body": 40,
                "legs": 40,
                "head": 40,
                "hands": 40,
                "feet": 40,
                "earrings": 40,
                "necklace": 40,
                "bracelet": 40,
                "ring1": 40,
                "ring2": 40,
            }
        )
    beam_width = 2200
    shortlist_limit = 72
    refinement_diversity_extra_limit = 8
    candidate_item_lookup_by_slot: Dict[
        str,
        Dict[Tuple[int, Tuple[Tuple[int, int], ...]], ItemRecord],
    ] = {}

    pruned_candidates: Dict[str, List[ItemRecord]] = {}
    for slot in slot_order:
        unique_items: Dict[Tuple[int, Tuple[Tuple[int, int], ...]], ItemRecord] = {}
        for item in candidate_items_by_slot.get(slot, []):
            if not item:
                continue
            unique_items[_search_item_key(item)] = item
        scored_candidates = [
            (
                _gear_search_item_score(
                    item,
                    job,
                    search_target_gcd,
                    level_value,
                    score_context=search_score_context,
                ),
                item,
            )
            for item in unique_items.values()
        ]
        scored_candidates.sort(
            key=lambda entry: (
                -entry[0],
                -int(entry[1].ilvl or 0),
                str(getattr(entry[1], "name_ja", None) or entry[1].name or ""),
                int(entry[1].item_id),
            )
        )
        candidates = [item for _score, item in scored_candidates]
        slot_limit = int(base_slot_limits.get(slot, 6))
        if slot in {"weapon", "offhand"} and any(_search_relic_stats(item) for item in candidates):
            slot_limit = max(slot_limit, min(len(candidates), beam_width))
        limit = max(1, min(len(candidates), slot_limit))
        pruned = candidates[:limit]
        pruned_candidates[slot] = pruned
        candidate_item_lookup_by_slot[slot] = {
            _search_item_key(item): item for item in pruned if item is not None
        }
        if debug_enabled:
            sim_log(
                f"[gear-search] slot={slot} raw={len(candidates)} pruned={len(pruned)} "
                f"beam_width={beam_width} shortlist_limit={shortlist_limit}"
            )

    beam: List[Dict[str, object]] = [
        {
            "score": 0.0,
            "items": {},
            "stats": {},
            "meld_capacity": 0,
            "weapon_damage": 0,
        }
    ]
    total_slots = len(slot_order)
    for idx, slot in enumerate(slot_order):
        if stop_event and stop_event.is_set():
            return []
        slot_candidates = pruned_candidates.get(slot) or []
        if not slot_candidates:
            continue
        slot_label = SLOT_LABELS.get(slot, slot)
        slot_total_states = max(1, len(beam))
        slot_total_candidates = max(1, len(slot_candidates))
        slot_total_work = max(1, slot_total_states * slot_total_candidates)
        slot_completed_work = 0
        slot_report_every = max(1, slot_total_work // 24)
        overall_start_pct = 5 + int((idx / max(1, total_slots)) * 25)
        overall_end_pct = 5 + int(((idx + 1) / max(1, total_slots)) * 25)
        next_states: List[Dict[str, object]] = []
        next_state_sequence = 0
        compact_threshold = max(beam_width * 20, beam_width + slot_total_candidates)
        for state in beam:
            selected = state.get("items") or {}
            current_stats = state.get("stats") or {}
            current_meld_capacity = int(state.get("meld_capacity") or 0)
            current_weapon_damage = int(state.get("weapon_damage") or 0)
            for item in slot_candidates:
                slot_completed_work += 1
                if (
                    stop_event
                    and (slot_completed_work % 1024) == 0
                    and stop_event.is_set()
                ):
                    return []
                if slot in {"ring1", "ring2"} and item.unique:
                    other_slot = "ring1" if slot == "ring2" else "ring2"
                    other_item = selected.get(other_slot)
                    if other_item and int(getattr(other_item, "item_id", 0) or 0) == int(item.item_id):
                        continue
                new_items = dict(selected)
                new_items[slot] = item
                new_stats = dict(current_stats)
                for stat_id, value in (item.base_params_hq or {}).items():
                    stat_key = int(stat_id)
                    new_stats[stat_key] = int(new_stats.get(stat_key, 0)) + int(value or 0)
                new_meld_capacity = current_meld_capacity + _total_meld_slots_cached(item)
                item_weapon_damage = max(int(item.damage_phys or 0), int(item.damage_mag or 0))
                new_weapon_damage = max(current_weapon_damage, item_weapon_damage)
                new_score = _gear_search_state_score(
                    new_stats,
                    job,
                    search_target_gcd,
                    level_value,
                    weapon_damage=new_weapon_damage,
                    meld_capacity=new_meld_capacity,
                    score_context=search_score_context,
                )
                new_secondary_score = _gear_search_secondary_score(
                    new_stats,
                    job,
                    search_target_gcd,
                    level_value,
                    score_context=search_score_context,
                )
                next_state_sequence += 1
                next_states.append(
                    {
                        "score": new_score,
                        "items": new_items,
                        "stats": new_stats,
                        "meld_capacity": new_meld_capacity,
                        "weapon_damage": new_weapon_damage,
                        "_search_sequence": next_state_sequence,
                        "_gear_search_secondary_score": new_secondary_score,
                    }
                )
                if len(next_states) >= compact_threshold:
                    next_states = _gear_search_ranked_state_union(
                        next_states,
                        beam_width,
                        job,
                        search_target_gcd,
                        level_value,
                        score_context=search_score_context,
                    )
                if progress and (
                    slot_completed_work == 1
                    or slot_completed_work == slot_total_work
                    or (slot_completed_work % slot_report_every) == 0
                ):
                    detail_pct = int((slot_completed_work / max(1, slot_total_work)) * 100)
                    mapped_pct = overall_start_pct + int(
                        ((overall_end_pct - overall_start_pct) * detail_pct) / 100
                    )
                    _emit_progress(
                        mapped_pct,
                        f"装備候補を探索中: {slot_label} ({len(next_states)}候補)",
                        detail_value=detail_pct,
                        detail_message=f"{slot_label}検索",
                    )
        beam = _gear_search_diversified_states(
            next_states,
            beam_width,
            job,
            search_target_gcd,
            level_value,
            score_context=search_score_context,
        )
        if progress:
            _emit_progress(
                overall_end_pct,
                f"装備候補を探索中: {slot_label} ({len(beam)}候補)",
                detail_value=100,
                detail_message=f"{slot_label}検索",
            )

    if not beam:
        return []

    preview_foods: List[Optional[FoodRecord]] = []
    seen_preview_food_ids: set[int] = set()
    for food in foods or []:
        if food is None:
            continue
        food_id = int(food.food_id or 0)
        if food_id in seen_preview_food_ids:
            continue
        seen_preview_food_ids.add(food_id)
        preview_foods.append(food)
    if not preview_foods:
        preview_foods.append(baseline_food)

    def _evaluate_preview_candidate(
        selected: Dict[str, ItemRecord],
        raw_stats: Dict[int, int],
        food: Optional[FoodRecord],
    ) -> Tuple[float, float]:
        return evaluate_score(
            raw_stats,
            job,
            casts,
            fight_duration_ms,
            gearset.target_gcd,
            damage_summary=damage_summary,
            job_mods=job_mods,
            food=food,
            party_bonus=party_bonus,
            baseline_raw_stats=baseline_raw_stats,
            baseline_items=baseline_items,
            selected_items=selected,
            baseline_food=baseline_food,
            mode=mode,
            race=gearset.race,
            baseline_party_bonus=baseline_party_bonus,
            baseline_race=baseline_race,
            party_synergies=party_synergies,
            debug=False,
            level=level_value,
            crit_rate_offset=crit_rate_offset,
            dhit_rate_offset=dhit_rate_offset,
            eval_ctx=preview_eval_ctx,
        )

    def _resistance_effective_stats(
        item: ItemRecord,
        allocation: Dict[int, int],
    ) -> Dict[int, int]:
        relic_base_stats = getattr(item, "_gear_search_relic_base_stats", None)
        base_stats = dict(
            relic_base_stats
            if relic_base_stats is not None
            else (item.base_params_hq or {})
        )
        effective_caps = {
            int(stat_id): int(value)
            for stat_id, value in dict(
                getattr(item, "_gear_search_relic_effective_caps", {}) or {}
            ).items()
        }
        effective_stats = dict(base_stats)
        for stat_id, value in allocation.items():
            applied = min(int(value), int(effective_caps.get(int(stat_id), value)))
            if applied > 0:
                effective_stats[int(stat_id)] = int(effective_stats.get(int(stat_id), 0)) + applied
        return effective_stats

    def _resistance_item_with_allocation(
        item: ItemRecord,
        allocation: Dict[int, int],
    ) -> ItemRecord:
        effective_stats = _resistance_effective_stats(item, allocation)
        candidate = ItemRecord(
            item_id=item.item_id,
            name=item.name,
            name_ja=item.name_ja,
            jobs=list(item.jobs),
            ilvl=item.ilvl,
            slot=item.slot,
            materia_slots=item.materia_slots,
            overmeld=item.overmeld,
            base_params=dict(effective_stats),
            base_params_hq=dict(effective_stats),
            damage_phys=item.damage_phys,
            damage_mag=item.damage_mag,
            delay_ms=item.delay_ms,
            occ_slot=item.occ_slot,
            unique=item.unique,
            icon_url=item.icon_url,
        )
        setattr(candidate, "_gear_search_relic_stats", dict(allocation))
        for attr_name in (
            "_gear_search_relic_kind",
            "_gear_search_relic_config",
            "_gear_search_relic_base_stats",
            "_gear_search_relic_effective_caps",
        ):
            if hasattr(item, attr_name):
                setattr(candidate, attr_name, getattr(item, attr_name))
        return candidate

    def _refine_resistance_preview_state(
        state: Dict[str, object],
    ) -> Optional[Dict[str, object]]:
        working_items = dict(state.get("items") or {})
        working_stats = dict(state.get("stats") or {})
        working_score = float(state.get("preview_score") or 0.0)
        working_gcd = float(state.get("preview_gcd") or 99.0)
        preview_food = state.get("_preview_food")
        changed = False
        evaluated_moves = 0
        refinement_error_logged = False
        for slot_name, current_item in list(working_items.items()):
            template_selection = (gearset.items or {}).get(slot_name)
            if _selection_lock_item(template_selection):
                continue
            if str(getattr(current_item, "_gear_search_relic_kind", "") or "") != "resistance":
                continue
            config = dict(getattr(current_item, "_gear_search_relic_config", {}) or {})
            stat_caps = {
                int(stat_id): int(value)
                for stat_id, value in dict(config.get("stat_caps", {}) or {}).items()
                if int(value or 0) > 0
            }
            allocation = _search_relic_stats(current_item)
            if not allocation or not stat_caps:
                continue
            allowed_stats = [
                int(stat_id)
                for stat_id in list(config.get("allowed_stats", []) or [])
                if int(stat_id) in stat_caps
            ]
            slot_changed = False
            for _iteration in range(6):
                best_move = None
                best_move_score = working_score
                best_move_gcd = working_gcd
                for source_stat in allowed_stats:
                    source_value = int(allocation.get(source_stat, 0) or 0)
                    if source_value <= 0:
                        continue
                    for target_stat in allowed_stats:
                        if target_stat == source_stat:
                            continue
                        room = int(stat_caps[target_stat]) - int(allocation.get(target_stat, 0) or 0)
                        max_transfer = min(source_value, room)
                        if max_transfer <= 0:
                            continue
                        for transfer in range(1, max_transfer + 1):
                            evaluated_moves += 1
                            if (
                                stop_event
                                and (evaluated_moves % 256) == 0
                                and stop_event.is_set()
                            ):
                                return None
                            candidate_allocation = dict(allocation)
                            candidate_allocation[source_stat] = source_value - transfer
                            candidate_allocation[target_stat] = int(
                                candidate_allocation.get(target_stat, 0)
                            ) + transfer
                            candidate_allocation = {
                                stat_id: value
                                for stat_id, value in candidate_allocation.items()
                                if value > 0
                            }
                            candidate_effective_stats = _resistance_effective_stats(
                                current_item,
                                candidate_allocation,
                            )
                            candidate_stats = dict(working_stats)
                            for stat_id, value in (current_item.base_params_hq or {}).items():
                                candidate_stats[int(stat_id)] = int(
                                    candidate_stats.get(int(stat_id), 0)
                                ) - int(value or 0)
                            for stat_id, value in candidate_effective_stats.items():
                                candidate_stats[int(stat_id)] = int(
                                    candidate_stats.get(int(stat_id), 0)
                                ) + int(value or 0)
                            try:
                                candidate_score, candidate_gcd = _evaluate_preview_candidate(
                                    working_items,
                                    candidate_stats,
                                    preview_food if isinstance(preview_food, FoodRecord) else None,
                                )
                            except Exception:
                                if not refinement_error_logged:
                                    logger.exception(
                                        "Failed to refine resistance weapon allocation "
                                        "(item_id=%s, allocation=%s)",
                                        int(current_item.item_id),
                                        candidate_allocation,
                                    )
                                    refinement_error_logged = True
                                continue
                            if candidate_score > best_move_score + 1e-9 or (
                                abs(candidate_score - best_move_score) <= 1e-9
                                and candidate_gcd < best_move_gcd
                            ):
                                best_move = (
                                    candidate_allocation,
                                    candidate_stats,
                                )
                                best_move_score = float(candidate_score)
                                best_move_gcd = float(candidate_gcd)
                if best_move is None:
                    break
                allocation, working_stats = best_move
                current_item = _resistance_item_with_allocation(current_item, allocation)
                working_items = dict(working_items)
                working_items[slot_name] = current_item
                working_score = best_move_score
                working_gcd = best_move_gcd
                slot_changed = True
                changed = True
            if slot_changed:
                candidate_items_by_slot.setdefault(slot_name, []).append(current_item)
                candidate_item_lookup_by_slot.setdefault(slot_name, {})[
                    _search_item_key(current_item)
                ] = current_item
        if not changed:
            return None
        return {
            "items": working_items,
            "stats": working_stats,
            "score": working_score,
            "heuristic_score": float(state.get("heuristic_score") or 0.0),
            "preview_score": working_score,
            "preview_gcd": working_gcd,
            "meld_capacity": int(state.get("meld_capacity") or 0),
            "_gear_search_secondary_score": _gear_search_secondary_score(
                working_stats,
                job,
                search_target_gcd,
                level_value,
                score_context=search_score_context,
            ),
            "_preview_food": preview_food,
        }

    reranked_shortlist: List[Dict[str, object]] = []
    preview_total = len(beam)
    preview_report_every = max(1, preview_total // 24)
    parallel_preview_results: Dict[int, Tuple[float, float, int]] = {}
    if optimization_session is not None:
        preview_candidates = [
            PreviewCandidate(
                request_id=index,
                selected_items=dict(state.get("items") or {}),
                raw_stats=dict(state.get("stats") or {}),
            )
            for index, state in enumerate(beam)
            if state.get("items")
        ]

        def _preview_progress(
            completed: int,
            total: int,
            elapsed: float,
            eta: Optional[float],
        ) -> None:
            if not progress:
                return
            detail_pct = int((completed / max(1, total)) * 100)
            eta_text = ""
            if eta is not None:
                eta_text = f"、残り約{max(0, int(round(eta)))}秒"
            _emit_progress(
                30 + int(detail_pct * 4 / 100),
                (
                    f"装備候補を再評価中 {completed}/{total} "
                    f"({optimization_session.worker_count}並列、"
                    f"経過{int(elapsed)}秒{eta_text})"
                ),
                detail_value=detail_pct,
                detail_message="候補再評価",
            )

        parallel_preview_results = optimization_session.evaluate_preview_batch(
            preview_candidates,
            job=job,
            target_gcd=gearset.target_gcd,
            race=gearset.race,
            level=level_value,
            foods=preview_foods,
            stop_event=stop_event,
            progress=_preview_progress,
        )
        if stop_event and stop_event.is_set():
            return []

    for preview_index, state in enumerate(beam, start=1):
        if stop_event and stop_event.is_set():
            return []
        selected_items = dict(state.get("items") or {})
        if not selected_items:
            continue
        raw_stats = dict(state.get("stats") or {})
        best_preview_food: Optional[FoodRecord] = None
        if optimization_session is not None:
            preview_score, preview_gcd, food_index = parallel_preview_results.get(
                preview_index - 1,
                (0.0, 99.0, -1),
            )
            if 0 <= food_index < len(preview_foods):
                best_preview_food = preview_foods[food_index]
        else:
            preview_score = float("-inf")
            preview_gcd = 99.0
            for preview_food in preview_foods:
                try:
                    candidate_score, candidate_gcd = _evaluate_preview_candidate(
                        selected_items,
                        raw_stats,
                        preview_food,
                    )
                except Exception:
                    logger.exception(
                        "Failed to evaluate gear-search preview candidate "
                        "(food_id=%s, items=%s)",
                        int(preview_food.food_id or 0) if preview_food else 0,
                        {
                            slot: int(item.item_id)
                            for slot, item in selected_items.items()
                        },
                    )
                    candidate_score, candidate_gcd = 0.0, 99.0
                if candidate_score > preview_score + 1e-9 or (
                    abs(candidate_score - preview_score) <= 1e-9
                    and candidate_gcd < preview_gcd
                ):
                    preview_score = float(candidate_score)
                    preview_gcd = float(candidate_gcd)
                    best_preview_food = preview_food
            if preview_score == float("-inf"):
                preview_score, preview_gcd = 0.0, 99.0
        reranked_shortlist.append(
            {
                "items": selected_items,
                "stats": raw_stats,
                "score": float(preview_score),
                "heuristic_score": float(state.get("score") or 0.0),
                "preview_score": float(preview_score),
                "preview_gcd": float(preview_gcd),
                "meld_capacity": int(state.get("meld_capacity") or 0),
                "_gear_search_secondary_score": state.get(
                    "_gear_search_secondary_score"
                ),
                "_preview_food": best_preview_food,
            }
        )

        if optimization_session is None and progress and (
            preview_index == 1
            or preview_index == preview_total
            or (preview_index % preview_report_every) == 0
        ):
            detail_pct = int((preview_index / max(1, preview_total)) * 100)
            _emit_progress(
                30 + int(detail_pct * 4 / 100),
                f"装備候補を再評価中 ({preview_index}/{preview_total}件)",
                detail_value=detail_pct,
                detail_message="候補再評価",
            )

    refinement_seeds = _gear_search_preview_shortlist(
        reranked_shortlist,
        max(1, shortlist_limit),
        refinement_diversity_extra_limit,
        job,
        search_target_gcd,
        level_value,
        score_context=search_score_context,
    )
    for refinement_seed in refinement_seeds:
        if stop_event and stop_event.is_set():
            return []
        refined_state = _refine_resistance_preview_state(refinement_seed)
        if refined_state is not None:
            reranked_shortlist.append(refined_state)
    shortlist = _gear_search_preview_shortlist(
        reranked_shortlist,
        max(1, shortlist_limit),
        0,
        job,
        search_target_gcd,
        level_value,
        score_context=search_score_context,
    )
    if progress:
        _emit_progress(
            34,
            f"装備候補を再評価中 ({len(shortlist)}件)",
            detail_value=100,
            detail_message="候補再評価",
        )

    results_by_key: Dict[Tuple, Tuple[Gearset, float, float]] = {}
    total_candidates = len(shortlist)
    optimize_result_cache: Dict[Tuple, Optional[Tuple[Gearset, float, float]]] = {}
    _cache_miss = object()

    def _result_key_for_best(best: Tuple[Gearset, float, float]) -> Tuple:
        key_slots = []
        for slot_name in GEAR_SLOTS:
            sel = (best[0].items or {}).get(slot_name)
            mats = tuple((m.base_param, m.grade) for m in (sel.materia or [])) if sel else tuple()
            relic = tuple(sorted((int(stat_id), int(val)) for stat_id, val in ((getattr(sel, "relic_stats", {}) or {}).items() if sel else []) if int(val or 0) > 0))
            key_slots.append((slot_name, sel.item_id if sel else None, mats, relic))
        return (best[0].food_id, tuple(key_slots))

    def _optimize_cache_key(
        gs: Gearset,
        selected_items: Optional[Dict[str, ItemRecord]] = None,
        no_meld_slots: Optional[set] = None,
    ) -> Tuple:
        return optimization_request_key(gs, selected_items, no_meld_slots)

    def _run_optimize_cached(
        candidate_gearset: Gearset,
        selected_items_override: Dict[str, ItemRecord],
        no_meld_slots_override: set,
        nested_progress: Optional[Callable[[int, str], None]],
    ) -> Optional[Tuple[Gearset, float, float]]:
        cache_key = _optimize_cache_key(
            candidate_gearset,
            selected_items_override,
            no_meld_slots_override,
        )
        cached = optimize_result_cache.get(cache_key, _cache_miss)
        if cached is not _cache_miss:
            return cached
        if optimization_session is not None:
            batch_results = optimization_session.optimize_batch(
                [
                    OptimizationRequest(
                        request_id=0,
                        cache_key=cache_key,
                        gearset=candidate_gearset,
                        selected_items=selected_items_override,
                        no_meld_slots=no_meld_slots_override,
                    )
                ],
                stop_event=stop_event,
            )
            best = batch_results.get(cache_key)
            optimize_result_cache.setdefault(cache_key, best)
            return best
        opt_results = optimize(
            candidate_gearset,
            items_by_id,
            materia_catalog,
            foods,
            casts,
            fight_duration_ms,
            cap_table,
            damage_summary=damage_summary,
            baseline_raw_stats=baseline_raw_stats,
            baseline_items=baseline_items,
            baseline_gcd=baseline_gcd,
            gcd_constraint=gcd_constraint,
            job_mods=job_mods,
            baseline_food=baseline_food,
            party_bonus=party_bonus,
            baseline_party_bonus=baseline_party_bonus,
            mode=mode,
            baseline_race=baseline_race,
            party_synergies=party_synergies,
            crit_rate_offset=crit_rate_offset,
            dhit_rate_offset=dhit_rate_offset,
            selected_items_override=selected_items_override,
            no_meld_slots=no_meld_slots_override,
            progress=nested_progress,
            stop_event=stop_event,
        )
        best = opt_results[0] if opt_results else None
        optimize_result_cache.setdefault(cache_key, best)
        return best

    def _prepare_search_candidate(
        index: int,
        state: Dict[str, object],
    ) -> Optional[Tuple[int, Tuple, Gearset, Dict[str, ItemRecord], set]]:
        if stop_event and stop_event.is_set():
            return None
        selected_items_local = dict(state.get("items") or {})
        if not selected_items_local:
            return None
        candidate_items = {slot: ItemSelection() for slot in GEAR_SLOTS}
        no_meld_slots_local: set = set()
        for slot, item in selected_items_local.items():
            template_sel = (gearset.items or {}).get(slot)
            initial_materia = []
            if _selection_lock_item(template_sel) and _selection_lock_materia(template_sel):
                initial_materia = list(template_sel.materia or [])
            search_relic_stats = _search_relic_stats(item)
            candidate_items[slot] = ItemSelection(
                item_id=int(item.item_id),
                materia=initial_materia,
                relic_stats=search_relic_stats,
                lock_item=_selection_lock_item(template_sel),
                lock_materia=_selection_lock_materia(template_sel),
                excluded_item_ids=list(getattr(template_sel, "excluded_item_ids", []) or []),
            )
            if _total_meld_slots_cached(item) <= 0:
                no_meld_slots_local.add(slot)
        candidate_gearset = Gearset(
            job=gearset.job,
            items=candidate_items,
            food_id=gearset.food_id,
            food_simulation=bool(getattr(gearset, "food_simulation", False)),
            target_gcd=gearset.target_gcd,
            note=gearset.note,
            race=gearset.race,
            level=level_value,
        )
        return (
            index,
            _optimize_cache_key(
                candidate_gearset,
                selected_items_local,
                no_meld_slots_local,
            ),
            candidate_gearset,
            selected_items_local,
            no_meld_slots_local,
        )

    def _optimize_search_candidate(
        index: int,
        state: Dict[str, object],
        nested_progress: Optional[Callable[[int, str], None]],
    ) -> Optional[Tuple[int, Tuple[Gearset, float, float]]]:
        prepared = _prepare_search_candidate(index, state)
        if prepared is None:
            return None
        (
            _prepared_index,
            _cache_key,
            candidate_gearset,
            selected_items_local,
            no_meld_slots_local,
        ) = prepared
        best = _run_optimize_cached(
            candidate_gearset,
            selected_items_local,
            no_meld_slots_local,
            nested_progress,
        )
        if not best:
            return None
        return index, best

    if optimization_session is not None:
        prepared_candidates = [
            prepared
            for idx, state in enumerate(shortlist)
            if (prepared := _prepare_search_candidate(idx, state)) is not None
        ]
        requests = [
            OptimizationRequest(
                request_id=idx,
                cache_key=cache_key,
                gearset=candidate_gearset,
                selected_items=selected_items_local,
                no_meld_slots=no_meld_slots_local,
            )
            for (
                idx,
                cache_key,
                candidate_gearset,
                selected_items_local,
                no_meld_slots_local,
            ) in prepared_candidates
        ]
        upper_bounds: Dict[Tuple, float] = {}
        if len(requests) > GEAR_SEARCH_REQUIRED_RESULTS:

            def _bound_progress(
                completed: int,
                total: int,
                elapsed: float,
                eta: Optional[float],
            ) -> None:
                if not progress:
                    return
                detail_pct = int((completed / max(1, total)) * 100)
                eta_text = ""
                if eta is not None:
                    eta_text = f"、残り約{max(0, int(round(eta)))}秒"
                _emit_progress(
                    35 + int(detail_pct * 5 / 100),
                    (
                        f"候補上限を計算中 {completed}/{total} "
                        f"({optimization_session.worker_count}並列、経過{int(elapsed)}秒{eta_text})"
                    ),
                    detail_value=detail_pct,
                    detail_message="安全な上限計算",
                )

            upper_bounds = optimization_session.evaluate_upper_bounds(
                requests,
                stop_event=stop_event,
                progress=_bound_progress,
            )
            if stop_event and stop_event.is_set():
                return []

        pending_requests = sorted(
            requests,
            key=lambda request: (
                -float(upper_bounds.get(request.cache_key, math.inf)),
                int(request.request_id),
            ),
        )
        deferred_requests: List[OptimizationRequest] = []
        bound_pruning_enabled = bool(upper_bounds)
        exact_started = time.perf_counter()
        exact_evaluated_requests = 0
        while pending_requests:
            if stop_event and stop_event.is_set():
                return []
            threshold: Optional[float] = None
            if (
                bound_pruning_enabled
                and len(results_by_key) >= GEAR_SEARCH_REQUIRED_RESULTS
            ):
                ranked_scores = sorted(
                    (float(result[1]) for result in results_by_key.values()),
                    reverse=True,
                )
                threshold = ranked_scores[GEAR_SEARCH_REQUIRED_RESULTS - 1]
                tolerance = max(
                    1e-7,
                    abs(threshold) * 1e-12,
                    score_tie_tolerance(mode),
                )
                retained_requests: List[OptimizationRequest] = []
                for request in pending_requests:
                    if (
                        float(upper_bounds.get(request.cache_key, math.inf))
                        >= threshold - tolerance
                    ):
                        retained_requests.append(request)
                    else:
                        deferred_requests.append(request)
                pending_requests = retained_requests
                if not pending_requests:
                    break

            exact_batch_size = (
                GEAR_SEARCH_REQUIRED_RESULTS
                if len(results_by_key) < GEAR_SEARCH_REQUIRED_RESULTS
                else max(1, int(optimization_session.worker_count))
            )
            batch = pending_requests[:exact_batch_size]
            pending_requests = pending_requests[exact_batch_size:]
            batch_results = optimization_session.optimize_batch(
                batch,
                stop_event=stop_event,
            )
            if stop_event and stop_event.is_set():
                return []
            exact_evaluated_requests += len(batch)
            for request in batch:
                best = batch_results.get(request.cache_key)
                optimize_result_cache.setdefault(request.cache_key, best)
                if best is None:
                    continue
                request_bound = float(
                    upper_bounds.get(request.cache_key, math.inf)
                )
                bound_tolerance = max(1e-7, abs(float(best[1])) * 1e-12)
                if (
                    bound_pruning_enabled
                    and math.isfinite(request_bound)
                    and float(best[1]) > request_bound + bound_tolerance
                ):
                    logger.error(
                        "Optimization upper bound violation; disabling pruning "
                        "(request_id=%s, score=%.12f, bound=%.12f)",
                        request.request_id,
                        float(best[1]),
                        request_bound,
                    )
                    bound_pruning_enabled = False
                    pending_requests.extend(deferred_requests)
                    deferred_requests.clear()
                    pending_requests.sort(key=lambda item: int(item.request_id))
                result_key = _result_key_for_best(best)
                existing = results_by_key.get(result_key)
                if existing is None or float(best[1]) > float(existing[1]):
                    results_by_key[result_key] = best
            if progress:
                elapsed = max(0.0, time.perf_counter() - exact_started)
                processed = exact_evaluated_requests + max(
                    0,
                    len(deferred_requests),
                )
                detail_pct = int((processed / max(1, len(requests))) * 100)
                _emit_progress(
                    40 + int(detail_pct * 50 / 100),
                    (
                        f"装備候補を精査中 {exact_evaluated_requests}件実行、"
                        f"残り最大{len(pending_requests)}件 "
                        f"({optimization_session.worker_count}並列、経過{int(elapsed)}秒)"
                    ),
                    detail_value=detail_pct,
                    detail_message="候補精査",
                )
        if debug_enabled and upper_bounds:
            sim_log(
                f"[gear-search] exact_upper_bound total={len(requests)} "
                f"evaluated={exact_evaluated_requests} "
                f"pruned={max(0, len(requests) - exact_evaluated_requests)}"
            )
    else:
        for idx, state in enumerate(shortlist):
            if stop_event and stop_event.is_set():
                return []
            if progress:
                _emit_progress(
                    35 + int((idx / max(1, total_candidates)) * 55),
                    f"装備候補を精査中 {idx + 1}/{total_candidates}",
                    detail_value=int(((idx + 1) / max(1, total_candidates)) * 100),
                    detail_message="候補精査",
                )

            def _nested_progress(pct: int, message: str, *, index: int = idx) -> None:
                if not progress:
                    return
                candidate_start = 35 + int((index / max(1, total_candidates)) * 55)
                candidate_span = max(1, int(55 / max(1, total_candidates)))
                mapped = candidate_start + int((max(0, min(100, pct)) / 100.0) * candidate_span)
                _emit_progress(
                    min(98, mapped),
                    f"装備候補 {index + 1}/{total_candidates}: {message}",
                    detail_value=max(0, min(100, int(pct))),
                    detail_message=f"候補 {index + 1}/{total_candidates}",
                )

            candidate_result = _optimize_search_candidate(idx, state, _nested_progress)
            if candidate_result is None:
                continue
            _idx, best = candidate_result
            result_key = _result_key_for_best(best)
            existing = results_by_key.get(result_key)
            if existing is None or float(best[1]) > float(existing[1]):
                results_by_key[result_key] = best

    results = list(results_by_key.values())
    results.sort(key=lambda entry: (-float(entry[1]), float(entry[2])))

    def _gear_search_result_sort_key(entry: Tuple[Gearset, float, float]) -> Tuple[float, float, int]:
        gs, score, gcd = entry
        return (-float(score), float(gcd), int((gs.food_id or 0)))

    def _gear_search_gearset_key(gs: Gearset) -> Tuple:
        key_slots = []
        for slot_name in GEAR_SLOTS:
            sel = (gs.items or {}).get(slot_name)
            mats = tuple((m.base_param, m.grade) for m in (sel.materia or [])) if sel else tuple()
            relic = tuple(sorted((int(stat_id), int(val)) for stat_id, val in ((getattr(sel, "relic_stats", {}) or {}).items() if sel else []) if int(val or 0) > 0))
            key_slots.append((slot_name, sel.item_id if sel else None, mats, relic))
        return (gs.food_id, tuple(key_slots))

    def _resolve_search_selected_items(gs: Gearset) -> Tuple[Dict[str, ItemRecord], set]:
        selected: Dict[str, ItemRecord] = {}
        no_meld: set = set()
        seen_unique: set = set()
        for slot_name in GEAR_SLOTS:
            sel = (gs.items or {}).get(slot_name)
            if not sel or not sel.item_id:
                continue
            item_id = int(sel.item_id)
            relic_key = tuple(
                sorted(
                    (int(stat_id), int(value))
                    for stat_id, value in dict(getattr(sel, "relic_stats", {}) or {}).items()
                    if int(value or 0) > 0
                )
            )
            slot_lookup = candidate_item_lookup_by_slot.get(slot_name, {})
            effective_item = slot_lookup.get((item_id, relic_key))
            if effective_item is None:
                effective_item = slot_lookup.get((item_id, ()))
            if effective_item is None:
                fallback_item = items_by_id.get(item_id)
                if fallback_item is None:
                    continue
                effective_item = fallback_item
            if slot_name in {"ring1", "ring2"} and bool(getattr(effective_item, "unique", False)):
                if item_id in seen_unique:
                    continue
                seen_unique.add(item_id)
            selected[slot_name] = effective_item
            if _total_meld_slots_cached(effective_item) <= 0:
                no_meld.add(slot_name)
        return selected, no_meld

    if results and mode == "dmg100p":
        refine_slots = [
            slot
            for slot in [
                "weapon",
                "body",
                "legs",
                "head",
                "hands",
                "feet",
                "earrings",
                "necklace",
                "bracelet",
                "ring1",
                "ring2",
                "offhand",
            ]
            if len(candidate_items_by_slot.get(slot) or []) > 1
            and not _selection_lock_item((gearset.items or {}).get(slot))
        ]
        local_refine_slot_limits = {
            "weapon": 12,
            "offhand": 8,
            "body": 10,
            "legs": 10,
            "head": 10,
            "hands": 10,
            "feet": 10,
            "earrings": 8,
            "necklace": 8,
            "bracelet": 8,
            "ring1": 8,
            "ring2": 8,
        }
        local_refine_candidates_by_slot: Dict[str, List[ItemRecord]] = {}
        for slot in refine_slots:
            pool = list(candidate_items_by_slot.get(slot) or [])
            pool.sort(
                key=lambda item: (
                    -_gear_search_item_score(
                        item,
                        job,
                        search_target_gcd,
                        level_value,
                        score_context=search_score_context,
                    ),
                    -int(item.ilvl or 0),
                    int(item.item_id),
                )
            )
            if int(level_sync_ilvl or 0) > 0:
                local_refine_slot_limits[slot] = max(local_refine_slot_limits.get(slot, 8), 12)
            limit = max(1, min(len(pool), int(local_refine_slot_limits.get(slot, 3))))
            local_refine_candidates_by_slot[slot] = pool[:limit]

        refine_result_limit = min(len(results), 2)
        refine_iterations = 2
        refined_candidates: List[Tuple[Gearset, float, float]] = []
        if progress:
            _emit_progress(
                99,
                f"装備候補を局所改善中 0/{refine_result_limit}",
                detail_value=0,
                detail_message="局所改善",
            )
        for result_index in range(refine_result_limit):
            if stop_event and stop_event.is_set():
                break
            best_gs, best_score, best_gcd = results[result_index]
            improved_any = False
            for iteration in range(refine_iterations):
                if stop_event and stop_event.is_set():
                    break
                improved_this_round = False
                for slot_name in refine_slots:
                    if progress:
                        slot_label = SLOT_LABELS.get(slot_name, slot_name)
                        _emit_progress(
                            99,
                            f"装備候補を局所改善中 {result_index + 1}/{refine_result_limit}: {slot_label}",
                            detail_value=int(((result_index + 1) / max(1, refine_result_limit)) * 100),
                            detail_message=f"{slot_label}改善",
                        )
                    current_sel = (best_gs.items or {}).get(slot_name)
                    current_item_id = int(current_sel.item_id) if current_sel and current_sel.item_id else 0
                    current_relic_stats = {
                        int(stat_id): int(value)
                        for stat_id, value in dict(
                            getattr(current_sel, "relic_stats", {}) or {}
                        ).items()
                        if int(value or 0) > 0
                    }
                    current_item_key = (current_item_id, tuple(sorted(current_relic_stats.items())))
                    slot_best_gs = best_gs
                    slot_best_score = best_score
                    slot_best_gcd = best_gcd
                    slot_candidates = list(local_refine_candidates_by_slot.get(slot_name) or [])
                    if (
                        current_item_id > 0
                        and not any(
                            _search_item_key(item) == current_item_key
                            for item in slot_candidates
                        )
                    ):
                        current_item = candidate_item_lookup_by_slot.get(slot_name, {}).get(
                            current_item_key
                        )
                        if current_item is not None:
                            slot_candidates.insert(0, current_item)
                    prepared_swaps: List[
                        Tuple[
                            Tuple,
                            Gearset,
                            Dict[str, ItemRecord],
                            set,
                        ]
                    ] = []
                    for candidate_item in slot_candidates:
                        candidate_item_id = int(getattr(candidate_item, "item_id", 0) or 0)
                        candidate_relic_stats = _search_relic_stats(candidate_item)
                        if candidate_item_id <= 0 or _search_item_key(candidate_item) == current_item_key:
                            continue
                        swapped = _clone_gearset_with_swapped_item(
                            best_gs,
                            slot_name,
                            candidate_item_id,
                            candidate_relic_stats,
                        )
                        swapped_selected, swapped_no_meld = _resolve_search_selected_items(swapped)
                        if not swapped_selected:
                            continue
                        prepared_swaps.append(
                            (
                                _optimize_cache_key(
                                    swapped,
                                    swapped_selected,
                                    swapped_no_meld,
                                ),
                                swapped,
                                swapped_selected,
                                swapped_no_meld,
                            )
                        )

                    parallel_swap_results: Dict[
                        Tuple,
                        Optional[Tuple[Gearset, float, float]],
                    ] = {}
                    evaluated_swap_keys: set = set()
                    if optimization_session is not None and prepared_swaps:
                        swap_requests = [
                            OptimizationRequest(
                                request_id=request_index,
                                cache_key=cache_key,
                                gearset=swapped,
                                selected_items=swapped_selected,
                                no_meld_slots=swapped_no_meld,
                            )
                            for request_index, (
                                cache_key,
                                swapped,
                                swapped_selected,
                                swapped_no_meld,
                            ) in enumerate(prepared_swaps)
                        ]
                        current_selected, current_no_meld = (
                            _resolve_search_selected_items(best_gs)
                        )
                        current_bound_request = OptimizationRequest(
                            request_id=len(swap_requests),
                            cache_key=_optimize_cache_key(
                                best_gs,
                                current_selected,
                                current_no_meld,
                            ),
                            gearset=best_gs,
                            selected_items=current_selected,
                            no_meld_slots=current_no_meld,
                        )
                        swap_bounds = optimization_session.evaluate_upper_bounds(
                            swap_requests + [current_bound_request],
                            stop_event=stop_event,
                        )
                        threshold_tolerance = max(
                            1e-7,
                            abs(float(slot_best_score)) * 1e-12,
                        )
                        current_bound = float(
                            swap_bounds.get(
                                current_bound_request.cache_key,
                                math.inf,
                            )
                        )
                        if (
                            math.isfinite(current_bound)
                            and float(slot_best_score)
                            > current_bound + threshold_tolerance
                        ):
                            logger.error(
                                "Optimization upper bound violation in local "
                                "refinement; disabling swap pruning "
                                "(score=%.12f, bound=%.12f)",
                                float(slot_best_score),
                                current_bound,
                            )
                        else:
                            swap_requests = [
                                request
                                for request in swap_requests
                                if float(
                                    swap_bounds.get(
                                        request.cache_key,
                                        math.inf,
                                    )
                                )
                                >= float(slot_best_score) - threshold_tolerance
                            ]
                        evaluated_swap_keys = {
                            request.cache_key for request in swap_requests
                        }

                        def _swap_progress(
                            completed: int,
                            total: int,
                            _elapsed: float,
                            _eta: Optional[float],
                        ) -> None:
                            if not progress:
                                return
                            detail_pct = int((completed / max(1, total)) * 100)
                            _emit_progress(
                                99,
                                (
                                    f"装備候補を局所改善中 "
                                    f"{result_index + 1}/{refine_result_limit}: "
                                    f"{slot_label} {completed}/{total}"
                                ),
                                detail_value=detail_pct,
                                detail_message=f"{slot_label}改善",
                            )

                        parallel_swap_results = optimization_session.optimize_batch(
                            swap_requests,
                            stop_event=stop_event,
                            progress=_swap_progress,
                        )

                    for candidate_index, (
                        cache_key,
                        swapped,
                        swapped_selected,
                        swapped_no_meld,
                    ) in enumerate(prepared_swaps, 1):
                        if stop_event and stop_event.is_set():
                            break
                        if progress and optimization_session is None:
                            _emit_progress(
                                99,
                                f"装備候補を局所改善中 {result_index + 1}/{refine_result_limit}: {slot_label}",
                                detail_value=int((candidate_index / max(1, len(prepared_swaps))) * 100),
                                detail_message=f"{slot_label}改善",
                            )
                        if optimization_session is not None:
                            if cache_key not in evaluated_swap_keys:
                                continue
                            swapped_best = parallel_swap_results.get(cache_key)
                            optimize_result_cache.setdefault(cache_key, swapped_best)
                        else:
                            swapped_best = _run_optimize_cached(
                                swapped,
                                swapped_selected,
                                swapped_no_meld,
                                None,
                            )
                        if not swapped_best:
                            continue
                        swapped_best_gs, swapped_best_score, swapped_best_gcd = swapped_best
                        if swapped_best_score > slot_best_score + 1e-6:
                            slot_best_gs = swapped_best_gs
                            slot_best_score = swapped_best_score
                            slot_best_gcd = swapped_best_gcd
                    if slot_best_score > best_score + 1e-6:
                        if debug_enabled:
                            sim_log(
                                f"[gear-search] local_refine result={result_index} iter={iteration + 1} "
                                f"slot={slot_name} score={best_score:.4f}->{slot_best_score:.4f}"
                            )
                        best_gs, best_score, best_gcd = slot_best_gs, slot_best_score, slot_best_gcd
                        improved_this_round = True
                        improved_any = True
                if not improved_this_round:
                    break
            if improved_any:
                refined_candidates.append((best_gs, best_score, best_gcd))
        if refined_candidates:
            results.extend(refined_candidates)
            results.sort(key=_gear_search_result_sort_key)
            deduped_results: List[Tuple[Gearset, float, float]] = []
            seen_keys: set = set()
            for gs, score, gcd in results:
                result_key = _gear_search_gearset_key(gs)
                if result_key in seen_keys:
                    continue
                seen_keys.add(result_key)
                deduped_results.append((gs, score, gcd))
            results = deduped_results

    if progress and finalize_progress:
        _emit_progress(
            100,
            "装備検索を含む最適化が完了しました",
            detail_value=100,
            detail_message="完了",
        )
    if debug_enabled:
        sim_log(
            f"[gear-search] done slots={len(slot_order)} shortlist={len(shortlist)} results={len(results)}"
        )
    return results[:8]


def MateriaAwareSelection(selection, melds: List[MateriaSlotSelection]):
    # helper to clone ItemSelection while replacing materia list
    return type(selection)(
        item_id=selection.item_id,
        materia=list(melds),
        relic_stats=dict(getattr(selection, "relic_stats", {}) or {}),
        lock_item=bool(getattr(selection, "lock_item", False)),
        lock_materia=bool(getattr(selection, "lock_materia", False)),
        excluded_item_ids=list(getattr(selection, "excluded_item_ids", []) or []),
    )
