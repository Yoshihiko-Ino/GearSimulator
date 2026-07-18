from __future__ import annotations

import re
import logging
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import Dict, Iterable, Optional

import httpx

from .cache import FileCache
from .models import ActionRecord, StatusEffectRecord


BASE_URL = "https://xivapi.com"
logger = logging.getLogger(__name__)


class XivApiClient:
    def __init__(self, cache: FileCache) -> None:
        self.cache = cache
        self._client = httpx.Client(
            base_url=BASE_URL,
            timeout=30,
            headers={"User-Agent": "GearSimulator/2.0.0"},
        )
        self._cache_lock = threading.RLock()
        self._action_cache: Dict[int, ActionRecord] = {}
        self._status_cache: Dict[int, StatusEffectRecord] = {}
        self._load_cache()

    @staticmethod
    def _fetch_worker_count(total: int) -> int:
        return max(1, min(6, int(total)))

    def _load_cache(self) -> None:
        cached = self.cache.load("xivapi_actions.json") or {}
        if not isinstance(cached, dict):
            logger.warning("Ignoring invalid XIVAPI action cache root: %s", type(cached).__name__)
            cached = {}
        for k, v in cached.items():
            if not isinstance(v, dict):
                continue
            try:
                action_id = int(k)
                action = ActionRecord(
                    action_id=action_id,
                    name=str(v.get("name", "") or ""),
                    name_ja=v.get("name_ja"),
                    potency=v.get("potency"),
                    dot_potency=v.get("dot_potency"),
                    attack_type=v.get("attack_type"),
                )
            except (TypeError, ValueError):
                continue
            self._action_cache[action_id] = action
        status_cached = self.cache.load("xivapi_statuses.json") or {}
        if not isinstance(status_cached, dict):
            logger.warning("Ignoring invalid XIVAPI status cache root: %s", type(status_cached).__name__)
            status_cached = {}
        for k, v in status_cached.items():
            if not isinstance(v, dict):
                continue
            try:
                status_id = int(k)
                status = StatusEffectRecord(
                    status_id=status_id,
                    name=str(v.get("name", "") or ""),
                    name_ja=v.get("name_ja"),
                    damage_up=float(v.get("damage_up", 0.0)),
                    crit_rate_up=float(v.get("crit_rate_up", 0.0)),
                    dhit_rate_up=float(v.get("dhit_rate_up", 0.0)),
                    force_crit=bool(v.get("force_crit", False)),
                    force_dhit=bool(v.get("force_dhit", False)),
                    dot_effect=bool(v.get("dot_effect", False)),
                )
            except (TypeError, ValueError):
                continue
            self._status_cache[status_id] = status

    def _save_cache(self) -> None:
        with self._cache_lock:
            payload = {
                str(k): {
                    "name": v.name,
                    "name_ja": v.name_ja,
                    "potency": v.potency,
                    "dot_potency": v.dot_potency,
                    "attack_type": v.attack_type,
                }
                for k, v in self._action_cache.items()
            }
            status_payload = {
                str(k): {
                    "name": v.name,
                    "name_ja": v.name_ja,
                    "damage_up": v.damage_up,
                    "crit_rate_up": v.crit_rate_up,
                    "dhit_rate_up": v.dhit_rate_up,
                    "force_crit": v.force_crit,
                    "force_dhit": v.force_dhit,
                    "dot_effect": v.dot_effect,
                }
                for k, v in self._status_cache.items()
            }
            self.cache.save("xivapi_actions.json", payload)
            self.cache.save("xivapi_statuses.json", status_payload)

    def close(self) -> None:
        self._client.close()

    def get_cached_action(self, action_id: int) -> Optional[ActionRecord]:
        with self._cache_lock:
            return self._action_cache.get(action_id)

    def fetch_actions(self, action_ids: Iterable[int]) -> Dict[int, ActionRecord]:
        updated = False
        result: Dict[int, ActionRecord] = {}
        missing_ids = []
        for action_id in sorted({int(a) for a in action_ids if a}):
            with self._cache_lock:
                cached_action = self._action_cache.get(action_id)
            if cached_action is not None:
                result[action_id] = cached_action
                continue
            missing_ids.append(action_id)
        if missing_ids:
            worker_count = self._fetch_worker_count(len(missing_ids))
            if worker_count == 1:
                fetched_pairs = ((action_id, self._fetch_action(action_id)) for action_id in missing_ids)
            else:
                with ThreadPoolExecutor(max_workers=worker_count) as ex:
                    future_map = {
                        ex.submit(self._fetch_action, action_id): action_id
                        for action_id in missing_ids
                    }
                    fetched_pairs = (
                        (future_map[fut], fut.result())
                        for fut in as_completed(future_map)
                    )
            for action_id, action in fetched_pairs:
                if action:
                    with self._cache_lock:
                        self._action_cache[action_id] = action
                    result[action_id] = action
                    updated = True
        if updated:
            self._save_cache()
        return result

    def get_cached_status(self, status_id: int) -> Optional[StatusEffectRecord]:
        with self._cache_lock:
            return self._status_cache.get(status_id)

    def fetch_statuses(self, status_ids: Iterable[int]) -> Dict[int, StatusEffectRecord]:
        updated = False
        result: Dict[int, StatusEffectRecord] = {}
        missing_statuses = []
        for raw_status_id in sorted({int(s) for s in status_ids if s}):
            status_id = _normalize_status_id(raw_status_id)
            with self._cache_lock:
                cached = self._status_cache.get(raw_status_id) or self._status_cache.get(status_id)
            if cached is not None:
                if raw_status_id >= 1_000_000 and not _record_has_effect(cached):
                    refreshed = self._fetch_status(status_id)
                    if refreshed is not None:
                        cached = refreshed
                        with self._cache_lock:
                            self._status_cache[status_id] = refreshed
                            self._status_cache[raw_status_id] = refreshed
                        updated = True
                result[raw_status_id] = cached
                # Keep a direct mapping for the FFLogs raw ID (100xxxx).
                with self._cache_lock:
                    if raw_status_id not in self._status_cache:
                        self._status_cache[raw_status_id] = cached
                        updated = True
                continue
            missing_statuses.append((raw_status_id, status_id))
        if missing_statuses:
            worker_count = self._fetch_worker_count(len(missing_statuses))
            if worker_count == 1:
                fetched_pairs = (
                    ((raw_status_id, status_id), self._fetch_status_chain(raw_status_id, status_id))
                    for raw_status_id, status_id in missing_statuses
                )
            else:
                with ThreadPoolExecutor(max_workers=worker_count) as ex:
                    future_map = {
                        ex.submit(self._fetch_status_chain, raw_status_id, status_id): (raw_status_id, status_id)
                        for raw_status_id, status_id in missing_statuses
                    }
                    fetched_pairs = (
                        (future_map[fut], fut.result())
                        for fut in as_completed(future_map)
                    )
            for (raw_status_id, status_id), status in fetched_pairs:
                if status:
                    with self._cache_lock:
                        self._status_cache[status_id] = status
                        self._status_cache[raw_status_id] = status
                    result[raw_status_id] = status
                    updated = True
        if updated:
            self._save_cache()
        return result

    def _fetch_status_chain(self, raw_status_id: int, status_id: int) -> Optional[StatusEffectRecord]:
        status = self._fetch_status(status_id)
        if status is None and status_id != raw_status_id:
            status = self._fetch_status(raw_status_id)
        if status is None:
            status = self._fetch_status_from_action(status_id)
        if status is None and status_id != raw_status_id:
            status = self._fetch_status_from_action(raw_status_id)
        return status

    def _fetch_action(self, action_id: int) -> Optional[ActionRecord]:
        try:
            resp = self._client.get(
                f"/Action/{action_id}",
                params={
                    "columns": "ID,Name,Name_ja,Description,ActionCategory,AttackType",
                    "language": "en",
                },
            )
            resp.raise_for_status()
        except Exception as exc:
            logger.warning("Failed to fetch XIVAPI action %s: %s", action_id, exc)
            return None
        data = resp.json()
        name = data.get("Name") or ""
        name_ja = data.get("Name_ja")
        desc = data.get("Description") or ""
        potency, dot_potency = _parse_potencies(desc)
        attack_type = None
        cat = data.get("ActionCategory") or {}
        if isinstance(cat, dict):
            attack_type = cat.get("Name_en") or cat.get("Name") or None
        if not attack_type:
            atk = data.get("AttackType") or {}
            if isinstance(atk, dict):
                attack_type = atk.get("Name_en") or atk.get("Name")
        return ActionRecord(
            action_id=action_id,
            name=name,
            name_ja=name_ja,
            potency=potency,
            dot_potency=dot_potency,
            attack_type=attack_type,
        )

    def _fetch_status(self, status_id: int) -> Optional[StatusEffectRecord]:
        try:
            resp = self._client.get(
                f"/Status/{status_id}",
                params={
                    "columns": "ID,Name,Name_ja,Description,Description_en,ParamEffect,ParamModifier",
                    "language": "en",
                },
            )
            resp.raise_for_status()
        except Exception as exc:
            logger.warning("Failed to fetch XIVAPI status %s: %s", status_id, exc)
            return None
        data = resp.json()
        name = data.get("Name") or ""
        name_ja = data.get("Name_ja")
        desc = _strip_html(data.get("Description_en") or data.get("Description") or "")
        damage_up, crit_up, dh_up, force_crit, force_dhit, dot_effect = _parse_status_effects(
            desc,
            data.get("ParamEffect"),
            data.get("ParamModifier"),
        )
        return StatusEffectRecord(
            status_id=status_id,
            name=name,
            name_ja=name_ja,
            damage_up=damage_up,
            crit_rate_up=crit_up,
            dhit_rate_up=dh_up,
            force_crit=force_crit,
            force_dhit=force_dhit,
            dot_effect=dot_effect,
        )

    def _fetch_status_from_action(self, action_id: int) -> Optional[StatusEffectRecord]:
        try:
            resp = self._client.get(
                f"/Action/{action_id}",
                params={
                    "columns": "ID,Name,Name_ja,Description",
                    "language": "en",
                },
            )
            resp.raise_for_status()
        except Exception as exc:
            logger.warning("Failed to fetch XIVAPI action fallback %s: %s", action_id, exc)
            return None
        data = resp.json()
        name = data.get("Name") or ""
        name_ja = data.get("Name_ja")
        desc = _strip_html(data.get("Description") or "")
        damage_up, crit_up, dh_up, force_crit, force_dhit, dot_effect = _parse_status_effects(desc)
        if (
            damage_up == 0.0
            and crit_up == 0.0
            and dh_up == 0.0
            and not force_crit
            and not force_dhit
            and not dot_effect
        ):
            return None
        return StatusEffectRecord(
            status_id=action_id,
            name=name,
            name_ja=name_ja,
            damage_up=damage_up,
            crit_rate_up=crit_up,
            dhit_rate_up=dh_up,
            force_crit=force_crit,
            force_dhit=force_dhit,
            dot_effect=dot_effect,
        )


_POTENCY_RE = re.compile(r"potency of (\d+)", re.IGNORECASE)
_DOT_RE = re.compile(r"damage over time with a potency of (\d+)", re.IGNORECASE)
_DMG_UP_RE = re.compile(r"increases? damage dealt by (\d+)%", re.IGNORECASE)
_CRIT_UP_RE = re.compile(r"increases? critical hit rate by (\d+)%", re.IGNORECASE)
_DH_UP_RE = re.compile(r"increases? direct hit rate by (\d+)%", re.IGNORECASE)
_FORCE_BOTH_RE = re.compile(r"(guarantees?|are) (?:critical and direct hits?|critical direct hits?)", re.IGNORECASE)
_FORCE_CRIT_RE = re.compile(r"(guarantees?|are) critical hits?", re.IGNORECASE)
_FORCE_DH_RE = re.compile(r"(guarantees?|are) direct hits?", re.IGNORECASE)


def _strip_html(text: str) -> str:
    if not text:
        return ""
    return re.sub(r"<[^>]+>", "", text)


def _normalize_status_id(status_id: int) -> int:
    # FFLogs v1 timeline can emit status IDs as 100xxxx while XIVAPI uses xxxx.
    if status_id >= 1_000_000:
        return status_id - 1_000_000
    return status_id


def _parse_potencies(description: str) -> tuple[Optional[int], Optional[int]]:
    text = _strip_html(description)
    dot_match = _DOT_RE.search(text)
    dot_potency = int(dot_match.group(1)) if dot_match else None
    pot_match = _POTENCY_RE.search(text)
    potency = int(pot_match.group(1)) if pot_match else None
    return potency, dot_potency


def _parse_status_effects(
    description: str,
    param_effect: Optional[object] = None,
    param_modifier: Optional[object] = None,
) -> tuple[float, float, float, bool, bool, bool]:
    if not description:
        return 0.0, 0.0, 0.0, False, False, False
    return _parse_status_effects_with_params(description, param_effect, param_modifier)


def _parse_status_effects_with_params(
    description: str,
    param_effect: Optional[object],
    param_modifier: Optional[object],
) -> tuple[float, float, float, bool, bool, bool]:
    damage_up = 0.0
    crit_up = 0.0
    dh_up = 0.0
    force_crit = False
    force_dhit = False
    dot_effect = False
    lower = description.lower()

    for m in _DMG_UP_RE.findall(description):
        try:
            damage_up += float(m) / 100.0
        except Exception:
            continue
    for m in _CRIT_UP_RE.findall(description):
        try:
            crit_up += float(m) / 100.0
        except Exception:
            continue
    for m in _DH_UP_RE.findall(description):
        try:
            dh_up += float(m) / 100.0
        except Exception:
            continue

    if _FORCE_BOTH_RE.search(description):
        force_crit = True
        force_dhit = True
    else:
        if _FORCE_CRIT_RE.search(description):
            force_crit = True
        if _FORCE_DH_RE.search(description):
            force_dhit = True

    if "damage over time" in lower or "potency over time" in lower:
        dot_effect = True

    pm = None
    try:
        pm = float(param_modifier)
    except Exception:
        pm = None

    # Many status descriptions in XIVAPI omit the explicit number ("is increased."),
    # but ParamModifier keeps the percentage value.
    if pm and pm > 0:
        if damage_up == 0.0 and "damage dealt is increased" in lower:
            damage_up = pm / 100.0
        if crit_up == 0.0 and "critical hit rate is increased" in lower:
            crit_up = pm / 100.0
        if dh_up == 0.0 and "direct hit rate is increased" in lower:
            dh_up = pm / 100.0

    return damage_up, crit_up, dh_up, force_crit, force_dhit, dot_effect


def _record_has_effect(rec: StatusEffectRecord) -> bool:
    return bool(
        (rec.damage_up or 0.0) > 0.0
        or (rec.crit_rate_up or 0.0) > 0.0
        or (rec.dhit_rate_up or 0.0) > 0.0
        or rec.force_crit
        or rec.force_dhit
        or rec.dot_effect
    )
