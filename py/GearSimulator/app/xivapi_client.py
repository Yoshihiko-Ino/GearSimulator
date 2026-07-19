from __future__ import annotations

import re
import logging
import math
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from email.utils import parsedate_to_datetime
from typing import Dict, Iterable, Optional, Tuple

import httpx

from . import APP_VERSION
from .cache import FileCache
from .models import ActionRecord, StatusEffectRecord


BASE_URL = "https://xivapi.com"
V2_BASE_URL = "https://v2.xivapi.com/api"
MAX_CONCURRENT_REQUESTS = 3
V2_BATCH_SIZE = 50
REQUEST_ATTEMPTS = 4
NEGATIVE_CACHE_TTL_SECONDS = 24 * 60 * 60
DICTIONARY_CACHE_METADATA_VERSION = 1
DICTIONARY_REFRESH_SECONDS = 7 * 24 * 60 * 60
logger = logging.getLogger(__name__)


class XivApiClient:
    def __init__(self, cache: FileCache) -> None:
        self.cache = cache
        self._client = httpx.Client(
            base_url=BASE_URL,
            timeout=30,
            headers={"User-Agent": f"GearSimulator/{APP_VERSION}"},
        )
        self._cache_lock = threading.RLock()
        self._request_semaphore = threading.BoundedSemaphore(MAX_CONCURRENT_REQUESTS)
        self._rate_limit_lock = threading.Lock()
        self._rate_limit_until = 0.0
        self._action_cache: Dict[int, ActionRecord] = {}
        self._status_cache: Dict[int, StatusEffectRecord] = {}
        self._negative_cache: Dict[str, float] = {}
        self._action_validated_at: Dict[int, float] = {}
        self._status_validated_at: Dict[int, float] = {}
        self._negative_revision = 0
        self._metadata_revision = 0
        self._last_action_failures: set[int] = set()
        self._last_action_not_found: set[int] = set()
        self._load_cache()

    @staticmethod
    def _fetch_worker_count(total: int) -> int:
        return max(1, min(MAX_CONCURRENT_REQUESTS, int(total)))

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
                    name_ja=_optional_text(v.get("name_ja")),
                    potency=_optional_int(v.get("potency")),
                    dot_potency=_optional_int(v.get("dot_potency")),
                    attack_type=_optional_text(v.get("attack_type")),
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
                    name_ja=_optional_text(v.get("name_ja")),
                    damage_up=_finite_float(v.get("damage_up", 0.0)),
                    crit_rate_up=_finite_float(v.get("crit_rate_up", 0.0)),
                    dhit_rate_up=_finite_float(v.get("dhit_rate_up", 0.0)),
                    force_crit=v.get("force_crit") is True,
                    force_dhit=v.get("force_dhit") is True,
                    dot_effect=v.get("dot_effect") is True,
                )
            except (TypeError, ValueError):
                continue
            self._status_cache[status_id] = status
        negative_cached = self.cache.load("xivapi_missing.json") or {}
        now = time.time()
        if isinstance(negative_cached, dict):
            for key, value in negative_cached.items():
                try:
                    saved_at = float(value)
                except (TypeError, ValueError, OverflowError):
                    continue
                if (
                    saved_at > 0
                    and saved_at <= now + 300.0
                    and now - saved_at < NEGATIVE_CACHE_TTL_SECONDS
                ):
                    self._negative_cache[str(key)] = saved_at
        metadata = self.cache.load("xivapi_metadata.json") or {}
        if (
            isinstance(metadata, dict)
            and metadata.get("version") == DICTIONARY_CACHE_METADATA_VERSION
        ):
            self._action_validated_at = _validated_timestamps(
                metadata.get("action_validated_at"), now
            )
            self._status_validated_at = _validated_timestamps(
                metadata.get("status_validated_at"), now
            )

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
            self.cache.save("xivapi_missing.json", dict(self._negative_cache))
            self.cache.save(
                "xivapi_metadata.json",
                {
                    "version": DICTIONARY_CACHE_METADATA_VERSION,
                    "action_validated_at": {
                        str(key): value for key, value in self._action_validated_at.items()
                    },
                    "status_validated_at": {
                        str(key): value for key, value in self._status_validated_at.items()
                    },
                },
            )

    def close(self) -> None:
        self._client.close()

    def get_cached_action(self, action_id: int) -> Optional[ActionRecord]:
        with self._cache_lock:
            return self._action_cache.get(action_id)

    def last_action_fetch_failures(self) -> Tuple[set[int], set[int]]:
        """Return transient failures and confirmed missing IDs from the last fetch."""
        with self._cache_lock:
            return set(self._last_action_failures), set(self._last_action_not_found)

    def fetch_actions(self, action_ids: Iterable[int]) -> Dict[int, ActionRecord]:
        with self._cache_lock:
            negative_revision_before = self._negative_revision
            metadata_revision_before = self._metadata_revision
        updated = False
        requested_ids = _normalized_ids(action_ids)
        with self._cache_lock:
            result = {
                action_id: self._action_cache[action_id]
                for action_id in requested_ids
                if action_id in self._action_cache
            }
        refresh_ids = [
            action_id
            for action_id in requested_ids
            if action_id not in result or not self._is_dictionary_fresh("action", action_id)
        ]
        fetch_ids = [
            action_id
            for action_id in refresh_ids
            if not self._is_negative_cached("action", action_id)
        ]
        not_found = {
            action_id
            for action_id in refresh_ids
            if action_id not in result and action_id not in fetch_ids
        }
        refreshed_ids: set[int] = set()
        if fetch_ids:
            batch_actions = self._fetch_actions_v2(fetch_ids)
            refreshed_ids.update(batch_actions)
            for action_id, action in batch_actions.items():
                with self._cache_lock:
                    self._action_cache[action_id] = action
                result[action_id] = action
                updated = True
            self._mark_dictionary_validated("action", batch_actions)
            fallback_ids = [action_id for action_id in fetch_ids if action_id not in batch_actions]
            worker_count = self._fetch_worker_count(len(fallback_ids))
            if worker_count == 1:
                fetched_pairs = ((action_id, self._fetch_action(action_id)) for action_id in fallback_ids)
            else:
                with ThreadPoolExecutor(max_workers=worker_count) as ex:
                    future_map = {
                        ex.submit(self._fetch_action, action_id): action_id
                        for action_id in fallback_ids
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
                    self._mark_dictionary_validated("action", [action_id])
                    refreshed_ids.add(action_id)
        refresh_failures = set(fetch_ids) - refreshed_ids
        confirmed_refresh_missing = {
            action_id
            for action_id in refresh_failures
            if self._is_negative_cached("action", action_id)
        }
        not_found.update(confirmed_refresh_missing)
        unresolved = set(requested_ids) - set(result)
        not_found.update(
            action_id
            for action_id in unresolved
            if self._is_negative_cached("action", action_id)
        )
        with self._cache_lock:
            self._last_action_not_found = not_found
            self._last_action_failures = (
                (unresolved - not_found)
                | (refresh_failures - confirmed_refresh_missing)
            )
        with self._cache_lock:
            cache_state_updated = (
                self._negative_revision != negative_revision_before
                or self._metadata_revision != metadata_revision_before
            )
        if updated or cache_state_updated:
            self._save_cache()
        return result

    def get_cached_status(self, status_id: int) -> Optional[StatusEffectRecord]:
        with self._cache_lock:
            return self._status_cache.get(status_id)

    def fetch_statuses(self, status_ids: Iterable[int]) -> Dict[int, StatusEffectRecord]:
        with self._cache_lock:
            negative_revision_before = self._negative_revision
            metadata_revision_before = self._metadata_revision
        updated = False
        result: Dict[int, StatusEffectRecord] = {}
        normalized_to_raw: Dict[int, list[int]] = {}
        for raw_status_id in _normalized_ids(status_ids):
            status_id = _normalize_status_id(raw_status_id)
            normalized_to_raw.setdefault(status_id, []).append(raw_status_id)
            with self._cache_lock:
                cached = self._status_cache.get(raw_status_id) or self._status_cache.get(status_id)
            if cached is not None:
                result[raw_status_id] = cached
                with self._cache_lock:
                    if raw_status_id not in self._status_cache:
                        self._status_cache[raw_status_id] = cached
                        updated = True
        refresh_ids = [
            status_id
            for status_id, raw_ids in normalized_to_raw.items()
            if not any(raw_id in result for raw_id in raw_ids)
            or not self._is_dictionary_fresh("status", status_id)
        ]
        batch_ids = [
            status_id
            for status_id in refresh_ids
            if not self._is_negative_cached("status", status_id)
        ]
        batch_statuses = self._fetch_statuses_v2(batch_ids) if batch_ids else {}
        self._mark_dictionary_validated("status", batch_statuses)
        fallback_ids = [
            status_id
            for status_id in refresh_ids
            if status_id not in batch_statuses
            and not (
                self._is_negative_cached("status", status_id)
                and self._is_negative_cached("action", status_id)
            )
        ]
        fetched_statuses = dict(batch_statuses)
        if fallback_ids:
            worker_count = self._fetch_worker_count(len(fallback_ids))
            if worker_count == 1:
                fetched_pairs = (
                    (status_id, self._fetch_status_chain(status_id, status_id))
                    for status_id in fallback_ids
                )
            else:
                with ThreadPoolExecutor(max_workers=worker_count) as ex:
                    future_map = {
                        ex.submit(self._fetch_status_chain, status_id, status_id): status_id
                        for status_id in fallback_ids
                    }
                    fetched_pairs = (
                        (future_map[fut], fut.result())
                        for fut in as_completed(future_map)
                    )
            for status_id, status in fetched_pairs:
                if status is not None:
                    fetched_statuses[status_id] = status
                    self._mark_dictionary_validated("status", [status_id])
        for status_id, status in fetched_statuses.items():
            raw_ids = normalized_to_raw.get(status_id, [])
            if raw_ids:
                with self._cache_lock:
                    self._status_cache[status_id] = status
                    for raw_status_id in raw_ids:
                        self._status_cache[raw_status_id] = status
                        result[raw_status_id] = status
                updated = True
        with self._cache_lock:
            cache_state_updated = (
                self._negative_revision != negative_revision_before
                or self._metadata_revision != metadata_revision_before
            )
        if updated or cache_state_updated:
            self._save_cache()
        return result

    def _fetch_status_chain(self, _raw_status_id: int, status_id: int) -> Optional[StatusEffectRecord]:
        status = self._fetch_status(status_id)
        if status is None:
            status = self._fetch_status_from_action(status_id)
        return status

    def _fetch_action(self, action_id: int) -> Optional[ActionRecord]:
        try:
            resp = self._request(
                f"/Action/{action_id}",
                params={
                    "columns": "ID,Name,Name_ja,ActionCategory,AttackType",
                    "language": "en",
                },
            )
            if resp is None:
                return None
            if getattr(resp, "status_code", 200) == 404:
                self._mark_negative("action", action_id)
                return None
            resp.raise_for_status()
            data = resp.json()
            if not isinstance(data, dict):
                raise ValueError("response root is not an object")
        except Exception as exc:
            logger.warning("Failed to fetch XIVAPI action %s: %s", action_id, exc)
            return None
        name = data.get("Name") or ""
        name_ja = data.get("Name_ja")
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
            potency=None,
            dot_potency=None,
            attack_type=attack_type,
        )

    def _fetch_status(self, status_id: int) -> Optional[StatusEffectRecord]:
        try:
            if self._is_negative_cached("status", status_id):
                return None
            resp = self._request(
                f"/Status/{status_id}",
                params={
                    "columns": "ID,Name,Name_ja,Description,Description_en,ParamEffect,ParamModifier",
                    "language": "en",
                },
            )
            if resp is None:
                return None
            if getattr(resp, "status_code", 200) == 404:
                self._mark_negative("status", status_id)
                return None
            resp.raise_for_status()
            data = resp.json()
            if not isinstance(data, dict):
                raise ValueError("response root is not an object")
        except Exception as exc:
            logger.warning("Failed to fetch XIVAPI status %s: %s", status_id, exc)
            return None
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
            if self._is_negative_cached("action", action_id):
                return None
            resp = self._request(
                f"/Action/{action_id}",
                params={
                    "columns": "ID,Name,Name_ja,Description",
                    "language": "en",
                },
            )
            if resp is None:
                return None
            if getattr(resp, "status_code", 200) == 404:
                self._mark_negative("action", action_id)
                return None
            resp.raise_for_status()
            data = resp.json()
            if not isinstance(data, dict):
                raise ValueError("response root is not an object")
        except Exception as exc:
            logger.warning("Failed to fetch XIVAPI action fallback %s: %s", action_id, exc)
            return None
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

    def _request(self, path: str, **kwargs: object) -> Optional[httpx.Response]:
        for attempt in range(REQUEST_ATTEMPTS):
            self._wait_for_rate_limit()
            try:
                with self._request_semaphore:
                    response = self._client.get(path, **kwargs)
            except (httpx.HTTPError, OSError) as exc:
                if attempt + 1 >= REQUEST_ATTEMPTS:
                    logger.warning("XIVAPI request failed %s: %s", path, exc)
                    return None
                time.sleep(float(2**attempt))
                continue
            if getattr(response, "status_code", 200) != 429:
                return response
            delay = self._retry_after_seconds(response, attempt)
            with self._rate_limit_lock:
                self._rate_limit_until = max(self._rate_limit_until, time.monotonic() + delay)
            if attempt + 1 >= REQUEST_ATTEMPTS:
                logger.warning("XIVAPI rate limit persisted after retries: %s", path)
                return None
        return None

    def _wait_for_rate_limit(self) -> None:
        while True:
            with self._rate_limit_lock:
                delay = self._rate_limit_until - time.monotonic()
            if delay <= 0:
                return
            time.sleep(delay)

    @staticmethod
    def _retry_after_seconds(response: httpx.Response, attempt: int) -> float:
        headers = getattr(response, "headers", {}) or {}
        value = headers.get("Retry-After")
        if value:
            try:
                return max(0.0, min(60.0, float(value)))
            except (TypeError, ValueError, OverflowError):
                try:
                    parsed = parsedate_to_datetime(str(value))
                    return max(0.0, min(60.0, parsed.timestamp() - time.time()))
                except (TypeError, ValueError, OverflowError):
                    pass
        return float(min(8, 2**attempt))

    @staticmethod
    def _negative_key(resource: str, record_id: int) -> str:
        return f"{resource}:{int(record_id)}"

    def _is_dictionary_fresh(self, resource: str, record_id: int) -> bool:
        with self._cache_lock:
            timestamps = (
                self._action_validated_at
                if resource == "action"
                else self._status_validated_at
            )
            validated_at = timestamps.get(int(record_id))
        if validated_at is None:
            return False
        age = time.time() - validated_at
        return 0.0 <= age < DICTIONARY_REFRESH_SECONDS

    def _mark_dictionary_validated(
        self,
        resource: str,
        record_ids: Iterable[int],
    ) -> None:
        ids = _normalized_ids(record_ids)
        if not ids:
            return
        now = time.time()
        with self._cache_lock:
            timestamps = (
                self._action_validated_at
                if resource == "action"
                else self._status_validated_at
            )
            for record_id in ids:
                timestamps[record_id] = now
            self._metadata_revision += 1

    def _is_negative_cached(self, resource: str, record_id: int) -> bool:
        key = self._negative_key(resource, record_id)
        with self._cache_lock:
            saved_at = self._negative_cache.get(key)
            if saved_at is None:
                return False
            if time.time() - saved_at < NEGATIVE_CACHE_TTL_SECONDS:
                return True
            self._negative_cache.pop(key, None)
            self._negative_revision += 1
        return False

    def _mark_negative(self, resource: str, record_id: int) -> None:
        with self._cache_lock:
            self._negative_cache[self._negative_key(resource, record_id)] = time.time()
            self._negative_revision += 1

    def _fetch_actions_v2(self, action_ids: Iterable[int]) -> Dict[int, ActionRecord]:
        result: Dict[int, ActionRecord] = {}
        ids = _normalized_ids(action_ids)
        for offset in range(0, len(ids), V2_BATCH_SIZE):
            chunk = ids[offset : offset + V2_BATCH_SIZE]
            action_rows = self._fetch_v2_rows(
                "Action",
                chunk,
                "Name@ja,Name@en,ActionCategory.Name@en,AttackType.Name@en",
            )
            if action_rows is None:
                continue
            for action_id, fields in action_rows.items():
                name = str(fields.get("Name@en") or fields.get("Name") or "")
                name_ja = fields.get("Name@ja")
                attack_type = _nested_name(fields.get("ActionCategory")) or _nested_name(
                    fields.get("AttackType")
                )
                result[action_id] = ActionRecord(
                    action_id=action_id,
                    name=name,
                    name_ja=str(name_ja) if name_ja else None,
                    potency=None,
                    dot_potency=None,
                    attack_type=attack_type,
                )
        return result

    def _fetch_statuses_v2(self, status_ids: Iterable[int]) -> Dict[int, StatusEffectRecord]:
        result: Dict[int, StatusEffectRecord] = {}
        ids = _normalized_ids(status_ids)
        for offset in range(0, len(ids), V2_BATCH_SIZE):
            chunk = ids[offset : offset + V2_BATCH_SIZE]
            rows = self._fetch_v2_rows(
                "Status",
                chunk,
                "Name@ja,Name@en,Description@en,ParamEffect,ParamModifier",
            )
            if rows is None:
                continue
            for status_id, fields in rows.items():
                desc = _strip_html(
                    str(fields.get("Description@en") or fields.get("Description") or "")
                )
                effects = _parse_status_effects(
                    desc,
                    fields.get("ParamEffect"),
                    fields.get("ParamModifier"),
                )
                result[status_id] = StatusEffectRecord(
                    status_id=status_id,
                    name=str(fields.get("Name@en") or fields.get("Name") or ""),
                    name_ja=(str(fields.get("Name@ja")) if fields.get("Name@ja") else None),
                    damage_up=effects[0],
                    crit_rate_up=effects[1],
                    dhit_rate_up=effects[2],
                    force_crit=effects[3],
                    force_dhit=effects[4],
                    dot_effect=effects[5],
                )
        return result

    def _fetch_v2_rows(
        self,
        sheet: str,
        row_ids: Iterable[int],
        fields: str,
    ) -> Optional[Dict[int, dict]]:
        ids = _normalized_ids(row_ids)
        if not ids:
            return {}
        try:
            response = self._request(
                f"{V2_BASE_URL}/sheet/{sheet}",
                params={"rows": ",".join(str(value) for value in ids), "fields": fields},
            )
        except Exception as exc:
            # Keep the v1 per-record fallback usable with alternate transports.
            logger.warning("Failed to request XIVAPI v2 %s batch: %s", sheet, exc)
            return None
        if response is None:
            return None
        try:
            response.raise_for_status()
            payload = response.json()
            rows = payload.get("rows") if isinstance(payload, dict) else None
            if not isinstance(rows, list):
                raise ValueError("response rows are not a list")
            result: Dict[int, dict] = {}
            for row in rows:
                if not isinstance(row, dict) or not isinstance(row.get("fields"), dict):
                    continue
                row_id = int(row.get("row_id"))
                if row_id in ids:
                    result[row_id] = row["fields"]
            return result
        except (httpx.HTTPError, TypeError, ValueError, OverflowError) as exc:
            logger.warning("Failed to fetch XIVAPI v2 %s batch: %s", sheet, exc)
            return None


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


def _normalized_ids(values: Iterable[int]) -> list[int]:
    result = set()
    for value in values:
        try:
            record_id = int(value)
        except (TypeError, ValueError, OverflowError):
            continue
        if record_id > 0:
            result.add(record_id)
    return sorted(result)


def _optional_text(value: object) -> Optional[str]:
    if value is None:
        return None
    text = str(value)
    return text or None


def _optional_int(value: object) -> Optional[int]:
    if value is None or isinstance(value, bool):
        return None
    try:
        return int(value)
    except (TypeError, ValueError, OverflowError):
        return None


def _finite_float(value: object) -> float:
    try:
        result = float(value)
    except (TypeError, ValueError, OverflowError) as exc:
        raise ValueError("invalid cached numeric value") from exc
    if not math.isfinite(result):
        raise ValueError("cached numeric value must be finite")
    return result


def _nested_name(value: object) -> Optional[str]:
    if not isinstance(value, dict):
        return None
    fields = value.get("fields")
    source = fields if isinstance(fields, dict) else value
    name = source.get("Name@en") or source.get("Name_en") or source.get("Name")
    return str(name) if name else None


def _normalize_status_id(status_id: int) -> int:
    # FFLogs v1 timeline can emit status IDs as 100xxxx while XIVAPI uses xxxx.
    if status_id >= 1_000_000:
        return status_id - 1_000_000
    return status_id


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
        except (TypeError, ValueError, OverflowError):
            continue
    for m in _CRIT_UP_RE.findall(description):
        try:
            crit_up += float(m) / 100.0
        except (TypeError, ValueError, OverflowError):
            continue
    for m in _DH_UP_RE.findall(description):
        try:
            dh_up += float(m) / 100.0
        except (TypeError, ValueError, OverflowError):
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
    except (TypeError, ValueError, OverflowError):
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


def _validated_timestamps(value: object, now: float) -> Dict[int, float]:
    if not isinstance(value, dict):
        return {}
    result: Dict[int, float] = {}
    for raw_id, raw_timestamp in value.items():
        try:
            record_id = int(raw_id)
            timestamp = float(raw_timestamp)
        except (TypeError, ValueError, OverflowError):
            continue
        if record_id > 0 and 0.0 < timestamp <= now + 300.0 and math.isfinite(timestamp):
            result[record_id] = timestamp
    return result
