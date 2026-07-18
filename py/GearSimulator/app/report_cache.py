from __future__ import annotations

import time
from typing import Dict, Iterable, List, Optional

from .cache import FileCache
from .report_utils import extract_report_code


DEFAULT_REPORT_CACHE_TTL_SECONDS = 15 * 60


class ReportCache:
    def __init__(self, cache: FileCache, ttl_seconds: int = DEFAULT_REPORT_CACHE_TTL_SECONDS) -> None:
        self.cache = cache
        self.ttl_seconds = max(0, int(ttl_seconds))

    @staticmethod
    def _key(code: str) -> str:
        normalized = extract_report_code(code)
        if not normalized:
            raise ValueError("invalid FFLogs report code")
        return f"fflogs_{normalized}.json"

    def load(
        self,
        code: str,
        *,
        allow_stale: bool = False,
        sections: Optional[Iterable[str]] = None,
    ) -> Optional[dict]:
        try:
            key = self._key(code)
        except ValueError:
            return None
        data = self.cache.load(key)
        if not isinstance(data, dict):
            return None
        if allow_stale:
            return data
        timestamps = data.get("saved_at_by_section")
        if not isinstance(timestamps, dict):
            timestamps = {}
        requested_sections = [str(section) for section in sections or [] if section]
        timestamp_values = []
        if requested_sections:
            timestamp_values.extend(
                timestamps.get(section, data.get("saved_at", 0.0)) for section in requested_sections
            )
        else:
            timestamp_values.append(data.get("saved_at", 0.0))
        now = time.time()
        for raw_timestamp in timestamp_values:
            try:
                saved_at = float(raw_timestamp or 0.0)
            except (TypeError, ValueError):
                return None
            if saved_at <= 0 or now - saved_at > self.ttl_seconds:
                return None
        return data

    def save(
        self,
        code: str,
        *,
        fights: Optional[List[dict]] = None,
        players_by_fight: Optional[Dict[str, List[dict]]] = None,
        enemy_npcs: Optional[List[dict]] = None,
    ) -> None:
        key = self._key(code)
        data = self.cache.load(key) or {"code": extract_report_code(code), "fights": [], "players_by_fight": {}}
        if not isinstance(data, dict):
            data = {"code": extract_report_code(code), "fights": [], "players_by_fight": {}}
        saved_at = time.time()
        timestamps = data.get("saved_at_by_section")
        if not isinstance(timestamps, dict):
            timestamps = {}
        if fights is not None:
            data["fights"] = fights
            timestamps["fights"] = saved_at
        if players_by_fight is not None:
            data["players_by_fight"] = players_by_fight
            timestamps["players_by_fight"] = saved_at
        if enemy_npcs is not None:
            data["enemy_npcs"] = enemy_npcs
            timestamps["enemy_npcs"] = saved_at
        data["saved_at_by_section"] = timestamps
        data["saved_at"] = saved_at
        self.cache.save(key, data)
