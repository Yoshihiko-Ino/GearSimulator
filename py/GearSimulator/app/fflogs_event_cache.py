from __future__ import annotations

import gzip
import json
import logging
import os
import re
import tempfile
import threading
import time
from pathlib import Path
from typing import Any, Dict, List, Optional

from .cache import FileCache
from .report_utils import extract_report_code


logger = logging.getLogger(__name__)

EVENT_CACHE_VERSION = 1
DEFAULT_EVENT_CACHE_LIMIT = 30
MAX_COMPRESSED_ENTRY_BYTES = 20 * 1024 * 1024
MAX_DECOMPRESSED_ENTRY_BYTES = 100 * 1024 * 1024
_ENTRY_ID_RE = re.compile(r"^[A-Za-z0-9]+_[1-9][0-9]*_[1-9][0-9]*_p[01]$")


class FFLogsEventCache:
    def __init__(
        self,
        cache: FileCache,
        *,
        entry_limit: int = DEFAULT_EVENT_CACHE_LIMIT,
    ) -> None:
        self.cache = cache
        self.entry_limit = max(1, int(entry_limit))
        self._lock = threading.RLock()
        self._index_name = "fflogs_events/index.json"

    @staticmethod
    def _context(
        report_code: str,
        fight_id: int,
        actor_id: int,
        include_pets: bool,
    ) -> Optional[Dict[str, Any]]:
        code = extract_report_code(str(report_code or ""))
        if not code:
            return None
        try:
            normalized_fight = int(fight_id)
            normalized_actor = int(actor_id)
        except (TypeError, ValueError, OverflowError):
            return None
        if normalized_fight <= 0 or normalized_actor <= 0:
            return None
        return {
            "report_code": code,
            "fight_id": normalized_fight,
            "actor_id": normalized_actor,
            "include_pets": bool(include_pets),
        }

    @staticmethod
    def _entry_id(context: Dict[str, Any]) -> str:
        pets = 1 if context["include_pets"] else 0
        return (
            f"{context['report_code']}_{context['fight_id']}_"
            f"{context['actor_id']}_p{pets}"
        )

    def _entry_path(self, entry_id: str) -> Path:
        return FileCache._safe_path(
            self.cache.base_dir,
            f"fflogs_events/{entry_id}.json.gz",
        )

    def _load_index(self) -> Dict[str, dict]:
        raw = self.cache.load(self._index_name)
        if not isinstance(raw, dict) or raw.get("version") != EVENT_CACHE_VERSION:
            return {}
        entries = raw.get("entries")
        if not isinstance(entries, dict):
            return {}
        return {
            str(key): dict(value)
            for key, value in entries.items()
            if isinstance(key, str)
            and _ENTRY_ID_RE.fullmatch(key)
            and isinstance(value, dict)
        }

    def _save_index(self, entries: Dict[str, dict]) -> None:
        self.cache.save(
            self._index_name,
            {"version": EVENT_CACHE_VERSION, "entries": entries},
        )

    @staticmethod
    def _timestamp(meta: object, *keys: str) -> float:
        if not isinstance(meta, dict):
            return 0.0
        for key in keys:
            try:
                value = float(meta.get(key) or 0.0)
            except (TypeError, ValueError, OverflowError):
                continue
            if value > 0:
                return value
        return 0.0

    def _read_entry(self, path: Path) -> Optional[dict]:
        try:
            if not path.is_file() or path.stat().st_size > MAX_COMPRESSED_ENTRY_BYTES:
                return None
            with gzip.open(path, "rb") as stream:
                raw = stream.read(MAX_DECOMPRESSED_ENTRY_BYTES + 1)
            if len(raw) > MAX_DECOMPRESSED_ENTRY_BYTES:
                return None
            data = json.loads(raw.decode("utf-8"))
        except (OSError, EOFError, UnicodeError, json.JSONDecodeError):
            logger.warning("Ignoring invalid FFLogs event cache: %s", path)
            return None
        return data if isinstance(data, dict) else None

    def _write_entry(self, path: Path, data: dict) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        encoded = json.dumps(
            data,
            ensure_ascii=False,
            separators=(",", ":"),
        ).encode("utf-8")
        if len(encoded) > MAX_DECOMPRESSED_ENTRY_BYTES:
            raise ValueError("FFLogs event cache entry is too large")
        temp_path: Optional[str] = None
        try:
            with tempfile.NamedTemporaryFile(
                "wb",
                dir=str(path.parent),
                prefix=f"{path.name}.",
                suffix=".tmp",
                delete=False,
            ) as stream:
                temp_path = stream.name
                with gzip.GzipFile(
                    fileobj=stream,
                    mode="wb",
                    compresslevel=6,
                    mtime=0,
                ) as compressed:
                    compressed.write(encoded)
                stream.flush()
                os.fsync(stream.fileno())
            if os.path.getsize(temp_path) > MAX_COMPRESSED_ENTRY_BYTES:
                raise ValueError("compressed FFLogs event cache entry is too large")
            os.replace(temp_path, path)
        finally:
            if temp_path and os.path.exists(temp_path):
                try:
                    os.remove(temp_path)
                except OSError:
                    pass

    @staticmethod
    def _valid_payload(data: dict, context: Dict[str, Any]) -> bool:
        if data.get("version") != EVENT_CACHE_VERSION:
            return False
        if data.get("context") != context:
            return False
        for key in ("casts", "timeline", "damage"):
            values = data.get(key)
            if not isinstance(values, list) or not all(
                isinstance(value, dict) for value in values
            ):
                return False
        tables = data.get("tables")
        return tables is None or isinstance(tables, dict)

    @staticmethod
    def table_key(start_time: Optional[int], end_time: Optional[int]) -> str:
        def normalize(value: Optional[int]) -> str:
            try:
                return str(int(value)) if value is not None else "none"
            except (TypeError, ValueError, OverflowError):
                return "none"

        return f"{normalize(start_time)}:{normalize(end_time)}"

    def load(
        self,
        report_code: str,
        fight_id: int,
        actor_id: int,
        *,
        include_pets: bool = True,
    ) -> Optional[dict]:
        context = self._context(report_code, fight_id, actor_id, include_pets)
        if context is None:
            return None
        entry_id = self._entry_id(context)
        with self._lock:
            path = self._entry_path(entry_id)
            data = self._read_entry(path)
            if data is None or not self._valid_payload(data, context):
                return None
            entries = self._load_index()
            now = time.time()
            meta = entries.get(entry_id, {})
            previous_access = self._timestamp(meta, "last_accessed", "saved_at")
            meta.update(
                {
                    "last_accessed": now,
                    "saved_at": self._timestamp(data, "saved_at") or now,
                    "size": path.stat().st_size,
                }
            )
            entries[entry_id] = meta
            if now - previous_access >= 60.0:
                self._save_index(entries)
            return data

    def save(
        self,
        report_code: str,
        fight_id: int,
        actor_id: int,
        *,
        casts: List[dict],
        timeline: List[dict],
        damage: List[dict],
        include_pets: bool = True,
        start_time: Optional[int] = None,
        end_time: Optional[int] = None,
        damage_table: Optional[dict] = None,
        damage_table_adps: Optional[dict] = None,
        replace_tables: bool = False,
    ) -> None:
        context = self._context(report_code, fight_id, actor_id, include_pets)
        if context is None:
            raise ValueError("invalid FFLogs event cache context")
        for values in (casts, timeline, damage):
            if not isinstance(values, list) or not all(
                isinstance(value, dict) for value in values
            ):
                raise TypeError("FFLogs event cache sections must contain objects")
        entry_id = self._entry_id(context)
        with self._lock:
            path = self._entry_path(entry_id)
            previous = self._read_entry(path)
            tables: Dict[str, dict] = {}
            if not replace_tables and previous and self._valid_payload(previous, context):
                previous_tables = previous.get("tables")
                if isinstance(previous_tables, dict):
                    tables.update(
                        (str(key), dict(value))
                        for key, value in previous_tables.items()
                        if isinstance(value, dict)
                    )
            if damage_table is not None or damage_table_adps is not None:
                tables[self.table_key(start_time, end_time)] = {
                    "summary": damage_table,
                    "adps": damage_table_adps,
                }
            now = time.time()
            payload = {
                "version": EVENT_CACHE_VERSION,
                "context": context,
                "saved_at": now,
                "casts": casts,
                "timeline": timeline,
                "damage": damage,
                "tables": tables,
            }
            self._write_entry(path, payload)
            entries = self._load_index()
            entries[entry_id] = {
                "saved_at": now,
                "last_accessed": now,
                "size": path.stat().st_size,
            }
            self._trim(entries, keep_entry_id=entry_id)
            self._save_index(entries)

    def _trim(self, entries: Dict[str, dict], *, keep_entry_id: str) -> None:
        while len(entries) > self.entry_limit:
            removable = [
                (entry_id, meta)
                for entry_id, meta in entries.items()
                if entry_id != keep_entry_id
            ]
            if not removable:
                break
            oldest_id, _meta = min(
                removable,
                key=lambda entry: self._timestamp(
                    entry[1], "last_accessed", "saved_at"
                ),
            )
            path = self._entry_path(oldest_id)
            try:
                path.unlink(missing_ok=True)
            except OSError as exc:
                logger.warning("Failed to remove old FFLogs event cache %s: %s", path, exc)
                break
            entries.pop(oldest_id, None)
