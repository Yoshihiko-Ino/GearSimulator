import json
import logging
import os
import tempfile
from pathlib import Path
from typing import Any, Optional

from .paths import bundled_cache_dir, writable_cache_dir


logger = logging.getLogger(__name__)


class FileCache:
    def __init__(
        self,
        base_dir: Optional[Path] = None,
        fallback_dir: Optional[Path] = None,
    ) -> None:
        self.base_dir = (base_dir or writable_cache_dir()).resolve()
        self.fallback_dir = (fallback_dir or bundled_cache_dir()).resolve()
        self.base_dir.mkdir(parents=True, exist_ok=True)

    @staticmethod
    def _safe_path(root: Path, name: str) -> Path:
        if not isinstance(name, str) or not name.strip():
            raise ValueError("cache name must be a non-empty string")
        relative = Path(name)
        if relative.is_absolute():
            raise ValueError("absolute cache paths are not allowed")
        candidate = (root / relative).resolve()
        try:
            candidate.relative_to(root)
        except ValueError as exc:
            raise ValueError("cache path escapes the cache directory") from exc
        return candidate

    def _path(self, name: str) -> Path:
        return self._safe_path(self.base_dir, name)

    def _fallback_path(self, name: str) -> Optional[Path]:
        if self.fallback_dir == self.base_dir:
            return None
        return self._safe_path(self.fallback_dir, name)

    def load(self, name: str) -> Optional[Any]:
        path = self._path(name)
        fallback_path = self._fallback_path(name)
        for candidate in (path, fallback_path):
            if candidate is None or not candidate.exists():
                continue
            try:
                with candidate.open("r", encoding="utf-8") as f:
                    return json.load(f)
            except (OSError, UnicodeError, json.JSONDecodeError) as exc:
                logger.warning("Failed to load cache %s: %s", candidate, exc)
        return None

    def save(self, name: str, data: Any) -> None:
        path = self._path(name)
        path.parent.mkdir(parents=True, exist_ok=True)
        temp_path: Optional[str] = None
        try:
            with tempfile.NamedTemporaryFile(
                "w",
                encoding="utf-8",
                dir=str(path.parent),
                prefix=f"{path.name}.",
                suffix=".tmp",
                delete=False,
            ) as f:
                temp_path = f.name
                json.dump(data, f, ensure_ascii=False, indent=2)
                f.flush()
                os.fsync(f.fileno())
            os.replace(temp_path, path)
        finally:
            if temp_path and os.path.exists(temp_path):
                try:
                    os.remove(temp_path)
                except OSError:
                    logger.warning("Failed to remove temporary cache file %s", temp_path)
