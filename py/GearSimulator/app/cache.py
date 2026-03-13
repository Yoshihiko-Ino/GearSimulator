import json
import time
from pathlib import Path
from typing import Any, Optional

from .paths import bundled_cache_dir, writable_cache_dir


class FileCache:
    def __init__(
        self,
        base_dir: Optional[Path] = None,
        fallback_dir: Optional[Path] = None,
    ) -> None:
        self.base_dir = base_dir or writable_cache_dir()
        self.fallback_dir = fallback_dir or bundled_cache_dir()
        self.base_dir.mkdir(parents=True, exist_ok=True)

    def _path(self, name: str) -> Path:
        return self.base_dir / name

    def _fallback_path(self, name: str) -> Optional[Path]:
        if self.fallback_dir == self.base_dir:
            return None
        return self.fallback_dir / name

    def load(self, name: str) -> Optional[Any]:
        path = self._path(name)
        fallback_path = self._fallback_path(name)
        for candidate in (path, fallback_path):
            if candidate is None or not candidate.exists():
                continue
            try:
                with candidate.open("r", encoding="utf-8") as f:
                    return json.load(f)
            except Exception:
                continue
        return None

    def save(self, name: str, data: Any) -> None:
        path = self._path(name)
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)

    def is_fresh(self, name: str, max_age_seconds: int) -> bool:
        path = self._path(name)
        if not path.exists():
            return False
        age = time.time() - path.stat().st_mtime
        return age <= max_age_seconds
