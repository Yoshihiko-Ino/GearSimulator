from __future__ import annotations

import sys
from pathlib import Path


def project_root() -> Path:
    return Path(__file__).resolve().parent.parent


def bundle_root() -> Path:
    if getattr(sys, "frozen", False):
        meipass = getattr(sys, "_MEIPASS", None)
        if meipass:
            return Path(meipass)
    return project_root()


def runtime_root() -> Path:
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return project_root()


def bundled_cache_dir() -> Path:
    return bundle_root() / "cache"


def writable_cache_dir() -> Path:
    return runtime_root() / "cache"


def writable_config_dir() -> Path:
    return runtime_root() / "config"


def ensure_runtime_dirs() -> None:
    writable_cache_dir().mkdir(parents=True, exist_ok=True)
    writable_config_dir().mkdir(parents=True, exist_ok=True)
