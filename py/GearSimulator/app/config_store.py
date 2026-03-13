import json
from typing import Dict, Any

from .paths import ensure_runtime_dirs, writable_config_dir

CONFIG_DIR = writable_config_dir()
AUTH_PATH = CONFIG_DIR / "auth.json"
SAVED_SETS_PATH = CONFIG_DIR / "saved_sets.json"
DEFAULT_AUTH: Dict[str, Any] = {}
DEFAULT_SAVED_SETS: Dict[str, Any] = {"version": 1, "items": []}


def _write_json(path, data: Dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)


def ensure_config_files() -> None:
    ensure_runtime_dirs()
    if not AUTH_PATH.exists():
        _write_json(AUTH_PATH, DEFAULT_AUTH)
    if not SAVED_SETS_PATH.exists():
        _write_json(SAVED_SETS_PATH, DEFAULT_SAVED_SETS)


def load_auth() -> Dict[str, Any]:
    ensure_config_files()
    if not AUTH_PATH.exists():
        return {}
    try:
        with AUTH_PATH.open("r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return {}


def save_auth(data: Dict[str, Any]) -> None:
    ensure_runtime_dirs()
    _write_json(AUTH_PATH, data)


def load_saved_sets() -> Dict[str, Any]:
    ensure_config_files()
    if not SAVED_SETS_PATH.exists():
        return {"version": 1, "items": []}
    try:
        with SAVED_SETS_PATH.open("r", encoding="utf-8") as f:
            data = json.load(f)
            if isinstance(data, dict):
                data.setdefault("version", 1)
                data.setdefault("items", [])
                return data
            return {"version": 1, "items": data or []}
    except Exception:
        return {"version": 1, "items": []}


def save_saved_sets(data: Dict[str, Any]) -> None:
    ensure_runtime_dirs()
    _write_json(SAVED_SETS_PATH, data)
