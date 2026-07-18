import base64
import json
import os
import tempfile
import time
from pathlib import Path
from typing import Any, Dict, List, Optional

from .paths import ensure_runtime_dirs, writable_config_dir

CONFIG_DIR = writable_config_dir()
AUTH_PATH = CONFIG_DIR / "auth.json"
SAVED_SETS_PATH = CONFIG_DIR / "saved_sets.json"
DEFAULT_AUTH: Dict[str, Any] = {}
DEFAULT_SAVED_SETS: Dict[str, Any] = {"version": 1, "items": []}

_CONFIG_WARNINGS: List[str] = []
_MIGRATED_CONFIG_DIRS: set[Path] = set()
_AUTH_SECRET_KEY = "client_secret"
_AUTH_SECRET_ENCRYPTED_KEY = "client_secret_encrypted"
_MIGRATION_VERSION = 1


def _write_json(path: Path, data: Dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temp_path = None
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
        if temp_path:
            try:
                if os.path.exists(temp_path):
                    os.remove(temp_path)
            except Exception:
                pass


def _record_warning(message: str) -> None:
    text = str(message or "").strip()
    if text:
        _CONFIG_WARNINGS.append(text)


def consume_config_warnings() -> List[str]:
    warnings = list(_CONFIG_WARNINGS)
    _CONFIG_WARNINGS.clear()
    return warnings


def _read_json_without_side_effects(path: Path) -> Optional[Any]:
    try:
        with path.open("r", encoding="utf-8") as f:
            return json.load(f)
    except (OSError, UnicodeError, json.JSONDecodeError):
        return None


def _legacy_config_dirs() -> List[Path]:
    current_root = CONFIG_DIR.resolve().parent
    parent = current_root.parent
    candidates = [parent / "config"]
    try:
        siblings = sorted(
            parent.glob("GearSimulator_v*/config"),
            key=lambda path: path.stat().st_mtime,
            reverse=True,
        )
    except OSError:
        siblings = []
    candidates.extend(siblings)
    result: List[Path] = []
    seen = {CONFIG_DIR.resolve()}
    for candidate in candidates:
        try:
            resolved = candidate.resolve()
        except OSError:
            continue
        if resolved in seen or not resolved.is_dir():
            continue
        seen.add(resolved)
        result.append(resolved)
    return result


def _is_empty_config_value(value: Any) -> bool:
    return value is None or value == "" or value == [] or value == {}


def _migrate_legacy_config_if_needed() -> None:
    target_dir = CONFIG_DIR.resolve()
    if target_dir in _MIGRATED_CONFIG_DIRS:
        return
    marker_path = CONFIG_DIR / ".migration_v1.0.8.json"
    marker = _read_json_without_side_effects(marker_path) if marker_path.exists() else None
    if isinstance(marker, dict) and marker.get("version") == _MIGRATION_VERSION:
        _MIGRATED_CONFIG_DIRS.add(target_dir)
        return
    legacy_dirs = _legacy_config_dirs()
    if not legacy_dirs:
        _write_json(
            marker_path,
            {"version": _MIGRATION_VERSION, "completed_at": time.time()},
        )
        _MIGRATED_CONFIG_DIRS.add(target_dir)
        return

    target_auth = _read_json_without_side_effects(AUTH_PATH) if AUTH_PATH.exists() else {}
    if isinstance(target_auth, dict):
        merged_auth = dict(target_auth)
        auth_source: Optional[Path] = None
        for legacy_dir in legacy_dirs:
            legacy_auth = _read_json_without_side_effects(legacy_dir / "auth.json")
            if not isinstance(legacy_auth, dict):
                continue
            for key, value in legacy_auth.items():
                if key in {_AUTH_SECRET_KEY, _AUTH_SECRET_ENCRYPTED_KEY}:
                    target_client_id = str(merged_auth.get("client_id") or "")
                    legacy_client_id = str(legacy_auth.get("client_id") or "")
                    if target_client_id and target_client_id != legacy_client_id:
                        continue
                if _is_empty_config_value(merged_auth.get(key)) and not _is_empty_config_value(value):
                    merged_auth[key] = value
                    auth_source = auth_source or legacy_dir
        if merged_auth != target_auth:
            _write_json(AUTH_PATH, merged_auth)
            _record_warning(f"旧バージョンの認証・画面設定を {auth_source} から引き継ぎました。")

    target_sets = _read_json_without_side_effects(SAVED_SETS_PATH) if SAVED_SETS_PATH.exists() else None
    target_items = target_sets.get("items") if isinstance(target_sets, dict) else target_sets
    target_sets_empty = target_sets is None or (
        isinstance(target_sets, (dict, list)) and not target_items
    )
    if target_sets_empty:
        for legacy_dir in legacy_dirs:
            legacy_sets = _read_json_without_side_effects(legacy_dir / "saved_sets.json")
            if isinstance(legacy_sets, list):
                legacy_sets = {"version": 1, "items": legacy_sets}
            if not isinstance(legacy_sets, dict) or not isinstance(legacy_sets.get("items"), list):
                continue
            if not legacy_sets["items"]:
                continue
            _write_json(SAVED_SETS_PATH, legacy_sets)
            _record_warning(f"旧バージョンの保存セットを {legacy_dir} から引き継ぎました。")
            break
    _write_json(
        marker_path,
        {"version": _MIGRATION_VERSION, "completed_at": time.time()},
    )
    _MIGRATED_CONFIG_DIRS.add(target_dir)


def _backup_corrupt_file(path: Path, label: str, exc: Exception) -> None:
    timestamp = time.strftime("%Y%m%d-%H%M%S")
    backup_path = path.with_name(f"{path.stem}.corrupt-{timestamp}{path.suffix}")
    counter = 1
    while backup_path.exists():
        counter += 1
        backup_path = path.with_name(f"{path.stem}.corrupt-{timestamp}-{counter}{path.suffix}")
    try:
        path.replace(backup_path)
        _record_warning(
            f"{label} が破損していたため {backup_path.name} に退避しました。"
        )
    except Exception:
        _record_warning(
            f"{label} の読み込みに失敗しました。元ファイルの退避は未確認です。({type(exc).__name__})"
        )


def _load_json_file(path: Path, *, label: str) -> Optional[Any]:
    ensure_config_files()
    if not path.exists():
        return None
    try:
        with path.open("r", encoding="utf-8") as f:
            return json.load(f)
    except Exception as exc:
        _backup_corrupt_file(path, label, exc)
        return None


if os.name == "nt":
    import ctypes
    from ctypes import wintypes

    class _DataBlob(ctypes.Structure):
        _fields_ = [
            ("cbData", wintypes.DWORD),
            ("pbData", ctypes.POINTER(ctypes.c_byte)),
        ]


    def _blob_from_bytes(data: bytes) -> "_DataBlob":
        if not data:
            return _DataBlob(0, None)
        buffer = ctypes.create_string_buffer(data)
        return _DataBlob(len(data), ctypes.cast(buffer, ctypes.POINTER(ctypes.c_byte)))


    def _bytes_from_blob(blob: "_DataBlob") -> bytes:
        if not blob.cbData or not blob.pbData:
            return b""
        return ctypes.string_at(blob.pbData, blob.cbData)


    def _dpapi_protect(data: bytes) -> Optional[bytes]:
        crypt32 = ctypes.windll.crypt32
        kernel32 = ctypes.windll.kernel32
        in_blob = _blob_from_bytes(data)
        out_blob = _DataBlob()
        if not crypt32.CryptProtectData(
            ctypes.byref(in_blob),
            "GearSimulator FFLogs Secret",
            None,
            None,
            None,
            0,
            ctypes.byref(out_blob),
        ):
            return None
        try:
            return _bytes_from_blob(out_blob)
        finally:
            if out_blob.pbData:
                kernel32.LocalFree(out_blob.pbData)


    def _dpapi_unprotect(data: bytes) -> Optional[bytes]:
        crypt32 = ctypes.windll.crypt32
        kernel32 = ctypes.windll.kernel32
        in_blob = _blob_from_bytes(data)
        out_blob = _DataBlob()
        if not crypt32.CryptUnprotectData(
            ctypes.byref(in_blob),
            None,
            None,
            None,
            None,
            0,
            ctypes.byref(out_blob),
        ):
            return None
        try:
            return _bytes_from_blob(out_blob)
        finally:
            if out_blob.pbData:
                kernel32.LocalFree(out_blob.pbData)

else:

    def _dpapi_protect(data: bytes) -> Optional[bytes]:
        return None


    def _dpapi_unprotect(data: bytes) -> Optional[bytes]:
        return None


def _encode_client_secret(secret: str) -> Dict[str, str]:
    if not secret:
        return {}
    encrypted = _dpapi_protect(secret.encode("utf-8"))
    if encrypted:
        return {_AUTH_SECRET_ENCRYPTED_KEY: base64.b64encode(encrypted).decode("ascii")}
    raise RuntimeError("client_secret を安全に暗号化できないため保存を中止しました。")


def _decode_client_secret(data: Dict[str, Any]) -> str:
    encrypted = data.get(_AUTH_SECRET_ENCRYPTED_KEY)
    if isinstance(encrypted, str) and encrypted:
        try:
            raw = base64.b64decode(encrypted.encode("ascii"))
        except Exception:
            _record_warning("auth.json の暗号化された client_secret を復号できませんでした。")
            return ""
        decrypted = _dpapi_unprotect(raw)
        if decrypted is None:
            _record_warning("auth.json の暗号化された client_secret を復号できませんでした。")
            return ""
        try:
            return decrypted.decode("utf-8")
        except Exception:
            _record_warning("auth.json の暗号化された client_secret の文字コードが不正です。")
            return ""
    legacy = data.get(_AUTH_SECRET_KEY)
    return str(legacy or "")


def ensure_config_files() -> None:
    ensure_runtime_dirs()
    _migrate_legacy_config_if_needed()
    if not AUTH_PATH.exists():
        _write_json(AUTH_PATH, DEFAULT_AUTH)
    if not SAVED_SETS_PATH.exists():
        _write_json(SAVED_SETS_PATH, DEFAULT_SAVED_SETS)


def load_auth() -> Dict[str, Any]:
    loaded = _load_json_file(AUTH_PATH, label="auth.json")
    if loaded is None:
        return {}
    if not isinstance(loaded, dict):
        _backup_corrupt_file(AUTH_PATH, "auth.json", TypeError("auth must be object"))
        return {}
    data = dict(loaded)
    data[_AUTH_SECRET_KEY] = _decode_client_secret(data)
    data.pop(_AUTH_SECRET_ENCRYPTED_KEY, None)
    return data


def save_auth(data: Dict[str, Any]) -> None:
    ensure_runtime_dirs()
    payload = dict(data or {})
    secret = str(payload.pop(_AUTH_SECRET_KEY, "") or "")
    payload.pop(_AUTH_SECRET_ENCRYPTED_KEY, None)
    payload.update(_encode_client_secret(secret))
    _write_json(AUTH_PATH, payload)


def load_saved_sets() -> Dict[str, Any]:
    loaded = _load_json_file(SAVED_SETS_PATH, label="saved_sets.json")
    if loaded is None:
        return {"version": 1, "items": []}
    if isinstance(loaded, list):
        return {"version": 1, "items": loaded}
    if not isinstance(loaded, dict):
        _backup_corrupt_file(SAVED_SETS_PATH, "saved_sets.json", TypeError("saved sets must be object"))
        return {"version": 1, "items": []}
    version = loaded.get("version")
    try:
        version_value = int(version) if version is not None else 1
    except Exception:
        version_value = 1
    items = loaded.get("items")
    if items is None:
        items = []
    elif not isinstance(items, list):
        _backup_corrupt_file(SAVED_SETS_PATH, "saved_sets.json", TypeError("saved sets items must be list"))
        return {"version": version_value, "items": []}
    return {"version": version_value, "items": items}


def save_saved_sets(data: Dict[str, Any]) -> None:
    ensure_runtime_dirs()
    payload = dict(data or {})
    items = payload.get("items")
    if not isinstance(items, list):
        items = []
    payload["items"] = items
    try:
        payload["version"] = int(payload.get("version", 1) or 1)
    except Exception:
        payload["version"] = 1
    _write_json(SAVED_SETS_PATH, payload)
