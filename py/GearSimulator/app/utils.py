import os
from typing import Optional, Tuple


_PROGRESS_DETAIL_PREFIX = "[[detail:"
_PROGRESS_DETAIL_SUFFIX = "]]"


def display_name_with_fallback(name_ja: Optional[str], name: str) -> str:
    return name_ja or name


def sim_debug_enabled() -> bool:
    val = os.environ.get("GEARSIM_DEBUG", "").strip().lower()
    return val in {"1", "true", "yes", "on"}


def sim_log(message: str) -> None:
    if sim_debug_enabled():
        print(message, flush=True)


def encode_progress_message(
    message: str,
    *,
    detail_value: Optional[int] = None,
    detail_message: Optional[str] = None,
) -> str:
    if detail_value is None and not detail_message:
        return str(message or "")
    safe_message = str(message or "").replace(_PROGRESS_DETAIL_SUFFIX, "")
    safe_detail_message = str(detail_message or "").replace(_PROGRESS_DETAIL_SUFFIX, "")
    safe_detail_message = safe_detail_message.replace("|", "/")
    detail_text = "" if detail_value is None else str(int(detail_value))
    return (
        f"{_PROGRESS_DETAIL_PREFIX}{detail_text}|{safe_detail_message}"
        f"{_PROGRESS_DETAIL_SUFFIX}{safe_message}"
    )


def decode_progress_message(message: str) -> Tuple[str, Optional[int], Optional[str]]:
    raw_message = str(message or "")
    if not raw_message.startswith(_PROGRESS_DETAIL_PREFIX):
        return raw_message, None, None
    marker_end = raw_message.find(_PROGRESS_DETAIL_SUFFIX)
    if marker_end < 0:
        return raw_message, None, None
    marker = raw_message[len(_PROGRESS_DETAIL_PREFIX):marker_end]
    payload = raw_message[marker_end + len(_PROGRESS_DETAIL_SUFFIX):]
    raw_value, sep, raw_detail = marker.partition("|")
    if not sep:
        raw_detail = ""
    try:
        detail_value = int(raw_value) if raw_value != "" else None
    except Exception:
        detail_value = None
    detail_message = raw_detail or None
    return payload, detail_value, detail_message
