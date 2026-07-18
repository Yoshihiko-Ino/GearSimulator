from __future__ import annotations

from datetime import datetime, timezone
from typing import Any


def utc_now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def timestamp_sort_value(value: Any) -> float:
    if not value:
        return 0.0
    try:
        parsed = datetime.fromisoformat(str(value))
    except (TypeError, ValueError):
        return 0.0
    if parsed.tzinfo is None:
        # v1.0.7 and earlier stored local wall-clock timestamps without an offset.
        parsed = parsed.astimezone()
    return parsed.timestamp()
