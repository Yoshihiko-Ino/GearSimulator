import os
from typing import Optional


def display_name_with_fallback(name_ja: Optional[str], name: str) -> str:
    return name_ja or name


def sim_debug_enabled() -> bool:
    val = os.environ.get("GEARSIM_DEBUG", "").strip().lower()
    return val in {"1", "true", "yes", "on"}


def sim_log(message: str) -> None:
    if sim_debug_enabled():
        print(message, flush=True)
