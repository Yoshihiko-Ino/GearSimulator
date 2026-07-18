from __future__ import annotations

from typing import Dict, Optional

from . import optimizer, xivmath
from .models import FoodRecord, ItemRecord, SPELL_SPEED_JOBS


def compute_saved_stats_snapshot(
    *,
    job: str,
    level: int,
    raw_stats: Dict[int, int],
    selected_items: Dict[str, ItemRecord],
    food: Optional[FoodRecord],
    job_mods: Dict[str, int],
    party_bonus: int,
    race: Optional[str] = None,
) -> Optional[Dict[str, int]]:
    meta = xivmath.JOB_META.get(job)
    if not meta:
        return None
    level_value = xivmath.normalize_supported_level(level)
    weapon = selected_items.get("weapon")
    wd_phys = weapon.damage_phys if weapon else 0
    wd_mag = weapon.damage_mag if weapon else 0
    delay = (weapon.delay_ms or 3000) / 1000.0 if weapon else 3.0
    comp = xivmath.build_computed_stats(
        job,
        raw_stats,
        job_mods,
        food.bonuses if food else None,
        party_bonus,
        wd_phys,
        wd_mag,
        delay,
        race=race or xivmath.DEFAULT_RACE,
        level=level_value,
    )
    level_data = xivmath.LEVEL_STATS[level_value]
    hp = xivmath.vit_to_hp(
        level_data,
        meta.role,
        job_mods.get("hp", 100),
        comp.vitality,
    )
    speed_value = comp.spellspeed if job in SPELL_SPEED_JOBS else comp.skillspeed
    main_stat_id = optimizer.MAIN_STAT_BY_JOB.get(job, 4)
    main_stat_value = {
        1: comp.strength,
        2: comp.dexterity,
        5: comp.mind,
    }.get(main_stat_id, comp.intelligence)
    return {
        "wd": int(max(wd_phys or 0, wd_mag or 0)),
        "hp": int(hp),
        "level": int(level_value),
        "main_stat_id": int(main_stat_id),
        "main_stat": int(main_stat_value),
        "int": int(comp.intelligence),
        "crit": int(comp.crit),
        "dhit": int(comp.dhit),
        "det": int(comp.det),
        "sps": int(speed_value),
    }
