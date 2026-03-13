from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Optional

SUPPORTED_LEVELS = (70, 80, 90, 100)
CURRENT_MAX_LEVEL = 100


@dataclass(frozen=True)
class LevelStats:
    level: int
    base_main: int
    base_sub: int
    level_div: int
    hp: int
    hp_scalar: Dict[str, float]
    main_stat_power_mod: Dict[str, int]


@dataclass(frozen=True)
class JobMeta:
    role: str
    main_stat: str
    auto_stat: str


@dataclass
class ComputedStats:
    strength: int
    dexterity: int
    vitality: int
    intelligence: int
    mind: int
    crit: int
    dhit: int
    det: int
    tenacity: int
    piety: int
    crit_chance: float
    crit_multi: float
    dhit_chance: float
    dhit_multi: float
    det_multi: float
    sps_dot_multi: float
    sks_dot_multi: float
    tnc_multi: float
    wd_multi: float
    aa_multi: float
    main_stat_multi: float
    aa_stat_multi: float
    auto_dh_bonus: float
    skillspeed: int
    spellspeed: int
    role: str
    job_meta: JobMeta

    def trait_multi(self, attack_type: str) -> float:
        if attack_type == "Auto-attack":
            return 1.0
        if self.role in {"Healer", "Caster"}:
            return 1.3
        if self.role == "Ranged":
            return 1.2
        return 1.0


LEVEL_STATS: Dict[int, LevelStats] = {
    70: LevelStats(
        level=70,
        base_main=292,
        base_sub=364,
        level_div=900,
        hp=1700,
        hp_scalar={"Tank": 18.8, "other": 14.0},
        main_stat_power_mod={"Tank": 105, "other": 125},
    ),
    80: LevelStats(
        level=80,
        base_main=340,
        base_sub=380,
        level_div=1300,
        hp=2000,
        hp_scalar={"Tank": 26.6, "other": 18.8},
        main_stat_power_mod={"Tank": 115, "other": 165},
    ),
    90: LevelStats(
        level=90,
        base_main=390,
        base_sub=400,
        level_div=1900,
        hp=3000,
        hp_scalar={"Tank": 34.6, "other": 24.3},
        main_stat_power_mod={"Tank": 156, "other": 195},
    ),
    100: LevelStats(
        level=100,
        base_main=440,
        base_sub=420,
        level_div=2780,
        hp=4000,
        hp_scalar={"Tank": 43.0, "other": 30.1},
        main_stat_power_mod={"Tank": 190, "other": 237},
    )
}

JOB_META: Dict[str, JobMeta] = {
    "WHM": JobMeta(role="Healer", main_stat="mind", auto_stat="strength"),
    "SGE": JobMeta(role="Healer", main_stat="mind", auto_stat="strength"),
    "SCH": JobMeta(role="Healer", main_stat="mind", auto_stat="strength"),
    "AST": JobMeta(role="Healer", main_stat="mind", auto_stat="strength"),
    "PLD": JobMeta(role="Tank", main_stat="strength", auto_stat="strength"),
    "WAR": JobMeta(role="Tank", main_stat="strength", auto_stat="strength"),
    "DRK": JobMeta(role="Tank", main_stat="strength", auto_stat="strength"),
    "GNB": JobMeta(role="Tank", main_stat="strength", auto_stat="strength"),
    "DRG": JobMeta(role="Melee", main_stat="strength", auto_stat="strength"),
    "MNK": JobMeta(role="Melee", main_stat="strength", auto_stat="strength"),
    "NIN": JobMeta(role="Melee", main_stat="dexterity", auto_stat="dexterity"),
    "SAM": JobMeta(role="Melee", main_stat="strength", auto_stat="strength"),
    "RPR": JobMeta(role="Melee", main_stat="strength", auto_stat="strength"),
    "VPR": JobMeta(role="Melee", main_stat="dexterity", auto_stat="dexterity"),
    "BRD": JobMeta(role="Ranged", main_stat="dexterity", auto_stat="dexterity"),
    "MCH": JobMeta(role="Ranged", main_stat="dexterity", auto_stat="dexterity"),
    "DNC": JobMeta(role="Ranged", main_stat="dexterity", auto_stat="dexterity"),
    "BLM": JobMeta(role="Caster", main_stat="intelligence", auto_stat="strength"),
    "SMN": JobMeta(role="Caster", main_stat="intelligence", auto_stat="strength"),
    "RDM": JobMeta(role="Caster", main_stat="intelligence", auto_stat="strength"),
    "PCT": JobMeta(role="Caster", main_stat="intelligence", auto_stat="strength"),
}

# Race/Clan stat bonuses (XIVGear compatible).
RACE_STATS: Dict[str, Dict[int, int]] = {
    # Elezen
    "Duskwight": {3: -1, 4: 3, 5: 1},
    "Wildwood": {2: 3, 3: -1, 4: 2, 5: -1},
    # Miqo'te
    "Seekers of the Sun": {1: 2, 2: 3, 4: -1, 5: -1},
    "Keepers of the Moon": {1: -1, 2: 2, 3: -2, 4: 1, 5: 3},
    # Roegadyn
    "Sea Wolf": {1: 2, 2: -1, 3: 3, 4: -2, 5: 1},
    "Hellsguard": {1: 0, 2: -2, 3: 3, 4: 0, 5: 2},
    # Hrothgar
    "The Lost": {1: 3, 2: -3, 3: 3, 4: -3, 5: 3},
    "Helion": {1: 3, 2: -3, 3: 3, 4: -3, 5: 3},
    # Hyur
    "Highlander": {1: 3, 2: 0, 3: 2, 4: -2, 5: 0},
    "Midlander": {1: 2, 2: -1, 3: 0, 4: 3, 5: -1},
    # Lalafell
    "Plainsfolk": {1: -1, 2: 3, 3: -1, 4: 2, 5: 0},
    "Dunesfolk": {1: -1, 2: 1, 3: -2, 4: 2, 5: 3},
    # Viera
    "Rava": {1: 0, 2: 3, 3: -2, 4: 1, 5: 1},
    "Veena": {1: -1, 2: 0, 3: -1, 4: 3, 5: 2},
    # Au Ra
    "Xaela": {1: 3, 2: 0, 3: 2, 4: 0, 5: -2},
    "Raen": {1: -1, 2: 2, 3: -1, 4: 0, 5: 3},
}

# Use a fixed "Average" race when race/clan selection is disabled.
DEFAULT_RACE = "Average"

def _compute_average_race_stats() -> Dict[int, int]:
    keys = [1, 2, 3, 4, 5]
    sums = {k: 0 for k in keys}
    count = max(1, len(RACE_STATS))
    for stats in RACE_STATS.values():
        for k in keys:
            sums[k] += stats.get(k, 0)
    return {k: int(round(sums[k] / count)) for k in keys}

RACE_STATS[DEFAULT_RACE] = _compute_average_race_stats()


def normalize_supported_level(level: Optional[int]) -> int:
    try:
        normalized = int(level or CURRENT_MAX_LEVEL)
    except Exception:
        return CURRENT_MAX_LEVEL
    if normalized in LEVEL_STATS:
        return normalized
    if normalized < min(SUPPORTED_LEVELS):
        return min(SUPPORTED_LEVELS)
    for supported in reversed(SUPPORTED_LEVELS):
        if normalized >= supported:
            return supported
    return CURRENT_MAX_LEVEL


def fl(value: float) -> int:
    floored = int(value // 1)
    loss = value - floored
    if loss >= 0.99999995:
        return floored + 1
    return floored


def trunc(value: float) -> int:
    if value > 0:
        return fl(value)
    if value < 0:
        return -fl(-value)
    return 0


def flp(places: int, value: float) -> float:
    multiplier = 10 ** places
    return fl(value * multiplier) / multiplier


def crit_chance(level: LevelStats, crit: int) -> float:
    return fl(200 * (crit - level.base_sub) / level.level_div + 50) / 1000.0


def crit_dmg(level: LevelStats, crit: int) -> float:
    return (1400 + fl(200 * (crit - level.base_sub) / level.level_div)) / 1000.0


def dhit_chance(level: LevelStats, dhit: int) -> float:
    return fl(550 * (dhit - level.base_sub) / level.level_div) / 1000.0


def dhit_dmg() -> float:
    return 1.25


def det_dmg(level: LevelStats, det: int) -> float:
    return (1000 + fl(140 * (det - level.base_main) / level.level_div)) / 1000.0


def tenacity_dmg(level: LevelStats, tenacity: int) -> float:
    return (1000 + fl(112 * (tenacity - level.base_sub) / level.level_div)) / 1000.0


def sps_tick_multi(level: LevelStats, sps: int) -> float:
    return (1000 + fl(130 * (sps - level.base_sub) / level.level_div)) / 1000.0


def sks_tick_multi(level: LevelStats, sks: int) -> float:
    return (1000 + fl(130 * (sks - level.base_sub) / level.level_div)) / 1000.0


def main_stat_power_mod(level: LevelStats, role: str) -> int:
    if role == "Tank":
        return level.main_stat_power_mod.get("Tank", level.main_stat_power_mod["other"])
    return level.main_stat_power_mod.get(role, level.main_stat_power_mod["other"])


def hp_scalar(level: LevelStats, role: str) -> float:
    if role == "Tank":
        return level.hp_scalar.get("Tank", level.hp_scalar.get("other", 0.0))
    return level.hp_scalar.get(role, level.hp_scalar.get("other", 0.0))


def vit_to_hp(level: LevelStats, role: str, job_hp_mod: int, vitality: int) -> int:
    hp_mod = hp_scalar(level, role)
    return fl(level.hp * job_hp_mod / 100) + fl((vitality - level.base_main) * hp_mod)


def main_stat_multi(level: LevelStats, role: str, main_stat: int) -> float:
    ap_mod = main_stat_power_mod(level, role)
    return max(0.0, (trunc(ap_mod * (main_stat - level.base_main) / level.base_main) + 100) / 100)


def wd_multi(level: LevelStats, job_mod: int, wd: int) -> float:
    return fl(level.base_main * job_mod / 1000 + wd) / 100


def auto_attack_modifier(level: LevelStats, job_mod: int, weapon_delay: float, wd: int) -> float:
    return fl(fl(level.base_main * job_mod / 1000 + wd) * (weapon_delay / 3)) / 100


def auto_dhit_bonus(level: LevelStats, dhit: int) -> float:
    return fl(140 * ((dhit - level.base_sub) / level.level_div)) / 1000.0


def sks_to_gcd(base_gcd: float, level: LevelStats, sks: int, haste: int = 0) -> float:
    return max(
        0.0,
        fl((fl((1000 - fl(130 * (sks - level.base_sub) / level.level_div)) * base_gcd) * (100 - haste)) / 1000)
        / 100,
    )


def sps_to_gcd(base_gcd: float, level: LevelStats, sps: int, haste: int = 0) -> float:
    return max(
        0.0,
        fl((fl((1000 - fl(130 * (sps - level.base_sub) / level.level_div)) * base_gcd) * (100 - haste)) / 1000)
        / 100,
    )


def build_computed_stats(
    job: str,
    raw_stats: Dict[int, int],
    job_mods: Optional[Dict[str, int]],
    food_bonuses: Optional[Dict[int, object]],
    party_bonus: int,
    wd_phys: int,
    wd_mag: int,
    weapon_delay: float,
    race: Optional[str] = None,
    level: int = 100,
) -> ComputedStats:
    level_stats = LEVEL_STATS[normalize_supported_level(level)]
    meta = JOB_META.get(job)
    if not meta:
        meta = JobMeta(role="Other", main_stat="strength", auto_stat="strength")

    mods = job_mods or {}
    mod_str = mods.get("strength", 100)
    mod_dex = mods.get("dexterity", 100)
    mod_int = mods.get("intelligence", 100)
    mod_mnd = mods.get("mind", 100)
    mod_vit = mods.get("vitality", 100)

    strength = fl(level_stats.base_main * mod_str / 100) + raw_stats.get(1, 0)
    dexterity = fl(level_stats.base_main * mod_dex / 100) + raw_stats.get(2, 0)
    vitality = fl(level_stats.base_main * mod_vit / 100) + raw_stats.get(3, 0)
    intelligence = fl(level_stats.base_main * mod_int / 100) + raw_stats.get(4, 0)
    mind = fl(level_stats.base_main * mod_mnd / 100) + raw_stats.get(5, 0)

    race_stats = RACE_STATS.get(race or "", {})
    strength += race_stats.get(1, 0)
    dexterity += race_stats.get(2, 0)
    vitality += race_stats.get(3, 0)
    intelligence += race_stats.get(4, 0)
    mind += race_stats.get(5, 0)

    crit = level_stats.base_sub + raw_stats.get(27, 0)
    dhit = level_stats.base_sub + raw_stats.get(22, 0)
    # Determination/Piety use base main stat (XIVGear compatible)
    det = level_stats.base_main + raw_stats.get(44, 0)
    piety = level_stats.base_main + raw_stats.get(6, 0)
    tenacity = level_stats.base_sub + raw_stats.get(19, 0)
    skillspeed = level_stats.base_sub + raw_stats.get(45, 0)
    spellspeed = level_stats.base_sub + raw_stats.get(46, 0)

    food_base = {
        27: crit,
        22: dhit,
        44: det,
        19: tenacity,
        45: skillspeed,
        46: spellspeed,
        6: piety,
    }

    party = 1 + (party_bonus / 100)
    if meta.main_stat == "strength":
        strength = fl(strength * party)
    elif meta.main_stat == "dexterity":
        dexterity = fl(dexterity * party)
    elif meta.main_stat == "intelligence":
        intelligence = fl(intelligence * party)
    elif meta.main_stat == "mind":
        mind = fl(mind * party)

    if meta.auto_stat != meta.main_stat:
        if meta.auto_stat == "strength":
            strength = fl(strength * party)
        elif meta.auto_stat == "dexterity":
            dexterity = fl(dexterity * party)
        elif meta.auto_stat == "intelligence":
            intelligence = fl(intelligence * party)
        elif meta.auto_stat == "mind":
            mind = fl(mind * party)

    vitality = fl(vitality * party)

    if food_bonuses:
        for stat_id, bonus in food_bonuses.items():
            pct = getattr(bonus, "percentage", 0)
            max_val = getattr(bonus, "maximum", 0)
            if pct <= 0 or max_val <= 0:
                continue
            base_val = food_base.get(stat_id)
            if base_val is None:
                continue
            add = min(int(base_val * pct / 100), max_val)
            if stat_id == 27:
                crit += add
            elif stat_id == 22:
                dhit += add
            elif stat_id == 44:
                det += add
            elif stat_id == 19:
                tenacity += add
            elif stat_id == 45:
                skillspeed += add
            elif stat_id == 46:
                spellspeed += add
            elif stat_id == 6:
                piety += add

    main_stat_value = {
        "strength": strength,
        "dexterity": dexterity,
        "intelligence": intelligence,
        "mind": mind,
    }.get(meta.main_stat, strength)
    aa_stat_value = {
        "strength": strength,
        "dexterity": dexterity,
        "intelligence": intelligence,
        "mind": mind,
    }.get(meta.auto_stat, strength)

    wd_effective = max(wd_phys, wd_mag)
    job_mod_main = mods.get(meta.main_stat, 100)
    job_mod_auto = mods.get(meta.auto_stat, 100)

    return ComputedStats(
        strength=strength,
        dexterity=dexterity,
        vitality=vitality,
        intelligence=intelligence,
        mind=mind,
        crit=crit,
        dhit=dhit,
        det=det,
        tenacity=tenacity,
        piety=piety,
        crit_chance=max(0.0, min(1.0, crit_chance(level_stats, crit))),
        crit_multi=crit_dmg(level_stats, crit),
        dhit_chance=max(0.0, min(1.0, dhit_chance(level_stats, dhit))),
        dhit_multi=dhit_dmg(),
        det_multi=det_dmg(level_stats, det),
        sps_dot_multi=sps_tick_multi(level_stats, spellspeed),
        sks_dot_multi=sks_tick_multi(level_stats, skillspeed),
        tnc_multi=tenacity_dmg(level_stats, tenacity),
        wd_multi=wd_multi(level_stats, job_mod_main, wd_effective),
        aa_multi=auto_attack_modifier(level_stats, job_mod_auto, weapon_delay, wd_phys),
        main_stat_multi=main_stat_multi(level_stats, meta.role, main_stat_value),
        aa_stat_multi=main_stat_multi(level_stats, meta.role, aa_stat_value),
        auto_dh_bonus=auto_dhit_bonus(level_stats, dhit),
        skillspeed=skillspeed,
        spellspeed=spellspeed,
        role=meta.role,
        job_meta=meta,
    )


def base_damage_full(
    stats: ComputedStats,
    potency: int,
    attack_type: str,
    auto_dh: bool = False,
    is_dot: bool = False,
) -> float:
    is_aa = attack_type == "Auto-attack"
    if is_aa:
        spd_multi = stats.sks_dot_multi
    elif is_dot:
        spd_multi = stats.sks_dot_multi if attack_type == "Weaponskill" else stats.sps_dot_multi
    else:
        spd_multi = 1.0

    main_stat_multi_val = stats.main_stat_multi
    wd_multi_val = stats.wd_multi
    if is_aa:
        main_stat_multi_val = stats.aa_stat_multi
        wd_multi_val = stats.aa_multi

    det_multi = stats.det_multi
    det_auto_dh = flp(3, det_multi + stats.auto_dh_bonus)
    effective_det = det_auto_dh if auto_dh else det_multi
    trait_multi_val = stats.trait_multi(attack_type)

    if stats.role in {"Caster", "Healer"} and attack_type != "Auto-attack":
        ap_det = flp(2, main_stat_multi_val * effective_det)
        base_potency = fl(ap_det * fl(wd_multi_val * potency))
        after_tnc = fl(base_potency * stats.tnc_multi)
        after_spd = fl(after_tnc * spd_multi)
        stage1 = after_spd
    else:
        base_potency = fl(potency * main_stat_multi_val)
        after_det = fl(base_potency * effective_det)
        after_tnc = fl(after_det * stats.tnc_multi)
        after_wd = fl(after_tnc * wd_multi_val)
        after_spd = fl(after_wd * spd_multi)
        stage1 = after_spd

    final_damage = fl(stage1 * trait_multi_val) + (1 if potency < 100 else 0)
    return max(1.0, float(final_damage))


def expected_damage_per_potency(
    stats: ComputedStats,
    attack_type: str,
    is_dot: bool,
    auto_dh: bool = False,
    auto_crit: bool = False,
    crit_chance_bonus: float = 0.0,
    dhit_chance_bonus: float = 0.0,
    damage_multiplier: float = 1.0,
) -> float:
    base = base_damage_full(stats, potency=100, attack_type=attack_type, auto_dh=auto_dh, is_dot=is_dot)
    crit_chance = max(0.0, min(1.0, stats.crit_chance + crit_chance_bonus))
    dhit_chance = max(0.0, min(1.0, stats.dhit_chance + dhit_chance_bonus))

    if auto_crit:
        crit_factor = stats.crit_multi
    else:
        crit_factor = 1.0 + crit_chance * (stats.crit_multi - 1.0)

    if auto_dh:
        dh_factor = stats.dhit_multi
    else:
        dh_factor = 1.0 + dhit_chance * (stats.dhit_multi - 1.0)

    return base * crit_factor * dh_factor * max(0.0, damage_multiplier)
