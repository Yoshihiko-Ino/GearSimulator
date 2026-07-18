from dataclasses import dataclass, field
from typing import Dict, List, Optional

# Jobs that scale GCD with Spell Speed instead of Skill Speed.
SPELL_SPEED_JOBS = {"BLM", "RDM", "SMN", "WHM", "SCH", "AST", "SGE", "PCT"}

# Slots we support in the gearset editor.
GEAR_SLOTS = [
    "weapon",
    "offhand",
    "head",
    "body",
    "hands",
    "legs",
    "feet",
    "earrings",
    "necklace",
    "bracelet",
    "ring1",
    "ring2",
]

RELIC_STAT_NAME_TO_ID = {
    "crit": 27,
    "criticalhit": 27,
    "dhit": 22,
    "directhit": 22,
    "directhitrate": 22,
    "determination": 44,
    "det": 44,
    "skillspeed": 45,
    "sks": 45,
    "spellspeed": 46,
    "sps": 46,
    "tenacity": 19,
    "ten": 19,
    "piety": 6,
    "pie": 6,
}


def _coerce_int(value: object, *, minimum: Optional[int] = None) -> Optional[int]:
    try:
        coerced = int(value)
    except Exception:
        return None
    if minimum is not None and coerced < minimum:
        return None
    return coerced


def _coerce_float(value: object) -> Optional[float]:
    try:
        return float(value)
    except Exception:
        return None


@dataclass
class ItemRecord:
    item_id: int
    name: str
    name_ja: Optional[str]
    jobs: List[str]
    ilvl: int
    slot: str
    materia_slots: int
    overmeld: bool
    base_params: Dict[int, int]
    base_params_hq: Dict[int, int]
    damage_phys: Optional[int] = None
    damage_mag: Optional[int] = None
    delay_ms: Optional[int] = None
    occ_slot: Optional[str] = None
    unique: bool = False
    icon_url: Optional[str] = None


@dataclass
class FoodBonus:
    base_param: int
    percentage: int
    maximum: int


@dataclass
class FoodRecord:
    food_id: int
    name: str
    name_ja: Optional[str]
    bonuses: Dict[int, FoodBonus]
    level_item: Optional[int] = None
    hq: bool = True
    source_row_id: Optional[int] = None


@dataclass
class MateriaGrade:
    name: str
    name_ja: Optional[str]
    grade: int
    value: int
    item_id: int
    item_ilvl: Optional[int] = None
    icon_url: Optional[str] = None


@dataclass
class MateriaCategory:
    base_param: int
    grades: List[MateriaGrade] = field(default_factory=list)


@dataclass
class BaseParamRecord:
    name: str
    meld_param: List[int]
    slots: Dict[str, int]


@dataclass
class JobRecord:
    abbreviation: str
    modifier_strength: int
    modifier_dexterity: int
    modifier_intelligence: int
    modifier_mind: int
    modifier_vitality: int
    modifier_hp: int


@dataclass
class MateriaSlotSelection:
    base_param: int
    grade: int


@dataclass
class ItemSelection:
    item_id: Optional[int] = None
    materia: List[MateriaSlotSelection] = field(default_factory=list)
    relic_stats: Dict[int, int] = field(default_factory=dict)
    lock_item: bool = False
    lock_materia: bool = False
    excluded_item_ids: List[int] = field(default_factory=list)


@dataclass
class Gearset:
    job: Optional[str] = None
    items: Dict[str, ItemSelection] = field(default_factory=dict)
    food_id: Optional[int] = None
    target_gcd: Optional[float] = None
    note: str = ""
    race: Optional[str] = None
    level: int = 100
    food_simulation: bool = False

    def to_dict(self) -> dict:
        return {
            "job": self.job,
            "level": self.level,
            "foodId": self.food_id,
            "foodSimulation": bool(self.food_simulation),
            "target_gcd": self.target_gcd,
            "note": self.note,
            "race": self.race,
            "items": {
                slot: {
                    "item_id": sel.item_id,
                    "lock_item": bool(getattr(sel, "lock_item", False)),
                    "lock_materia": bool(getattr(sel, "lock_materia", False)),
                    "excluded_item_ids": list(
                        dict.fromkeys(
                            int(v)
                            for v in list(getattr(sel, "excluded_item_ids", []) or [])
                            if int(v or 0) > 0
                        )
                    ),
                    "relic_stats": {
                        str(int(stat_id)): int(value)
                        for stat_id, value in sorted((getattr(sel, "relic_stats", {}) or {}).items(), key=lambda entry: int(entry[0]))
                        if int(value or 0) > 0
                    },
                    "materia": [
                        {"base_param": (m.base_param if m else 0), "grade": (m.grade if m else 0)}
                        for m in (sel.materia or [])
                    ],
                }
                for slot, sel in self.items.items()
            },
        }

    @classmethod
    def from_dict(cls, data: dict) -> "Gearset":
        if not isinstance(data, dict):
            data = {}
        items_data = data.get("items", {})
        if not isinstance(items_data, dict):
            items_data = {}
        items: Dict[str, ItemSelection] = {}
        for slot, sel in items_data.items():
            if not isinstance(sel, dict):
                continue
            slot_name = str(slot or "").strip()
            if not slot_name:
                continue
            materia = []
            raw_materia = sel.get("materia", [])
            if not isinstance(raw_materia, list):
                raw_materia = []
            for m in raw_materia:
                if not isinstance(m, dict):
                    continue
                base_param = _coerce_int(m.get("base_param"), minimum=1) or 0
                grade = _coerce_int(m.get("grade"), minimum=1) or 0
                if base_param <= 0 or grade <= 0:
                    continue
                materia.append(MateriaSlotSelection(base_param=base_param, grade=grade))
            relic_stats: Dict[int, int] = {}
            raw_relic_stats = sel.get("relic_stats")
            if not isinstance(raw_relic_stats, dict):
                raw_relic_stats = sel.get("relicStats")
            if isinstance(raw_relic_stats, dict):
                for raw_stat_id, raw_value in raw_relic_stats.items():
                    try:
                        stat_id = int(raw_stat_id)
                    except Exception:
                        stat_id = RELIC_STAT_NAME_TO_ID.get(str(raw_stat_id or "").strip().lower(), 0)
                    try:
                        stat_value = int(raw_value or 0)
                    except Exception:
                        continue
                    if stat_id <= 0 or stat_value <= 0:
                        continue
                    relic_stats[stat_id] = stat_value
            item_id = _coerce_int(sel.get("item_id"), minimum=1)
            items[slot_name] = ItemSelection(
                item_id=item_id,
                materia=materia,
                relic_stats=relic_stats,
                lock_item=bool(sel.get("lock_item", False)),
                lock_materia=bool(sel.get("lock_materia", False)),
                excluded_item_ids=list(
                    dict.fromkeys(
                        int(v)
                        for v in list(sel.get("excluded_item_ids", []) or [])
                        if _coerce_int(v, minimum=1) is not None
                    )
                ),
            )
        level_value = _coerce_int(data.get("level"), minimum=1)
        food_id = _coerce_int(data.get("foodId"), minimum=1)
        target_gcd = _coerce_float(data.get("target_gcd"))
        job = data.get("job")
        if job is not None:
            job = str(job).strip() or None
        race = data.get("race")
        if race is not None:
            race = str(race).strip() or None
        return cls(
            job=job,
            items=items,
            level=level_value or 100,
            food_id=food_id,
            food_simulation=bool(data.get("foodSimulation", False)),
            target_gcd=target_gcd,
            note=str(data.get("note") or ""),
            race=race,
        )


@dataclass
class ActionRecord:
    action_id: int
    name: str
    name_ja: Optional[str]
    potency: Optional[int]
    dot_potency: Optional[int]
    attack_type: Optional[str]


@dataclass
class StatusEffectRecord:
    status_id: int
    name: str
    name_ja: Optional[str]
    damage_up: float
    crit_rate_up: float
    dhit_rate_up: float
    force_crit: bool
    force_dhit: bool
    dot_effect: bool
