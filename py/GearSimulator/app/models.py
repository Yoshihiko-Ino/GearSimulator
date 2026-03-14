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

    def best_grades(self, limit: int = 4) -> List[MateriaGrade]:
        # Return top values descending.
        return sorted(self.grades, key=lambda g: g.value, reverse=True)[:limit]


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
    lock_item: bool = False
    lock_materia: bool = False


@dataclass
class Gearset:
    job: Optional[str] = None
    items: Dict[str, ItemSelection] = field(default_factory=dict)
    food_id: Optional[int] = None
    target_gcd: Optional[float] = None
    note: str = ""
    race: Optional[str] = None
    level: int = 100

    def to_dict(self) -> dict:
        return {
            "job": self.job,
            "level": self.level,
            "foodId": self.food_id,
            "target_gcd": self.target_gcd,
            "note": self.note,
            "race": self.race,
            "items": {
                slot: {
                    "item_id": sel.item_id,
                    "lock_item": bool(getattr(sel, "lock_item", False)),
                    "lock_materia": bool(getattr(sel, "lock_materia", False)),
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
        items_data = data.get("items", {})
        items: Dict[str, ItemSelection] = {}
        for slot, sel in items_data.items():
            materia = []
            for m in sel.get("materia", []):
                base_param = m.get("base_param", 0) or 0
                grade = m.get("grade", 0) or 0
                materia.append(MateriaSlotSelection(base_param=base_param, grade=grade))
            items[slot] = ItemSelection(
                item_id=sel.get("item_id"),
                materia=materia,
                lock_item=bool(sel.get("lock_item", False)),
                lock_materia=bool(sel.get("lock_materia", False)),
            )
        return cls(
            job=data.get("job"),
            items=items,
            level=int(data.get("level", 100) or 100),
            food_id=data.get("foodId"),
            target_gcd=data.get("target_gcd"),
            note=data.get("note", ""),
            race=data.get("race"),
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
