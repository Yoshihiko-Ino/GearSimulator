from __future__ import annotations

import httpx
import logging
from typing import Dict, List, Optional, Callable

from .cache import FileCache
from .models import (
    FoodBonus,
    FoodRecord,
    ItemRecord,
    BaseParamRecord,
    JobRecord,
    MateriaCategory,
    MateriaGrade,
)

BASE_URL = "https://data.xivgear.app"
COMBAT_FOOD_BONUS_STATS = {1, 2, 3, 4, 5, 6, 19, 22, 27, 44, 45, 46}
logger = logging.getLogger(__name__)


def _has_combat_food_bonus(bonuses: Dict[int, FoodBonus]) -> bool:
    for stat_id in bonuses.keys():
        try:
            if int(stat_id) in COMBAT_FOOD_BONUS_STATS:
                return True
        except Exception:
            continue
    return False


class XivGearClient:
    def __init__(self, cache: FileCache) -> None:
        self.cache = cache
        self._client = httpx.Client(base_url=BASE_URL, timeout=30)

    def close(self) -> None:
        self._client.close()

    def _load_dict_cache(self, cache_key: str) -> Optional[dict]:
        cached = self.cache.load(cache_key)
        if cached is not None and not isinstance(cached, dict):
            logger.warning("Ignoring invalid cache root for %s: %s", cache_key, type(cached).__name__)
            return None
        return cached

    def _load_list_cache(self, cache_key: str) -> Optional[list]:
        cached = self.cache.load(cache_key)
        if cached is not None and not isinstance(cached, list):
            logger.warning("Ignoring invalid cache root for %s: %s", cache_key, type(cached).__name__)
            return None
        return cached

    def fetch_base_params(
        self, force: bool = False
    ) -> Dict[int, BaseParamRecord]:
        cache_key = "base_params.json"
        if not force:
            cached = self._load_dict_cache(cache_key)
            if cached:
                try:
                    if all(isinstance(v, dict) and "meld_param" in v for v in cached.values()):
                        return {
                            int(k): BaseParamRecord(
                                name=v.get("name", ""),
                                meld_param=v.get("meld_param", []),
                                slots=v.get("slots", {}),
                            )
                            for k, v in cached.items()
                        }
                except (TypeError, ValueError):
                    logger.warning("Ignoring invalid cache entries for %s", cache_key)

        resp = self._client.get("/BaseParams")
        resp.raise_for_status()
        items = resp.json().get("items", [])
        mapping: Dict[int, BaseParamRecord] = {}
        for entry in items:
            row_id = entry.get("rowId")
            if row_id is None:
                continue
            slots = {
                "Weapon2H": entry.get("twoHandWeaponPercent", 0),
                "Weapon1H": entry.get("oneHandWeaponPercent", 0),
                "OffHand": entry.get("offHandPercent", 0),
                "Head": entry.get("headPercent", 0),
                "Body": entry.get("chestPercent", 0),
                "Hand": entry.get("handsPercent", 0),
                "Legs": entry.get("legsPercent", 0),
                "Feet": entry.get("feetPercent", 0),
                "Ears": entry.get("earringPercent", 0),
                "Neck": entry.get("necklacePercent", 0),
                "Wrist": entry.get("braceletPercent", 0),
                "Ring": entry.get("ringPercent", 0),
                "ChestHeadLegsFeet": entry.get("chestHeadLegsFeetPercent", 0),
                "ChestHead": entry.get("chestHeadPercent", 0),
                "ChestLegsFeet": entry.get("chestLegsFeetPercent", 0),
                "ChestLegsGloves": entry.get("chestLegsGlovesPercent", 0),
                "HeadChestHandsLegsFeet": entry.get("headChestHandsLegsFeetPercent", 0),
                "LegsFeet": entry.get("legsFeetPercent", 0),
            }
            mapping[int(row_id)] = BaseParamRecord(
                name=entry.get("name", ""),
                meld_param=entry.get("meldParam", []) or [],
                slots=slots,
            )
        cache_payload = {
            str(k): {"name": v.name, "meld_param": v.meld_param, "slots": v.slots}
            for k, v in mapping.items()
        }
        self.cache.save(cache_key, cache_payload)
        return mapping

    def fetch_item_levels(self, force: bool = False) -> Dict[int, dict]:
        cache_key = "item_levels.json"
        if not force:
            cached = self._load_dict_cache(cache_key)
            if cached:
                try:
                    if all(isinstance(v, dict) for v in cached.values()):
                        return {int(k): v for k, v in cached.items()}
                except (TypeError, ValueError):
                    logger.warning("Ignoring invalid cache entries for %s", cache_key)
        resp = self._client.get("/ItemLevel")
        resp.raise_for_status()
        items = resp.json().get("items", []) or []
        levels: Dict[int, dict] = {}
        for entry in items:
            row_id = entry.get("rowId")
            if row_id is None:
                continue
            levels[int(row_id)] = entry
        cache_payload = {str(k): v for k, v in levels.items()}
        self.cache.save(cache_key, cache_payload)
        return levels

    def fetch_materia(
        self, force: bool = False
    ) -> Dict[int, MateriaCategory]:
        cache_key = "materia.json"
        if not force:
            cached = self._load_dict_cache(cache_key)
            if cached:
                try:
                    valid_shape = all(
                        isinstance(grades, list) and all(isinstance(g, dict) for g in grades)
                        for grades in cached.values()
                    )
                    needs_refresh = not valid_shape or any(
                        any(("name_ja" not in g or "item_ilvl" not in g) for g in grades)
                        for grades in cached.values()
                    )
                    if not needs_refresh:
                        return self._deserialize_materia(cached)
                except (KeyError, TypeError, ValueError):
                    logger.warning("Ignoring invalid cache entries for %s", cache_key)

        resp = self._client.get("/Materia")
        resp.raise_for_status()
        raw = resp.json().get("items", [])
        materia: Dict[int, MateriaCategory] = {}
        for entry in raw:
            base_param = entry.get("baseParam")
            if not base_param:
                continue
            values: List[int] = entry.get("value", [])
            items = entry.get("item", [])
            grades: List[MateriaGrade] = []
            for idx, item in enumerate(items):
                name = item.get("name", "")
                translations = item.get("nameTranslations") or {}
                name_ja = translations.get("ja")
                if not name:
                    continue
                value = values[idx] if idx < len(values) else 0
                icon = item.get("icon") or {}
                grades.append(
                    MateriaGrade(
                        name=name,
                        name_ja=name_ja,
                        grade=idx + 1,
                        value=value,
                        item_id=item.get("rowId", 0),
                        item_ilvl=item.get("ilvl"),
                        icon_url=icon.get("pngIconUrl") or icon.get("url"),
                    )
                )
            if grades:
                materia[base_param] = MateriaCategory(
                    base_param=base_param, grades=grades
                )
        # cache raw form for quicker reload
        cache_payload = {
            str(k): [
                {
                    "name": g.name,
                    "name_ja": g.name_ja,
                    "grade": g.grade,
                    "value": g.value,
                    "item_id": g.item_id,
                    "item_ilvl": g.item_ilvl,
                    "icon_url": g.icon_url,
                }
                for g in v.grades
            ]
            for k, v in materia.items()
        }
        self.cache.save(cache_key, cache_payload)
        return materia

    def fetch_food(self, force: bool = False) -> List[FoodRecord]:
        cache_key = "food.json"
        if not force:
            cached = self._load_list_cache(cache_key)
            if cached:
                try:
                    # If cache lacks new fields, refetch
                    needs_refresh = any(
                        not isinstance(entry, dict)
                        or "name_ja" not in entry
                        or "level_item" not in entry
                        or "source_row_id" not in entry
                        for entry in cached
                    )
                    if not needs_refresh:
                        foods = self._deserialize_food(cached)
                        # Normalize old cache by dropping non-combat foods.
                        if len(foods) != len(cached):
                            self.cache.save(cache_key, self._serialize_food(foods))
                        return foods
                except (KeyError, TypeError, ValueError):
                    logger.warning("Ignoring invalid cache entries for %s", cache_key)

        resp = self._client.get("/Food")
        resp.raise_for_status()
        raw = resp.json().get("items", [])
        foods: List[FoodRecord] = []
        for entry in raw:
            name = entry.get("name", "不明")
            translations = entry.get("nameTranslations") or {}
            name_ja = translations.get("ja")
            food_id = entry.get("foodItemId") or entry.get("rowId")
            source_row_id = entry.get("rowId")
            level_item = entry.get("levelItem")
            bonuses = entry.get("bonusesHQ") or entry.get("bonuses") or {}
            bonus_objects: Dict[int, FoodBonus] = {}
            for key, bonus in bonuses.items():
                try:
                    stat_id = int(key)
                except Exception:
                    continue
                bonus_objects[stat_id] = FoodBonus(
                    base_param=stat_id,
                    percentage=bonus.get("percentage", 0),
                    maximum=bonus.get("max", 0),
                )
            if not _has_combat_food_bonus(bonus_objects):
                continue
            foods.append(
                FoodRecord(
                    food_id=food_id,
                    name=name,
                    name_ja=name_ja,
                    level_item=level_item,
                    bonuses=bonus_objects,
                    source_row_id=source_row_id,
                )
            )

        self.cache.save(cache_key, self._serialize_food(foods))
        return foods

    def fetch_jobs(self, force: bool = False) -> Dict[str, JobRecord]:
        cache_key = "jobs.json"
        if not force:
            cached = self._load_dict_cache(cache_key)
            if cached:
                if all(isinstance(val, dict) for val in cached.values()):
                    return {
                        str(key): JobRecord(
                            abbreviation=str(key),
                            modifier_strength=val.get("modifier_strength", 100),
                            modifier_dexterity=val.get("modifier_dexterity", 100),
                            modifier_intelligence=val.get("modifier_intelligence", 100),
                            modifier_mind=val.get("modifier_mind", 100),
                            modifier_vitality=val.get("modifier_vitality", 100),
                            modifier_hp=val.get("modifier_hp", 100),
                        )
                        for key, val in cached.items()
                    }
                logger.warning("Ignoring invalid cache entries for %s", cache_key)

        resp = self._client.get("/Jobs")
        resp.raise_for_status()
        raw = resp.json().get("items", []) or []
        jobs: Dict[str, JobRecord] = {}
        for entry in raw:
            abbr = entry.get("abbreviation")
            if not abbr:
                continue
            jobs[abbr] = JobRecord(
                abbreviation=abbr,
                modifier_strength=entry.get("modifierStrength", 100),
                modifier_dexterity=entry.get("modifierDexterity", 100),
                modifier_intelligence=entry.get("modifierIntelligence", 100),
                modifier_mind=entry.get("modifierMind", 100),
                modifier_vitality=entry.get("modifierVitality", 100),
                modifier_hp=entry.get("modifierHitPoints", 100),
            )

        cache_payload = {
            k: {
                "modifier_strength": v.modifier_strength,
                "modifier_dexterity": v.modifier_dexterity,
                "modifier_intelligence": v.modifier_intelligence,
                "modifier_mind": v.modifier_mind,
                "modifier_vitality": v.modifier_vitality,
                "modifier_hp": v.modifier_hp,
            }
            for k, v in jobs.items()
        }
        self.cache.save(cache_key, cache_payload)
        return jobs

    def fetch_items_for_jobs(
        self,
        jobs: List[str],
        force: bool = False,
        progress: Optional[Callable[[int, str], None]] = None,
        stop_event=None,
    ) -> List[ItemRecord]:
        jobs_sorted = sorted(set(jobs))
        cache_key = f"items_{'_'.join(jobs_sorted)}.json"
        if not force:
            cached = self._load_list_cache(cache_key)
            if cached:
                try:
                    # If cache lacks Japanese names or damage values, refetch
                    needs_refresh = any(
                        not isinstance(entry, dict)
                        or "name_ja" not in entry
                        or "damage_phys" not in entry
                        or "delay_ms" not in entry
                        or "occ_slot" not in entry
                        or "icon_url" not in entry
                        for entry in cached
                    )
                    if not needs_refresh:
                        return self._deserialize_items(cached)
                except (KeyError, TypeError, ValueError):
                    logger.warning("Ignoring invalid cache entries for %s", cache_key)

        if progress:
            progress(5, f"{', '.join(jobs_sorted)} の装備を取得中")
        params = [("job", job) for job in jobs_sorted]
        resp = self._client.get("/Items", params=params)
        resp.raise_for_status()
        raw_items = resp.json().get("items", [])
        parsed: List[ItemRecord] = []
        for idx, entry in enumerate(raw_items):
            if stop_event and stop_event.is_set():
                break
            equip_cat = entry.get("equipSlotCategory") or {}
            slot = slot_from_category(equip_cat)
            if slot is None:
                continue
            occ_slot = occ_slot_from_category(equip_cat)
            icon = entry.get("icon") or {}
            icon_url = icon.get("pngIconUrl") or icon.get("url")
            translations = entry.get("nameTranslations") or {}
            name_ja = translations.get("ja")
            base_params = {int(k): v for k, v in (entry.get("baseParamMapHQ") or entry.get("baseParamMap") or {}).items()}
            base_params_hq = {int(k): v for k, v in (entry.get("baseParamMapHQ") or {}).items()}
            parsed.append(
                ItemRecord(
                    item_id=entry.get("rowId"),
                    name=entry.get("name", "不明"),
                    name_ja=name_ja,
                    jobs=entry.get("classJobs") or [],
                    ilvl=entry.get("ilvl", 0),
                    slot=slot,
                    materia_slots=entry.get("materiaSlotCount", 0),
                    overmeld=bool(entry.get("advancedMeldingPermitted")),
                    base_params=base_params,
                    base_params_hq=base_params_hq or base_params,
                    damage_phys=entry.get("damagePhys"),
                    damage_mag=entry.get("damageMag"),
                    delay_ms=entry.get("delayMs"),
                    occ_slot=occ_slot,
                    unique=bool(entry.get("unique", False)),
                    icon_url=icon_url,
                )
            )
            if progress and idx % 200 == 0:
                pct = int((idx / max(1, len(raw_items))) * 100)
                progress(min(pct, 95), "装備データを解析中")

        payload = [
            {
                "item_id": it.item_id,
                "name": it.name,
                "name_ja": it.name_ja,
                "jobs": it.jobs,
                "ilvl": it.ilvl,
                "slot": it.slot,
                "materia_slots": it.materia_slots,
                "overmeld": it.overmeld,
                "base_params": it.base_params,
                "base_params_hq": it.base_params_hq,
                "damage_phys": it.damage_phys,
                "damage_mag": it.damage_mag,
                "delay_ms": it.delay_ms,
                "occ_slot": it.occ_slot,
                "unique": it.unique,
                "icon_url": it.icon_url,
            }
            for it in parsed
        ]
        self.cache.save(cache_key, payload)
        return parsed

    # --- deserializers ---
    def _deserialize_materia(self, cached: dict) -> Dict[int, MateriaCategory]:
        materia: Dict[int, MateriaCategory] = {}
        for key, grades in cached.items():
            base_param = int(key)
            materia[base_param] = MateriaCategory(
                base_param=base_param,
                grades=[
                    MateriaGrade(
                        name=g["name"],
                        name_ja=g.get("name_ja"),
                        grade=g["grade"],
                        value=g["value"],
                        item_id=g.get("item_id", 0),
                        item_ilvl=g.get("item_ilvl"),
                        icon_url=g.get("icon_url"),
                    )
                    for g in grades
                ],
            )
        return materia

    def _deserialize_food(self, cached: list) -> List[FoodRecord]:
        foods: List[FoodRecord] = []
        for entry in cached:
            bonuses = {
                int(stat): FoodBonus(
                    base_param=int(stat),
                    percentage=bonus["percentage"],
                    maximum=bonus["maximum"],
                )
                for stat, bonus in entry.get("bonuses", {}).items()
            }
            if not _has_combat_food_bonus(bonuses):
                continue
            foods.append(
                FoodRecord(
                    food_id=entry.get("food_id"),
                    name=entry.get("name", "不明"),
                    name_ja=entry.get("name_ja"),
                    level_item=entry.get("level_item"),
                    bonuses=bonuses,
                    source_row_id=entry.get("source_row_id"),
                )
            )
        return foods

    def _serialize_food(self, foods: List[FoodRecord]) -> list:
        return [
            {
                "food_id": f.food_id,
                "name": f.name,
                "name_ja": f.name_ja,
                "level_item": f.level_item,
                "source_row_id": f.source_row_id,
                "bonuses": {
                    str(b.base_param): {
                        "percentage": b.percentage,
                        "maximum": b.maximum,
                    }
                    for b in f.bonuses.values()
                },
            }
            for f in foods
        ]

    def _deserialize_items(self, cached: list) -> List[ItemRecord]:
        return [
            ItemRecord(
                item_id=entry["item_id"],
                name=entry["name"],
                name_ja=entry.get("name_ja"),
                jobs=entry.get("jobs", []),
                ilvl=entry.get("ilvl", 0),
                slot=entry.get("slot"),
                materia_slots=entry.get("materia_slots", 0),
                overmeld=entry.get("overmeld", False),
                base_params={int(k): v for k, v in entry.get("base_params", {}).items()},
                base_params_hq={int(k): v for k, v in entry.get("base_params_hq", {}).items()},
                damage_phys=entry.get("damage_phys"),
                damage_mag=entry.get("damage_mag"),
                delay_ms=entry.get("delay_ms"),
                occ_slot=entry.get("occ_slot"),
                unique=entry.get("unique", False),
                icon_url=entry.get("icon_url"),
            )
            for entry in cached
        ]


def slot_from_category(cat: dict) -> Optional[str]:
    mapping = {
        "mainHand": "weapon",
        "offHand": "offhand",
        "head": "head",
        "body": "body",
        "gloves": "hands",
        "legs": "legs",
        "feet": "feet",
        "ears": "earrings",
        "neck": "necklace",
        "wrists": "bracelet",
        "fingerL": "ring",
        "fingerR": "ring",
    }
    for key, slot in mapping.items():
        if cat.get(key) == 1:
            return slot
    return None


def occ_slot_from_category(cat: dict) -> Optional[str]:
    def slot_value(raw: int) -> str:
        if raw == 1:
            return "equip"
        if raw == -1:
            return "block"
        return "none"

    slots = {
        "Weapon": slot_value(cat.get("mainHand", 0)),
        "OffHand": slot_value(cat.get("offHand", 0)),
        "Head": slot_value(cat.get("head", 0)),
        "Body": slot_value(cat.get("body", 0)),
        "Hand": slot_value(cat.get("gloves", 0)),
        "Legs": slot_value(cat.get("legs", 0)),
        "Feet": slot_value(cat.get("feet", 0)),
        "Ears": slot_value(cat.get("ears", 0)),
        "Neck": slot_value(cat.get("neck", 0)),
        "Wrist": slot_value(cat.get("wrists", 0)),
        "RingLeft": slot_value(cat.get("fingerL", 0)),
        "RingRight": slot_value(cat.get("fingerR", 0)),
    }

    def can(slot: str) -> bool:
        return slots.get(slot) == "equip"

    def equip_or_blocked() -> List[str]:
        order = ["Weapon", "OffHand", "Head", "Body", "Hand", "Legs", "Feet", "Ears", "Neck", "Wrist", "RingLeft", "RingRight"]
        return [s for s in order if slots.get(s) != "none"]

    if can("Weapon"):
        return "Weapon2H" if slots.get("OffHand") == "block" else "Weapon1H"
    if can("RingLeft") or can("RingRight"):
        return "Ring"

    blocked = equip_or_blocked()
    if blocked:
        if blocked == ["Head", "Body", "Legs", "Feet"]:
            return "ChestHeadLegsFeet"
        if blocked == ["Head", "Body"]:
            return "ChestHead"
        if blocked == ["Body", "Legs", "Feet"]:
            return "ChestLegsFeet"
        if blocked == ["Body", "Hand", "Legs"]:
            return "ChestLegsGloves"
        if blocked == ["Head", "Body", "Hand", "Legs", "Feet"]:
            return "HeadChestHandsLegsFeet"
        if blocked == ["Legs", "Feet"]:
            return "LegsFeet"

    normal_order = ["OffHand", "Head", "Body", "Hand", "Legs", "Feet", "Ears", "Neck", "Wrist"]
    for slot in normal_order:
        if can(slot):
            return slot
    return None
