from typing import Dict, Optional

from .models import GEAR_SLOTS, Gearset, ItemSelection


def normalized_export_item_ids(raw_ids: Optional[dict], items_by_id: Dict[int, object]) -> Dict[str, int]:
    if not isinstance(raw_ids, dict):
        return {}
    normalized: Dict[str, int] = {}
    for slot, raw_item_id in raw_ids.items():
        slot_name = str(slot or "").strip()
        if slot_name not in GEAR_SLOTS:
            continue
        try:
            item_id = int(raw_item_id or 0)
        except Exception:
            continue
        if item_id <= 0:
            continue
        item = items_by_id.get(item_id)
        if item is not None:
            expected_slot = "ring" if slot_name in {"ring1", "ring2"} else slot_name
            if str(getattr(item, "slot", "")) != expected_slot:
                continue
        normalized[slot_name] = item_id
    return normalized


def duplicate_unique_ring_slot_for_export(
    slot: str,
    item_id: Optional[int],
    items_by_id: Dict[int, object],
    gearset: Gearset,
    export_item_ids: Optional[Dict[str, int]] = None,
) -> Optional[str]:
    if slot not in {"ring1", "ring2"} or not item_id:
        return None
    item = items_by_id.get(int(item_id))
    if not item or not bool(getattr(item, "unique", False)):
        return None
    other_slot = "ring1" if slot == "ring2" else "ring2"
    export_ids = export_item_ids or {}
    other_override = export_ids.get(other_slot)
    try:
        other_item_id = int(other_override or 0)
    except Exception:
        other_item_id = 0
    if other_item_id <= 0:
        other_sel = (gearset.items or {}).get(other_slot) or ItemSelection()
        other_item_id = int(other_sel.item_id or 0) if other_sel.item_id else 0
    if other_item_id == int(item_id):
        return other_slot
    return None


def gearset_with_export_overrides(
    gear: Gearset,
    context: Optional[dict],
    items_by_id: Dict[int, object],
) -> Gearset:
    export_item_ids = normalized_export_item_ids((context or {}).get("export_item_ids"), items_by_id)
    if not export_item_ids:
        return gear
    cloned = Gearset.from_dict(gear.to_dict())
    for slot, item_id in export_item_ids.items():
        if duplicate_unique_ring_slot_for_export(slot, item_id, items_by_id, cloned, export_item_ids) is not None:
            continue
        sel = (cloned.items or {}).get(slot) or ItemSelection()
        sel.item_id = item_id
        cloned.items[slot] = sel
    return cloned
