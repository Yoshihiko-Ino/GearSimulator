from __future__ import annotations

from typing import Callable, Dict, Iterable, List, Optional

from .models import ItemRecord
from .xivgear_client import XivGearClient


ProgressCallback = Callable[[int, str], None]


class GearDataService:
    def __init__(self, client: XivGearClient) -> None:
        self.client = client

    def fetch(
        self,
        *,
        force: bool,
        jobs_to_refresh: Iterable[str],
        progress: Optional[ProgressCallback] = None,
        stop_event=None,
    ) -> dict:
        bp = self.client.fetch_base_params(force=force)
        if progress:
            progress(10, "基礎ステータス取得中")
        materia = self.client.fetch_materia(force=force)
        if progress:
            progress(25, "マテリア取得中")
        food = self.client.fetch_food(force=force)
        if progress:
            progress(40, "食事データ取得中")
        levels = self.client.fetch_item_levels(force=force)
        if progress:
            progress(55, "ItemLevel取得中")
        jobs = self.client.fetch_jobs(force=force)

        target_jobs = sorted({str(job) for job in jobs_to_refresh if job}) if force else []
        refreshed_items: Dict[str, List[ItemRecord]] = {}
        for index, job in enumerate(target_jobs):
            if stop_event and stop_event.is_set():
                break
            if progress:
                pct = 60 + int((index / max(1, len(target_jobs))) * 35)
                progress(pct, f"{job} の装備データを再取得中")
            refreshed_items[job] = self.client.fetch_items_for_jobs(
                [job],
                force=True,
                stop_event=stop_event,
            )
        if progress:
            progress(100, "装備データ取得完了")
        return {
            "bp": bp,
            "materia": materia,
            "food": food,
            "jobs": jobs,
            "levels": levels,
            "items_by_job": refreshed_items,
            "forced": force,
            "from_cache": False,
        }
