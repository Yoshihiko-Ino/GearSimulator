from __future__ import annotations

import copy
import json
import math
import os
import time
import re
import uuid
from urllib.parse import quote_plus
from pathlib import Path
import hashlib
import logging
import traceback
from concurrent.futures import ThreadPoolExecutor
from itertools import combinations, permutations
from typing import Dict, List, Optional, Tuple

from PySide6.QtCore import Qt, QThreadPool, QSize, QTimer, QSignalBlocker, QUrl
from PySide6.QtGui import QDesktopServices, QIcon, QPixmap
from PySide6.QtWidgets import (
    QApplication,
    QAbstractItemView,
    QComboBox,
    QDoubleSpinBox,
    QFormLayout,
    QGroupBox,
    QHBoxLayout,
    QLabel,
    QLineEdit,
    QListWidget,
    QListWidgetItem,
    QMainWindow,
    QMessageBox,
    QPushButton,
    QProgressBar,
    QSplitter,
    QTabWidget,
    QVBoxLayout,
    QWidget,
    QTextEdit,
    QCheckBox,
    QSpinBox,
    QDialog,
    QDialogButtonBox,
    QGridLayout,
    QTableWidget,
    QTableWidgetItem,
    QInputDialog,
    QToolButton,
    QScrollArea,
    QSizePolicy,
    QFrame,
    QHeaderView,
    QMenu,
    QTabBar,
)

import httpx

from .cache import FileCache
from .fflogs_client import FFLogsClient
from .gear_data_service import GearDataService
from .gcd_analysis import LogGcdConstraint, LogGcdEstimate, build_log_gcd_constraint, estimate_log_gcd
from .models import (
    GEAR_SLOTS,
    Gearset,
    ItemRecord,
    ItemSelection,
    MateriaGrade,
    MateriaSlotSelection,
    SPELL_SPEED_JOBS,
)
from .workers import Worker
from .export_utils import (
    duplicate_unique_ring_slot_for_export,
    gearset_with_export_overrides,
    normalized_export_item_ids,
)
from .utils import (
    decode_progress_message,
    display_name_with_fallback,
    encode_progress_message,
    sim_log,
    sim_debug_enabled,
)
from .xivgear_client import XivGearClient
from .xivapi_client import XivApiClient
from .report_utils import extract_report_code
from .report_cache import ReportCache
from .saved_stats import compute_saved_stats_snapshot
from .time_utils import timestamp_sort_value, utc_now_iso
from .config_store import (
    consume_config_warnings,
    ensure_config_files,
    load_auth,
    save_auth,
    load_saved_sets,
    save_saved_sets,
)
from .paths import ensure_runtime_dirs, writable_cache_dir
from . import APP_VERSION, optimizer, xivmath


logger = logging.getLogger(__name__)

DEFAULT_RACE = xivmath.DEFAULT_RACE
FOOD_SIMULATION_DATA = "__food_simulation__"
MAIN_STAT_LABELS = {
    1: "str",
    2: "dex",
    4: "int",
    5: "mnd",
}
MAIN_STAT_HEADERS = {
    1: "STR",
    2: "DEX",
    4: "INT",
    5: "MND",
}

SAVED_COL_HANDLE = 0
SAVED_COL_LOCK = 1
SAVED_COL_NAME = 2
SAVED_COL_MODE = 3
SAVED_COL_SCORE = 4
SAVED_COL_EXPECTED_SCORE = 5
SAVED_COL_GCD = 6
SAVED_COL_WD = 7
SAVED_COL_HP = 8
SAVED_COL_MAIN = 9
SAVED_COL_CRT = 10
SAVED_COL_DHT = 11
SAVED_COL_DET = 12
SAVED_COL_SPS = 13
SAVED_COL_FOOD = 14
SAVED_COL_EXPORT = 15

XIVGEAR_SLOT_MAP = {
    "Weapon": "weapon",
    "MainHand": "weapon",
    "OffHand": "offhand",
    "Shield": "offhand",
    "Head": "head",
    "Body": "body",
    "Hand": "hands",
    "Hands": "hands",
    "Legs": "legs",
    "Feet": "feet",
    "Ears": "earrings",
    "Earrings": "earrings",
    "Neck": "necklace",
    "Necklace": "necklace",
    "Wrist": "bracelet",
    "Bracelet": "bracelet",
    "RingLeft": "ring1",
    "Ring1": "ring1",
    "RingRight": "ring2",
    "Ring2": "ring2",
}
GEARSIM_TO_XIVGEAR_SLOT_MAP = {
    "weapon": "Weapon",
    "offhand": "OffHand",
    "head": "Head",
    "body": "Body",
    "hands": "Hand",
    "legs": "Legs",
    "feet": "Feet",
    "earrings": "Ears",
    "necklace": "Neck",
    "bracelet": "Wrist",
    "ring1": "RingLeft",
    "ring2": "RingRight",
}


class PersistentCheckMenu(QMenu):
    # Keep the popup open when toggling checkable actions.
    # It closes normally when clicking outside the menu.
    def mouseReleaseEvent(self, event) -> None:
        action = self.activeAction()
        if action and action.isEnabled() and action.isCheckable():
            action.trigger()
            event.accept()
            return
        super().mouseReleaseEvent(event)


class SplitterDragBar(QWidget):
    """A thin draggable bar that adjusts a target QSplitter handle."""

    def __init__(self, splitter: Optional[QSplitter] = None, handle_index: int = 1, parent=None):
        super().__init__(parent)
        self._splitter = splitter
        self._handle_index = handle_index
        self._dragging = False
        self._start_y = 0
        self._start_sizes: List[int] = []
        self.setFixedHeight(12)
        self.setCursor(Qt.SizeVerCursor)
        self.setStyleSheet("background-color: rgba(127, 143, 163, 0.12); border-radius: 2px;")
        layout = QHBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)
        label = QLabel("≡", self)
        label.setAlignment(Qt.AlignCenter)
        label.setStyleSheet("color: #7f8fa3; font-weight: 600;")
        layout.addWidget(label)
        self.setToolTip("ドラッグで表示サイズを変更")

    def set_target(self, splitter: Optional[QSplitter], handle_index: int) -> None:
        self._splitter = splitter
        self._handle_index = max(1, int(handle_index))

    def _apply_drag_delta(self, dy: int) -> None:
        splitter = self._splitter
        if splitter is None:
            return
        sizes = list(self._start_sizes)
        if len(sizes) < 2:
            return
        left = self._handle_index - 1
        right = self._handle_index
        if left < 0 or right >= len(sizes):
            return
        new_left = sizes[left] + dy
        new_right = sizes[right] - dy

        left_widget = splitter.widget(left)
        right_widget = splitter.widget(right)
        min_left = left_widget.minimumHeight() if left_widget else 0
        min_right = right_widget.minimumHeight() if right_widget else 0
        min_left = max(0, int(min_left))
        min_right = max(0, int(min_right))

        if new_left < min_left:
            diff = min_left - new_left
            new_left = min_left
            new_right -= diff
        if new_right < min_right:
            diff = min_right - new_right
            new_right = min_right
            new_left -= diff
        if new_left < min_left or new_right < min_right:
            return

        sizes[left] = new_left
        sizes[right] = new_right
        splitter.setSizes(sizes)

    def mousePressEvent(self, event) -> None:
        if event.button() == Qt.LeftButton:
            self._dragging = True
            self._start_y = int(event.globalPosition().y())
            self._start_sizes = list(self._splitter.sizes()) if self._splitter else []
            event.accept()
            return
        super().mousePressEvent(event)

    def mouseMoveEvent(self, event) -> None:
        if self._dragging and self._splitter is not None:
            dy = int(event.globalPosition().y()) - self._start_y
            self._apply_drag_delta(dy)
            event.accept()
            return
        super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event) -> None:
        if self._dragging and event.button() == Qt.LeftButton:
            self._dragging = False
            event.accept()
            return
        super().mouseReleaseEvent(event)


STAT_ABBR = {
    27: "CRT",
    22: "DHT",
    44: "DET",
    45: "SkS",
    46: "SpS",
    19: "TEN",
    6: "PIE",
}

RELIC_TOTAL_CAP_BY_ILVL = {
    515: 462,
    535: 468,
}

RELIC_STAT_ORDER = [27, 22, 44, 45, 46, 19, 6]
MANDERVILLE_FIXED_STAT_VALUES = (293, 293, 72)
MANDERVILLOUS_FIXED_STAT_VALUES = (306, 306, 72)
MANDERVILLE_PRIMARY_STAT_VALUE = 293
MANDERVILLOUS_PRIMARY_STAT_VALUE = 306
MANDERVILLE_TERTIARY_STAT_VALUE = 72
MANDERVILLE_NAME_PREFIXES = (
    "Majestic Manderville",
    "Mandervillous",
    "マンダヴィル・マジェスティック",
    "マンダヴィラス",
)
PHANTOM_NAME_PREFIXES = (
    "Phantom ",
    "ファントム",
)
SPECIAL_WEAPON_EDIT_BUTTON_LABEL = "特殊武器補正編集"

XIVGEAR_RELIC_STAT_NAME_BY_ID = {
    27: "crit",
    22: "dhit",
    44: "determination",
    45: "skillspeed",
    46: "spellspeed",
    19: "tenacity",
    6: "piety",
}

XIVGEAR_RELIC_STAT_ID_BY_NAME = {
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


SLOT_LABELS = {
    "weapon": "武器",
    "offhand": "サブ武器",
    "head": "頭",
    "body": "胴",
    "hands": "手",
    "legs": "脚",
    "feet": "足",
    "earrings": "耳",
    "necklace": "首",
    "bracelet": "腕",
    "ring1": "指輪1",
    "ring2": "指輪2",
}


STATS_VERSION = 4
SCORE_META_VERSION = 2
SCORE_MODEL_NAMES = {
    "dmg100p": "xivgear_dmg100p",
    "simdps": "simdps_adps",
    "simdps_self": "simdps_ndps",
}
SYNC_LEVEL_INFER_THRESHOLDS = (
    (430, 70),
    (560, 80),
    (670, 90),
)


def _score_payload_hash(payload: object) -> str:
    encoded = json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":"), default=str)
    return hashlib.sha256(encoded.encode("utf-8")).hexdigest()


def _score_normalize_mapping_keys(value: object) -> object:
    if isinstance(value, dict):
        return [
            [repr(key), _score_normalize_mapping_keys(item)]
            for key, item in sorted(value.items(), key=lambda pair: repr(pair[0]))
        ]
    if isinstance(value, (list, tuple)):
        return [_score_normalize_mapping_keys(item) for item in value]
    return value


def _score_gear_payload(raw_gear: object) -> Dict[str, object]:
    gear = raw_gear if isinstance(raw_gear, dict) else {}
    raw_items = gear.get("items")
    items: Dict[str, object] = {}
    if isinstance(raw_items, dict):
        for slot, raw_selection in sorted(raw_items.items(), key=lambda pair: str(pair[0])):
            selection = raw_selection if isinstance(raw_selection, dict) else {}
            raw_materia = selection.get("materia")
            materia = []
            if isinstance(raw_materia, list):
                materia = [
                    {
                        "base_param": entry.get("base_param"),
                        "grade": entry.get("grade"),
                    }
                    for entry in raw_materia
                    if isinstance(entry, dict)
                ]
            raw_relic_stats = selection.get("relic_stats")
            if not isinstance(raw_relic_stats, dict):
                raw_relic_stats = selection.get("relicStats")
            if not isinstance(raw_relic_stats, dict):
                raw_relic_stats = {}
            relic_stats = dict(sorted(raw_relic_stats.items(), key=lambda pair: str(pair[0])))
            items[str(slot)] = {
                "item_id": selection.get("item_id", selection.get("itemId")),
                "materia": materia,
                "relic_stats": relic_stats,
            }
    return {
        "job": gear.get("job"),
        "level": gear.get("level"),
        "food_id": gear.get("foodId", gear.get("food_id")),
        "food_simulation": bool(gear.get("foodSimulation", gear.get("food_simulation", False))),
        "target_gcd": gear.get("target_gcd"),
        "race": gear.get("race"),
        "items": items,
    }


def _saved_score_context_payload(entry: object) -> Dict[str, object]:
    saved = entry if isinstance(entry, dict) else {}
    raw_context = saved.get("ui_context")
    context = raw_context if isinstance(raw_context, dict) else {}
    score_context_keys = (
        "level_sync_enabled",
        "level_sync_il",
        "level_sync_level",
        "calc_mode",
        "party_bonus",
        "crit_rate_adjust",
        "dhit_rate_adjust",
        "party_synergies",
    )
    return {
        "mode": saved.get("mode"),
        "gearset": _score_gear_payload(saved.get("gearset")),
        "food_id": saved.get("food_id"),
        "party_bonus": saved.get("party_bonus"),
        "report_code": extract_report_code(str(saved.get("report_code") or "")) or None,
        "fight_id": saved.get("fight_id"),
        "actor_id": saved.get("actor_id"),
        "stats": saved.get("stats"),
        "stats_version": saved.get("stats_version"),
        "ui_context": {key: context.get(key) for key in score_context_keys},
    }

JOB_ORDER = [
    "PLD",
    "WAR",
    "DRK",
    "GNB",
    "WHM",
    "SCH",
    "AST",
    "SGE",
    "MNK",
    "DRG",
    "NIN",
    "SAM",
    "RPR",
    "VPR",
    "BRD",
    "MCH",
    "DNC",
    "BLM",
    "RDM",
    "SMN",
    "PCT",
]

JOB_NAME_MAP = {
    "Paladin": "PLD",
    "Warrior": "WAR",
    "DarkKnight": "DRK",
    "Gunbreaker": "GNB",
    "WhiteMage": "WHM",
    "Scholar": "SCH",
    "Astrologian": "AST",
    "Sage": "SGE",
    "Monk": "MNK",
    "Dragoon": "DRG",
    "Ninja": "NIN",
    "Samurai": "SAM",
    "Reaper": "RPR",
    "Viper": "VPR",
    "Bard": "BRD",
    "Machinist": "MCH",
    "Dancer": "DNC",
    "BlackMage": "BLM",
    "Summoner": "SMN",
    "RedMage": "RDM",
    "Pictomancer": "PCT",
}

ULTIMATE_LEVEL_SYNC_IL = {
    "UCoB": (70, 345),
    "UWU": (70, 375),
    "TEA": (80, 475),
    "DSR": (90, 605),
    "TOP": (90, 635),
    "FRU": (100, 735),
}

# Level-sync content specific threshold where substats are effectively capped.
# Used to aggressively collapse high IL options in synced content.
SYNC_SUBSTAT_CAP_START_IL = {
    ULTIMATE_LEVEL_SYNC_IL["UCoB"][1]: 470,
    ULTIMATE_LEVEL_SYNC_IL["UWU"][1]: 500,
    ULTIMATE_LEVEL_SYNC_IL["TEA"][1]: 595,
    ULTIMATE_LEVEL_SYNC_IL["DSR"][1]: 725,
    ULTIMATE_LEVEL_SYNC_IL["TOP"][1]: 760,
}
_USE_CURRENT_SYNC = object()


class MainWindow(QMainWindow):
    def __init__(self) -> None:
        super().__init__()
        self.setWindowTitle(f"FF14 ギアシミュレーター v{APP_VERSION}")
        self.resize(1400, 900)

        self.cache = FileCache()
        self.report_cache = ReportCache(self.cache)
        self.xiv_client = XivGearClient(self.cache)
        self.gear_data_service = GearDataService(self.xiv_client)
        self.xivapi_client = XivApiClient(self.cache)
        self.ff_client = FFLogsClient()
        self.thread_pool = QThreadPool.globalInstance()
        self.icon_thread_pool = QThreadPool()
        self.icon_thread_pool.setMaxThreadCount(4)
        self.active_worker: Optional[Worker] = None
        self._saved_stats_worker: Optional[Worker] = None
        self._fflogs_context_locked = False
        self._job_context_locked = False
        self._closing = False

        # Data state
        self.base_params: Dict[int, object] = {}
        self.item_levels: Dict[int, object] = {}
        self.materia_catalog = {}
        self.foods: List = []
        self.jobs_data: Dict[str, object] = {}
        self.items_by_job: Dict[str, List] = {}
        self.items_by_id: Dict[int, object] = {}
        self.cap_table = {}
        self._applying_gearset = False
        self._pending_gearset: Optional[Gearset] = None
        self.slot_row_index: Dict[str, Dict[int, int]] = {}
        self._last_selected_items: Dict[str, Optional[int]] = {}
        self.fights: List[dict] = []
        self._raw_fights: List[dict] = []
        self.players: List[dict] = []
        self.selected_fight: Optional[dict] = None
        self.selected_actor: Optional[dict] = None
        self.casts: List[dict] = []
        self.timeline_events: List[dict] = []
        self.damage_events: List[dict] = []
        self.damage_summary: Optional[Dict[str, float]] = None
        self.damage_table: Optional[dict] = None
        self.damage_table_adps: Optional[dict] = None
        self.damage_summary_self: Optional[Dict[str, float]] = None
        self.enemy_npcs: List[dict] = []
        self.friendly_ids: set = set()
        self.last_optimize_mode: str = "simdps_self"
        self._last_optimize_used_gear_search: bool = False
        self.last_eval: Optional[dict] = None
        self.saved_sets = load_saved_sets().get("items", [])
        self._pending_fight_id: Optional[int] = None
        self._pending_actor_id: Optional[int] = None
        self.slot_tables: Dict[str, QTableWidget] = {}
        self.slot_lock_item_checks: Dict[str, QCheckBox] = {}
        self.slot_lock_materia_checks: Dict[str, QCheckBox] = {}
        self.slot_exclude_labels: Dict[str, QToolButton] = {}
        self._optimal_variant_entries: List[Dict[str, object]] = []
        self._applying_optimal_variant_tab: bool = False
        self._materia_icon_cache: Dict[str, QIcon] = {}
        self.action_data: Dict[int, object] = {}
        self.status_data: Dict[int, object] = {}
        self._pending_icon_buttons: Dict[str, List[QToolButton]] = {}
        self._pending_item_icon_cells: Dict[str, List[Tuple[QTableWidget, int, int]]] = {}
        self._icon_fetching: set = set()
        self._icon_workers: Dict[str, Worker] = {}
        self._icon_cache_dir = writable_cache_dir() / "icons"
        self._prefetch_icons_started: bool = False
        self._prefetched_item_icon_urls: set = set()
        self._food_lookup_by_id: Dict[int, object] = {}
        self._job_mods_cache: Dict[str, Dict[str, int]] = {}
        self._relic_model_cache: Dict[Tuple[int, str], Optional[Dict[str, object]]] = {}
        self._display_sync_item_cache: Dict[Tuple[int, str, int], ItemRecord] = {}
        self._saved_stats_cache: Dict[Tuple[str, Optional[int], int], Dict[str, int]] = {}
        self._raw_stats_cache: Dict[Tuple, Tuple[Dict[int, int], Dict[str, object]]] = {}
        self._populate_queue: List[dict] = []
        self._is_populating: bool = False
        self._pending_populate: Optional[Tuple[object, ...]] = None
        self._last_populate_key: Optional[Tuple[object, ...]] = None
        self._populate_immediate_mode: bool = False
        self._pending_score_after_populate: bool = False
        self._pending_score_after_worker: bool = False
        self._auto_calc_suspended: int = 0
        self._last_preview_signature: Optional[Tuple] = None
        self._table_sized: Dict[str, bool] = {}
        self._tables_to_resize: List[str] = []
        self._phase_transitions: List[dict] = []
        self._phase_meta: Dict[int, dict] = {}
        self._pending_phase_request: Optional[Tuple[str, dict]] = None
        self._suppress_busy_dialog: bool = True
        self._saved_table_sized_once: bool = False
        self._updating_saved_table: bool = False
        self._saved_stats_worker_active: bool = False
        self._saved_sets_reordering: bool = False
        self._saved_sets_dirty: bool = False
        self._saved_sets_flush_timer = QTimer(self)
        self._saved_sets_flush_timer.setSingleShot(True)
        self._saved_sets_flush_timer.timeout.connect(self._flush_saved_sets)
        self._pending_saved_jobs: set = set()
        self._il_filter_initialized_jobs: set = set()
        self._loading_saved_jobs: bool = False
        self._last_populated_job: Optional[str] = None
        self._simdps_baseline_gearset: Optional[Gearset] = None
        self._simdps_baseline_raw_stats: Optional[Dict[int, int]] = None
        self._simdps_baseline_items: Optional[Dict[str, object]] = None
        self._simdps_baseline_food: Optional[object] = None
        self._simdps_baseline_party: Optional[int] = None
        self._simdps_baseline_race: Optional[str] = None
        self._simdps_baseline_exact: bool = False
        self._simdps_baseline_name: Optional[str] = None
        self._simdps_baseline_entry_id: Optional[int] = None
        self._log_gcd_estimate: Optional[LogGcdEstimate] = None
        self._log_gcd_constraint: Optional[LogGcdConstraint] = None
        self._current_export_item_ids: Dict[str, int] = {}
        self._pending_saved_set_entry: Optional[dict] = None
        self._pending_saved_set_ui_context: Optional[dict] = None
        self._current_loaded_saved_set_id: Optional[int] = None
        self._pending_saved_score_recalculation_id: Optional[int] = None
        self._pending_saved_score_recalculation_name: Optional[str] = None
        self._auto_calc_timer = QTimer(self)
        self._auto_calc_timer.setSingleShot(True)
        self._auto_calc_timer.timeout.connect(self._update_score_preview)
        self.current_gearset = Gearset(
            items={slot: ItemSelection() for slot in GEAR_SLOTS},
            target_gcd=2.50,
            race=DEFAULT_RACE,
        )

        self._build_ui()
        self._load_saved_auth()
        self._show_pending_config_warnings()
        self._load_cached_gear_data()
        self._refresh_saved_sets_table()
        QTimer.singleShot(0, self._ensure_initial_job_items_loaded)

    def showEvent(self, event) -> None:
        super().showEvent(event)
        # Allow busy dialog after the first show to avoid startup warnings.
        if self._suppress_busy_dialog:
            QTimer.singleShot(0, self._disable_startup_busy_dialog)

    def _disable_startup_busy_dialog(self) -> None:
        self._suppress_busy_dialog = False

    # ---- UI construction ----
    def _build_ui(self) -> None:
        splitter = QSplitter(Qt.Horizontal)
        splitter.addWidget(self._build_fflogs_panel())
        splitter.addWidget(self._build_gear_panel())
        splitter.setStretchFactor(0, 2)
        splitter.setStretchFactor(1, 3)

        sim_panel = QWidget()
        sim_layout = QVBoxLayout(sim_panel)
        sim_layout.setContentsMargins(0, 0, 0, 0)
        sim_layout.addWidget(splitter)

        settings_panel = self._build_settings_panel()

        tabs = QTabWidget()
        tabs.addTab(sim_panel, "シミュレーション")
        tabs.addTab(settings_panel, "設定")

        self.progress_bar = QProgressBar()
        self.progress_bar.setRange(0, 100)
        self.progress_bar.setValue(0)
        self.progress_bar.setFormat("全体 %p%")
        self.progress_label = QLabel("待機中")
        self.progress_detail_bar = QProgressBar()
        self.progress_detail_bar.setRange(0, 100)
        self.progress_detail_bar.setValue(0)
        self.progress_detail_bar.setFormat("項目 %p%")
        self.progress_detail_label = QLabel("-")
        self.btn_cancel = QPushButton("キャンセル")
        self.btn_cancel.clicked.connect(self.on_cancel)
        self.btn_cancel.setEnabled(False)
        self.btn_cancel.setVisible(False)

        overall_box = QVBoxLayout()
        overall_box.setContentsMargins(0, 0, 0, 0)
        overall_box.setSpacing(2)
        overall_box.addWidget(self.progress_label)
        overall_box.addWidget(self.progress_bar)

        detail_box = QVBoxLayout()
        detail_box.setContentsMargins(0, 0, 0, 0)
        detail_box.setSpacing(2)
        detail_box.addWidget(self.progress_detail_label)
        detail_box.addWidget(self.progress_detail_bar)

        bottom = QHBoxLayout()
        bottom.addLayout(overall_box, 1)
        bottom.addLayout(detail_box, 1)
        bottom.addWidget(self.btn_cancel)

        root_layout = QVBoxLayout()
        root_layout.addWidget(tabs)
        root_layout.addLayout(bottom)

        container = QWidget()
        container.setLayout(root_layout)
        self.setCentralWidget(container)
        self.btn_cancel.hide()

    def _populate_race_clan_options(self) -> None:
        if not self.race_clan_combo:
            return
        self.race_clan_combo.blockSignals(True)
        self.race_clan_combo.clear()
        self.race_clan_combo.addItem("平均", DEFAULT_RACE)
        self.race_clan_combo.setCurrentIndex(0)
        self.race_clan_combo.blockSignals(False)

    def _current_race(self) -> Optional[str]:
        return DEFAULT_RACE

    def _set_race_clan(self, _clan_key: Optional[str]) -> None:
        if self.race_clan_combo:
            self.race_clan_combo.setCurrentIndex(0)
        self.current_gearset.race = DEFAULT_RACE

    def _build_fflogs_panel(self) -> QWidget:
        panel = QWidget()
        layout = QVBoxLayout(panel)

        report_group = QGroupBox("レポート / ファイト / アクター")
        report_layout = QVBoxLayout()
        top_line = QHBoxLayout()
        self.input_report_code = QLineEdit()
        self.input_report_code.setPlaceholderText("レポートコード (例: a1b2c3d4 または URL)")
        btn_load_fights = QPushButton("ファイト取得")
        btn_load_fights.clicked.connect(self.on_load_fights)
        self.chk_force_fflogs = QCheckBox("FFLogsを強制再取得")
        top_line.addWidget(self.input_report_code)
        top_line.addWidget(btn_load_fights)
        top_line.addWidget(self.chk_force_fflogs)
        report_layout.addLayout(top_line)

        self.fight_list = QListWidget()
        self.fight_list.itemSelectionChanged.connect(self.on_fight_selected)
        report_layout.addWidget(QLabel("ファイト一覧"))
        report_layout.addWidget(self.fight_list, stretch=1)

        report_layout.addWidget(QLabel("フェーズ一覧"))
        self.phase_list = QListWidget()
        self.phase_list.itemSelectionChanged.connect(self._on_phase_changed)
        all_phase_item = QListWidgetItem("全フェーズ")
        all_phase_item.setData(Qt.UserRole, None)
        self.phase_list.addItem(all_phase_item)
        self.phase_list.setCurrentRow(0)
        report_layout.addWidget(self.phase_list)

        phase_line = QHBoxLayout()
        self.chk_include_wipes = QCheckBox("非クリア回も表示")
        self.chk_include_wipes.toggled.connect(self._on_include_wipes_toggled)
        phase_line.addStretch(1)
        phase_line.addWidget(self.chk_include_wipes)
        report_layout.addLayout(phase_line)

        report_layout.addWidget(QLabel("ジョブ一覧"))
        filter_line = QHBoxLayout()
        self.actor_search = QLineEdit()
        self.actor_search.setPlaceholderText("アクター検索")
        self.actor_search.textChanged.connect(self.filter_actors)
        self.actor_job_filter = QComboBox()
        self.actor_job_filter.addItem("全ジョブ", None)
        for job in JOB_ORDER:
            self.actor_job_filter.addItem(job, job)
        self.actor_job_filter.currentIndexChanged.connect(self.filter_actors)
        filter_line.addWidget(self.actor_search)
        filter_line.addWidget(self.actor_job_filter)

        self.actor_list = QListWidget()
        self.actor_list.itemSelectionChanged.connect(self.on_actor_selected)
        btn_load_casts = QPushButton("キャスト取得")
        btn_load_casts.clicked.connect(self.on_load_casts)
        self.calc_result_label_left = QLabel("計算結果: -")
        self.calc_result_label_left.setWordWrap(True)

        report_layout.addLayout(filter_line)
        report_layout.addWidget(self.actor_list, stretch=1)
        report_layout.addWidget(btn_load_casts)
        report_layout.addWidget(self.calc_result_label_left)
        report_group.setLayout(report_layout)

        layout.addWidget(report_group)
        return panel

    def _build_settings_panel(self) -> QWidget:
        panel = QWidget()
        layout = QVBoxLayout(panel)

        gear_fetch_group = QGroupBox("装備データ")
        gear_fetch_layout = QHBoxLayout()
        self.btn_fetch_gear = QPushButton("装備データ取得")
        self.btn_fetch_gear.clicked.connect(self.on_fetch_gear_data)
        self.chk_force_gear = QCheckBox("強制再取得")
        gear_fetch_layout.addWidget(self.btn_fetch_gear)
        gear_fetch_layout.addWidget(self.chk_force_gear)
        gear_fetch_group.setLayout(gear_fetch_layout)

        creds_group = QGroupBox("FFLogs V2 認証")
        creds_form = QFormLayout()
        self.input_client_id = QLineEdit()
        self.input_client_id.setPlaceholderText("クライアントID")
        self.input_client_secret = QLineEdit()
        self.input_client_secret.setEchoMode(QLineEdit.Password)
        self.input_client_secret.setPlaceholderText("クライアントシークレット")
        btn_save_auth = QPushButton("認証情報を保存")
        btn_save_auth.clicked.connect(self.on_save_auth)
        creds_form.addRow("クライアントID", self.input_client_id)
        creds_form.addRow("クライアントシークレット", self.input_client_secret)
        creds_form.addRow(btn_save_auth)
        creds_group.setLayout(creds_form)

        debug_group = QGroupBox("デバッグ")
        debug_layout = QHBoxLayout()
        self.chk_debug_mode = QCheckBox("Debugモード（詳細ログを出力）")
        self.chk_debug_mode.setChecked(sim_debug_enabled())
        self.chk_debug_mode.toggled.connect(self.on_debug_mode_toggled)
        debug_layout.addWidget(self.chk_debug_mode)
        debug_layout.addStretch(1)
        debug_group.setLayout(debug_layout)

        optimize_group = QGroupBox("最適化")
        optimize_form = QFormLayout()
        self.optimize_worker_combo = QComboBox()
        self.optimize_worker_combo.addItem("自動（推奨）", 0)
        for worker_count in (1, 2, 4, 6, 8):
            self.optimize_worker_combo.addItem(f"{worker_count}プロセス", worker_count)
        self.optimize_worker_combo.addItem("12プロセス（高負荷）", 12)
        self.optimize_worker_combo.addItem("16プロセス（64GB推奨）", 16)
        self.optimize_worker_combo.setToolTip(
            "装備シミュレーションのCPU並列数。自動はCPUと空きメモリから決定します。"
            "12／16プロセスは処理が速くなる一方、一時メモリが大きくなります。"
        )
        self.optimize_worker_combo.currentIndexChanged.connect(
            self._on_optimize_worker_changed
        )
        optimize_form.addRow("CPU並列数", self.optimize_worker_combo)
        optimize_group.setLayout(optimize_form)

        view_group = QGroupBox("表示")
        view_layout = QVBoxLayout()
        self.chk_icon_display = QCheckBox("アイコン表示を有効化")
        self.chk_icon_display.setChecked(True)
        self.chk_icon_display.toggled.connect(self._on_icon_display_toggled)
        self.chk_icon_prefetch_visible_only = QCheckBox(
            "アイコン先読みを現在ジョブ＋現在IL範囲の表示候補に限定"
        )
        self.chk_icon_prefetch_visible_only.setChecked(True)
        self.chk_icon_prefetch_visible_only.toggled.connect(self._on_icon_prefetch_mode_toggled)
        view_layout.addWidget(self.chk_icon_display)
        view_layout.addWidget(self.chk_icon_prefetch_visible_only)
        view_group.setLayout(view_layout)

        layout.addWidget(gear_fetch_group)
        layout.addWidget(creds_group)
        layout.addWidget(optimize_group)
        layout.addWidget(debug_group)
        layout.addWidget(view_group)
        layout.addStretch(1)
        return panel

    def _build_gear_panel(self) -> QWidget:
        panel = QWidget()
        layout = QVBoxLayout(panel)

        job_line = QHBoxLayout()
        job_line.setSpacing(8)
        job_line.setAlignment(Qt.AlignLeft)
        sync_line = QHBoxLayout()
        sync_line.setSpacing(8)
        sync_line.setAlignment(Qt.AlignLeft)
        self.job_combo = QComboBox()
        self.job_combo.addItem("ジョブを選択", None)
        for job in JOB_ORDER:
            self.job_combo.addItem(job, job)
        self.job_combo.currentIndexChanged.connect(self.on_job_changed)
        self.item_il_min = QSpinBox()
        self.item_il_min.setRange(1, 9999)
        self.item_il_min.setValue(1)
        self.item_il_min.setFixedWidth(70)
        self.item_il_min.valueChanged.connect(self.on_il_filter_changed)
        self.item_il_max = QSpinBox()
        self.item_il_max.setRange(1, 9999)
        self.item_il_max.setValue(9999)
        self.item_il_max.setFixedWidth(70)
        self.item_il_max.valueChanged.connect(self.on_il_filter_changed)
        self.input_target_gcd = QDoubleSpinBox()
        self.input_target_gcd.setDecimals(3)
        self.input_target_gcd.setRange(1.5, 3.5)
        self.input_target_gcd.setSingleStep(0.01)
        self.input_target_gcd.setValue(2.50)
        self.input_target_gcd.setFixedWidth(80)
        self.input_target_gcd.valueChanged.connect(self._schedule_auto_score_update)
        self.party_bonus = QSpinBox()
        self.party_bonus.setRange(0, 5)
        self.party_bonus.setValue(5)
        self.party_bonus.setFixedWidth(60)
        self.party_bonus.valueChanged.connect(self._schedule_auto_score_update)
        self.crit_rate_adjust_spin = QSpinBox()
        self.crit_rate_adjust_spin.setRange(-20, 20)
        self.crit_rate_adjust_spin.setValue(0)
        self.crit_rate_adjust_spin.setSuffix("%")
        self.crit_rate_adjust_spin.setFixedWidth(70)
        self.crit_rate_adjust_spin.setToolTip("計算時のクリティカル率に直接加算する補正値です")
        self.crit_rate_adjust_spin.valueChanged.connect(self._on_rate_adjustment_changed)
        self.dhit_rate_adjust_spin = QSpinBox()
        self.dhit_rate_adjust_spin.setRange(-20, 20)
        self.dhit_rate_adjust_spin.setValue(0)
        self.dhit_rate_adjust_spin.setSuffix("%")
        self.dhit_rate_adjust_spin.setFixedWidth(70)
        self.dhit_rate_adjust_spin.setToolTip("計算時のダイレクトヒット率に直接加算する補正値です")
        self.dhit_rate_adjust_spin.valueChanged.connect(self._on_rate_adjustment_changed)
        self.chk_level_sync = QCheckBox("レベルシンク")
        self.chk_level_sync.toggled.connect(self.on_level_sync_changed)
        self.level_sync_il = QSpinBox()
        self.level_sync_il.setRange(1, 9999)
        self.level_sync_il.setValue(730)
        self.level_sync_il.setFixedWidth(70)
        self.level_sync_il.setEnabled(False)
        self.level_sync_il.valueChanged.connect(self.on_level_sync_changed)
        self.level_sync_level_combo = QComboBox()
        self.level_sync_level_combo.setFixedWidth(72)
        for supported_level in xivmath.SUPPORTED_LEVELS:
            self.level_sync_level_combo.addItem(str(int(supported_level)), int(supported_level))
        self.level_sync_level_combo.setCurrentIndex(
            max(0, self.level_sync_level_combo.findData(int(xivmath.CURRENT_MAX_LEVEL)))
        )
        self.level_sync_level_combo.setEnabled(False)
        self.level_sync_level_combo.currentIndexChanged.connect(self.on_level_sync_changed)
        job_line.addWidget(QLabel("ジョブ"))
        job_line.addWidget(self.job_combo)
        self.race_clan_combo = QComboBox()
        self.race_clan_combo.setEnabled(False)
        self._populate_race_clan_options()
        job_line.addWidget(QLabel("IL下限"))
        job_line.addWidget(self.item_il_min)
        job_line.addWidget(QLabel("IL上限"))
        job_line.addWidget(self.item_il_max)
        job_line.addWidget(QLabel("PTボーナス"))
        job_line.addWidget(self.party_bonus)
        job_line.addWidget(QLabel("CRT補正"))
        job_line.addWidget(self.crit_rate_adjust_spin)
        job_line.addWidget(QLabel("DH補正"))
        job_line.addWidget(self.dhit_rate_adjust_spin)
        sync_line.addWidget(self.chk_level_sync)
        sync_line.addWidget(QLabel("シンクIL"))
        sync_line.addWidget(self.level_sync_il)
        sync_line.addWidget(QLabel("シンクLv"))
        sync_line.addWidget(self.level_sync_level_combo)
        sync_line.addWidget(QLabel("目標GCD"))
        sync_line.addWidget(self.input_target_gcd)
        self.chk_log_gcd_constraint = QCheckBox("ログGCD維持")
        self.chk_log_gcd_constraint.setChecked(True)
        self.chk_log_gcd_constraint.setEnabled(False)
        self.chk_log_gcd_constraint.setToolTip("ログ実測GCDと同じ0.01秒段階の候補だけを探索します")
        self.chk_log_gcd_constraint.toggled.connect(self._schedule_auto_score_update)
        sync_line.addWidget(self.chk_log_gcd_constraint)
        self.log_gcd_status_label = QLabel("ログGCD: 未取得")
        self.log_gcd_status_label.setToolTip("キャスト取得後に実測GCDを推定します")
        sync_line.addWidget(self.log_gcd_status_label)

        self.food_combo = QComboBox()
        self.food_combo.addItem("食事なし（固定）", None)
        self.food_combo.addItem("食事をシミュレーション", FOOD_SIMULATION_DATA)
        self.food_combo.setToolTip(
            "食事なしは食事を使わず固定します。食事をシミュレーションは最高IL帯の戦闘食を比較します。"
        )
        self.food_combo.currentIndexChanged.connect(self._on_food_combo_changed)
        self.food_il_min = QSpinBox()
        self.food_il_min.setRange(1, 9999)
        self.food_il_min.setValue(1)
        self.food_il_max = QSpinBox()
        self.food_il_max.setRange(1, 9999)
        self.food_il_max.setValue(9999)
        self.food_il_min.valueChanged.connect(self.refresh_food_combo)
        self.food_il_max.valueChanged.connect(self.refresh_food_combo)

        gear_group = QGroupBox("装備セット編集")
        gear_group.setMinimumHeight(0)
        gear_layout = QGridLayout()
        self.slot_tables = {}
        gear_layout.addWidget(self._create_slot_group("weapon", SLOT_LABELS.get("weapon", "武器")), 0, 0)
        gear_layout.addWidget(self._create_slot_group("offhand", SLOT_LABELS.get("offhand", "サブ武器")), 0, 1)
        gear_layout.addWidget(self._create_slot_group("head", SLOT_LABELS.get("head", "頭")), 1, 0)
        gear_layout.addWidget(self._create_slot_group("earrings", SLOT_LABELS.get("earrings", "耳")), 1, 1)
        gear_layout.addWidget(self._create_slot_group("body", SLOT_LABELS.get("body", "胴")), 2, 0)
        gear_layout.addWidget(self._create_slot_group("necklace", SLOT_LABELS.get("necklace", "首")), 2, 1)
        gear_layout.addWidget(self._create_slot_group("hands", SLOT_LABELS.get("hands", "手")), 3, 0)
        gear_layout.addWidget(self._create_slot_group("bracelet", SLOT_LABELS.get("bracelet", "腕")), 3, 1)
        gear_layout.addWidget(self._create_slot_group("legs", SLOT_LABELS.get("legs", "脚")), 4, 0)
        gear_layout.addWidget(self._create_slot_group("ring1", SLOT_LABELS.get("ring1", "指輪1")), 4, 1)
        gear_layout.addWidget(self._create_slot_group("feet", SLOT_LABELS.get("feet", "足")), 5, 0)
        gear_layout.addWidget(self._create_slot_group("ring2", SLOT_LABELS.get("ring2", "指輪2")), 5, 1)
        gear_group.setLayout(gear_layout)

        self.note_edit = QTextEdit()
        self.note_edit.setPlaceholderText("メモ（任意）")
        self.note_edit.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)

        self.btn_calculate = QPushButton("計算")
        self.btn_calculate.clicked.connect(self.on_calculate)
        self.btn_optimize = QPushButton("マテリア＋食事を最適化")
        self.btn_optimize.clicked.connect(self.on_optimize)
        self.calc_mode = QComboBox()
        self.calc_mode.addItem("試算DPS（logs基準）", "simdps_self")
        self.calc_mode.addItem("XiVGear（Dmg/100p）", "dmg100p")
        self.calc_mode.currentIndexChanged.connect(self._schedule_auto_score_update)
        self.calc_mode.currentIndexChanged.connect(self._refresh_log_gcd_ui)

        saved_group = QGroupBox("保存セット")
        saved_group.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Ignored)
        saved_group.setMinimumHeight(saved_group.fontMetrics().height() + 12)
        saved_layout = QVBoxLayout()
        self.saved_sets_table = QTableWidget(0, 16)
        if hasattr(self.saved_sets_table, "setUniformRowHeights"):
            self.saved_sets_table.setUniformRowHeights(True)
        self.saved_sets_table.setHorizontalHeaderLabels(
            ["", "鍵", "セット名", "モード", "スコア", "期待値スコア", "GCD", "WD", "HP", "MAIN", "CRT", "DHT", "DET", "SPS", "食事", "出力"]
        )
        self.saved_sets_table.verticalHeader().setVisible(False)
        self.saved_sets_table.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.saved_sets_table.setSelectionMode(QAbstractItemView.SingleSelection)
        self.saved_sets_table.setDragEnabled(True)
        self.saved_sets_table.setAcceptDrops(True)
        self.saved_sets_table.setDropIndicatorShown(True)
        self.saved_sets_table.setDragDropMode(QAbstractItemView.InternalMove)
        self.saved_sets_table.setDefaultDropAction(Qt.MoveAction)
        self.saved_sets_table.setDragDropOverwriteMode(False)
        self.saved_sets_table.setEditTriggers(
            QAbstractItemView.DoubleClicked | QAbstractItemView.EditKeyPressed
        )
        self.saved_sets_table.horizontalHeader().setDefaultAlignment(Qt.AlignLeft | Qt.AlignVCenter)
        self._saved_set_name_col_width = max(
            100,
            self.saved_sets_table.fontMetrics().horizontalAdvance("あ" * 6) + 24,
        )
        for col in range(16):
            if col in {SAVED_COL_HANDLE, SAVED_COL_LOCK, SAVED_COL_EXPORT}:
                mode = QHeaderView.Fixed
            elif col == SAVED_COL_NAME:
                mode = QHeaderView.Interactive
            else:
                mode = QHeaderView.ResizeToContents
            self.saved_sets_table.horizontalHeader().setSectionResizeMode(col, mode)
        self.saved_sets_table.horizontalHeader().setMinimumSectionSize(24)
        self.saved_sets_table.horizontalHeader().setStretchLastSection(False)
        self.saved_sets_table.setColumnWidth(SAVED_COL_HANDLE, 30)
        self.saved_sets_table.setColumnWidth(SAVED_COL_LOCK, 56)
        self.saved_sets_table.setColumnWidth(SAVED_COL_NAME, self._saved_set_name_col_width)
        self.saved_sets_table.setColumnWidth(SAVED_COL_EXPORT, 48)
        self.saved_sets_table.itemSelectionChanged.connect(self.on_saved_set_selected)
        self.saved_sets_table.itemChanged.connect(self.on_saved_set_item_changed)
        self.saved_sets_table.cellClicked.connect(self.on_saved_set_cell_clicked)
        self.saved_sets_table.setContextMenuPolicy(Qt.CustomContextMenu)
        self.saved_sets_table.customContextMenuRequested.connect(self.on_saved_set_context_menu)
        model = self.saved_sets_table.model()
        if model is not None:
            model.rowsAboutToBeMoved.connect(self._on_saved_sets_rows_about_to_move)
            model.rowsMoved.connect(self._on_saved_sets_rows_moved)
        self.saved_sets_table.setMinimumHeight(self._table_min_height(self.saved_sets_table, 2))
        saved_layout.addWidget(self.saved_sets_table)
        self.saved_section_drag_bar = SplitterDragBar()
        saved_layout.addWidget(self.saved_section_drag_bar)
        saved_group.setLayout(saved_layout)
        self.btn_save_set = QPushButton("保存セットに追加")
        self.btn_save_set.clicked.connect(self.on_save_set_to_history)
        self.btn_import_xivgear_clipboard = QPushButton("jsonをｸﾘｯﾌﾟﾎﾞｰﾄﾞからｲﾝﾎﾟｰﾄ(XIVGear)")
        self.btn_import_xivgear_clipboard.clicked.connect(self.on_import_xivgear_clipboard)
        self.party_synergy_checks = {}
        self.party_synergy_defs = [
            ("dnc", "踊"), ("brd", "詩"), ("drg", "竜"),
            ("mnk", "モ"), ("rpr", "リ"), ("nin", "忍"),
            ("rdm", "赤"), ("pct", "ピ"),
            ("ast", "占"), ("sch", "学"),
        ]
        job_line.addWidget(QLabel("食事"))
        job_line.addWidget(self.food_combo)
        self.party_synergy_menu = PersistentCheckMenu(self)
        for key, text in self.party_synergy_defs:
            action = self.party_synergy_menu.addAction(text)
            action.setCheckable(True)
            action.toggled.connect(self._on_party_synergy_changed)
            self.party_synergy_checks[key] = action
        self.party_synergy_button = QToolButton()
        self.party_synergy_button.setPopupMode(QToolButton.InstantPopup)
        self.party_synergy_button.setMenu(self.party_synergy_menu)
        self.party_synergy_button.setToolButtonStyle(Qt.ToolButtonTextOnly)
        # Reserve about 6 full-width chars + arrow/padding.
        synergy_width = self.fontMetrics().horizontalAdvance("あ" * 6) + 36
        self.party_synergy_button.setMinimumWidth(max(90, synergy_width))
        job_line.addWidget(QLabel("PTシナジー"))
        job_line.addWidget(self.party_synergy_button)
        self.chk_gear_search_mode = QCheckBox("装備シミュレーション")
        self.chk_gear_search_mode.setChecked(False)
        self.chk_gear_search_mode.setToolTip("ON の場合は装備・マテリア・食事をまとめて探索します")
        self.chk_gear_search_mode.toggled.connect(self._on_gear_search_mode_toggled)
        job_line.addWidget(self.chk_gear_search_mode)
        sync_line.addWidget(QLabel("評価モード"))
        sync_line.addWidget(self.calc_mode)
        sync_line.addWidget(self.btn_save_set)
        sync_line.addWidget(self.btn_import_xivgear_clipboard)
        self._refresh_party_synergy_ui()
        top_controls = QVBoxLayout()
        top_controls.setContentsMargins(0, 0, 0, 0)
        top_controls.setSpacing(4)
        top_controls.addLayout(job_line)
        top_controls.addLayout(sync_line)
        layout.addLayout(top_controls)
        # 追加は後で行う
        gear_scroll = QScrollArea()
        gear_scroll.setWidgetResizable(True)
        gear_scroll.setFrameShape(QFrame.NoFrame)
        gear_scroll.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Ignored)
        gear_scroll.setMinimumHeight(gear_group.fontMetrics().height() + 12)
        gear_scroll.setWidget(gear_group)

        calc_line = QHBoxLayout()
        calc_line.addWidget(self.btn_calculate)
        calc_line.addWidget(self.btn_optimize)
        self._update_optimize_button_text()

        gear_container = QWidget()
        gear_container.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Ignored)
        gear_container_layout = QVBoxLayout(gear_container)
        gear_container_layout.setContentsMargins(0, 0, 0, 0)
        gear_container_layout.addWidget(gear_scroll, stretch=1)
        self.optimal_variant_tabs = QTabBar()
        self.optimal_variant_tabs.setDocumentMode(True)
        self.optimal_variant_tabs.setDrawBase(False)
        self.optimal_variant_tabs.setUsesScrollButtons(True)
        self.optimal_variant_tabs.setExpanding(False)
        self.optimal_variant_tabs.setVisible(False)
        self.optimal_variant_tabs.currentChanged.connect(self._on_optimal_variant_tab_changed)
        gear_container_layout.addWidget(self.optimal_variant_tabs)
        gear_container_layout.addLayout(calc_line)

        memo_group = QGroupBox("メモ")
        memo_group.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Ignored)
        memo_group.setMinimumHeight(memo_group.fontMetrics().height() + 12)
        memo_layout = QVBoxLayout()
        self.memo_section_drag_bar = SplitterDragBar()
        memo_layout.addWidget(self.memo_section_drag_bar)
        memo_layout.addWidget(self.note_edit)
        memo_group.setLayout(memo_layout)

        section_splitter = QSplitter(Qt.Vertical)
        section_splitter.setChildrenCollapsible(True)
        section_splitter.addWidget(saved_group)
        section_splitter.addWidget(gear_container)
        section_splitter.addWidget(memo_group)
        section_splitter.setStretchFactor(0, 2)
        section_splitter.setStretchFactor(1, 5)
        section_splitter.setStretchFactor(2, 1)
        self.section_splitter = section_splitter
        self.saved_section_drag_bar.set_target(section_splitter, 1)
        self.memo_section_drag_bar.set_target(section_splitter, 2)

        layout.addWidget(section_splitter, stretch=1)
        return panel

    def _create_slot_group(self, slot: str, title: str) -> QGroupBox:
        group = QGroupBox(title)
        layout = QVBoxLayout()
        header = QHBoxLayout()
        chk_lock_item = QCheckBox("装備固定")
        chk_lock_item.toggled.connect(lambda _checked, s=slot: self._on_slot_lock_toggled(s))
        self.slot_lock_item_checks[slot] = chk_lock_item
        header.addWidget(chk_lock_item)
        chk_lock_materia = QCheckBox("マテリア固定")
        chk_lock_materia.toggled.connect(lambda _checked, s=slot: self._on_slot_lock_toggled(s))
        self.slot_lock_materia_checks[slot] = chk_lock_materia
        header.addWidget(chk_lock_materia)
        header.addStretch(1)
        exclude_label = QToolButton()
        exclude_label.setText("除外: 0")
        exclude_label.setAutoRaise(True)
        exclude_label.setCursor(Qt.PointingHandCursor)
        exclude_label.setToolTip("クリックして除外装備一覧を表示")
        exclude_label.clicked.connect(
            lambda _checked=False, s=slot: self._show_excluded_slot_items_dialog(s)
        )
        self.slot_exclude_labels[slot] = exclude_label
        header.addWidget(exclude_label)
        layout.addLayout(header)
        table = QTableWidget()
        if hasattr(table, "setUniformRowHeights"):
            table.setUniformRowHeights(True)
        table.setColumnCount(8)
        table.verticalHeader().setVisible(False)
        table.setSelectionBehavior(QAbstractItemView.SelectRows)
        table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        table.horizontalHeader().setDefaultAlignment(Qt.AlignLeft | Qt.AlignVCenter)
        table.horizontalHeader().setMinimumSectionSize(48)
        for col in range(8):
            mode = QHeaderView.Stretch if col == 1 else QHeaderView.ResizeToContents
            table.horizontalHeader().setSectionResizeMode(col, mode)
        table.setMinimumHeight(self._table_min_height(table, 3))
        table.itemSelectionChanged.connect(lambda s=slot, t=table: self.on_slot_table_selected(s, t))
        table.setContextMenuPolicy(Qt.CustomContextMenu)
        table.customContextMenuRequested.connect(
            lambda pos, s=slot, t=table: self.on_slot_table_context_menu(s, t, pos)
        )
        layout.addWidget(table)
        chip_container = QWidget()
        chip_layout = QHBoxLayout()
        chip_layout.setContentsMargins(0, 0, 0, 0)
        chip_container.setLayout(chip_layout)
        chip_container.setMinimumHeight(30)
        if not hasattr(self, "slot_materia_layouts"):
            self.slot_materia_layouts = {}
        self.slot_materia_layouts[slot] = chip_layout
        layout.addWidget(chip_container)
        group.setLayout(layout)
        self.slot_tables[slot] = table
        return group

    def on_slot_table_selected(self, slot: str, table: QTableWidget) -> None:
        if self._applying_gearset or self._is_populating:
            return
        self._clear_optimal_variant_tabs()
        row = table.currentRow()
        if row < 0:
            return
        item_cell = table.item(row, 0)
        if not item_cell:
            return
        item_id = self._resolve_slot_row_item_id(slot, table, row)
        if not item_id:
            return
        duplicate_slot = self._duplicate_unique_ring_slot(slot, item_id)
        if duplicate_slot is not None:
            other_label = SLOT_LABELS.get(duplicate_slot, duplicate_slot)
            QMessageBox.information(
                self,
                "ユニーク装備",
                f"この装備は unique のため、{other_label} と重複して設定できません。",
            )
            previous_sel = (self.current_gearset.items or {}).get(slot) or ItemSelection()
            self._select_table_row(table, previous_sel.item_id)
            return
        sel = self.current_gearset.items.get(slot) or ItemSelection()
        if sel.item_id != item_id:
            sel.item_id = item_id
            sel.materia = []
            sel.relic_stats = {}
            self.current_gearset.items[slot] = sel
            self._clear_export_item_override(slot)
            self._sync_selected_saved_set_ui_context()
        self._refresh_slot_selected_display(slot)
        self._schedule_auto_score_update()

    def on_slot_table_context_menu(self, slot: str, table: QTableWidget, pos) -> None:
        if self._applying_gearset or self._is_populating:
            return
        viewport_pos = pos
        if not table.viewport().rect().contains(viewport_pos):
            viewport_pos = table.viewport().mapFrom(table, pos)
        item = table.itemAt(viewport_pos)
        if not item:
            return
        row = item.row()
        if row < 1:
            return
        if table.currentRow() != row:
            blocker = QSignalBlocker(table)
            table.setCurrentCell(row, 0)
            del blocker
        menu = QMenu(table)
        is_compressed = self._is_compressed_table_row(table, row)
        row_member_ids = self._row_member_ids_for_exclusion(table, row)
        is_excluded = bool(row_member_ids) and all(
            item_id in self._slot_excluded_item_id_set(slot) for item_id in row_member_ids
        )
        if is_compressed:
            member_ids = self._compressed_row_member_ids(table, row)
            if len(member_ids) <= 1:
                return
            action_grouped = menu.addAction("まとめ装備一覧を表示")
            action_exclude = menu.addAction(
                "検索時除外を解除" if is_excluded else "検索時除外"
            )
            chosen = menu.exec(table.viewport().mapToGlobal(viewport_pos))
            if chosen is action_grouped:
                self._show_grouped_slot_items_dialog(slot, member_ids)
            elif chosen is action_exclude:
                self._toggle_slot_item_exclusion(slot, member_ids, exclude=not is_excluded)
            return
        item_id = self._table_row_item_id(table, row)
        if not item_id:
            return
        action_search = menu.addAction("FF14公式DBで検索")
        action_exclude = menu.addAction("検索時除外を解除" if is_excluded else "検索時除外")
        chosen = menu.exec(table.viewport().mapToGlobal(viewport_pos))
        if chosen is action_search:
            self._open_official_db_search_for_item(item_id)
        elif chosen is action_exclude:
            self._toggle_slot_item_exclusion(slot, [item_id], exclude=not is_excluded)

    # ---- Task helpers ----
    def start_worker(
        self,
        fn,
        finished_cb,
        silent_if_busy: bool = False,
        lock_fflogs_context: bool = False,
        lock_job_context: bool = False,
        **kwargs,
    ) -> bool:
        if self.active_worker:
            if not silent_if_busy and not self._suppress_busy_dialog:
                QMessageBox.warning(self, "実行中", "別の処理が動作中です。")
            return False
        worker = Worker(fn, **kwargs)
        self.active_worker = worker
        if lock_fflogs_context:
            self._set_fflogs_context_enabled(False)
            self._fflogs_context_locked = True
        if lock_job_context:
            self._set_job_context_enabled(False)
            self._job_context_locked = True
        worker.kwargs.setdefault("progress", worker.signals.progress.emit)
        worker.signals.finished.connect(
            lambda res: self._on_worker_finished(finished_cb, res), Qt.QueuedConnection
        )
        worker.signals.error.connect(self.on_worker_error, Qt.QueuedConnection)
        worker.signals.cancelled.connect(self.on_worker_cancelled, Qt.QueuedConnection)
        worker.signals.progress.connect(self.update_progress, Qt.QueuedConnection)
        self.btn_cancel.setEnabled(True)
        self.btn_cancel.setVisible(True)
        try:
            self.thread_pool.start(worker)
        except Exception as exc:
            self.active_worker = None
            self.btn_cancel.setEnabled(False)
            self.btn_cancel.setVisible(False)
            self._unlock_fflogs_context()
            self._unlock_job_context()
            logger.exception("Failed to start background worker")
            if not self._closing:
                QMessageBox.critical(
                    self,
                    "開始エラー",
                    f"バックグラウンド処理を開始できませんでした: {type(exc).__name__}",
                )
            return False
        return True

    def _schedule_saved_sets_flush(self, immediate: bool = False) -> None:
        self._saved_sets_dirty = True
        if immediate:
            self._saved_sets_flush_timer.stop()
            self._flush_saved_sets()
            return
        self._saved_sets_flush_timer.start(500)

    def _flush_saved_sets(self) -> bool:
        if not self._saved_sets_dirty:
            return True
        try:
            save_saved_sets({"version": 1, "items": self.saved_sets})
        except Exception as exc:
            logger.exception("Failed to save saved sets")
            if hasattr(self, "progress_label"):
                self.progress_label.setText(f"保存セットの保存に失敗しました: {type(exc).__name__}")
            return False
        self._saved_sets_dirty = False
        return True

    def _on_worker_finished(self, cb, result) -> None:
        self.active_worker = None
        self.btn_cancel.setEnabled(False)
        self.btn_cancel.setVisible(False)
        if self._closing:
            return
        callback_error = None
        try:
            if cb:
                self.update_progress(-1, "結果を反映中...")
                cb(result)
        except Exception:
            callback_error = traceback.format_exc()
        finally:
            self._unlock_fflogs_context()
            self._unlock_job_context()
        if callback_error is not None:
            self.on_worker_error(callback_error)
            return
        self._finish_worker_progress()
        # 保存セット用の装備データ読み込みが待機中なら開始
        if not self.active_worker:
            self._start_saved_jobs_load()
        if (not self.active_worker) and self._pending_phase_request:
            report_code, fight = self._pending_phase_request
            self._pending_phase_request = None
            self._load_phases_for_fight(report_code, fight)
        if (not self.active_worker) and self._pending_gearset and self._pending_gearset.job in self.items_by_job:
            gear = self._pending_gearset
            self._pending_gearset = None
            self._apply_gearset_to_ui(gear)
        if self._pending_score_after_worker:
            self._pending_score_after_worker = False
            self._schedule_auto_score_update()

    def _set_progress_bar_state(self, bar: QProgressBar, value: int) -> None:
        if value < 0:
            if bar.minimum() != 0 or bar.maximum() != 0:
                bar.setRange(0, 0)
            return
        if bar.minimum() == 0 and bar.maximum() == 0:
            bar.setRange(0, 100)
        bar.setValue(max(0, min(100, int(value))))

    def _set_detail_progress(self, value: int, message: str) -> None:
        self._set_progress_bar_state(self.progress_detail_bar, value)
        detail_text = str(message or "").strip() or "-"
        self.progress_detail_label.setText(detail_text)

    def _reset_detail_progress(self) -> None:
        self._set_progress_bar_state(self.progress_detail_bar, 0)
        self.progress_detail_label.setText("-")

    def _finish_worker_progress(self) -> None:
        completion_text = str(self.progress_label.text() or "").strip()
        if not completion_text or completion_text == "結果を反映中...":
            self.update_progress(0, "待機中")
            return
        self._set_progress_bar_state(self.progress_bar, 100)
        self._set_detail_progress(100, completion_text)

    def _parse_progress_update(
        self,
        message: str,
    ) -> Tuple[str, Optional[int], Optional[str]]:
        text, detail_value, detail_message = decode_progress_message(message)
        if detail_value is not None or detail_message:
            return text, detail_value, detail_message
        match = re.match(
            r"^(?P<label>.+?)\s+(?P<current>\d+)/(?P<total>\d+)(?::\s*(?P<extra>.+))?$",
            text.strip(),
        )
        if not match:
            return text, None, None
        try:
            current = int(match.group("current"))
            total = max(1, int(match.group("total")))
        except Exception:
            return text, None, None
        detail_pct = int((max(0, min(total, current)) / total) * 100)
        detail_label = (match.group("extra") or match.group("label") or "").strip() or None
        return text, detail_pct, detail_label

    def update_progress(self, value: int, message: str) -> None:
        text, detail_value, detail_message = self._parse_progress_update(message)
        self._set_progress_bar_state(self.progress_bar, value)
        overall_text = str(text or "").strip() or "待機中"
        self.progress_label.setText(overall_text)
        if detail_value is not None or detail_message:
            effective_detail = detail_value if detail_value is not None else -1
            self._set_detail_progress(effective_detail, detail_message or overall_text)
        elif value == 0 and overall_text == "待機中":
            self._reset_detail_progress()
        elif value < 0:
            self._set_detail_progress(-1, overall_text)
        else:
            self._set_detail_progress(-1, overall_text)

    def on_worker_error(self, trace: str) -> None:
        self.active_worker = None
        self.btn_cancel.setEnabled(False)
        self.btn_cancel.setVisible(False)
        if self._closing:
            return
        self._unlock_fflogs_context()
        self._unlock_job_context()
        QMessageBox.critical(self, "エラー", trace)
        self.update_progress(0, "待機中")
        if not self.active_worker:
            self._start_saved_jobs_load()
        if (not self.active_worker) and self._pending_phase_request:
            report_code, fight = self._pending_phase_request
            self._pending_phase_request = None
            self._load_phases_for_fight(report_code, fight)
        if (not self.active_worker) and self._pending_gearset and self._pending_gearset.job in self.items_by_job:
            gear = self._pending_gearset
            self._pending_gearset = None
            self._apply_gearset_to_ui(gear)
        if self._pending_score_after_worker:
            self._pending_score_after_worker = False
            self._schedule_auto_score_update()

    def on_worker_cancelled(self) -> None:
        self.active_worker = None
        self.btn_cancel.setEnabled(False)
        self.btn_cancel.setVisible(False)
        if self._closing:
            return
        self._unlock_fflogs_context()
        self._unlock_job_context()
        self._pending_phase_request = None
        self._pending_gearset = None
        self._pending_saved_set_entry = None
        self._pending_saved_set_ui_context = None
        self._pending_score_after_worker = False
        self._set_progress_bar_state(self.progress_bar, 0)
        self.progress_label.setText("キャンセルしました")
        self._reset_detail_progress()
        if not self.active_worker:
            self._start_saved_jobs_load()

    def on_cancel(self) -> None:
        if self.active_worker:
            self.active_worker.cancel()
            self.progress_label.setText("キャンセル中...")
            self.btn_cancel.setEnabled(False)

    def _set_fflogs_context_enabled(self, enabled: bool) -> None:
        for name in ("input_report_code", "fight_list", "actor_list", "phase_list"):
            widget = getattr(self, name, None)
            if widget is not None:
                widget.setEnabled(enabled)

    def _unlock_fflogs_context(self) -> None:
        if self._fflogs_context_locked:
            self._set_fflogs_context_enabled(True)
            self._fflogs_context_locked = False

    def _set_job_context_enabled(self, enabled: bool) -> None:
        job_combo = getattr(self, "job_combo", None)
        if job_combo is not None:
            job_combo.setEnabled(enabled)

    def _unlock_job_context(self) -> None:
        if self._job_context_locked:
            self._set_job_context_enabled(True)
            self._job_context_locked = False

    # ---- Auth persistence ----
    def _apply_debug_mode(self, enabled: bool) -> None:
        if enabled:
            os.environ["GEARSIM_DEBUG"] = "1"
        else:
            os.environ.pop("GEARSIM_DEBUG", None)

    def on_debug_mode_toggled(self, checked: bool) -> None:
        self._apply_debug_mode(bool(checked))
        self.on_save_auth(silent=True)
        self.progress_label.setText("Debugモードを更新しました")

    def _icon_display_enabled(self) -> bool:
        if hasattr(self, "chk_icon_display"):
            return bool(self.chk_icon_display.isChecked())
        return True

    def _item_icon_prefetch_visible_only(self) -> bool:
        if hasattr(self, "chk_icon_prefetch_visible_only"):
            return bool(self.chk_icon_prefetch_visible_only.isChecked())
        return True

    def _gear_search_enabled(self) -> bool:
        if hasattr(self, "chk_gear_search_mode"):
            return bool(self.chk_gear_search_mode.isChecked())
        return False

    def _optimization_worker_preference(self) -> int:
        if not hasattr(self, "optimize_worker_combo"):
            return 0
        try:
            return max(
                0,
                min(
                    optimizer.MAX_OPTIMIZATION_WORKERS,
                    int(self.optimize_worker_combo.currentData() or 0),
                ),
            )
        except (TypeError, ValueError):
            return 0

    def _optimization_worker_count(self) -> int:
        preference = self._optimization_worker_preference()
        return preference or optimizer.recommended_optimization_workers()

    def _on_optimize_worker_changed(self, _index: int) -> None:
        self.on_save_auth(silent=True)
        self.progress_label.setText(
            f"CPU並列数を更新しました（実行時 {self._optimization_worker_count()}プロセス）"
        )

    def _slot_item_lock_enabled(self, slot: str) -> bool:
        checkbox = self.slot_lock_item_checks.get(slot)
        return bool(checkbox and checkbox.isChecked())

    def _slot_materia_lock_enabled(self, slot: str) -> bool:
        checkbox = self.slot_lock_materia_checks.get(slot)
        return bool(checkbox and checkbox.isChecked())

    def _duplicate_unique_ring_slot(
        self,
        slot: str,
        item_id: Optional[int],
        gearset: Optional[Gearset] = None,
    ) -> Optional[str]:
        if slot not in {"ring1", "ring2"} or not item_id:
            return None
        item = self.items_by_id.get(int(item_id))
        if not item or not bool(getattr(item, "unique", False)):
            return None
        other_slot = "ring1" if slot == "ring2" else "ring2"
        target_gearset = gearset or self.current_gearset
        other_sel = (target_gearset.items or {}).get(other_slot) or ItemSelection()
        other_item_id = int(other_sel.item_id or 0) if other_sel.item_id else 0
        if other_item_id == int(item_id):
            return other_slot
        return None

    def _normalized_export_item_ids(self, raw_ids: Optional[dict]) -> Dict[str, int]:
        return normalized_export_item_ids(raw_ids, self.items_by_id)

    def _clear_export_item_override(self, slot: str) -> None:
        if slot in self._current_export_item_ids:
            self._current_export_item_ids.pop(slot, None)

    def _duplicate_unique_ring_slot_for_export(
        self,
        slot: str,
        item_id: Optional[int],
        gearset: Optional[Gearset] = None,
        export_item_ids: Optional[Dict[str, int]] = None,
    ) -> Optional[str]:
        target_gearset = gearset or self.current_gearset
        export_ids = export_item_ids or self._current_export_item_ids
        return duplicate_unique_ring_slot_for_export(
            slot,
            item_id,
            self.items_by_id,
            target_gearset,
            export_ids,
        )

    def _export_item_ids_for_capture(self, gearset: Optional[Gearset] = None) -> Dict[str, int]:
        target_gearset = gearset or self.current_gearset
        normalized = self._normalized_export_item_ids(self._current_export_item_ids)
        captured: Dict[str, int] = {}
        for slot, item_id in normalized.items():
            if self._duplicate_unique_ring_slot_for_export(slot, item_id, target_gearset, normalized) is not None:
                continue
            current_sel = (target_gearset.items or {}).get(slot) or ItemSelection()
            current_item_id = int(current_sel.item_id or 0) if current_sel.item_id else 0
            if current_item_id == item_id:
                continue
            captured[slot] = item_id
        return captured

    def _normalize_unique_ring_duplicates(self, gear: Gearset) -> Gearset:
        if not gear or not getattr(gear, "items", None):
            return gear
        seen_unique: set = set()
        for slot in ("ring1", "ring2"):
            sel = (gear.items or {}).get(slot)
            if not sel or not sel.item_id:
                continue
            item_id = int(sel.item_id or 0)
            item = self.items_by_id.get(item_id)
            if not item or not bool(getattr(item, "unique", False)):
                continue
            if item_id in seen_unique:
                sel.item_id = None
                sel.materia = []
                sel.lock_item = False
                sel.lock_materia = False
                gear.items[slot] = sel
                continue
            seen_unique.add(item_id)
        return gear

    def _slot_excluded_item_ids(self, slot: str) -> List[int]:
        sel = (self.current_gearset.items or {}).get(slot) or ItemSelection()
        seen: set = set()
        excluded_ids: List[int] = []
        for value in list(getattr(sel, "excluded_item_ids", []) or []):
            try:
                item_id = int(value or 0)
            except Exception:
                continue
            if item_id <= 0 or item_id in seen:
                continue
            seen.add(item_id)
            excluded_ids.append(item_id)
        return excluded_ids

    def _slot_excluded_item_id_set(self, slot: str) -> set[int]:
        return set(self._slot_excluded_item_ids(slot))

    def _dedupe_item_ids(self, values: List[int]) -> List[int]:
        seen: set[int] = set()
        member_ids: List[int] = []
        for value in values:
            try:
                item_id = int(value or 0)
            except Exception:
                continue
            if item_id <= 0 or item_id in seen:
                continue
            seen.add(item_id)
            member_ids.append(item_id)
        return member_ids

    def _row_member_ids_for_exclusion(self, table: QTableWidget, row: int) -> List[int]:
        if row < 0:
            return []
        member_ids = self._compressed_row_member_ids(table, row)
        if member_ids:
            return member_ids
        item_id = self._table_row_item_id(table, row)
        return [item_id] if item_id else []

    def _resolve_slot_row_item_id(self, slot: str, table: QTableWidget, row: int) -> Optional[int]:
        member_ids = self._dedupe_item_ids(self._row_member_ids_for_exclusion(table, row))
        if not member_ids:
            return None
        current_sel = (self.current_gearset.items or {}).get(slot) or ItemSelection()
        current_item_id = int(current_sel.item_id or 0) if current_sel.item_id else 0
        if current_item_id in member_ids and self._duplicate_unique_ring_slot(slot, current_item_id) is None:
            return current_item_id
        for candidate_id in member_ids:
            if self._duplicate_unique_ring_slot(slot, candidate_id) is None:
                return int(candidate_id)
        return int(member_ids[0])

    def _set_row_excluded_style(self, table: QTableWidget, row: int, excluded: bool) -> None:
        for col in range(table.columnCount()):
            cell = table.item(row, col)
            if not cell:
                continue
            font = cell.font()
            if font.strikeOut() != excluded:
                font.setStrikeOut(excluded)
                cell.setFont(font)

    def _refresh_slot_exclusion_visuals(self, slot: str) -> None:
        label = self.slot_exclude_labels.get(slot)
        excluded_ids = self._slot_excluded_item_id_set(slot)
        if label is not None:
            label.setText(f"除外: {len(excluded_ids)}")
            label.setEnabled(bool(excluded_ids))
        table = self.slot_tables.get(slot)
        if table is None:
            return
        for row in range(table.rowCount()):
            member_ids = self._row_member_ids_for_exclusion(table, row)
            excluded = bool(member_ids) and all(item_id in excluded_ids for item_id in member_ids)
            self._set_row_excluded_style(table, row, excluded)

    def _refresh_all_slot_exclusion_visuals(self) -> None:
        for slot in self.slot_tables.keys():
            self._refresh_slot_exclusion_visuals(slot)

    def _toggle_slot_item_exclusion(
        self,
        slot: str,
        item_ids: List[int],
        *,
        exclude: Optional[bool] = None,
    ) -> None:
        normalized_ids: List[int] = []
        seen: set = set()
        for value in item_ids:
            try:
                item_id = int(value or 0)
            except Exception:
                continue
            if item_id <= 0 or item_id in seen:
                continue
            seen.add(item_id)
            normalized_ids.append(item_id)
        if not normalized_ids:
            return
        self._clear_optimal_variant_tabs()
        sel = self.current_gearset.items.get(slot) or ItemSelection()
        current = self._slot_excluded_item_id_set(slot)
        if exclude is None:
            exclude = not all(item_id in current for item_id in normalized_ids)
        if exclude:
            current.update(normalized_ids)
        else:
            current.difference_update(normalized_ids)
        sel.excluded_item_ids = sorted(current)
        self.current_gearset.items[slot] = sel
        self._refresh_slot_exclusion_visuals(slot)
        self._persist_current_gearset_to_selected_saved_set()
        slot_label = SLOT_LABELS.get(slot, slot)
        self.progress_label.setText(
            f"{slot_label} の除外設定を更新しました"
        )

    def _on_slot_lock_toggled(self, slot: str) -> None:
        if self._applying_gearset or self._is_populating:
            return
        self._clear_optimal_variant_tabs()
        sel = self.current_gearset.items.get(slot) or ItemSelection()
        sel.lock_item = self._slot_item_lock_enabled(slot)
        sel.lock_materia = self._slot_materia_lock_enabled(slot)
        self.current_gearset.items[slot] = sel
        self._persist_current_gearset_to_selected_saved_set()
        self.progress_label.setText(
            f"{SLOT_LABELS.get(slot, slot)} の固定設定を更新しました"
        )

    def _persist_current_gearset_to_selected_saved_set(self) -> None:
        if self._saved_sets_reordering or not hasattr(self, "saved_sets_table"):
            return
        row = self.saved_sets_table.currentRow()
        if row < 0:
            return
        entry_item = self.saved_sets_table.item(row, SAVED_COL_NAME)
        entry = entry_item.data(Qt.UserRole) if entry_item else None
        if not isinstance(entry, dict) or bool(entry.get("locked", False)):
            return
        entry_id = entry.get("id")
        if entry_id is None:
            return
        target = None
        for saved in self.saved_sets:
            if isinstance(saved, dict) and saved.get("id") == entry_id:
                target = saved
                break
        if target is None:
            return
        gear_dict = self.current_gearset.to_dict()
        if target.get("gearset") == gear_dict:
            return
        target["gearset"] = gear_dict
        target["saved_at"] = utc_now_iso()
        entry.update(target)
        if entry_item:
            entry_item.setData(Qt.UserRole, entry)
        self._schedule_saved_sets_flush(immediate=False)

    def _show_materia_only_fixed_message(self) -> None:
        QMessageBox.information(self, "固定不可", "マテリアのみ固定できません。")

    def _validate_simulation_fixed_slots(self) -> bool:
        for slot in GEAR_SLOTS:
            sel = (self.current_gearset.items or {}).get(slot) or ItemSelection()
            if bool(getattr(sel, "lock_materia", False)) and not bool(getattr(sel, "lock_item", False)):
                self._show_materia_only_fixed_message()
                return False
            if bool(getattr(sel, "lock_item", False)) and not sel.item_id:
                QMessageBox.warning(
                    self,
                    "未選択",
                    f"{SLOT_LABELS.get(slot, slot)} を固定するには装備を選択してください。",
                )
                return False
        return True

    def _crit_rate_adjust_percent(self) -> int:
        if hasattr(self, "crit_rate_adjust_spin"):
            return int(self.crit_rate_adjust_spin.value())
        return 0

    def _dhit_rate_adjust_percent(self) -> int:
        if hasattr(self, "dhit_rate_adjust_spin"):
            return int(self.dhit_rate_adjust_spin.value())
        return 0

    def _crit_rate_adjust_value(self) -> float:
        return float(self._crit_rate_adjust_percent()) / 100.0

    def _dhit_rate_adjust_value(self) -> float:
        return float(self._dhit_rate_adjust_percent()) / 100.0

    def _eval_rate_adjust_kwargs(self) -> Dict[str, float]:
        return {
            "crit_rate_offset": self._crit_rate_adjust_value(),
            "dhit_rate_offset": self._dhit_rate_adjust_value(),
        }

    def _update_optimize_button_text(self) -> None:
        if not hasattr(self, "btn_optimize"):
            return
        base = "装備＋マテリア" if self._gear_search_enabled() else "マテリア"
        food_mode = (
            self.food_combo.currentData()
            if hasattr(self, "food_combo")
            else None
        )
        if food_mode == FOOD_SIMULATION_DATA:
            self.btn_optimize.setText(f"{base}＋食事を最適化")
        elif food_mode is None:
            self.btn_optimize.setText(f"{base}を最適化（食事なし）")
        else:
            self.btn_optimize.setText(f"{base}を最適化（食事固定）")

    def _on_icon_display_toggled(self, checked: bool) -> None:
        enabled = bool(checked)
        if hasattr(self, "chk_icon_prefetch_visible_only"):
            self.chk_icon_prefetch_visible_only.setEnabled(enabled)
        self._pending_item_icon_cells.clear()
        self._pending_icon_buttons.clear()
        self.on_save_auth(silent=True)
        job = self.job_combo.currentData() if hasattr(self, "job_combo") else None
        if not job:
            job = self.current_gearset.job
        if job and job in self.items_by_job:
            self.populate_items(job)
        self._refresh_all_slot_displays()
        self.progress_label.setText("アイコン表示設定を更新しました")

    def _on_icon_prefetch_mode_toggled(self, _checked: bool) -> None:
        self._prefetched_item_icon_urls.clear()
        self.on_save_auth(silent=True)
        if not self._icon_display_enabled():
            return
        job = self.job_combo.currentData() if hasattr(self, "job_combo") else None
        if not job:
            job = self.current_gearset.job
        if job and job in self.items_by_job:
            self.populate_items(job)
        self.progress_label.setText("アイコン先読み設定を更新しました")

    def _on_gear_search_mode_toggled(self, _checked: bool) -> None:
        self._update_optimize_button_text()
        self._sync_selected_saved_set_ui_context()
        self.on_save_auth(silent=True)
        mode_text = "装備込み" if self._gear_search_enabled() else "マテリア＋食事のみ"
        self.progress_label.setText(f"最適化対象を更新しました（{mode_text}）")

    def _on_rate_adjustment_changed(self, _value: int) -> None:
        self._sync_selected_saved_set_ui_context()
        self.on_save_auth(silent=True)
        self.progress_label.setText(
            f"CRT/DH補正を更新しました（CRT {self._crit_rate_adjust_percent():+d}% / DH {self._dhit_rate_adjust_percent():+d}%）"
        )
        self._schedule_auto_score_update()

    def _selected_party_synergies(self) -> Dict[str, bool]:
        checks = getattr(self, "party_synergy_checks", {}) or {}
        return {key: bool(cb.isChecked()) for key, cb in checks.items()}

    def _party_synergy_text(self) -> str:
        checks = getattr(self, "party_synergy_checks", {}) or {}
        defs = getattr(self, "party_synergy_defs", []) or []
        selected: List[str] = []
        for key, label in defs:
            item = checks.get(key)
            if item and item.isChecked():
                selected.append(label)
        return "".join(selected)

    def _refresh_party_synergy_ui(self) -> None:
        text = self._party_synergy_text()
        if hasattr(self, "party_synergy_button"):
            self.party_synergy_button.setText(text if text else "選択なし")

    def _set_party_synergies(self, data: Optional[Dict[str, bool]]) -> None:
        checks = getattr(self, "party_synergy_checks", {}) or {}
        values = data or {}
        for key, cb in checks.items():
            cb.blockSignals(True)
            cb.setChecked(bool(values.get(key, False)))
            cb.blockSignals(False)
        self._refresh_party_synergy_ui()

    def _on_party_synergy_changed(self, *_args) -> None:
        self._refresh_party_synergy_ui()
        self.on_save_auth(silent=True)
        self._schedule_auto_score_update()

    def _load_saved_auth(self) -> None:
        data = load_auth()
        if not data:
            if hasattr(self, "chk_debug_mode"):
                self._apply_debug_mode(self.chk_debug_mode.isChecked())
            if hasattr(self, "chk_icon_prefetch_visible_only"):
                self.chk_icon_prefetch_visible_only.setEnabled(self._icon_display_enabled())
            self.party_bonus.setValue(5)
            return
        debug_mode = data.get("debug_mode")
        if hasattr(self, "chk_debug_mode") and debug_mode is not None:
            self.chk_debug_mode.blockSignals(True)
            self.chk_debug_mode.setChecked(bool(debug_mode))
            self.chk_debug_mode.blockSignals(False)
            self._apply_debug_mode(bool(debug_mode))
        if hasattr(self, "input_client_id"):
            self.input_client_id.setText(data.get("client_id", ""))
        if hasattr(self, "input_client_secret"):
            self.input_client_secret.setText(data.get("client_secret", ""))
        icon_display = bool(data.get("icon_display_enabled", True))
        icon_visible_prefetch = bool(data.get("icon_prefetch_visible_only", True))
        gear_search_mode = bool(data.get("gear_search_mode", False))
        optimize_worker_count = int(data.get("optimize_worker_count", 0) or 0)
        crit_rate_adjust = int(data.get("crit_rate_adjust", 0) or 0)
        dhit_rate_adjust = int(data.get("dhit_rate_adjust", 0) or 0)
        if hasattr(self, "chk_icon_display"):
            self.chk_icon_display.blockSignals(True)
            self.chk_icon_display.setChecked(icon_display)
            self.chk_icon_display.blockSignals(False)
        if hasattr(self, "chk_icon_prefetch_visible_only"):
            self.chk_icon_prefetch_visible_only.blockSignals(True)
            self.chk_icon_prefetch_visible_only.setChecked(icon_visible_prefetch)
            self.chk_icon_prefetch_visible_only.setEnabled(icon_display)
            self.chk_icon_prefetch_visible_only.blockSignals(False)
        if hasattr(self, "chk_gear_search_mode"):
            self.chk_gear_search_mode.blockSignals(True)
            self.chk_gear_search_mode.setChecked(gear_search_mode)
            self.chk_gear_search_mode.blockSignals(False)
            self._update_optimize_button_text()
        if hasattr(self, "optimize_worker_combo"):
            self.optimize_worker_combo.blockSignals(True)
            worker_index = self.optimize_worker_combo.findData(optimize_worker_count)
            self.optimize_worker_combo.setCurrentIndex(max(0, worker_index))
            self.optimize_worker_combo.blockSignals(False)
        if hasattr(self, "crit_rate_adjust_spin"):
            self.crit_rate_adjust_spin.blockSignals(True)
            self.crit_rate_adjust_spin.setValue(max(-20, min(20, crit_rate_adjust)))
            self.crit_rate_adjust_spin.blockSignals(False)
        if hasattr(self, "dhit_rate_adjust_spin"):
            self.dhit_rate_adjust_spin.blockSignals(True)
            self.dhit_rate_adjust_spin.setValue(max(-20, min(20, dhit_rate_adjust)))
            self.dhit_rate_adjust_spin.blockSignals(False)
        self.input_report_code.setText(data.get("last_report", ""))
        client_id = data.get("client_id")
        client_secret = data.get("client_secret")
        if client_id and client_secret:
            self.ff_client.set_credentials(client_id, client_secret)
        self._pending_fight_id = data.get("last_fight_id")
        self._pending_actor_id = data.get("last_actor_id")
        self._set_race_clan(data.get("race"))
        self.party_bonus.setValue(int(data.get("party_bonus", 5)))
        level_sync_enabled = bool(data.get("level_sync_enabled", False))
        level_sync_il = int(data.get("level_sync_il", 730) or 730)
        level_sync_level = xivmath.normalize_supported_level(data.get("level_sync_level", xivmath.CURRENT_MAX_LEVEL))
        if hasattr(self, "chk_level_sync") and hasattr(self, "level_sync_il"):
            self.chk_level_sync.blockSignals(True)
            self.level_sync_il.blockSignals(True)
            if hasattr(self, "level_sync_level_combo"):
                self.level_sync_level_combo.blockSignals(True)
            self.chk_level_sync.setChecked(level_sync_enabled)
            self.level_sync_il.setValue(level_sync_il)
            self.level_sync_il.setEnabled(level_sync_enabled)
            if hasattr(self, "level_sync_level_combo"):
                idx = self.level_sync_level_combo.findData(level_sync_level)
                if idx != -1:
                    self.level_sync_level_combo.setCurrentIndex(idx)
                self.level_sync_level_combo.setEnabled(level_sync_enabled)
            self.chk_level_sync.blockSignals(False)
            self.level_sync_il.blockSignals(False)
            if hasattr(self, "level_sync_level_combo"):
                self.level_sync_level_combo.blockSignals(False)
        self.current_gearset.level = self._effective_calc_level()
        self._set_party_synergies(data.get("party_synergies"))
        self._apply_ui_state(data.get("ui_state"))
        self._restore_cached_report()

    def _show_pending_config_warnings(self) -> None:
        warnings = consume_config_warnings()
        if not warnings:
            return
        message = "\n".join(f"- {text}" for text in warnings)
        QTimer.singleShot(
            0,
            lambda msg=message: QMessageBox.warning(
                self,
                "設定ファイルを復旧しました",
                msg,
            ),
        )

    def on_save_auth(self, silent: bool = False) -> bool:
        data = {
            "client_id": self.input_client_id.text().strip() if hasattr(self, "input_client_id") else "",
            "client_secret": self.input_client_secret.text().strip() if hasattr(self, "input_client_secret") else "",
            "last_report": self.input_report_code.text().strip(),
            "race": self._current_race(),
            "party_bonus": self.party_bonus.value() if hasattr(self, "party_bonus") else 5,
            "level_sync_enabled": self.chk_level_sync.isChecked() if hasattr(self, "chk_level_sync") else False,
            "level_sync_il": self.level_sync_il.value() if hasattr(self, "level_sync_il") else 730,
            "level_sync_level": self._selected_sync_level_value(),
            "ui_state": self._collect_ui_state(),
            "debug_mode": self.chk_debug_mode.isChecked() if hasattr(self, "chk_debug_mode") else sim_debug_enabled(),
            "party_synergies": self._selected_party_synergies(),
            "icon_display_enabled": self._icon_display_enabled(),
            "icon_prefetch_visible_only": self._item_icon_prefetch_visible_only(),
            "gear_search_mode": self._gear_search_enabled(),
            "optimize_worker_count": self._optimization_worker_preference(),
            "crit_rate_adjust": self._crit_rate_adjust_percent(),
            "dhit_rate_adjust": self._dhit_rate_adjust_percent(),
        }
        if self.selected_fight:
            data["last_fight_id"] = self.selected_fight.get("id")
        if self.selected_actor:
            data["last_actor_id"] = self.selected_actor.get("id")
        try:
            save_auth(data)
        except Exception as exc:
            logger.exception("Failed to save auth settings")
            if not silent:
                QMessageBox.warning(
                    self,
                    "保存失敗",
                    f"認証・設定情報を保存できませんでした。\n{type(exc).__name__}: {exc}",
                )
            return False
        self._apply_debug_mode(bool(data.get("debug_mode")))
        client_id = data.get("client_id") or ""
        client_secret = data.get("client_secret") or ""
        if client_id and client_secret:
            self.ff_client.set_credentials(client_id, client_secret)
        else:
            self.ff_client.clear_credentials()
        if not silent:
            self.progress_label.setText("認証情報を保存しました")
        return True

    def _collect_ui_state(self) -> Dict[str, object]:
        state: Dict[str, object] = {}
        if hasattr(self, "section_splitter") and self.section_splitter:
            sizes = [int(v) for v in self.section_splitter.sizes()]
            # Avoid persisting invalid all-zero sizes (can happen during shutdown).
            if sum(sizes) > 0:
                state["section_splitter_sizes"] = sizes
        return state

    def _apply_ui_state(self, state: Optional[Dict[str, object]]) -> None:
        if not state:
            self._apply_default_section_sizes()
            return
        sizes = state.get("section_splitter_sizes")
        if sizes and hasattr(self, "section_splitter") and self.section_splitter:
            def apply_sizes():
                try:
                    normalized = self._normalize_section_sizes([int(v) for v in sizes])
                    self.section_splitter.setSizes(normalized)
                except Exception:
                    self._apply_default_section_sizes()
            QTimer.singleShot(0, apply_sizes)
        else:
            self._apply_default_section_sizes()

    def _normalize_section_sizes(self, sizes: List[int]) -> List[int]:
        saved_h = self._table_min_height(self.saved_sets_table, 2)
        memo_line = self.note_edit.fontMetrics().height() + 8 + self.note_edit.frameWidth() * 2
        memo_h = max(memo_line, self.note_edit.fontMetrics().height() + 12)
        gear_h = max(320, saved_h * 3)
        defaults = [saved_h, gear_h, memo_h]
        if not sizes or len(sizes) < 3:
            return defaults
        vals = [max(0, int(v)) for v in sizes[:3]]
        if sum(vals) <= 0:
            return defaults
        mins = [saved_h, 220, memo_h]
        for i in range(3):
            if vals[i] < mins[i]:
                vals[i] = mins[i]
        return vals

    def _apply_default_section_sizes(self) -> None:
        if not hasattr(self, "section_splitter") or not self.section_splitter:
            return
        saved_h = self._table_min_height(self.saved_sets_table, 2)
        memo_line = self.note_edit.fontMetrics().height() + 8 + self.note_edit.frameWidth() * 2
        memo_h = max(memo_line, self.note_edit.fontMetrics().height() + 12)
        gear_h = max(320, saved_h * 3)
        QTimer.singleShot(
            0, lambda: self.section_splitter.setSizes(self._normalize_section_sizes([saved_h, gear_h, memo_h]))
        )

    def _load_cached_gear_data(self) -> None:
        required = [
            "base_params.json",
            "materia.json",
            "food.json",
            "item_levels.json",
            "jobs.json",
        ]
        if not all(self.cache.load(name) for name in required):
            return
        # キャッシュ読み込みは軽量なので同期で実行してOK
        bp = self.xiv_client.fetch_base_params(force=False)
        materia = self.xiv_client.fetch_materia(force=False)
        food = self.xiv_client.fetch_food(force=False)
        levels = self.xiv_client.fetch_item_levels(force=False)
        jobs = self.xiv_client.fetch_jobs(force=False)
        self._after_gear_data(
            {
                "bp": bp,
                "materia": materia,
                "food": food,
                "jobs": jobs,
                "levels": levels,
                "from_cache": True,
            },
            from_cache=True,
        )

    def _load_report_cache(
        self,
        code: str,
        *,
        sections: Optional[List[str]] = None,
        allow_stale: bool = False,
    ) -> Optional[dict]:
        return self.report_cache.load(
            code,
            sections=sections,
            allow_stale=allow_stale,
        )

    def _save_report_cache(
        self,
        code: str,
        fights: Optional[List[dict]] = None,
        players_by_fight: Optional[dict] = None,
        enemy_npcs: Optional[List[dict]] = None,
    ) -> None:
        try:
            self.report_cache.save(
                code,
                fights=fights,
                players_by_fight=players_by_fight,
                enemy_npcs=enemy_npcs,
            )
        except (OSError, ValueError) as exc:
            logger.warning("Failed to save FFLogs report cache: %s", exc)

    def _fflogs_force_refresh_enabled(self) -> bool:
        return bool(hasattr(self, "chk_force_fflogs") and self.chk_force_fflogs.isChecked())

    def _restore_cached_report(self) -> None:
        code = extract_report_code(self.input_report_code.text())
        if not code:
            return
        cached = self._load_report_cache(code, sections=["fights"])
        if cached and cached.get("fights"):
            self._after_fights(
                {"fights": cached.get("fights", []), "enemy_npcs": cached.get("enemy_npcs", [])},
                from_cache=True,
                request_code=code,
            )

    def _select_fight_by_id(self, fight_id: Optional[int]) -> None:
        if fight_id is None:
            return
        for i in range(self.fight_list.count()):
            item = self.fight_list.item(i)
            fight = item.data(Qt.UserRole)
            if fight and fight.get("id") == fight_id:
                self.fight_list.setCurrentRow(i)
                break

    def _select_actor_by_id(self, actor_id: Optional[int]) -> None:
        if actor_id is None:
            return
        for i in range(self.actor_list.count()):
            item = self.actor_list.item(i)
            actor = item.data(Qt.UserRole)
            if actor and actor.get("id") == actor_id:
                self.actor_list.setCurrentRow(i)
                break

    # ---- Saved sets ----
    def _rebuild_food_lookup_cache(self) -> None:
        lookup: Dict[int, object] = {}
        for food in self.foods:
            food_id = int(getattr(food, "food_id", 0) or 0)
            source_row_id = int(getattr(food, "source_row_id", 0) or 0)
            if food_id > 0:
                lookup[food_id] = food
            if source_row_id > 0:
                lookup[source_row_id] = food
        self._food_lookup_by_id = lookup

    def _find_food_by_id(self, food_id: Optional[int]):
        if not food_id:
            return None
        try:
            target_id = int(food_id)
        except Exception:
            return None
        if not self._food_lookup_by_id and self.foods:
            self._rebuild_food_lookup_cache()
        return self._food_lookup_by_id.get(target_id)

    def _resolve_food_id(self, raw_food_id: Optional[int]) -> Optional[int]:
        if raw_food_id is None:
            return None
        food = self._find_food_by_id(raw_food_id)
        if food is None:
            try:
                return int(raw_food_id)
            except Exception:
                return None
        return int(food.food_id)

    def _food_label_by_id(self, food_id: Optional[int]) -> str:
        if not food_id:
            return "食事なし"
        food = self._find_food_by_id(food_id)
        if not food:
            return f"ID {food_id}"
        name = display_name_with_fallback(getattr(food, "name_ja", None), food.name)
        level = food.level_item if food.level_item is not None else "?"
        return f"[IL{level}] {name}"

    def _infer_sync_level_from_il(self, sync_il: Optional[int], fallback: Optional[int] = None) -> int:
        try:
            sync_il_value = int(sync_il or 0)
        except Exception:
            sync_il_value = 0
        if sync_il_value > 0:
            for threshold, level in SYNC_LEVEL_INFER_THRESHOLDS:
                if sync_il_value <= threshold:
                    return int(level)
        return xivmath.normalize_supported_level(fallback)

    def _infer_sync_level_from_gear(self, gear: Optional[Gearset]) -> int:
        if gear is None:
            return int(xivmath.CURRENT_MAX_LEVEL)
        return xivmath.normalize_supported_level(getattr(gear, "level", xivmath.CURRENT_MAX_LEVEL))

    def _capture_saved_set_ui_context(self, job: Optional[str] = None) -> Dict[str, object]:
        current_job = job or self.current_gearset.job
        return {
            "job": current_job,
            "item_il_min": int(self.item_il_min.value()) if hasattr(self, "item_il_min") else None,
            "item_il_max": int(self.item_il_max.value()) if hasattr(self, "item_il_max") else None,
            "food_il_min": int(self.food_il_min.value()) if hasattr(self, "food_il_min") else None,
            "food_il_max": int(self.food_il_max.value()) if hasattr(self, "food_il_max") else None,
            "level_sync_enabled": self._level_sync_enabled(),
            "level_sync_il": int(self.level_sync_il.value()) if hasattr(self, "level_sync_il") else None,
            "level_sync_level": self._selected_sync_level_value(),
            "calc_mode": self.calc_mode.currentData() if hasattr(self, "calc_mode") else None,
            "party_bonus": int(self.party_bonus.value()) if hasattr(self, "party_bonus") else None,
            "crit_rate_adjust": self._crit_rate_adjust_percent(),
            "dhit_rate_adjust": self._dhit_rate_adjust_percent(),
            "party_synergies": self._selected_party_synergies(),
            "gear_search_mode": self._gear_search_enabled(),
            "export_item_ids": self._export_item_ids_for_capture(self.current_gearset),
        }

    def _saved_set_ui_context(self, entry: Optional[dict], gear: Optional[Gearset] = None) -> Dict[str, object]:
        context = dict((entry or {}).get("ui_context") or {})
        context.pop("high_precision_mode", None)
        if gear and gear.job and not context.get("job"):
            context["job"] = gear.job
        if "calc_mode" not in context and entry and entry.get("mode") is not None:
            context["calc_mode"] = entry.get("mode")
        if "party_bonus" not in context and entry and entry.get("party_bonus") is not None:
            context["party_bonus"] = entry.get("party_bonus")
        if "crit_rate_adjust" not in context:
            context["crit_rate_adjust"] = 0
        if "dhit_rate_adjust" not in context:
            context["dhit_rate_adjust"] = 0
        if "party_synergies" not in context:
            context["party_synergies"] = {}
        if "gear_search_mode" not in context:
            context["gear_search_mode"] = False
        context["export_item_ids"] = self._normalized_export_item_ids(context.get("export_item_ids"))
        if gear and gear.job:
            inferred = self._infer_saved_set_ui_context(entry, gear)
            for key, value in inferred.items():
                if key not in context and value is not None:
                    context[key] = value
        return context

    def _persist_saved_set_ui_context(self, entry: Optional[dict], context: Optional[dict]) -> None:
        if not isinstance(entry, dict) or not isinstance(context, dict):
            return
        normalized = dict(context)
        if entry.get("ui_context") == normalized:
            return
        entry["ui_context"] = normalized
        entry_id = entry.get("id")
        for target in self.saved_sets:
            if isinstance(target, dict) and target.get("id") == entry_id:
                target["ui_context"] = dict(normalized)
                break
        self._schedule_saved_sets_flush(immediate=False)

    def _sync_selected_saved_set_ui_context(self) -> None:
        if self._saved_sets_reordering or not hasattr(self, "saved_sets_table"):
            return
        row = self.saved_sets_table.currentRow()
        if row < 0:
            return
        entry_item = self.saved_sets_table.item(row, SAVED_COL_NAME)
        entry = entry_item.data(Qt.UserRole) if entry_item else None
        if not isinstance(entry, dict) or bool(entry.get("locked", False)):
            return
        gear_data = entry.get("gearset")
        gear = Gearset.from_dict(gear_data) if isinstance(gear_data, dict) else self.current_gearset
        job = gear.job if isinstance(gear, Gearset) and gear.job else self.current_gearset.job
        self._persist_saved_set_ui_context(entry, self._capture_saved_set_ui_context(job))
        if entry_item:
            entry_item.setData(Qt.UserRole, entry)

    def _infer_saved_set_ui_context(self, entry: Optional[dict], gear: Optional[Gearset]) -> Dict[str, object]:
        if not gear or not gear.job:
            return {}
        inferred_level = self._infer_sync_level_from_gear(gear)
        selected_items: List[ItemRecord] = []
        for sel in (gear.items or {}).values():
            if not sel or not sel.item_id:
                continue
            item = self.items_by_id.get(sel.item_id)
            if item:
                selected_items.append(item)
        if not selected_items:
            return {
                "job": gear.job,
                "level_sync_level": inferred_level,
            }

        inferred: Dict[str, object] = {"job": gear.job, "level_sync_level": inferred_level}
        job_items = self.items_by_job.get(gear.job, []) or []
        max_job_il = max((int(getattr(item, "ilvl", 0) or 0) for item in job_items), default=max(int(item.ilvl or 0) for item in selected_items))

        weapon_sel = (gear.items or {}).get("weapon")
        weapon_item = self.items_by_id.get(weapon_sel.item_id) if weapon_sel and weapon_sel.item_id else None
        saved_stats = (entry or {}).get("stats") if isinstance(entry, dict) else None
        inferred_sync_il = None
        if weapon_item and isinstance(saved_stats, dict) and self.item_levels:
            try:
                saved_wd = int(saved_stats.get("wd") or 0)
            except Exception:
                saved_wd = 0
            actual_wd = max(int(weapon_item.damage_phys or 0), int(weapon_item.damage_mag or 0))
            if saved_wd > 0 and actual_wd > saved_wd:
                candidates: List[int] = []
                for ilvl, row in self.item_levels.items():
                    try:
                        ilvl_int = int(ilvl)
                    except Exception:
                        continue
                    if ilvl_int > int(weapon_item.ilvl or 0):
                        continue
                    row_wd = row.get("magicalDamage")
                    if row_wd is None:
                        row_wd = row.get("physicalDamage")
                    try:
                        if int(row_wd or 0) == saved_wd:
                            candidates.append(ilvl_int)
                    except Exception:
                        continue
                if candidates:
                    inferred_sync_il = max(candidates)

        if inferred_sync_il is not None:
            inferred["level_sync_enabled"] = True
            inferred["level_sync_il"] = inferred_sync_il
            inferred["item_il_min"] = max(1, int(inferred_sync_il) - 10)
            inferred["item_il_max"] = max(1, int(max_job_il))
            inferred["level_sync_level"] = self._infer_sync_level_from_il(inferred_sync_il, fallback=inferred_level)
        else:
            inferred["level_sync_enabled"] = False
            min_selected_il = min(int(item.ilvl or 0) for item in selected_items)
            max_selected_il = max(int(item.ilvl or 0) for item in selected_items)
            inferred["level_sync_il"] = max_selected_il
            inferred["item_il_min"] = max(1, min_selected_il)
            inferred["item_il_max"] = max(max_selected_il, int(max_job_il))
        return inferred

    def _apply_saved_set_ui_context(self, context: Optional[dict], job: Optional[str] = None) -> None:
        if not isinstance(context, dict):
            self._current_export_item_ids = {}
            return
        context_job = context.get("job")
        if context_job and job and str(context_job) != str(job):
            return
        self._current_export_item_ids = self._normalized_export_item_ids(context.get("export_item_ids"))

        widgets_to_block = [
            getattr(self, "item_il_min", None),
            getattr(self, "item_il_max", None),
            getattr(self, "food_il_min", None),
            getattr(self, "food_il_max", None),
            getattr(self, "chk_level_sync", None),
            getattr(self, "level_sync_il", None),
            getattr(self, "level_sync_level_combo", None),
            getattr(self, "calc_mode", None),
            getattr(self, "party_bonus", None),
            getattr(self, "crit_rate_adjust_spin", None),
            getattr(self, "dhit_rate_adjust_spin", None),
            getattr(self, "chk_gear_search_mode", None),
        ]
        for widget in widgets_to_block:
            if widget is not None:
                widget.blockSignals(True)
        try:
            level_sync_enabled = context.get("level_sync_enabled")
            if hasattr(self, "chk_level_sync") and level_sync_enabled is not None:
                self.chk_level_sync.setChecked(bool(level_sync_enabled))
            level_sync_il = context.get("level_sync_il")
            if hasattr(self, "level_sync_il") and level_sync_il is not None:
                self.level_sync_il.setValue(max(1, int(level_sync_il)))
            level_sync_level = context.get("level_sync_level")
            if hasattr(self, "level_sync_level_combo") and level_sync_level is not None:
                idx = self.level_sync_level_combo.findData(xivmath.normalize_supported_level(level_sync_level))
                if idx != -1:
                    self.level_sync_level_combo.setCurrentIndex(idx)
            if hasattr(self, "level_sync_il") and hasattr(self, "chk_level_sync"):
                self.level_sync_il.setEnabled(bool(self.chk_level_sync.isChecked()))
            if hasattr(self, "level_sync_level_combo") and hasattr(self, "chk_level_sync"):
                self.level_sync_level_combo.setEnabled(bool(self.chk_level_sync.isChecked()))

            item_il_min = context.get("item_il_min")
            item_il_max = context.get("item_il_max")
            if item_il_min is not None and item_il_max is not None and hasattr(self, "item_il_min") and hasattr(self, "item_il_max"):
                target_min = max(1, int(item_il_min))
                target_max = max(target_min, int(item_il_max))
                self.item_il_min.setValue(target_min)
                self.item_il_max.setValue(target_max)

            food_il_min = context.get("food_il_min")
            food_il_max = context.get("food_il_max")
            if food_il_min is not None and food_il_max is not None and hasattr(self, "food_il_min") and hasattr(self, "food_il_max"):
                target_food_min = max(1, int(food_il_min))
                target_food_max = max(target_food_min, int(food_il_max))
                self.food_il_min.setValue(target_food_min)
                self.food_il_max.setValue(target_food_max)

            calc_mode = context.get("calc_mode")
            if calc_mode and hasattr(self, "calc_mode"):
                idx = self.calc_mode.findData(calc_mode)
                if idx != -1:
                    self.calc_mode.setCurrentIndex(idx)

            party_bonus = context.get("party_bonus")
            if party_bonus is not None and hasattr(self, "party_bonus"):
                self.party_bonus.setValue(max(0, min(5, int(party_bonus))))

            crit_rate_adjust = context.get("crit_rate_adjust")
            if crit_rate_adjust is not None and hasattr(self, "crit_rate_adjust_spin"):
                self.crit_rate_adjust_spin.setValue(max(-20, min(20, int(crit_rate_adjust))))

            dhit_rate_adjust = context.get("dhit_rate_adjust")
            if dhit_rate_adjust is not None and hasattr(self, "dhit_rate_adjust_spin"):
                self.dhit_rate_adjust_spin.setValue(max(-20, min(20, int(dhit_rate_adjust))))

            party_synergies = context.get("party_synergies")
            if isinstance(party_synergies, dict):
                self._set_party_synergies(party_synergies)

            gear_search_mode = context.get("gear_search_mode")
            if gear_search_mode is not None and hasattr(self, "chk_gear_search_mode"):
                self.chk_gear_search_mode.setChecked(bool(gear_search_mode))
        finally:
            for widget in reversed(widgets_to_block):
                if widget is not None:
                    widget.blockSignals(False)
        if "food_il_min" in context or "food_il_max" in context:
            self.refresh_food_combo()
        self._update_optimize_button_text()

    def _main_stat_id_for_job(self, job: Optional[str]) -> int:
        return optimizer.MAIN_STAT_BY_JOB.get(job or "", 4)

    def _main_stat_header_for_job(self, job: Optional[str]) -> str:
        stat_id = self._main_stat_id_for_job(job)
        return MAIN_STAT_HEADERS.get(stat_id, "MAIN")

    def _saved_stats_main_value(self, stats: Optional[Dict[str, int]], job: Optional[str]) -> Optional[int]:
        if not stats:
            return None
        main_val = stats.get("main_stat")
        if main_val is not None:
            return int(main_val)
        stat_id = self._main_stat_id_for_job(job)
        if stat_id == 1 and stats.get("str") is not None:
            return int(stats.get("str"))
        if stat_id == 2 and stats.get("dex") is not None:
            return int(stats.get("dex"))
        if stat_id == 5 and stats.get("mnd") is not None:
            return int(stats.get("mnd"))
        legacy_int = stats.get("int")
        if legacy_int is not None:
            return int(legacy_int)
        return None

    def _saved_stats_gcd_value(
        self,
        stats: Optional[Dict[str, int]],
        job: Optional[str],
        level: Optional[int] = None,
    ) -> Optional[float]:
        if not stats or not job:
            return None
        speed_total = stats.get("sps")
        if speed_total is None:
            return None
        try:
            level_value = xivmath.normalize_supported_level(level if level is not None else stats.get("level"))
            return float(optimizer.calc_gcd_seconds(int(speed_total), job, level=level_value))
        except Exception:
            return None

    def _compute_saved_stats(self, gearset: Gearset, food_id: Optional[int], party_bonus: Optional[int] = None) -> Optional[Dict[str, int]]:
        job = gearset.job
        if not job or not self.jobs_data:
            return None
        resolved_food_id = self._resolve_food_id(food_id)
        party = int(party_bonus if party_bonus is not None else self.party_bonus.value())
        cache_key = (self._gearset_dedup_signature(gearset), resolved_food_id, party)
        cached = self._saved_stats_cache.get(cache_key)
        if cached is not None:
            return dict(cached)
        raw_stats, selected_items = self._compute_raw_stats_with_melds(gearset)
        food = self._find_food_by_id(resolved_food_id) if self.foods else None
        job_mods = self._get_job_mods(job)
        level_value = optimizer.gearset_level(gearset)
        result = compute_saved_stats_snapshot(
            job=job,
            level=level_value,
            raw_stats=raw_stats,
            selected_items=selected_items,
            food=food,
            job_mods=job_mods,
            party_bonus=party,
            race=DEFAULT_RACE,
        )
        if result is None:
            return None
        self._saved_stats_cache[cache_key] = dict(result)
        return result

    def _ensure_saved_sets_jobs_loaded(self) -> bool:
        jobs_needed = set()
        for entry in self.saved_sets:
            job = entry.get("job")
            if not job:
                gear_data = entry.get("gearset")
                if gear_data:
                    job = gear_data.get("job")
            if job and job not in self.items_by_job:
                jobs_needed.add(job)
        if not jobs_needed:
            return False
        self._pending_saved_jobs.update(jobs_needed)
        self._start_saved_jobs_load()
        return True

    def _start_saved_jobs_load(self) -> None:
        if self._loading_saved_jobs:
            return
        if self.active_worker:
            return
        if not self._pending_saved_jobs:
            return
        jobs = sorted(self._pending_saved_jobs)
        self._pending_saved_jobs.clear()
        self._loading_saved_jobs = True

        def task(progress=None, stop_event=None):
            items = self.xiv_client.fetch_items_for_jobs(
                jobs, force=False, progress=progress, stop_event=stop_event
            )
            return {"jobs": jobs, "items": items}

        self.progress_label.setText("保存セット用の装備データを読み込み中...")
        self.start_worker(
            task,
            self._after_saved_jobs,
            silent_if_busy=True,
            lock_job_context=True,
        )

    def _after_saved_jobs(self, payload: dict) -> None:
        self._loading_saved_jobs = False
        if not payload:
            return
        jobs = payload.get("jobs", [])
        items = payload.get("items", []) or []
        # 取得したアイテムをジョブごとに振り分け
        for job in jobs:
            job_items = [it for it in items if job in (it.jobs or [])]
            if job_items:
                self.items_by_job[job] = job_items
                for it in job_items:
                    self.items_by_id[it.item_id] = it
        # 表示更新
        self._refresh_saved_sets_table()
        if self._simdps_baseline_gearset and self._gearset_items_ready(self._simdps_baseline_gearset):
            self._update_simdps_baseline_data()
        if self._pending_gearset and self._pending_gearset.job in self.items_by_job:
            gear = self._pending_gearset
            self._pending_gearset = None
            self._apply_gearset_to_ui(gear)

    def _refresh_saved_sets_table(self) -> None:
        if not hasattr(self, "saved_sets_table"):
            return
        self._ensure_saved_sets_jobs_loaded()
        selected_job = self.job_combo.currentData() if hasattr(self, "job_combo") else None
        selected_entry_id = None
        current_row = self.saved_sets_table.currentRow()
        if current_row >= 0:
            current_item = self.saved_sets_table.item(current_row, SAVED_COL_NAME)
            current_entry = current_item.data(Qt.UserRole) if current_item else None
            if isinstance(current_entry, dict):
                selected_entry_id = current_entry.get("id")
        main_header = self._main_stat_header_for_job(selected_job) if selected_job else "MAIN"
        main_header_item = self.saved_sets_table.horizontalHeaderItem(SAVED_COL_MAIN)
        if main_header_item and main_header_item.text() != main_header:
            main_header_item.setText(main_header)
        self._updating_saved_table = True
        blocker = QSignalBlocker(self.saved_sets_table)
        pending_stats: List[dict] = []
        restored_row = -1
        try:
            self.saved_sets_table.setRowCount(0)
            for entry in self.saved_sets:
                entry_job = entry.get("job")
                entry_level = None
                if not entry_job:
                    gear_data = entry.get("gearset") or {}
                    entry_job = gear_data.get("job")
                else:
                    gear_data = entry.get("gearset") or {}
                if isinstance(gear_data, dict):
                    try:
                        entry_level = Gearset.from_dict(gear_data).level
                    except Exception:
                        entry_level = None
                if selected_job and entry_job and entry_job != selected_job:
                    continue
                row = self.saved_sets_table.rowCount()
                self.saved_sets_table.insertRow(row)
                name = entry.get("name") or "セット"
                mode = entry.get("mode") or "simdps"
                score_label, expected_score_label, score_tooltip = self._saved_score_labels(entry)
                food_label = self._food_label_by_id(entry.get("food_id"))
                stats = entry.get("stats")
                if stats is not None and entry.get("stats_version") != STATS_VERSION:
                    stats = None
                if stats is None:
                    job = entry.get("job")
                    if not job:
                        gear_data = entry.get("gearset")
                        if gear_data:
                            job = gear_data.get("job")
                    if job and job not in self.items_by_job:
                        stats = None
                if stats is None:
                    gear_data = entry.get("gearset")
                    if gear_data and self.jobs_data:
                        gear = Gearset.from_dict(gear_data)
                        if self._gearset_items_ready(gear):
                            pending_stats.append(entry)

                mode_label = "XiVGear（Dmg/100p）" if mode == "dmg100p" else "試算DPS（logs基準）"
                gcd = self._saved_stats_gcd_value(stats, entry_job, entry_level)
                if gcd is None:
                    gcd = entry.get("gcd")
                gcd_label = f"{gcd:.3f}s" if gcd else "-"
                wd_label = f"{stats.get('wd')}" if stats else "-"
                hp_label = f"{stats.get('hp')}" if stats else "-"
                main_stat_val = self._saved_stats_main_value(stats, entry_job)
                main_stat_label = f"{main_stat_val}" if main_stat_val is not None else "-"
                crit_label = f"{stats.get('crit')}" if stats else "-"
                dhit_label = f"{stats.get('dhit')}" if stats else "-"
                det_label = f"{stats.get('det')}" if stats else "-"
                sps_label = f"{stats.get('sps')}" if stats else "-"

                handle_item = QTableWidgetItem("≡")
                handle_item.setFlags(
                    Qt.ItemIsSelectable
                    | Qt.ItemIsEnabled
                    | Qt.ItemIsDragEnabled
                )
                handle_item.setTextAlignment(Qt.AlignCenter)
                self.saved_sets_table.setItem(row, SAVED_COL_HANDLE, handle_item)

                locked = bool(entry.get("locked", False))
                lock_item = QTableWidgetItem("🔒" if locked else "🔓")
                lock_item.setFlags(
                    Qt.ItemIsSelectable
                    | Qt.ItemIsEnabled
                )
                lock_item.setTextAlignment(Qt.AlignCenter)
                self.saved_sets_table.setItem(row, SAVED_COL_LOCK, lock_item)

                name_item = QTableWidgetItem(name)
                name_item.setData(Qt.UserRole, entry)
                name_item.setFlags(
                    Qt.ItemIsSelectable
                    | Qt.ItemIsEnabled
                    | Qt.ItemIsEditable
                )
                self.saved_sets_table.setItem(row, SAVED_COL_NAME, name_item)
                export_item = QTableWidgetItem("")
                export_item.setFlags(
                    Qt.ItemIsSelectable
                    | Qt.ItemIsEnabled
                    | Qt.ItemIsUserCheckable
                )
                export_item.setCheckState(Qt.Checked if bool(entry.get("export_checked", False)) else Qt.Unchecked)
                export_item.setTextAlignment(Qt.AlignCenter)
                export_item.setData(Qt.UserRole, entry)
                self.saved_sets_table.setItem(row, SAVED_COL_EXPORT, export_item)
                if selected_entry_id is not None and entry.get("id") == selected_entry_id:
                    restored_row = row
                for col, text in (
                    (SAVED_COL_MODE, mode_label),
                    (SAVED_COL_SCORE, score_label),
                    (SAVED_COL_EXPECTED_SCORE, expected_score_label),
                    (SAVED_COL_GCD, gcd_label),
                    (SAVED_COL_WD, wd_label),
                    (SAVED_COL_HP, hp_label),
                    (SAVED_COL_MAIN, main_stat_label),
                    (SAVED_COL_CRT, crit_label),
                    (SAVED_COL_DHT, dhit_label),
                    (SAVED_COL_DET, det_label),
                    (SAVED_COL_SPS, sps_label),
                    (SAVED_COL_FOOD, food_label),
                ):
                    item = QTableWidgetItem(text)
                    item.setFlags(
                        Qt.ItemIsSelectable
                        | Qt.ItemIsEnabled
                    )
                    if score_tooltip and col in {SAVED_COL_SCORE, SAVED_COL_EXPECTED_SCORE}:
                        item.setToolTip(score_tooltip)
                    self.saved_sets_table.setItem(row, col, item)
            if restored_row >= 0:
                self.saved_sets_table.setCurrentCell(restored_row, SAVED_COL_NAME)
            else:
                self.saved_sets_table.clearSelection()
            if not self._saved_table_sized_once:
                self.saved_sets_table.setColumnWidth(SAVED_COL_HANDLE, 30)
                self.saved_sets_table.setColumnWidth(SAVED_COL_LOCK, 56)
                self.saved_sets_table.setColumnWidth(SAVED_COL_NAME, self._saved_set_name_col_width)
                self.saved_sets_table.setColumnWidth(SAVED_COL_EXPORT, 48)
                for col in range(SAVED_COL_MODE, self.saved_sets_table.columnCount()):
                    self.saved_sets_table.resizeColumnToContents(col)
                self._saved_table_sized_once = True
        finally:
            del blocker
            self._updating_saved_table = False
        if pending_stats and not self._saved_stats_worker_active:
            self._start_saved_stats_compute(pending_stats)

    def _gearset_items_ready(self, gear: Gearset) -> bool:
        for sel in gear.items.values():
            if sel.item_id and sel.item_id not in self.items_by_id:
                return False
        return True

    def _gearset_has_selected_items(self, gear: Optional[Gearset]) -> bool:
        if not gear:
            return False
        for sel in gear.items.values():
            if sel and sel.item_id:
                return True
        return False

    def _start_saved_stats_compute(self, entries: List[dict]) -> None:
        if self._saved_stats_worker_active:
            return
        self._saved_stats_worker_active = True
        default_party_bonus = int(self.party_bonus.value())
        payload = []
        for entry in entries:
            if not entry.get("gearset"):
                continue
            try:
                gear = Gearset.from_dict(entry.get("gearset") or {})
                if not gear.job or not self.jobs_data or not self._gearset_items_ready(gear):
                    continue
                raw_stats, selected_items = self._compute_raw_stats_with_melds(gear)
                food_id = self._resolve_food_id(entry.get("food_id"))
                food = self._find_food_by_id(food_id) if self.foods else None
                payload.append(
                    {
                        "id": entry.get("id"),
                        "job": gear.job,
                        "level": optimizer.gearset_level(gear),
                        "raw_stats": dict(raw_stats),
                        "selected_items": dict(selected_items),
                        "food": food,
                        "job_mods": self._get_job_mods(gear.job),
                        "party_bonus": int(
                            entry.get("party_bonus")
                            if entry.get("party_bonus") is not None
                            else default_party_bonus
                        ),
                        "race": DEFAULT_RACE,
                    }
                )
            except (TypeError, ValueError):
                logger.warning("Skipped invalid saved-set statistics entry %s", entry.get("id"))

        def task(stop_event=None, progress=None):
            results = []
            for entry in payload:
                if stop_event and stop_event.is_set():
                    break
                stats = compute_saved_stats_snapshot(
                    job=entry["job"],
                    level=entry["level"],
                    raw_stats=entry["raw_stats"],
                    selected_items=entry["selected_items"],
                    food=entry["food"],
                    job_mods=entry["job_mods"],
                    party_bonus=entry["party_bonus"],
                    race=entry["race"],
                )
                if stats:
                    results.append((entry.get("id"), stats))
            return results

        worker = Worker(task)
        self._saved_stats_worker = worker
        worker.signals.finished.connect(self._after_saved_stats_compute, Qt.QueuedConnection)
        worker.signals.error.connect(self._after_saved_stats_error, Qt.QueuedConnection)
        worker.signals.cancelled.connect(self._after_saved_stats_cancelled, Qt.QueuedConnection)
        self.thread_pool.start(worker)

    def _after_saved_stats_compute(self, results) -> None:
        self._saved_stats_worker = None
        self._saved_stats_worker_active = False
        if not results:
            return
        stats_map = {entry_id: stats for entry_id, stats in results}
        updated = False
        for entry in self.saved_sets:
            entry_id = entry.get("id")
            if entry_id in stats_map:
                entry["stats"] = stats_map[entry_id]
                entry["stats_version"] = STATS_VERSION
                updated = True
        if updated:
            self._schedule_saved_sets_flush(immediate=True)
            self._refresh_saved_sets_table()

    def _after_saved_stats_error(self, _trace: str) -> None:
        self._saved_stats_worker = None
        self._saved_stats_worker_active = False

    def _after_saved_stats_cancelled(self) -> None:
        self._saved_stats_worker = None
        self._saved_stats_worker_active = False

    def _set_last_eval(self, mode: str, score: float, gcd: float, expected_score: Optional[float] = None) -> None:
        self.last_eval = {
            "mode": mode,
            "score": score,
            "expected_score": score if expected_score is None else float(expected_score),
            "gcd": gcd,
            "ts": time.time(),
        }

    def _result_text_for_mode(self, mode: str, score: float) -> str:
        if mode == "dmg100p":
            return f"計算結果: Dmg/100p {score:.2f}"
        if mode in {"simdps", "simdps_self"}:
            return f"計算結果: 試算DPS {score:.1f}"
        return f"計算結果: スコア {score:.1f}"

    def _format_saved_score(self, mode: str, score: Optional[float]) -> str:
        if score is None:
            return "-"
        try:
            value = float(score)
        except (TypeError, ValueError):
            return "-"
        if not math.isfinite(value):
            return "-"
        return f"{value:.2f}" if mode == "dmg100p" else f"{value:.1f}"

    @staticmethod
    def _saved_numeric_changed(old_value: object, new_value: float) -> bool:
        try:
            old_numeric = float(old_value)
        except (TypeError, ValueError):
            return True
        return not math.isfinite(old_numeric) or abs(old_numeric - float(new_value)) > 1e-9

    def _saved_score_labels(self, entry: dict) -> Tuple[str, str, str]:
        mode = str(entry.get("mode") or "simdps")
        score = entry.get("score")
        expected_score = self._saved_expected_score_value(entry)
        score_valid, message = self._saved_score_validation(entry)
        if score is None or score_valid:
            return (
                self._format_saved_score(mode, score),
                self._format_saved_score(mode, expected_score),
                "",
            )
        old_score = self._format_saved_score(mode, score)
        old_expected = self._format_saved_score(mode, expected_score)
        tooltip = f"{message}\n以前の保存値: {{value}}"
        return "要再計算", "要再計算", tooltip.format(value=f"{old_score} / {old_expected}")

    @staticmethod
    def _score_baseline_hash(gear: Gearset, party_bonus: int, race: Optional[str]) -> str:
        return _score_payload_hash(
            {
                "gearset": _score_gear_payload(gear.to_dict()),
                "party_bonus": int(party_bonus),
                "race": race or gear.race or DEFAULT_RACE,
            }
        )

    @staticmethod
    def _score_log_data_hash(summary: Dict[str, object]) -> str:
        return _score_payload_hash(_score_normalize_mapping_keys(summary))

    def _score_data_hash_for_entry(self, entry: dict) -> Optional[str]:
        gear_data = entry.get("gearset")
        if not isinstance(gear_data, dict):
            return None
        gear = Gearset.from_dict(gear_data)
        jobs_data = getattr(self, "jobs_data", {})
        items_by_id = getattr(self, "items_by_id", {})
        base_params = getattr(self, "base_params", {})
        item_levels = getattr(self, "item_levels", {})
        if not gear.job or gear.job not in jobs_data or not base_params or not item_levels:
            return None
        item_payload: Dict[str, object] = {}
        materia_payload: List[Tuple[str, int, int, int]] = []
        relevant_item_levels = set()
        for slot, selection in sorted((gear.items or {}).items()):
            item_id = int(selection.item_id or 0)
            if item_id <= 0:
                continue
            item = items_by_id.get(item_id)
            if item is None:
                return None
            item_payload[slot] = {
                "item_id": int(item.item_id),
                "ilvl": int(item.ilvl),
                "slot": item.slot,
                "occ_slot": item.occ_slot,
                "base_params": item.base_params,
                "base_params_hq": item.base_params_hq,
                "damage_phys": item.damage_phys,
                "damage_mag": item.damage_mag,
                "delay_ms": item.delay_ms,
            }
            relevant_item_levels.add(int(item.ilvl))
            for materia in selection.materia or []:
                value = self._materia_value(int(materia.base_param), int(materia.grade))
                if value <= 0:
                    return None
                materia_payload.append((slot, int(materia.base_param), int(materia.grade), int(value)))

        raw_context = entry.get("ui_context")
        context = raw_context if isinstance(raw_context, dict) else {}
        if context.get("level_sync_enabled"):
            try:
                relevant_item_levels.add(int(context.get("level_sync_il")))
            except (TypeError, ValueError):
                return None
        item_level_payload = {}
        for ilvl in sorted(relevant_item_levels):
            row = item_levels.get(ilvl)
            if row is None:
                return None
            item_level_payload[ilvl] = row
        base_param_payload = {}
        for stat_id in optimizer.MELDABLE_STATS:
            record = base_params.get(stat_id)
            if record is None:
                continue
            base_param_payload[int(stat_id)] = {
                "meld_param": getattr(record, "meld_param", []),
                "slots": getattr(record, "slots", {}),
            }

        food_payload = None
        food_id = entry.get("food_id")
        if food_id is not None:
            food = self._find_food_by_id(food_id)
            if food is None:
                return None
            food_payload = {
                "food_id": int(food.food_id),
                "level_item": food.level_item,
                "hq": bool(food.hq),
                "bonuses": {
                    int(stat_id): {
                        "percentage": int(bonus.percentage),
                        "maximum": int(bonus.maximum),
                    }
                    for stat_id, bonus in sorted(food.bonuses.items())
                },
            }
        return _score_payload_hash(
            {
                "stats_version": STATS_VERSION,
                "items": item_payload,
                "item_levels": item_level_payload,
                "base_params": base_param_payload,
                "materia": materia_payload,
                "food": food_payload,
                "job_mods": self._get_job_mods(gear.job),
                "level_data": xivmath.LEVEL_STATS.get(gear.level),
            }
        )

    def _entry_with_current_score_context(
        self,
        entry: dict,
        mode: str,
        stats: Optional[Dict[str, int]],
    ) -> dict:
        snapshot = dict(entry)
        snapshot.update(
            {
                "mode": mode,
                "food_id": self.current_gearset.food_id,
                "gearset": self.current_gearset.to_dict(),
                "party_bonus": self.party_bonus.value(),
                "ui_context": self._capture_saved_set_ui_context(self.current_gearset.job),
                "report_code": extract_report_code(self.input_report_code.text()),
                "fight_id": self.selected_fight.get("id") if self.selected_fight else None,
                "actor_id": self.selected_actor.get("id") if self.selected_actor else None,
                "stats": stats,
                "stats_version": STATS_VERSION if stats else None,
            }
        )
        return snapshot

    def _saved_score_context_matches_current(
        self,
        entry: dict,
        mode: str,
        stats: Optional[Dict[str, int]],
    ) -> bool:
        current = _saved_score_context_payload(
            self._entry_with_current_score_context(entry, mode, stats)
        )
        saved = _saved_score_context_payload(entry)
        # These values are derived from the protected gear and may legitimately
        # change after a stats formula/data update. They must not prevent refresh.
        for payload in (current, saved):
            payload.pop("stats", None)
            payload.pop("stats_version", None)
            if mode == "dmg100p":
                # Dmg/100p does not depend on an FFLogs selection.
                payload.pop("report_code", None)
                payload.pop("fight_id", None)
                payload.pop("actor_id", None)
        return current == saved

    def _build_score_meta_for_entry(self, entry: dict, mode: str) -> Optional[Dict[str, object]]:
        model_name = SCORE_MODEL_NAMES.get(mode)
        model_version = optimizer.SCORE_MODEL_VERSIONS.get(mode)
        if not model_name or model_version is None:
            return None
        data_hash = self._score_data_hash_for_entry(entry)
        if data_hash is None:
            return None
        meta: Dict[str, object] = {
            "meta_version": SCORE_META_VERSION,
            "model": model_name,
            "model_version": int(model_version),
            "app_version": APP_VERSION,
            "context_hash": _score_payload_hash(_saved_score_context_payload(entry)),
            "data_hash": data_hash,
            "result_hash": _score_payload_hash(
                {
                    "score": entry.get("score"),
                    "expected_score": entry.get("expected_score"),
                    "gcd": entry.get("gcd"),
                }
            ),
        }
        if mode not in {"simdps", "simdps_self"}:
            previous_meta = entry.get("score_meta")
            comparable_previous = dict(previous_meta) if isinstance(previous_meta, dict) else {}
            comparable_previous.pop("calculated_at", None)
            meta["calculated_at"] = (
                previous_meta.get("calculated_at") or utc_now_iso()
                if isinstance(previous_meta, dict) and comparable_previous == meta
                else utc_now_iso()
            )
            return meta

        summary = self.damage_summary_self if mode == "simdps_self" else self.damage_summary
        if not isinstance(summary, dict):
            return None
        damage_total = float(summary.get("total_amount") or summary.get("total_damage") or 0.0)
        if not math.isfinite(damage_total) or damage_total <= 0:
            return None
        fight_ms = 0
        if self.selected_fight:
            start_time = self.selected_fight.get("startTime", self.selected_fight.get("start_time", 0))
            end_time = self.selected_fight.get("endTime", self.selected_fight.get("end_time", 0))
            fight_ms = int(end_time - start_time)
        effective_duration_ms = self._simdps_effective_duration_ms(fight_ms)
        report_code = extract_report_code(str(entry.get("report_code") or ""))
        fight_id = entry.get("fight_id")
        actor_id = entry.get("actor_id")
        if effective_duration_ms <= 0 or not report_code or fight_id is None or actor_id is None:
            return None

        baseline_gear = self._simdps_baseline_gearset or self.current_gearset
        baseline_party_value = self._simdps_baseline_party
        baseline_party = int(self.party_bonus.value() if baseline_party_value is None else baseline_party_value)
        baseline_race = self._simdps_baseline_race or baseline_gear.race or self._current_race()
        baseline_entry = next(
            (
                saved
                for saved in self.saved_sets
                if isinstance(saved, dict) and saved.get("id") == self._simdps_baseline_entry_id
            ),
            None,
        )
        baseline_data_entry = baseline_entry or {
            "gearset": baseline_gear.to_dict(),
            "food_id": baseline_gear.food_id,
        }
        baseline_data_hash = self._score_data_hash_for_entry(baseline_data_entry)
        if baseline_data_hash is None:
            return None
        meta.update(
            {
                "metric": "ndps" if mode == "simdps_self" else "adps",
                "report_code": report_code,
                "fight_id": fight_id,
                "actor_id": actor_id,
                "effective_duration_ms": int(effective_duration_ms),
                "damage_total": damage_total,
                "log_data_hash": self._score_log_data_hash(summary),
                "baseline_entry_id": self._simdps_baseline_entry_id,
                "baseline_gearset": baseline_gear.to_dict(),
                "baseline_hash": self._score_baseline_hash(baseline_gear, baseline_party, baseline_race),
                "baseline_data_hash": baseline_data_hash,
            }
        )
        previous_meta = entry.get("score_meta")
        comparable_previous = dict(previous_meta) if isinstance(previous_meta, dict) else {}
        comparable_previous.pop("calculated_at", None)
        meta["calculated_at"] = (
            previous_meta.get("calculated_at") or utc_now_iso()
            if isinstance(previous_meta, dict) and comparable_previous == meta
            else utc_now_iso()
        )
        return meta

    def _saved_score_validation(self, entry: dict) -> Tuple[bool, str]:
        if entry.get("score") is None:
            return False, ""
        try:
            numeric_values = [float(entry["score"])]
            for key in ("expected_score", "gcd"):
                if entry.get(key) is not None:
                    numeric_values.append(float(entry[key]))
        except (TypeError, ValueError):
            return False, "保存スコアの数値が不正です。再計算してください。"
        if not all(math.isfinite(value) for value in numeric_values):
            return False, "保存スコアの数値が不正です。再計算してください。"
        mode = str(entry.get("mode") or "simdps")
        meta = entry.get("score_meta")
        if not isinstance(meta, dict):
            return False, "旧形式の保存スコアです。セットを選択して再計算してください。"
        if meta.get("meta_version") != SCORE_META_VERSION:
            return False, "保存スコアの検証形式が更新されています。再計算してください。"
        if (
            meta.get("model") != SCORE_MODEL_NAMES.get(mode)
            or meta.get("model_version") != optimizer.SCORE_MODEL_VERSIONS.get(mode)
        ):
            return False, "計算モデルが更新されています。セットを選択して再計算してください。"
        context_payload = _saved_score_context_payload(entry)
        if meta.get("context_hash") != _score_payload_hash(context_payload):
            return False, "保存後に装備または計算条件が変更されています。再計算してください。"
        expected_result_hash = _score_payload_hash(
            {
                "score": entry.get("score"),
                "expected_score": entry.get("expected_score"),
                "gcd": entry.get("gcd"),
            }
        )
        if meta.get("result_hash") != expected_result_hash:
            return False, "保存スコアの値が検証情報と一致しません。再計算してください。"
        stored_data_hash = meta.get("data_hash")
        if not stored_data_hash:
            return False, "装備データの検証情報がありません。再計算してください。"
        current_data_hash = self._score_data_hash_for_entry(entry)
        if current_data_hash is not None and current_data_hash != stored_data_hash:
            return False, "装備・食事データが更新されています。再計算してください。"
        if mode not in {"simdps", "simdps_self"}:
            return True, ""
        expected_metric = "ndps" if mode == "simdps_self" else "adps"
        if meta.get("metric") != expected_metric:
            return False, "ログ評価指標が現在の計算方式と一致しません。再計算してください。"
        for key in ("report_code", "fight_id", "actor_id"):
            if meta.get(key) != context_payload.get(key):
                return False, "保存スコアとログ条件が一致しません。再計算してください。"
        try:
            duration_ms = int(meta.get("effective_duration_ms") or 0)
            damage_total = float(meta.get("damage_total") or 0.0)
        except (TypeError, ValueError):
            return False, "保存スコアの検証情報が不正です。再計算してください。"
        if duration_ms <= 0 or not math.isfinite(damage_total) or damage_total <= 0:
            return False, "保存スコアのログ基準値が不足しています。再計算してください。"
        if not meta.get("log_data_hash"):
            return False, "ログ集計の検証情報がありません。再計算してください。"
        active_report_code = (
            extract_report_code(self.input_report_code.text())
            if hasattr(self, "input_report_code")
            else None
        )
        active_fight_id = self.selected_fight.get("id") if getattr(self, "selected_fight", None) else None
        active_actor_id = self.selected_actor.get("id") if getattr(self, "selected_actor", None) else None
        if (
            active_report_code == context_payload.get("report_code")
            and active_fight_id == context_payload.get("fight_id")
            and active_actor_id == context_payload.get("actor_id")
        ):
            active_summary = self.damage_summary_self if mode == "simdps_self" else self.damage_summary
            if isinstance(active_summary, dict):
                if meta.get("log_data_hash") != self._score_log_data_hash(active_summary):
                    return False, "ログ集計データが保存後に変更されています。再計算してください。"
                if isinstance(getattr(self, "damage_table", None), dict):
                    start_time = self.selected_fight.get("startTime", self.selected_fight.get("start_time", 0))
                    end_time = self.selected_fight.get("endTime", self.selected_fight.get("end_time", 0))
                    current_duration_ms = self._simdps_effective_duration_ms(int(end_time - start_time))
                    if current_duration_ms > 0 and current_duration_ms != duration_ms:
                        return False, "ログの有効戦闘時間が保存後に変更されています。再計算してください。"
        if not meta.get("baseline_data_hash"):
            return False, "ログ基準装備のデータ検証情報がありません。再計算してください。"

        baseline_entry_id = meta.get("baseline_entry_id")
        if baseline_entry_id is not None:
            baseline_entry = next(
                (
                    saved
                    for saved in self.saved_sets
                    if isinstance(saved, dict) and saved.get("id") == baseline_entry_id
                ),
                None,
            )
            if not baseline_entry or not isinstance(baseline_entry.get("gearset"), dict):
                return False, "ログ基準装備が見つかりません。基準装備を設定して再計算してください。"
            baseline_gear = Gearset.from_dict(baseline_entry["gearset"])
            try:
                baseline_party = int(baseline_entry.get("party_bonus", 0) or 0)
            except (TypeError, ValueError):
                return False, "ログ基準装備の検証情報が不正です。再計算してください。"
            baseline_hash = self._score_baseline_hash(baseline_gear, baseline_party, baseline_gear.race)
            if meta.get("baseline_hash") != baseline_hash:
                return False, "ログ基準装備が保存後に変更されています。再計算してください。"
            baseline_data_hash = self._score_data_hash_for_entry(baseline_entry)
            if baseline_data_hash is not None and meta.get("baseline_data_hash") != baseline_data_hash:
                return False, "ログ基準装備のデータが更新されています。再計算してください。"
        elif not meta.get("baseline_hash"):
            return False, "ログ基準装備の検証情報がありません。再計算してください。"
        else:
            baseline_gearset = meta.get("baseline_gearset")
            if not isinstance(baseline_gearset, dict):
                return False, "ログ基準装備の保存情報がありません。再計算してください。"
            baseline_probe = {
                "gearset": baseline_gearset,
                "food_id": Gearset.from_dict(baseline_gearset).food_id,
            }
            baseline_data_hash = self._score_data_hash_for_entry(baseline_probe)
            if baseline_data_hash is not None and meta.get("baseline_data_hash") != baseline_data_hash:
                return False, "ログ基準装備のデータが更新されています。再計算してください。"
        return True, ""

    def _saved_expected_score_value(self, entry: Optional[dict]) -> Optional[float]:
        if not isinstance(entry, dict):
            return None
        expected_score = entry.get("expected_score")
        if expected_score is not None:
            try:
                return float(expected_score)
            except Exception:
                return None
        context = entry.get("ui_context") if isinstance(entry.get("ui_context"), dict) else {}
        crit_adjust = int(context.get("crit_rate_adjust", 0) or 0)
        dhit_adjust = int(context.get("dhit_rate_adjust", 0) or 0)
        if crit_adjust == 0 and dhit_adjust == 0:
            score = entry.get("score")
            if score is not None:
                try:
                    return float(score)
                except Exception:
                    return None
        return None

    def _score_tie_tolerance(self, mode: str) -> float:
        return optimizer.score_tie_tolerance(mode)

    def _clear_optimal_variant_tabs(self) -> None:
        self._optimal_variant_entries = []
        if not hasattr(self, "optimal_variant_tabs"):
            return
        blocker = QSignalBlocker(self.optimal_variant_tabs)
        try:
            while self.optimal_variant_tabs.count() > 0:
                self.optimal_variant_tabs.removeTab(self.optimal_variant_tabs.count() - 1)
            self.optimal_variant_tabs.setVisible(False)
        finally:
            del blocker

    def _set_optimal_variant_tabs(
        self,
        entries: List[Dict[str, object]],
        *,
        selected_index: int = 0,
    ) -> None:
        self._clear_optimal_variant_tabs()
        if len(entries) <= 1 or not hasattr(self, "optimal_variant_tabs"):
            return
        self._optimal_variant_entries = list(entries)
        blocker = QSignalBlocker(self.optimal_variant_tabs)
        try:
            for idx, entry in enumerate(self._optimal_variant_entries, 1):
                tab_index = self.optimal_variant_tabs.addTab(str(idx))
                tooltip = (
                    f"候補 {idx}\n"
                    f"スコア: {self._format_saved_score(self.last_optimize_mode or 'simdps_self', entry.get('score'))}\n"
                    f"期待値スコア: {self._format_saved_score(self.last_optimize_mode or 'simdps_self', entry.get('expected_score'))}"
                )
                self.optimal_variant_tabs.setTabToolTip(tab_index, tooltip)
            self.optimal_variant_tabs.setCurrentIndex(max(0, min(selected_index, len(self._optimal_variant_entries) - 1)))
            self.optimal_variant_tabs.setVisible(True)
        finally:
            del blocker

    def _on_optimal_variant_tab_changed(self, index: int) -> None:
        if self._applying_optimal_variant_tab:
            return
        if index < 0 or index >= len(self._optimal_variant_entries):
            return
        entry = self._optimal_variant_entries[index]
        gear = entry.get("gearset")
        if not isinstance(gear, Gearset):
            return
        mode = self.last_optimize_mode or "simdps_self"
        self._applying_optimal_variant_tab = True
        try:
            self._pending_saved_set_ui_context = self._capture_saved_set_ui_context(gear.job)
            self._apply_gearset_to_ui(gear)
        finally:
            self._applying_optimal_variant_tab = False
        for slot in self.slot_tables.keys():
            self._refresh_slot_selected_display(slot)
        self._apply_eval_result(
            mode,
            float(entry.get("score") or 0.0),
            float(entry.get("gcd") or 0.0),
            float(entry.get("expected_score") or entry.get("score") or 0.0),
        )
        self.progress_label.setText(f"候補 {index + 1} を反映しました。")

    def _gearset_has_uncompressed_difference(self, base: Gearset, other: Gearset) -> bool:
        for slot in GEAR_SLOTS:
            base_sel = (base.items or {}).get(slot) or ItemSelection()
            other_sel = (other.items or {}).get(slot) or ItemSelection()
            base_id = int(base_sel.item_id or 0) if base_sel.item_id else 0
            other_id = int(other_sel.item_id or 0) if other_sel.item_id else 0
            if self._selection_relic_stats(base_sel) != self._selection_relic_stats(other_sel):
                return True
            if base_id == other_id:
                continue
            table = self.slot_tables.get(slot)
            row_map = self.slot_row_index.get(slot, {})
            base_row = row_map.get(base_id)
            other_row = row_map.get(other_id)
            if table is None or base_row is None or other_row is None:
                return True
            if base_row != other_row:
                return True
            if not self._is_compressed_table_row(table, base_row):
                return True
        return False

    def _evaluate_gearset_scores(self, gearset: Gearset, mode: str) -> Optional[Tuple[float, float, float]]:
        job = gearset.job
        if not job:
            return None
        if mode == "dmg100p" and not self.jobs_data:
            return None
        if mode in {"simdps", "simdps_self"}:
            summary = self.damage_summary_self if mode == "simdps_self" else self.damage_summary
            if not summary:
                return None
        food = self._find_food_by_id(gearset.food_id)
        raw_stats, selected_items = self._compute_raw_stats_with_melds(gearset)
        if self._simdps_baseline_raw_stats is None or self._simdps_baseline_items is None:
            self._update_simdps_baseline_data()
        baseline_raw, baseline_items, baseline_food, baseline_party, baseline_race = self._resolve_simdps_baseline(
            raw_stats,
            selected_items,
            food,
        )
        party_synergies = self._selected_party_synergies()
        fight_ms = 0
        if self.selected_fight:
            start_time = self.selected_fight.get("startTime", self.selected_fight.get("start_time", 0))
            end_time = self.selected_fight.get("endTime", self.selected_fight.get("end_time", 0))
            fight_ms = end_time - start_time
        if mode in {"simdps", "simdps_self"}:
            if fight_ms <= 0:
                return None
            fight_ms = self._simdps_effective_duration_ms(fight_ms)
        eval_kwargs = {
            "job_mods": self._get_job_mods(job),
            "food": food,
            "party_bonus": self.party_bonus.value(),
            "baseline_raw_stats": baseline_raw,
            "baseline_items": baseline_items,
            "selected_items": selected_items,
            "baseline_food": baseline_food,
            "baseline_party_bonus": baseline_party,
            "baseline_race": baseline_race,
            "party_synergies": party_synergies,
            "race": gearset.race,
            "mode": mode,
            "level": gearset.level,
        }
        summary = self.damage_summary_self if mode == "simdps_self" else self.damage_summary
        score, expected_score, gcd = optimizer.evaluate_score_pair(
            raw_stats,
            job,
            self.casts,
            fight_ms,
            gearset.target_gcd,
            damage_summary=summary if mode in {"simdps", "simdps_self"} else None,
            debug=False,
            crit_rate_offset=self._crit_rate_adjust_value(),
            dhit_rate_offset=self._dhit_rate_adjust_value(),
            **eval_kwargs,
        )
        return float(score), float(expected_score), float(gcd)

    def _build_optimal_variant_entries(
        self,
        results: List[Tuple[Gearset, float, float]],
        mode: str,
    ) -> List[Dict[str, object]]:
        if not results:
            return []
        evaluated_entries: List[Dict[str, object]] = []
        for gear, raw_score, raw_gcd in results:
            evaluated = self._evaluate_gearset_scores(gear, mode)
            if evaluated is None:
                score = float(raw_score)
                expected_score = float(raw_score)
                gcd = float(raw_gcd)
            else:
                score, expected_score, gcd = evaluated
            evaluated_entries.append(
                {
                    "gearset": gear,
                    "score": float(score),
                    "expected_score": float(expected_score),
                    "gcd": float(gcd),
                }
            )
        evaluated_entries.sort(
            key=lambda entry: (
                -float(entry["score"]),
                float(entry["gcd"]),
            )
        )
        base_entry = evaluated_entries[0]
        tie_tolerance = self._score_tie_tolerance(mode)
        entries: List[Dict[str, object]] = [base_entry]
        base_gear = base_entry["gearset"]
        base_score = float(base_entry["score"])
        for entry in evaluated_entries[1:]:
            gear = entry["gearset"]
            if not isinstance(gear, Gearset):
                continue
            if abs(float(entry["score"]) - base_score) > tie_tolerance:
                continue
            if not self._gearset_has_uncompressed_difference(base_gear, gear):
                continue
            entries.append(entry)
        return entries

    def _top_tied_optimized_results(
        self,
        results: List[Tuple[Gearset, float, float]],
        mode: str,
    ) -> List[Tuple[Gearset, float, float]]:
        if not results:
            return []
        tie_tolerance = self._score_tie_tolerance(mode)
        best_score = float(results[0][1])
        tied: List[Tuple[Gearset, float, float]] = []
        for entry in results:
            if abs(float(entry[1]) - best_score) > tie_tolerance:
                break
            tied.append(entry)
        return tied

    def _current_rate_adjust_text(self) -> str:
        job = self.current_gearset.job
        if not job or not self.jobs_data:
            return ""
        raw_stats, selected_items = self._compute_raw_stats_with_melds(self.current_gearset)
        job_mods = self._get_job_mods(job)
        if not job_mods:
            return ""
        food = self._find_food_by_id(self.current_gearset.food_id)
        weapon = selected_items.get("weapon")
        wd_phys = weapon.damage_phys if weapon else 0
        wd_mag = weapon.damage_mag if weapon else 0
        delay = (weapon.delay_ms or 3000) / 1000.0 if weapon else 3.0
        comp = xivmath.build_computed_stats(
            job,
            raw_stats,
            job_mods,
            food.bonuses if food else None,
            self.party_bonus.value(),
            wd_phys,
            wd_mag,
            delay,
            race=self.current_gearset.race,
            level=self.current_gearset.level,
        )
        base_crit = max(0.0, min(1.0, float(comp.crit_chance)))
        base_dhit = max(0.0, min(1.0, float(comp.dhit_chance)))
        adj_crit = max(0.0, min(1.0, base_crit + self._crit_rate_adjust_value()))
        adj_dhit = max(0.0, min(1.0, base_dhit + self._dhit_rate_adjust_value()))
        if abs(adj_crit - base_crit) < 1e-9 and abs(adj_dhit - base_dhit) < 1e-9:
            return f"CRT {base_crit * 100:.1f}% / DH {base_dhit * 100:.1f}%"
        return (
            f"CRT {base_crit * 100:.1f}%→{adj_crit * 100:.1f}% / "
            f"DH {base_dhit * 100:.1f}%→{adj_dhit * 100:.1f}%"
        )

    def _evaluate_current_gearset_scores(self, mode: str) -> Optional[Tuple[float, float, float]]:
        self._sync_ui_to_gearset()
        return self._evaluate_gearset_scores(self.current_gearset, mode)

    def _apply_eval_result(
        self,
        mode: str,
        score: float,
        gcd: float,
        expected_score: Optional[float] = None,
        update_label: bool = True,
    ) -> None:
        if update_label and hasattr(self, "calc_result_label_left"):
            label = self._result_text_for_mode(mode, score)
            rate_text = self._current_rate_adjust_text()
            if rate_text:
                label = f"{label}\n{rate_text}"
            self.calc_result_label_left.setText(label)
        normalized_expected = float(score) if expected_score is None else float(expected_score)
        self._set_last_eval(mode, float(score), float(gcd), normalized_expected)
        self._update_live_saved_set_preview(mode, float(score), float(gcd), normalized_expected)
        self._finish_pending_saved_score_recalculation()

    def _set_pending_saved_score_recalculation_waiting(self, reason: str) -> None:
        if getattr(self, "_pending_saved_score_recalculation_id", None) is None or not hasattr(self, "progress_label"):
            return
        name = getattr(self, "_pending_saved_score_recalculation_name", None) or "保存セット"
        self.progress_label.setText(f"「{name}」は再計算待機中です。{reason}")

    def _begin_saved_score_recalculation(self, entry: Optional[dict]) -> bool:
        valid, _message = self._saved_score_validation(entry) if isinstance(entry, dict) else (True, "")
        needs_recalculation = bool(
            isinstance(entry, dict) and entry.get("score") is not None and not valid
        )
        self._pending_saved_score_recalculation_id = (
            entry.get("id") if needs_recalculation else None
        )
        self._pending_saved_score_recalculation_name = (
            str(entry.get("name") or "保存セット") if needs_recalculation else None
        )
        if needs_recalculation and hasattr(self, "progress_label"):
            self.progress_label.setText(
                f"「{self._pending_saved_score_recalculation_name}」の保存スコアを再計算中..."
            )
        return needs_recalculation

    def _finish_pending_saved_score_recalculation(self) -> None:
        entry_id = getattr(self, "_pending_saved_score_recalculation_id", None)
        if entry_id is None:
            return
        name = getattr(self, "_pending_saved_score_recalculation_name", None) or "保存セット"
        entry = next(
            (
                saved
                for saved in self.saved_sets
                if isinstance(saved, dict) and saved.get("id") == entry_id
            ),
            None,
        )
        valid, message = self._saved_score_validation(entry) if entry is not None else (False, "保存セットが見つかりません。")
        if hasattr(self, "progress_label"):
            if valid:
                self.progress_label.setText(f"「{name}」の保存スコアを再計算しました。")
            else:
                self.progress_label.setText(f"「{name}」の再計算結果を保存できません。{message}")
        self._pending_saved_score_recalculation_id = None
        self._pending_saved_score_recalculation_name = None

    def _parse_json_objects_from_text(self, text: str) -> List[dict]:
        raw = (text or "").strip()
        if not raw:
            return []
        # Allow pasted ```json fenced blocks.
        if raw.startswith("```"):
            raw = re.sub(r"^\s*```[a-zA-Z0-9_-]*\s*", "", raw)
            raw = re.sub(r"\s*```\s*$", "", raw)
            raw = raw.strip()
        objects: List[dict] = []
        try:
            parsed = json.loads(raw)
            if isinstance(parsed, dict):
                return [parsed]
            if isinstance(parsed, list):
                return [obj for obj in parsed if isinstance(obj, dict)]
        except Exception:
            pass
        decoder = json.JSONDecoder()
        idx = 0
        n = len(raw)
        while idx < n:
            while idx < n and raw[idx] in " \t\r\n,;":
                idx += 1
            if idx >= n:
                break
            try:
                obj, end = decoder.raw_decode(raw, idx)
            except json.JSONDecodeError:
                break
            if isinstance(obj, dict):
                objects.append(obj)
            idx = end
        return objects

    def _xivgear_target_gcd_from_name(self, name: str) -> Optional[float]:
        if not name:
            return None
        m = re.search(r"([0-9]+(?:\.[0-9]+)?)\s*GCD", name, flags=re.IGNORECASE)
        if not m:
            m = re.search(r"GCD\s*([0-9]+(?:\.[0-9]+)?)", name, flags=re.IGNORECASE)
        if not m:
            return None
        try:
            gcd = float(m.group(1))
        except Exception:
            return None
        if 1.5 <= gcd <= 3.5:
            return gcd
        return None

    def _xivgear_materia_item_lookup(self) -> Dict[int, Tuple[int, int]]:
        lookup: Dict[int, Tuple[int, int]] = {}
        for base_param, category in (self.materia_catalog or {}).items():
            try:
                base_param_id = int(base_param)
            except Exception:
                continue
            for grade in category.grades:
                try:
                    lookup[int(grade.item_id)] = (base_param_id, int(grade.grade))
                except Exception:
                    continue
        return lookup

    def _xivgear_materia_export_lookup(self) -> Dict[Tuple[int, int], int]:
        lookup: Dict[Tuple[int, int], int] = {}
        for base_param, category in (self.materia_catalog or {}).items():
            try:
                base_param_id = int(base_param)
            except Exception:
                continue
            for grade in category.grades:
                try:
                    key = (base_param_id, int(grade.grade))
                    lookup[key] = int(grade.item_id)
                except Exception:
                    continue
        return lookup

    def _checked_saved_set_entries(self) -> List[dict]:
        return [
            entry
            for entry in self.saved_sets
            if isinstance(entry, dict) and bool(entry.get("export_checked", False))
        ]

    def _xivgear_export_food_id(self, food_id: Optional[int]) -> Optional[int]:
        food = self._find_food_by_id(food_id)
        if not food:
            return None
        source_row_id = int(getattr(food, "source_row_id", 0) or 0)
        if source_row_id > 0:
            return source_row_id
        resolved_food_id = int(getattr(food, "food_id", 0) or 0)
        return resolved_food_id or None

    def _xivgear_export_set(
        self,
        entry: dict,
        materia_lookup: Dict[Tuple[int, int], int],
    ) -> Tuple[Optional[dict], int]:
        if not isinstance(entry, dict):
            return None, 0
        gear_data = entry.get("gearset")
        if not isinstance(gear_data, dict):
            return None, 0
        gear = Gearset.from_dict(gear_data)
        if not gear.job:
            return None, 0
        context = self._saved_set_ui_context(entry, gear)
        gear = self._gearset_with_export_overrides(gear, context)
        items_blob: Dict[str, dict] = {}
        missing_materia = 0
        for slot in GEAR_SLOTS:
            sel = (gear.items or {}).get(slot)
            if not sel or not sel.item_id:
                continue
            xiv_slot = GEARSIM_TO_XIVGEAR_SLOT_MAP.get(slot)
            if not xiv_slot:
                continue
            materia_blob: List[dict] = []
            for meld in list(sel.materia or []):
                try:
                    key = (int(meld.base_param), int(meld.grade))
                except Exception:
                    continue
                materia_item_id = materia_lookup.get(key)
                if not materia_item_id:
                    missing_materia += 1
                    continue
                materia_blob.append({"id": int(materia_item_id), "locked": False})
            item_payload = {"id": int(sel.item_id), "materia": materia_blob}
            relic_stats = self._selection_relic_stats(sel)
            if relic_stats:
                item_payload["relicStats"] = {
                    XIVGEAR_RELIC_STAT_NAME_BY_ID[int(stat_id)]: int(value)
                    for stat_id, value in relic_stats.items()
                    if int(stat_id) in XIVGEAR_RELIC_STAT_NAME_BY_ID and int(value or 0) > 0
                }
            items_blob[xiv_slot] = item_payload
        if not items_blob:
            return None, missing_materia
        sync_enabled = bool(context.get("level_sync_enabled", False))
        sync_il = int(context.get("level_sync_il", 0) or 0) if sync_enabled else None
        level_value = xivmath.normalize_supported_level(context.get("level_sync_level", gear.level))
        target_gcd = gear.target_gcd if gear.target_gcd is not None else context.get("target_gcd")
        set_payload = {
            "name": str(entry.get("name") or "セット"),
            "items": items_blob,
            "food": self._xivgear_export_food_id(entry.get("food_id", gear.food_id)),
            "description": str(gear.note or ""),
            "isSeparator": False,
            "relicStatMemory": {},
            "materiaMemory": {},
            "job": gear.job,
            "partyBonus": int(context.get("party_bonus", entry.get("party_bonus", 0)) or 0),
            "level": int(level_value),
        }
        if sync_il:
            set_payload["ilvlSync"] = int(sync_il)
        if target_gcd:
            set_payload["target_gcd"] = float(target_gcd)
        return set_payload, missing_materia

    def _build_xivgear_export_payload(self, entries: List[dict]) -> Tuple[Optional[dict], int]:
        if not entries:
            return None, 0
        materia_lookup = self._xivgear_materia_export_lookup()
        export_sets: List[dict] = []
        missing_materia = 0
        jobs: List[str] = []
        levels: List[int] = []
        party_bonuses: List[int] = []
        sync_ils: List[int] = []
        target_gcds: List[float] = []
        first_context: Optional[dict] = None
        for entry in entries:
            gear_data = entry.get("gearset")
            gear = Gearset.from_dict(gear_data) if isinstance(gear_data, dict) else None
            set_payload, missing_count = self._xivgear_export_set(entry, materia_lookup)
            missing_materia += missing_count
            if not set_payload:
                continue
            export_sets.append(set_payload)
            if gear and gear.job:
                jobs.append(str(gear.job))
            levels.append(int(set_payload.get("level") or (gear.level if gear else xivmath.CURRENT_MAX_LEVEL)))
            party_bonuses.append(int(set_payload.get("partyBonus") or 0))
            if set_payload.get("ilvlSync") is not None:
                sync_ils.append(int(set_payload.get("ilvlSync") or 0))
            if set_payload.get("target_gcd") is not None:
                try:
                    target_gcds.append(float(set_payload.get("target_gcd")))
                except Exception:
                    pass
            if first_context is None and gear is not None:
                first_context = self._saved_set_ui_context(entry, gear)
        if not export_sets:
            return None, missing_materia
        first_job = jobs[0] if jobs else (self.current_gearset.job or "")
        unique_jobs = sorted(set(jobs))
        speed_pref = "spellspeed" if first_job in SPELL_SPEED_JOBS else "skillspeed"
        context = first_context or self._capture_saved_set_ui_context(first_job)
        item_il_min = int(context.get("item_il_min", 1) or 1)
        item_il_max = int(context.get("item_il_max", 999) or 999)
        food_il_min = int(context.get("food_il_min", 1) or 1)
        food_il_max = int(context.get("food_il_max", 999) or 999)
        payload = {
            "name": "GearSimulator Export",
            "sets": export_sets,
            "level": int(levels[0] if levels else xivmath.CURRENT_MAX_LEVEL),
            "job": first_job,
            "partyBonus": int(party_bonuses[0] if party_bonuses else 0),
            "sims": [{"stub": "pr-sim", "settings": {"includeInExport": True}, "name": "Dmg/100p"}],
            "itemDisplaySettings": {
                "showNq": False,
                "higherRelics": True,
                "minILvlFood": food_il_min,
                "maxILvlFood": food_il_max,
                "showOneStatFood": False,
                "minILvl": item_il_min,
                "maxILvl": item_il_max,
            },
            "mfm": "retain_item",
            "mfp": [speed_pref, "crit", "dhit", "determination"],
            "mfMinGcd": min(target_gcds) if target_gcds else 2.05,
            "description": "",
            "customItems": [],
            "customFoods": [],
            "timestamp": int(time.time() * 1000),
            "isMultiJob": len(unique_jobs) > 1,
            "specialStats": None,
        }
        if sync_ils:
            payload["ilvlSync"] = int(sync_ils[0])
        return payload, missing_materia

    def _build_bisbuddy_export_payload(self, entry: dict) -> Tuple[Optional[dict], int]:
        if not isinstance(entry, dict):
            return None, 0
        gear_data = entry.get("gearset")
        if not isinstance(gear_data, dict):
            return None, 0
        gear = Gearset.from_dict(gear_data)
        if not gear.job:
            return None, 0
        context = self._saved_set_ui_context(entry, gear)
        gear = self._gearset_with_export_overrides(gear, context)
        materia_lookup = self._xivgear_materia_export_lookup()
        gearpieces: List[dict] = []
        missing_materia = 0
        for slot in GEAR_SLOTS:
            sel = (gear.items or {}).get(slot)
            if not sel or not sel.item_id:
                continue
            materia_blob: List[dict] = []
            for meld in list(sel.materia or []):
                try:
                    key = (int(meld.base_param), int(meld.grade))
                except Exception:
                    continue
                materia_item_id = materia_lookup.get(key)
                if not materia_item_id:
                    missing_materia += 1
                    continue
                materia_blob.append(
                    {
                        "ItemId": int(materia_item_id),
                        "IsCollected": False,
                        "CollectLock": False,
                    }
                )
            gearpieces.append(
                {
                    "ItemId": int(sel.item_id),
                    "IsCollected": False,
                    "CollectLock": False,
                    "ItemMateria": materia_blob,
                }
            )
        if not gearpieces:
            return None, missing_materia
        payload = {
            "Id": str(uuid.uuid4()),
            "Name": str(entry.get("name") or "GearSimulator Set"),
            "SourceType": 2,
            "JobAbbrv": str(gear.job),
            "IsActive": True,
            "Priority": 0,
            "Gearpieces": gearpieces,
        }
        return payload, missing_materia

    def _gearset_dedup_signature(self, gear: Gearset) -> str:
        payload = gear.to_dict()
        encoded = json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        return hashlib.sha1(encoded.encode("utf-8")).hexdigest()

    def _build_xivgear_import_entries(self, payloads: List[dict]) -> Tuple[List[dict], List[int], int]:
        created: List[dict] = []
        unknown_materia: set = set()
        skipped = 0
        materia_lookup = self._xivgear_materia_item_lookup()
        existing_signatures: set = set()
        for entry in self.saved_sets:
            gear_data = entry.get("gearset")
            if not isinstance(gear_data, dict):
                continue
            try:
                existing_signatures.add(
                    hashlib.sha1(
                        json.dumps(
                            gear_data, ensure_ascii=False, sort_keys=True, separators=(",", ":")
                        ).encode("utf-8")
                    ).hexdigest()
                )
            except Exception:
                continue
        imported_signatures: set = set()

        def _to_int(v) -> Optional[int]:
            try:
                n = int(v)
            except Exception:
                return None
            return n if n > 0 else None

        def _iter_sets(blob: dict):
            sets = blob.get("sets")
            if isinstance(sets, list):
                for s in sets:
                    if isinstance(s, dict):
                        yield s
            elif isinstance(blob.get("items"), dict):
                yield blob

        now_ms = int(time.time() * 1000)
        entry_idx = 0
        for payload in payloads:
            top_job = payload.get("job")
            top_party_bonus = payload.get("partyBonus")
            top_level = payload.get("level")
            for set_data in _iter_sets(payload):
                if set_data.get("isSeparator"):
                    continue
                name = (
                    str(set_data.get("name") or "").strip()
                    or str(payload.get("name") or "").strip()
                    or f"XIVGear Set {entry_idx + 1}"
                )
                items_blob = set_data.get("items")
                if not isinstance(items_blob, dict):
                    skipped += 1
                    continue

                gear_items: Dict[str, ItemSelection] = {}
                for xiv_slot, item_blob in items_blob.items():
                    slot = XIVGEAR_SLOT_MAP.get(str(xiv_slot))
                    if not slot or not isinstance(item_blob, dict):
                        continue
                    item_id = _to_int(item_blob.get("id"))
                    materia_list: List[MateriaSlotSelection] = []
                    relic_stats: Dict[int, int] = {}
                    for m in (item_blob.get("materia") or []):
                        if not isinstance(m, dict):
                            continue
                        mat_item_id = _to_int(m.get("id"))
                        if not mat_item_id:
                            continue
                        mapped = materia_lookup.get(mat_item_id)
                        if not mapped:
                            unknown_materia.add(mat_item_id)
                            continue
                        materia_list.append(
                            MateriaSlotSelection(base_param=mapped[0], grade=mapped[1])
                        )
                    raw_relic_stats = item_blob.get("relicStats")
                    if isinstance(raw_relic_stats, dict):
                        for raw_name, raw_value in raw_relic_stats.items():
                            try:
                                stat_name = str(raw_name or "").strip().lower()
                                stat_value = int(raw_value or 0)
                            except Exception:
                                continue
                            stat_id = XIVGEAR_RELIC_STAT_ID_BY_NAME.get(stat_name)
                            if not stat_id or stat_value <= 0:
                                continue
                            relic_stats[int(stat_id)] = stat_value
                    gear_items[slot] = ItemSelection(item_id=item_id, materia=materia_list, relic_stats=relic_stats)

                if not gear_items:
                    skipped += 1
                    continue

                job = str(set_data.get("job") or top_job or self.current_gearset.job or "").strip()
                if not job:
                    skipped += 1
                    continue
                party_bonus_raw = set_data.get("partyBonus", top_party_bonus)
                try:
                    party_bonus = int(party_bonus_raw) if party_bonus_raw is not None else int(self.party_bonus.value())
                except Exception:
                    party_bonus = int(self.party_bonus.value())
                raw_food_id = _to_int(set_data.get("food") if set_data.get("food") is not None else payload.get("food"))
                food_id = self._resolve_food_id(raw_food_id)
                xivgear_sync_il = _to_int(
                    set_data.get("ilvlSync") if set_data.get("ilvlSync") is not None else payload.get("ilvlSync")
                )
                xivgear_level = xivmath.normalize_supported_level(set_data.get("level", top_level))
                target_gcd = self._xivgear_target_gcd_from_name(name)
                if target_gcd is None:
                    tg = set_data.get("target_gcd", payload.get("target_gcd"))
                    try:
                        target_gcd = float(tg) if tg is not None else None
                    except Exception:
                        target_gcd = None
                gear = Gearset(
                    job=job,
                    items=gear_items,
                    food_id=food_id,
                    target_gcd=target_gcd,
                    note=str(set_data.get("description") or ""),
                    race=DEFAULT_RACE,
                    level=xivgear_level,
                )
                sig = self._gearset_dedup_signature(gear)
                if sig in imported_signatures or sig in existing_signatures:
                    skipped += 1
                    continue
                imported_signatures.add(sig)
                ui_context = self._capture_saved_set_ui_context(job)
                ui_context["level_sync_level"] = int(xivgear_level)
                if xivgear_sync_il:
                    ui_context["level_sync_enabled"] = True
                    ui_context["level_sync_il"] = int(xivgear_sync_il)
                ui_context["party_bonus"] = party_bonus

                entry = {
                    "id": now_ms + entry_idx,
                    "name": name,
                    "saved_at": utc_now_iso(),
                    "mode": self.calc_mode.currentData() or "simdps_self",
                    "score": None,
                    "expected_score": None,
                    "gcd": target_gcd,
                    "food_id": food_id,
                    "gearset": gear.to_dict(),
                    "report_code": None,
                    "fight_id": None,
                    "actor_id": None,
                    "party_bonus": party_bonus,
                    "ui_context": ui_context,
                    "source": "xivgear_clipboard",
                    "locked": False,
                    "export_checked": False,
                }
                stats = self._compute_saved_stats(gear, food_id, party_bonus)
                if stats:
                    entry["stats"] = stats
                    entry["stats_version"] = STATS_VERSION
                created.append(entry)
                entry_idx += 1

        return created, sorted(unknown_materia), skipped

    def on_import_xivgear_clipboard(self) -> None:
        clipboard = QApplication.clipboard()
        raw = clipboard.text() if clipboard else ""
        if not raw or not raw.strip():
            QMessageBox.warning(self, "貼付けデータなし", "クリップボードにJSONテキストがありません。")
            return
        payloads = self._parse_json_objects_from_text(raw)
        if not payloads:
            QMessageBox.warning(self, "JSON不正", "クリップボードのJSONを解析できませんでした。")
            return
        entries, unknown_materia, skipped = self._build_xivgear_import_entries(payloads)
        if not entries:
            detail = ""
            if skipped:
                detail += f"\nスキップ: {skipped}件"
            if unknown_materia:
                preview = ", ".join(str(x) for x in unknown_materia[:12])
                suffix = " ..." if len(unknown_materia) > 12 else ""
                detail += f"\n未対応マテリアID: {preview}{suffix}"
            QMessageBox.information(self, "取込結果", f"取り込めるセットがありませんでした。{detail}")
            return
        self.saved_sets.extend(entries)
        self._schedule_saved_sets_flush(immediate=True)
        self._refresh_saved_sets_table()
        msg_lines = [f"{len(entries)}件のXIVGearセットを取り込みました。"]
        if skipped:
            msg_lines.append(f"スキップ: {skipped}件（重複/不正/不足データ）")
        if unknown_materia:
            preview = ", ".join(str(x) for x in unknown_materia[:12])
            suffix = " ..." if len(unknown_materia) > 12 else ""
            msg_lines.append(f"未対応マテリアID: {preview}{suffix}")
        self.progress_label.setText(f"XIVGear取込: {len(entries)}件")
        QMessageBox.information(self, "取込完了", "\n".join(msg_lines))

    def _entry_with_current_gearset_for_export(self, entry: dict) -> dict:
        if not isinstance(entry, dict):
            return entry
        entry_id = entry.get("id")
        if entry_id is None or entry_id != self._current_loaded_saved_set_id:
            return entry
        merged = dict(entry)
        merged["gearset"] = self.current_gearset.to_dict()
        merged["food_id"] = self.current_gearset.food_id
        merged["party_bonus"] = self.party_bonus.value()
        merged["ui_context"] = self._capture_saved_set_ui_context(self.current_gearset.job)
        return merged

    def _gearset_with_export_overrides(self, gear: Gearset, context: Optional[dict]) -> Gearset:
        return gearset_with_export_overrides(gear, context, self.items_by_id)

    def _copy_xivgear_entries_to_clipboard(self, entries: List[dict]) -> bool:
        if not entries:
            QMessageBox.warning(self, "対象なし", "出力対象の保存セットがありません。")
            return False
        export_entries = [self._entry_with_current_gearset_for_export(entry) for entry in entries]
        payload, missing_materia = self._build_xivgear_export_payload(export_entries)
        if not payload:
            QMessageBox.warning(self, "出力不可", "XIVGear形式で出力できる保存セットがありませんでした。")
            return False
        clipboard = QApplication.clipboard()
        if clipboard is None:
            QMessageBox.warning(self, "コピー失敗", "クリップボードを取得できませんでした。")
            return False
        clipboard.setText(json.dumps(payload, ensure_ascii=False, indent=2))
        message = f"{len(payload.get('sets') or [])}件の保存セットをXIVGear JSONとしてコピーしました。"
        if missing_materia > 0:
            message += f" マテリア {missing_materia}件は省略しました。"
        self.progress_label.setText(message)
        QMessageBox.information(self, "コピー完了", message)
        return True

    def on_export_bisbuddy_clipboard(self, entry: Optional[dict] = None) -> None:
        target = entry
        if not isinstance(target, dict):
            row = self.saved_sets_table.currentRow() if hasattr(self, "saved_sets_table") else -1
            if row >= 0 and hasattr(self, "saved_sets_table"):
                item = self.saved_sets_table.item(row, SAVED_COL_NAME)
                target = item.data(Qt.UserRole) if item else None
        if not isinstance(target, dict):
            QMessageBox.warning(self, "対象なし", "保存セットが選択されていません。")
            return
        target = self._entry_with_current_gearset_for_export(target)
        payload, missing_materia = self._build_bisbuddy_export_payload(target)
        if not payload:
            QMessageBox.warning(self, "出力不可", "BisBuddy 形式で出力できる保存セットではありません。")
            return
        clipboard = QApplication.clipboard()
        if clipboard is None:
            QMessageBox.warning(self, "コピー失敗", "クリップボードを取得できませんでした。")
            return
        clipboard.setText(json.dumps(payload, ensure_ascii=False, indent=2))
        message = "BisBuddy JSONとしてコピーしました。"
        if missing_materia > 0:
            message += f" マテリア {missing_materia}件は省略しました。"
        self.progress_label.setText(message)
        QMessageBox.information(self, "コピー完了", message)

    def on_save_set_to_history(self) -> None:
        # 保持しているマテリアを消さないため、保存時は明示的に必要項目のみ更新
        self.current_gearset.target_gcd = self.input_target_gcd.value()
        self._sync_food_selection_to_gearset()
        self.current_gearset.race = self._current_race()
        self.current_gearset.level = self._effective_calc_level()
        save_mode = self.calc_mode.currentData() or "simdps_self"
        current_eval = self._evaluate_current_gearset_scores(save_mode)
        if current_eval is None:
            res = QMessageBox.question(
                self,
                "結果なし",
                "計算結果がありません。スコアなしで保存しますか？",
                QMessageBox.Yes | QMessageBox.No,
            )
            if res != QMessageBox.Yes:
                return
        default_name = self.note_edit.toPlainText().strip() or f"セット {len(self.saved_sets) + 1}"
        name, ok = QInputDialog.getText(self, "セット名", "保存するセット名を入力してください。", text=default_name)
        if not ok:
            return
        name = (name or "").strip() or default_name
        food_id = self.current_gearset.food_id
        entry = {
            "id": int(time.time() * 1000),
            "name": name,
            "saved_at": utc_now_iso(),
            "mode": save_mode,
            "score": current_eval[0] if current_eval else None,
            "expected_score": current_eval[1] if current_eval else None,
            "gcd": current_eval[2] if current_eval else None,
            "food_id": food_id,
            "gearset": self.current_gearset.to_dict(),
            "report_code": extract_report_code(self.input_report_code.text()),
            "fight_id": self.selected_fight.get("id") if self.selected_fight else None,
            "actor_id": self.selected_actor.get("id") if self.selected_actor else None,
            "party_bonus": self.party_bonus.value(),
            "ui_context": self._capture_saved_set_ui_context(self.current_gearset.job),
            "locked": False,
            "export_checked": False,
        }
        stats = self._compute_saved_stats(self.current_gearset, food_id, self.party_bonus.value())
        if stats:
            entry["stats"] = stats
            entry["stats_version"] = STATS_VERSION
        if entry.get("score") is not None:
            score_meta = self._build_score_meta_for_entry(entry, str(entry["mode"]))
            if score_meta is not None:
                entry["score_meta"] = score_meta
        self.saved_sets.append(entry)
        self._schedule_saved_sets_flush(immediate=True)
        self._refresh_saved_sets_table()
        self.progress_label.setText("保存セットに追加しました。")

    def on_delete_saved_set(self) -> None:
        row = self.saved_sets_table.currentRow()
        if row < 0:
            return
        entry_item = self.saved_sets_table.item(row, SAVED_COL_NAME)
        entry = entry_item.data(Qt.UserRole) if entry_item else None
        if not entry:
            return
        res = QMessageBox.question(self, "削除", "選択中の保存セットを削除しますか？", QMessageBox.Yes | QMessageBox.No)
        if res != QMessageBox.Yes:
            return
        if entry.get("id") == self._current_loaded_saved_set_id:
            self._current_loaded_saved_set_id = None
        if entry.get("id") == self._simdps_baseline_entry_id:
            self._simdps_baseline_entry_id = None
            self._simdps_baseline_exact = False
            self._simdps_baseline_name = None
            self._log_gcd_constraint = None
            self._refresh_log_gcd_ui()
        self.saved_sets = [e for e in self.saved_sets if e.get("id") != entry.get("id")]
        self._schedule_saved_sets_flush(immediate=True)
        self._refresh_saved_sets_table()

    def on_saved_set_context_menu(self, pos) -> None:
        if self._updating_saved_table or self._saved_sets_reordering:
            return
        table = self.saved_sets_table
        item = table.itemAt(pos)
        if not item:
            return
        row = item.row()
        if row < 0:
            return
        if table.currentRow() != row:
            blocker = QSignalBlocker(table)
            table.setCurrentCell(row, SAVED_COL_NAME)
            del blocker
        entry_item = table.item(row, SAVED_COL_NAME)
        entry = entry_item.data(Qt.UserRole) if entry_item else None
        if not isinstance(entry, dict):
            return
        menu = QMenu(table)
        checked_entries = self._checked_saved_set_entries()
        action_xivgear_export = menu.addAction("XIVGear ｴｸｽﾎﾟｰﾄ")
        action_xivgear_export_checked = None
        if checked_entries:
            action_xivgear_export_checked = menu.addAction("XIVGear ｴｸｽﾎﾟｰﾄ(ﾁｪｯｸ済み)")
        action_bisbuddy_export = menu.addAction("BisBuddy ｴｸｽﾎﾟｰﾄ")
        action_log_baseline = menu.addAction("ログ基準装備に設定")
        menu.addSeparator()
        action_delete = menu.addAction("削除")
        chosen = menu.exec(table.viewport().mapToGlobal(pos))
        if chosen is action_xivgear_export:
            self._copy_xivgear_entries_to_clipboard([entry])
        elif action_xivgear_export_checked is not None and chosen is action_xivgear_export_checked:
            self._copy_xivgear_entries_to_clipboard(checked_entries)
        elif chosen is action_bisbuddy_export:
            self.on_export_bisbuddy_clipboard(entry)
        elif chosen is action_log_baseline:
            self._set_saved_set_as_log_baseline(entry)
        elif chosen is action_delete:
            self.on_delete_saved_set()

    def _set_saved_set_as_log_baseline(self, entry: dict) -> None:
        code = extract_report_code(self.input_report_code.text())
        fight_id = self.selected_fight.get("id") if self.selected_fight else None
        actor_id = self.selected_actor.get("id") if self.selected_actor else None
        entry_code = extract_report_code(str(entry.get("report_code") or ""))
        try:
            exact_context = (
                bool(code)
                and entry_code == code
                and int(entry.get("fight_id")) == int(fight_id)
                and int(entry.get("actor_id")) == int(actor_id)
            )
        except (TypeError, ValueError):
            exact_context = False
        gear = Gearset.from_dict(entry.get("gearset") or {})
        context = entry.get("ui_context")
        if exact_context and isinstance(context, dict):
            saved_sync = context.get("level_sync_enabled")
            if saved_sync is not None and bool(saved_sync) != self._level_sync_enabled():
                exact_context = False
            if exact_context and bool(saved_sync):
                try:
                    if context.get("level_sync_il") is not None:
                        exact_context = int(context.get("level_sync_il")) == self._level_sync_il_value()
                    if exact_context and context.get("level_sync_level") is not None:
                        exact_context = int(context.get("level_sync_level")) == self._effective_calc_level()
                except (TypeError, ValueError):
                    exact_context = False
        if not exact_context or gear.job != self.current_gearset.job:
            QMessageBox.warning(
                self,
                "ログ条件不一致",
                "現在選択中のReport・Fight・Actor・ジョブと完全一致する保存セットだけをログ基準にできます。",
            )
            return
        for saved in self.saved_sets:
            if not isinstance(saved, dict):
                continue
            saved_code = extract_report_code(str(saved.get("report_code") or ""))
            if (
                saved_code == code
                and saved.get("fight_id") == entry.get("fight_id")
                and saved.get("actor_id") == entry.get("actor_id")
            ):
                saved.pop("baseline_role", None)
        entry["baseline_role"] = "log_source"
        self._schedule_saved_sets_flush(immediate=True)
        self._simdps_baseline_gearset = Gearset.from_dict(gear.to_dict())
        self._simdps_baseline_exact = True
        self._simdps_baseline_name = str(entry.get("name") or "")
        self._simdps_baseline_entry_id = entry.get("id")
        self._simdps_baseline_party = int(entry.get("party_bonus", self.party_bonus.value()))
        self._simdps_baseline_race = gear.race or self._current_race()
        self._update_simdps_baseline_data()
        self._refresh_log_gcd_profile()
        self.progress_label.setText(f"「{self._simdps_baseline_name}」をログ基準装備に設定しました。")

    def on_saved_set_selected(self) -> None:
        if self._saved_sets_reordering or self._updating_saved_table:
            return
        row = self.saved_sets_table.currentRow()
        if row < 0:
            return
        entry_item = self.saved_sets_table.item(row, SAVED_COL_NAME)
        entry = entry_item.data(Qt.UserRole) if entry_item else None
        if not entry:
            return
        gear_data = entry.get("gearset")
        if not gear_data:
            return
        gear = Gearset.from_dict(gear_data)
        needs_score_recalculation = self._begin_saved_score_recalculation(entry)
        # A saved-set selection must run once even when its inputs match the last preview.
        self._last_preview_signature = None
        self._pending_saved_set_entry = entry
        restored_ui_context = self._saved_set_ui_context(entry, gear)
        self._pending_saved_set_ui_context = restored_ui_context
        self._persist_saved_set_ui_context(entry, restored_ui_context)
        self._current_loaded_saved_set_id = entry.get("id")
        self._apply_gearset_to_ui(gear)
        self.last_eval = None
        if hasattr(self, "calc_result_label_left"):
            self.calc_result_label_left.setText(
                "計算結果: 保存スコアを再計算中..."
                if needs_score_recalculation
                else "計算結果: 更新中..."
            )
        self._schedule_auto_score_update()

    def on_saved_set_item_changed(self, item: QTableWidgetItem) -> None:
        if self._updating_saved_table:
            return
        if not item:
            return
        entry = item.data(Qt.UserRole)
        if not isinstance(entry, dict):
            return
        if item.column() == SAVED_COL_EXPORT:
            entry_id = entry.get("id")
            new_checked = item.checkState() == Qt.Checked
            entry["export_checked"] = new_checked
            for e in self.saved_sets:
                if isinstance(e, dict) and e.get("id") == entry_id:
                    e["export_checked"] = new_checked
                    break
            self._schedule_saved_sets_flush(immediate=False)
            return
        if item.column() != SAVED_COL_NAME:
            return
        new_name = item.text().strip()
        if not new_name:
            self._updating_saved_table = True
            item.setText(entry.get("name") or "セット")
            self._updating_saved_table = False
            return
        entry_id = entry.get("id")
        for e in self.saved_sets:
            if e.get("id") == entry_id:
                e["name"] = new_name
                break
        self._schedule_saved_sets_flush(immediate=True)

    def on_saved_set_cell_clicked(self, row: int, column: int) -> None:
        if self._updating_saved_table or self._saved_sets_reordering:
            return
        if row < 0 or column != SAVED_COL_LOCK:
            return
        entry_item = self.saved_sets_table.item(row, SAVED_COL_NAME)
        if not entry_item:
            return
        entry = entry_item.data(Qt.UserRole)
        if not isinstance(entry, dict):
            return
        entry_id = entry.get("id")
        target = None
        for e in self.saved_sets:
            if isinstance(e, dict) and e.get("id") == entry_id:
                target = e
                break
        if target is None:
            return
        new_locked = not bool(target.get("locked", False))
        target["locked"] = new_locked
        entry["locked"] = new_locked
        entry_item.setData(Qt.UserRole, entry)
        lock_item = self.saved_sets_table.item(row, SAVED_COL_LOCK)
        if lock_item:
            lock_item.setText("🔒" if new_locked else "🔓")
        self._schedule_saved_sets_flush(immediate=True)
        self.progress_label.setText("保存セットをロックしました。" if new_locked else "保存セットのロックを解除しました。")

    def _saved_set_entry_job(self, entry: dict) -> Optional[str]:
        if not isinstance(entry, dict):
            return None
        entry_job = entry.get("job")
        if entry_job:
            return str(entry_job)
        gear_data = entry.get("gearset") or {}
        job = gear_data.get("job")
        if not job:
            return None
        return str(job)

    def _saved_set_visible_for_job(self, entry: dict, selected_job: Optional[str]) -> bool:
        entry_job = self._saved_set_entry_job(entry)
        if selected_job and entry_job and entry_job != selected_job:
            return False
        return True

    def _on_saved_sets_rows_about_to_move(self, *args) -> None:
        self._saved_sets_reordering = True
        self._auto_calc_timer.stop()

    def _on_saved_sets_rows_moved(self, *args) -> None:
        try:
            if self._updating_saved_table:
                return
            self._sync_saved_sets_order_from_table()
        finally:
            QTimer.singleShot(0, self._finish_saved_sets_reorder)

    def _finish_saved_sets_reorder(self) -> None:
        self._saved_sets_reordering = False

    def _sync_saved_sets_order_from_table(self) -> None:
        if not hasattr(self, "saved_sets_table"):
            return
        if not isinstance(self.saved_sets, list) or len(self.saved_sets) <= 1:
            return
        selected_job = self.job_combo.currentData() if hasattr(self, "job_combo") else None
        visible_entries = [
            entry
            for entry in self.saved_sets
            if self._saved_set_visible_for_job(entry, selected_job)
        ]
        if len(visible_entries) <= 1:
            return

        table_entries: List[dict] = []
        for row in range(self.saved_sets_table.rowCount()):
            name_item = self.saved_sets_table.item(row, SAVED_COL_NAME)
            entry = name_item.data(Qt.UserRole) if name_item else None
            if isinstance(entry, dict):
                table_entries.append(entry)
        if not table_entries:
            return

        # Resolve table rows back to the canonical objects inside self.saved_sets.
        by_id: Dict[int, List[dict]] = {}
        for entry in visible_entries:
            entry_id = entry.get("id")
            if isinstance(entry_id, int):
                by_id.setdefault(entry_id, []).append(entry)

        resolved_visible: List[dict] = []
        used_obj_ids: set = set()
        for table_entry in table_entries:
            resolved = None
            table_id = table_entry.get("id")
            if isinstance(table_id, int):
                candidates = by_id.get(table_id) or []
                while candidates:
                    candidate = candidates.pop(0)
                    if id(candidate) not in used_obj_ids:
                        resolved = candidate
                        break
            if resolved is None and table_entry in visible_entries and id(table_entry) not in used_obj_ids:
                resolved = table_entry
            if resolved is not None and id(resolved) not in used_obj_ids:
                resolved_visible.append(resolved)
                used_obj_ids.add(id(resolved))

        for entry in visible_entries:
            if id(entry) not in used_obj_ids:
                resolved_visible.append(entry)
                used_obj_ids.add(id(entry))

        if len(resolved_visible) != len(visible_entries):
            return

        it = iter(resolved_visible)
        new_saved_sets: List[dict] = []
        changed = False
        for entry in self.saved_sets:
            if self._saved_set_visible_for_job(entry, selected_job):
                moved = next(it)
                new_saved_sets.append(moved)
                if moved is not entry:
                    changed = True
            else:
                new_saved_sets.append(entry)

        if changed:
            self.saved_sets = new_saved_sets
            self._schedule_saved_sets_flush(immediate=False)

    def _apply_gearset_to_ui(self, gear: Gearset) -> None:
        if not self._applying_optimal_variant_tab:
            self._clear_optimal_variant_tabs()
        gear.race = DEFAULT_RACE
        gear.level = self._infer_sync_level_from_gear(gear)
        gear.food_id = self._resolve_food_id(gear.food_id)
        gear = self._normalize_unique_ring_duplicates(gear)
        pending_entry = self._pending_saved_set_entry if isinstance(self._pending_saved_set_entry, dict) else None
        pending_ui_context = self._pending_saved_set_ui_context if isinstance(self._pending_saved_set_ui_context, dict) else None
        need_job_reload = bool(
            gear.job
            and (
                gear.job not in self.items_by_job
                or not self._gearset_items_ready(gear)
            )
        )
        if need_job_reload:
            self._pending_gearset = gear
            idx = self.job_combo.findData(gear.job)
            if idx != -1:
                self.job_combo.blockSignals(True)
                self.job_combo.setCurrentIndex(idx)
                self.job_combo.blockSignals(False)
            # Trigger load for the job if needed
            if gear.job:
                if self.active_worker:
                    return
                def task(progress=None, stop_event=None):
                    items = self.xiv_client.fetch_items_for_jobs([gear.job], force=False, progress=progress, stop_event=stop_event)
                    return items
                self.start_worker(
                    task,
                    lambda items: self._after_items(gear.job, items),
                    lock_job_context=True,
                )
            return

        self._applying_gearset = True
        self.setUpdatesEnabled(False)
        self.current_gearset = gear
        self.job_combo.blockSignals(True)
        self.food_combo.blockSignals(True)
        self.race_clan_combo.blockSignals(True)
        self.party_bonus.blockSignals(True)
        for checkbox in self.slot_lock_item_checks.values():
            checkbox.blockSignals(True)
        for checkbox in self.slot_lock_materia_checks.values():
            checkbox.blockSignals(True)
        for table in self.slot_tables.values():
            table.blockSignals(True)
        try:
            if gear.job:
                idx = self.job_combo.findData(gear.job)
                if idx != -1 and self.job_combo.currentIndex() != idx:
                    self.job_combo.setCurrentIndex(idx)
                if gear.job in self.items_by_job and self.base_params and self.item_levels:
                    self.cap_table = optimizer.build_cap_table(
                        self.items_by_job[gear.job],
                        self.base_params,
                        self.item_levels,
                        gear.job,
                    )
                    self._raw_stats_cache.clear()
                if gear.job in self.items_by_job:
                    if pending_entry is not None:
                        refreshed_ui_context = self._saved_set_ui_context(pending_entry, gear)
                        pending_ui_context = refreshed_ui_context
                        self._pending_saved_set_ui_context = refreshed_ui_context
                        self._persist_saved_set_ui_context(pending_entry, refreshed_ui_context)
                    elif pending_ui_context is None:
                        self._current_export_item_ids = {}
                    self._apply_saved_set_ui_context(pending_ui_context, gear.job)
                    self._ensure_il_filter_for_gearset(gear, pending_ui_context, immediate=True)
                    need_populate = gear.job != self._last_populated_job
                    if not need_populate:
                        for table in self.slot_tables.values():
                            if table.rowCount() <= 1:
                                need_populate = True
                                break
                    if need_populate:
                        self.populate_items(gear.job, immediate=True)
            self._set_race_clan(gear.race)
            target_gcd = float(gear.target_gcd or 2.5)
            if abs(float(self.input_target_gcd.value()) - target_gcd) > 0.0005:
                self.input_target_gcd.setValue(target_gcd)
            note_text = str(gear.note or "")
            if self.note_edit.toPlainText() != note_text:
                self.note_edit.setPlainText(note_text)
            for slot in self.slot_tables.keys():
                sel = (gear.items or {}).get(slot) or ItemSelection()
                item_lock = self.slot_lock_item_checks.get(slot)
                if item_lock is not None:
                    desired_item_lock = bool(getattr(sel, "lock_item", False))
                    if item_lock.isChecked() != desired_item_lock:
                        item_lock.setChecked(desired_item_lock)
                materia_lock = self.slot_lock_materia_checks.get(slot)
                if materia_lock is not None:
                    desired_materia_lock = bool(getattr(sel, "lock_materia", False))
                    if materia_lock.isChecked() != desired_materia_lock:
                        materia_lock.setChecked(desired_materia_lock)
            if not self._is_populating:
                for slot, sel in gear.items.items():
                    table = self.slot_tables.get(slot)
                    if not table:
                        continue
                    self._select_table_row(table, sel.item_id)
            self._refresh_all_slot_exclusion_visuals()
            self._ensure_food_combo_item(gear.food_id)
            target_food_data = (
                FOOD_SIMULATION_DATA
                if bool(getattr(gear, "food_simulation", False))
                else self._resolve_food_id(gear.food_id)
            )
            idx = self.food_combo.findData(target_food_data)
            target_index = idx if idx != -1 else 0
            if self.food_combo.currentIndex() != target_index:
                self.food_combo.setCurrentIndex(target_index)
        finally:
            for table in self.slot_tables.values():
                table.blockSignals(False)
            for checkbox in self.slot_lock_materia_checks.values():
                checkbox.blockSignals(False)
            for checkbox in self.slot_lock_item_checks.values():
                checkbox.blockSignals(False)
            self.party_bonus.blockSignals(False)
            self.race_clan_combo.blockSignals(False)
            self.food_combo.blockSignals(False)
            self.job_combo.blockSignals(False)
            self.setUpdatesEnabled(True)
            self._applying_gearset = False
            if pending_entry is self._pending_saved_set_entry:
                self._pending_saved_set_entry = None
            if pending_ui_context is self._pending_saved_set_ui_context:
                self._pending_saved_set_ui_context = None
        if not self._is_populating:
            for slot in self.slot_tables.keys():
                self._refresh_slot_selected_display(slot)
        self._update_optimize_button_text()
        self._schedule_auto_score_update()

    # ---- FFLogs handlers ----
    def _fflogs_context_matches(
        self,
        report_code: str,
        fight_id: Optional[int] = None,
        actor_id: Optional[int] = None,
    ) -> bool:
        if extract_report_code(self.input_report_code.text()) != report_code:
            return False
        if fight_id is not None:
            current_fight_id = (self.selected_fight or {}).get("id")
            if current_fight_id != fight_id:
                return False
        if actor_id is not None:
            current_actor_id = (self.selected_actor or {}).get("id")
            if current_actor_id != actor_id:
                return False
        return True

    def on_load_fights(self) -> None:
        client_id = self.input_client_id.text().strip() if hasattr(self, "input_client_id") else ""
        client_secret = self.input_client_secret.text().strip() if hasattr(self, "input_client_secret") else ""
        if client_id and client_secret:
            self.ff_client.set_credentials(client_id, client_secret)
        code = extract_report_code(self.input_report_code.text())
        if not code:
            QMessageBox.warning(self, "入力不正", "FFLogsレポートコードまたはURLを正しく入力してください。")
            return
        force_refresh = self._fflogs_force_refresh_enabled()
        if force_refresh:
            self.ff_client.clear_cache()
        cached = None if force_refresh else self._load_report_cache(code, sections=["fights"])
        if cached and cached.get("fights"):
            self._after_fights(
                {"fights": cached.get("fights", []), "enemy_npcs": cached.get("enemy_npcs", [])},
                from_cache=True,
                request_code=code,
            )
            return
        if not self.ff_client.ready():
            QMessageBox.warning(self, "認証情報未設定", "先にFFLogs V2のクライアント情報を設定してください。")
            return

        def task(progress=None, stop_event=None):
            fights = self.ff_client.fetch_fights(code)
            if progress:
                progress(100, f"ファイト {len(fights)} 件取得")
            return {"fights": fights, "enemy_npcs": self.ff_client.last_enemy_npcs}

        self.start_worker(
            task,
            lambda result: self._after_fights(result, request_code=code),
            lock_fflogs_context=True,
        )

    def _after_fights(
        self,
        fights: object,
        from_cache: bool = False,
        request_code: Optional[str] = None,
    ) -> None:
        code = request_code or extract_report_code(self.input_report_code.text())
        if request_code and not self._fflogs_context_matches(request_code):
            logger.info("Discarded stale FFLogs fights result for report %s", request_code)
            return
        raw_fights: List[dict] = []
        enemy_npcs: List[dict] = []
        if isinstance(fights, dict):
            raw_fights = fights.get("fights") or []
            enemy_npcs = fights.get("enemy_npcs") or []
        else:
            raw_fights = fights or []
        self.enemy_npcs = enemy_npcs
        self._raw_fights = raw_fights
        self._refresh_fight_list()
        if code and not from_cache:
            self._save_report_cache(code, fights=raw_fights, enemy_npcs=self.enemy_npcs)
        if not self.fights:
            self.progress_label.setText("撃破ファイトが見つかりませんでした")
        else:
            self.progress_label.setText("ファイトを読み込みました（キャッシュ）" if from_cache else "ファイトを読み込みました")
        self.on_save_auth(silent=True)
        if self._pending_fight_id:
            self._select_fight_by_id(self._pending_fight_id)
            self._pending_fight_id = None
        self._reset_phase_combo()

    def _is_kill_fight(self, fight: dict) -> bool:
        if fight is None:
            return False
        kill = fight.get("kill")
        if isinstance(kill, bool):
            return kill
        if isinstance(kill, (int, float)) and kill == 1:
            return True
        boss_pct = fight.get("bossPercentage")
        if boss_pct is not None:
            try:
                if float(boss_pct) <= 0:
                    return True
            except Exception:
                pass
        fight_pct = fight.get("fightPercentage")
        if fight_pct is not None:
            try:
                if float(fight_pct) <= 0:
                    return True
            except Exception:
                pass
        return False

    def _refresh_fight_list(self) -> None:
        include_wipes = bool(self.chk_include_wipes.isChecked()) if hasattr(self, "chk_include_wipes") else False
        if include_wipes:
            self.fights = list(self._raw_fights or [])
        else:
            self.fights = [f for f in (self._raw_fights or []) if self._is_kill_fight(f)]
        self.fight_list.clear()
        for fight in self.fights:
            start_time = fight.get("startTime", fight.get("start_time", 0))
            end_time = fight.get("endTime", fight.get("end_time", 0))
            dur = (end_time - start_time) / 1000
            item = QListWidgetItem(f"#{fight.get('id')} {fight.get('name')} ({dur:.1f}s)")
            item.setData(Qt.UserRole, fight)
            self.fight_list.addItem(item)

    def _reset_phase_combo(self) -> None:
        if not hasattr(self, "phase_list") or self.phase_list is None:
            return
        self.phase_list.blockSignals(True)
        self.phase_list.clear()
        item = QListWidgetItem("全フェーズ")
        item.setData(Qt.UserRole, None)
        self.phase_list.addItem(item)
        self.phase_list.setCurrentRow(0)
        self.phase_list.blockSignals(False)
        self._phase_transitions = []
        self._phase_meta = {}

    def _on_include_wipes_toggled(self, _checked: bool) -> None:
        self._refresh_fight_list()

    def _on_phase_changed(self) -> None:
        # During startup the phase list can emit before gear controls are built.
        if not hasattr(self, "party_bonus"):
            return
        self.on_save_auth(silent=True)

    def _populate_phase_from_transitions(self) -> None:
        if not hasattr(self, "phase_list") or self.phase_list is None:
            return
        transitions = [t for t in (self._phase_transitions or []) if isinstance(t, dict) and t.get("startTime") is not None]
        if not transitions:
            return
        transitions = sorted(transitions, key=lambda t: t.get("startTime"))
        fight = self.selected_fight or {}
        fight_end = fight.get("endTime", fight.get("end_time"))
        self.phase_list.blockSignals(True)
        self.phase_list.clear()
        item = QListWidgetItem("全フェーズ")
        item.setData(Qt.UserRole, None)
        self.phase_list.addItem(item)
        for idx, t in enumerate(transitions, start=1):
            pid = t.get("id")
            try:
                pid = int(pid)
            except Exception:
                pid = idx
            start = t.get("startTime")
            end = transitions[idx].get("startTime") if idx < len(transitions) else fight_end
            label = f"P{idx}"
            phase_item = QListWidgetItem(label)
            phase_item.setData(Qt.UserRole, {"id": pid, "start": start, "end": end})
            self.phase_list.addItem(phase_item)
        self.phase_list.setCurrentRow(0)
        self.phase_list.blockSignals(False)

    def _resolve_phase_window(self, fight: dict) -> Tuple[Optional[int], Optional[int]]:
        start_time = fight.get("startTime", fight.get("start_time"))
        end_time = fight.get("endTime", fight.get("end_time"))
        if not hasattr(self, "phase_list") or self.phase_list is None:
            return start_time, end_time
        phase_item = self.phase_list.currentItem()
        phase_data = phase_item.data(Qt.UserRole) if phase_item else None
        if phase_data is None:
            return start_time, end_time
        if isinstance(phase_data, dict):
            p_start = phase_data.get("start")
            p_end = phase_data.get("end")
            if p_start is not None:
                start_time = p_start
            if p_end is not None:
                end_time = p_end
            return start_time, end_time
        phase_id = phase_data
        transitions = [t for t in (self._phase_transitions or []) if isinstance(t, dict)]
        if not transitions:
            return start_time, end_time
        # Sort by time to compute phase windows.
        transitions = sorted(
            [t for t in transitions if t.get("startTime") is not None],
            key=lambda t: t.get("startTime"),
        )
        idx = None
        for i, t in enumerate(transitions):
            tid = t.get("id")
            try:
                tid = int(tid)
            except Exception:
                pass
            if tid == phase_id:
                idx = i
                break
        if idx is None:
            return start_time, end_time
        start_time = transitions[idx].get("startTime", start_time)
        if idx + 1 < len(transitions):
            end_time = transitions[idx + 1].get("startTime", end_time)
        return start_time, end_time

    def on_fight_selected(self) -> None:
        items = self.fight_list.selectedItems()
        if not items:
            return
        fight = items[0].data(Qt.UserRole)
        if not isinstance(fight, dict):
            return
        fight = dict(fight)
        fight_id = fight.get("id")
        self.selected_fight = fight
        self._reset_phase_combo()
        self._phase_transitions = fight.get("phaseTransitions") or []
        self._phase_transitions = sorted(
            [t for t in self._phase_transitions if isinstance(t, dict) and t.get("startTime") is not None],
            key=lambda t: t.get("startTime"),
        )
        self._populate_phase_from_transitions()
        code = extract_report_code(self.input_report_code.text())
        self.on_save_auth(silent=True)
        self.selected_actor = None
        self.actor_list.clear()
        cached = (
            self._load_report_cache(code, sections=["players_by_fight"])
            if code and not self._fflogs_force_refresh_enabled()
            else None
        )
        if cached:
            players_by_fight = cached.get("players_by_fight", {})
            cached_players = players_by_fight.get(str(fight.get("id")))
            if cached_players:
                self._after_players(
                    cached_players,
                    from_cache=True,
                    request_code=code,
                    request_fight_id=fight_id,
                )
                if code and fight:
                    self._load_phases_for_fight(code, fight)
                return

        def task(progress=None, stop_event=None):
            players = self.ff_client.fetch_players(code, fight.get("id"))
            phases_payload = {}
            if code and fight:
                encounter_id = fight.get("encounterID") or fight.get("encounterId")
                norm_encounter = None
                if encounter_id is not None:
                    try:
                        norm_encounter = int(encounter_id)
                    except Exception:
                        norm_encounter = None
                phases_payload = self.ff_client.fetch_phases(code, norm_encounter) or {}
            if progress:
                progress(100, f"アクター {len(players)} 件取得")
            return {"players": players, "phases_payload": phases_payload}

        self.start_worker(
            task,
            lambda result: self._after_players(
                result,
                request_code=code,
                request_fight_id=fight_id,
            ),
            lock_fflogs_context=True,
        )

    def _load_phases_for_fight(self, report_code: str, fight: dict) -> None:
        if self.active_worker:
            self._pending_phase_request = (report_code, dict(fight))
            return
        encounter_id = fight.get("encounterID") or fight.get("encounterId")
        fight_id = fight.get("id")

        def task(progress=None, stop_event=None):
            norm_encounter = None
            if encounter_id is not None:
                try:
                    norm_encounter = int(encounter_id)
                except Exception:
                    norm_encounter = None
            phases_payload = self.ff_client.fetch_phases(report_code, norm_encounter)
            return phases_payload or {}

        def after(payload):
            if self._fflogs_context_matches(report_code, fight_id):
                self._apply_phase_payload(payload)
            else:
                logger.info("Discarded stale FFLogs phase result for report %s", report_code)

        self.start_worker(
            task,
            after,
            silent_if_busy=True,
            lock_fflogs_context=True,
        )

    def _resolve_actor_job(self, actor: dict) -> Optional[str]:
        if not isinstance(actor, dict):
            return None
        candidates: List[object] = [
            actor.get("job"),
            actor.get("subType"),
            actor.get("type"),
            actor.get("spec"),
            actor.get("actorType"),
            actor.get("icon"),
        ]
        aliases = {
            "paladin": "PLD",
            "warrior": "WAR",
            "darkknight": "DRK",
            "gunbreaker": "GNB",
            "whitemage": "WHM",
            "scholar": "SCH",
            "astrologian": "AST",
            "sage": "SGE",
            "monk": "MNK",
            "dragoon": "DRG",
            "ninja": "NIN",
            "samurai": "SAM",
            "reaper": "RPR",
            "viper": "VPR",
            "bard": "BRD",
            "machinist": "MCH",
            "dancer": "DNC",
            "blackmage": "BLM",
            "summoner": "SMN",
            "redmage": "RDM",
            "pictomancer": "PCT",
            "limitbreak": "LB",
            "limit break": "LB",
        }
        for raw in candidates:
            if raw is None:
                continue
            val = str(raw).strip()
            if not val:
                continue
            upper = val.upper()
            if upper in JOB_ORDER:
                return upper
            mapped = JOB_NAME_MAP.get(val) or JOB_NAME_MAP.get(val.replace(" ", ""))
            if mapped:
                return mapped
            for job in JOB_ORDER:
                if job and job in upper:
                    return job
            norm = val.lower().replace(" ", "").replace("_", "").replace("-", "")
            if norm in aliases:
                return aliases[norm]
        return None

    def _apply_phase_payload(self, payload: object) -> None:
        phases = payload.get("phases") if isinstance(payload, dict) else None
        if not isinstance(phases, list):
            self._populate_phase_from_transitions()
            return
        transitions = [
            t for t in (self._phase_transitions or [])
            if isinstance(t, dict) and t.get("startTime") is not None
        ]
        transitions = sorted(transitions, key=lambda t: t.get("startTime"))
        fight = self.selected_fight or {}
        fight_end = fight.get("endTime", fight.get("end_time"))
        self.phase_list.blockSignals(True)
        self.phase_list.clear()
        all_item = QListWidgetItem("全フェーズ")
        all_item.setData(Qt.UserRole, None)
        self.phase_list.addItem(all_item)
        self._phase_meta = {}
        for idx, ph in enumerate(phases):
            try:
                pid = int(ph.get("id"))
            except Exception:
                continue
            name = ph.get("name") or f"P{pid}"
            if ph.get("isIntermission"):
                name = f"{name} (インターミッション)"
            # Map phase by transition order to guarantee a valid time window
            # even if phase id does not match transition id.
            start = transitions[idx].get("startTime") if idx < len(transitions) else None
            if idx + 1 < len(transitions):
                end = transitions[idx + 1].get("startTime")
            else:
                end = fight_end
            phase_item = QListWidgetItem(name)
            phase_item.setData(Qt.UserRole, {"id": pid, "start": start, "end": end})
            self.phase_list.addItem(phase_item)
            self._phase_meta[pid] = ph
        self.phase_list.setCurrentRow(0)
        self.phase_list.blockSignals(False)
        if self.phase_list.count() <= 1:
            self._populate_phase_from_transitions()

    def _after_players(
        self,
        players: List[dict],
        from_cache: bool = False,
        request_code: Optional[str] = None,
        request_fight_id: Optional[int] = None,
    ) -> None:
        code = request_code or extract_report_code(self.input_report_code.text())
        fight_id = request_fight_id
        if fight_id is None and self.selected_fight:
            fight_id = self.selected_fight.get("id")
        if request_code and not self._fflogs_context_matches(request_code, request_fight_id):
            logger.info(
                "Discarded stale FFLogs players result for report %s fight %s",
                request_code,
                request_fight_id,
            )
            return
        phase_payload = None
        if isinstance(players, dict):
            phase_payload = players.get("phases_payload")
            players = players.get("players") or []
        filtered_players: List[dict] = []
        for actor in players or []:
            job = self._resolve_actor_job(actor)
            if not job or job not in JOB_ORDER:
                continue
            # Copy so cached objects are not mutated unexpectedly.
            actor_copy = dict(actor)
            actor_copy["job"] = job
            filtered_players.append(actor_copy)
        self.players = sorted(
            filtered_players,
            key=lambda p: (
                JOB_ORDER.index(p.get("job")) if p.get("job") in JOB_ORDER else 999,
                str(p.get("name") or "").lower(),
            ),
        )
        self.friendly_ids = {p.get("id") for p in self.players if p.get("id") is not None}
        # Rebuild job filter to only show jobs present in this fight.
        self.actor_job_filter.blockSignals(True)
        self.actor_job_filter.clear()
        self.actor_job_filter.addItem("全ジョブ", None)
        present_jobs = {p.get("job") for p in self.players if p.get("job")}
        for job in JOB_ORDER:
            if job in present_jobs:
                self.actor_job_filter.addItem(job, job)
        self.actor_job_filter.blockSignals(False)
        self.actor_list.clear()
        for actor in self.players:
            job = actor.get("job")
            name = actor.get("name")
            item = QListWidgetItem(f"({job}) {name}")
            item.setData(Qt.UserRole, actor)
            self.actor_list.addItem(item)
        self.filter_actors()
        if self.actor_list.count() > 0 and not self.actor_list.currentItem():
            self.actor_list.setCurrentRow(0)
        if code and fight_id is not None and not from_cache:
            cached = self._load_report_cache(code, allow_stale=True) or {
                "code": code,
                "fights": self.fights,
                "players_by_fight": {},
            }
            players_by_fight = cached.get("players_by_fight", {})
            if not isinstance(players_by_fight, dict):
                players_by_fight = {}
            players_by_fight[str(fight_id)] = self.players
            self._save_report_cache(code, players_by_fight=players_by_fight)
        if self._pending_actor_id:
            self._select_actor_by_id(self._pending_actor_id)
            self._pending_actor_id = None
        if from_cache:
            self.progress_label.setText("アクターを読み込みました（キャッシュ）")
        if phase_payload:
            self._apply_phase_payload(phase_payload)

    def filter_actors(self) -> None:
        text = self.actor_search.text().lower()
        job_filter = self.actor_job_filter.currentData()
        for i in range(self.actor_list.count()):
            item = self.actor_list.item(i)
            actor = item.data(Qt.UserRole)
            name = actor.get("name", "").lower()
            job = actor.get("job")
            visible = text in name and (not job_filter or job_filter == job)
            item.setHidden(not visible)

    def on_actor_selected(self) -> None:
        items = self.actor_list.selectedItems()
        if not items:
            return
        actor = items[0].data(Qt.UserRole)
        self.selected_actor = actor
        job = actor.get("job")
        if job:
            idx = self.job_combo.findData(job)
            if idx != -1:
                self.job_combo.setCurrentIndex(idx)
        self.on_save_auth()

    def _find_simdps_baseline_entry(self, report_code: str, fight_id: Optional[int], actor_id: Optional[int]) -> Optional[dict]:
        def _norm_int(value: object) -> Optional[int]:
            try:
                if value is None:
                    return None
                return int(value)
            except Exception:
                return None

        wanted_code = extract_report_code(str(report_code or ""))
        wanted_fight = _norm_int(fight_id)
        wanted_actor = _norm_int(actor_id)
        if not wanted_code or wanted_fight is None or wanted_actor is None:
            return None
        candidates: List[dict] = []
        for entry in self.saved_sets or []:
            if not isinstance(entry, dict):
                continue
            if not entry.get("gearset"):
                continue
            entry_code = extract_report_code(str(entry.get("report_code") or ""))
            if entry_code != wanted_code:
                continue
            entry_fight = _norm_int(entry.get("fight_id"))
            if entry_fight != wanted_fight:
                continue
            entry_actor = _norm_int(entry.get("actor_id"))
            if entry_actor != wanted_actor:
                continue
            gear = Gearset.from_dict(entry.get("gearset") or {})
            current_job = self.current_gearset.job
            if current_job and gear.job != current_job:
                continue
            context = entry.get("ui_context")
            if isinstance(context, dict) and hasattr(self, "chk_level_sync"):
                saved_sync = context.get("level_sync_enabled")
                if saved_sync is not None and bool(saved_sync) != self._level_sync_enabled():
                    continue
                if bool(saved_sync):
                    saved_il = _norm_int(context.get("level_sync_il"))
                    saved_level = _norm_int(context.get("level_sync_level"))
                    if saved_il is not None and saved_il != self._level_sync_il_value():
                        continue
                    if saved_level is not None and saved_level != self._effective_calc_level():
                        continue
            candidates.append(entry)
        if not candidates:
            return None
        explicit = [entry for entry in candidates if entry.get("baseline_role") == "log_source"]
        if explicit:
            explicit.sort(key=lambda e: timestamp_sort_value(e.get("saved_at")), reverse=True)
            return explicit[0]
        selected = [entry for entry in candidates if entry.get("id") == self._current_loaded_saved_set_id]
        if selected:
            return selected[0]
        preferred: List[dict] = []
        for entry in candidates:
            name = str(entry.get("name") or "")
            lower_name = name.lower()
            if "今の装備" in name or "current" in lower_name:
                preferred.append(entry)
        if not preferred:
            return None
        preferred.sort(key=lambda e: timestamp_sort_value(e.get("saved_at")), reverse=True)
        return preferred[0]

    def on_load_casts(self) -> None:
        if not self.selected_fight or not self.selected_actor:
            QMessageBox.warning(self, "未選択", "先にファイトとアクターを選択してください。")
            return
        client_id = self.input_client_id.text().strip() if hasattr(self, "input_client_id") else ""
        client_secret = self.input_client_secret.text().strip() if hasattr(self, "input_client_secret") else ""
        if client_id and client_secret:
            self.ff_client.set_credentials(client_id, client_secret)
        if not self.ff_client.ready():
            QMessageBox.warning(self, "認証情報未設定", "先にFFLogs V2のクライアント情報を設定してください。")
            return
        code = extract_report_code(self.input_report_code.text())
        if not code:
            QMessageBox.warning(self, "入力不正", "FFLogsレポートコードまたはURLを正しく入力してください。")
            return
        if self._fflogs_force_refresh_enabled():
            self.ff_client.clear_cache()
        fight = dict(self.selected_fight)
        actor = dict(self.selected_actor)
        actor_id = actor.get("id")
        fight_id = fight.get("id")
        start_time, end_time = self._resolve_phase_window(fight)
        fight_end = fight.get("endTime", fight.get("end_time"))
        enemy_npcs_snapshot = [dict(npc) for npc in self.enemy_npcs if isinstance(npc, dict)]
        job = self.current_gearset.job or ""
        friendly_ids = set(self.friendly_ids or set())
        # Capture baseline gearset for simdps. Prefer a saved set that matches this log context.
        self._sync_ui_to_gearset()
        baseline_source = Gearset.from_dict(self.current_gearset.to_dict())
        baseline_party = self.party_bonus.value()
        baseline_race = self._current_race()
        baseline_entry = self._find_simdps_baseline_entry(code, fight_id, actor_id)
        self._simdps_baseline_exact = baseline_entry is not None
        self._simdps_baseline_name = str(baseline_entry.get("name") or "") if baseline_entry else None
        self._simdps_baseline_entry_id = baseline_entry.get("id") if baseline_entry else None
        self._log_gcd_estimate = None
        self._log_gcd_constraint = None
        self._refresh_log_gcd_ui()
        if baseline_entry:
            try:
                candidate = Gearset.from_dict(baseline_entry.get("gearset") or {})
                if candidate.job and (not job or candidate.job == job):
                    baseline_source = candidate
                    baseline_party = int(baseline_entry.get("party_bonus", baseline_party))
                    baseline_race = candidate.race or baseline_race
                    sim_log(
                        f"[simdps] baseline_source=saved_set name={baseline_entry.get('name')} "
                        f"weapon={baseline_entry.get('gearset', {}).get('items', {}).get('weapon', {}).get('item_id')}"
                    )
            except Exception:
                pass
        self._simdps_baseline_gearset = Gearset.from_dict(baseline_source.to_dict())
        self._simdps_baseline_raw_stats = None
        self._simdps_baseline_items = None
        self._simdps_baseline_food = None
        self._simdps_baseline_party = baseline_party
        self._simdps_baseline_race = baseline_race
        # Freeze baseline snapshot from baseline source when possible.
        try:
            base_raw, base_items = self._compute_raw_stats_with_melds(baseline_source)
            if base_items:
                self._simdps_baseline_raw_stats = base_raw
                self._simdps_baseline_items = base_items
                if baseline_source.food_id:
                    self._simdps_baseline_food = self._find_food_by_id(baseline_source.food_id)
                base_weapon = getattr(base_items.get("weapon"), "item_id", None)
                main_stat_id = optimizer.MAIN_STAT_BY_JOB.get(job or "", 4)
                main_stat_label = MAIN_STAT_LABELS.get(main_stat_id, f"stat{main_stat_id}")
                sim_log(
                    f"[simdps] baseline_captured weapon={base_weapon} {main_stat_label}={base_raw.get(main_stat_id, 0)} "
                    f"crit={base_raw.get(27, 0)} dhit={base_raw.get(22, 0)} det={base_raw.get(44, 0)}"
                )
            else:
                if self._gearset_has_selected_items(baseline_source):
                    sim_log(
                        "[simdps] baseline capture deferred: selected items are not resolved yet"
                    )
                else:
                    sim_log(
                        "[simdps] baseline capture deferred: baseline source has no selected items"
                    )
        except Exception:
            pass

        def task(progress=None, stop_event=None):
            sim_log(
                f"[flow] fetch_start report={code} fight_id={fight_id} actor_id={actor_id} "
                f"start={start_time} end={end_time}"
            )
            def filter_damage_local(events: List[dict]) -> List[dict]:
                if not events:
                    return []
                filtered: List[dict] = []
                for ev in events:
                    tid = ev.get("targetID") or ev.get("targetId") or ev.get("targetid")
                    if tid is not None and tid in friendly_ids:
                        continue
                    filtered.append(ev)
                sim_log(
                    f"[simdps] damage_filter friendly={len(friendly_ids)} boss_targets=off "
                    f"raw={len(events)} kept={len(filtered)}"
                )
                return filtered

            enemy_npcs = enemy_npcs_snapshot
            if not enemy_npcs:
                try:
                    self.ff_client.fetch_fights(code)
                    enemy_npcs = [
                        dict(npc)
                        for npc in self.ff_client.last_enemy_npcs
                        if isinstance(npc, dict)
                    ]
                except Exception:
                    enemy_npcs = enemy_npcs_snapshot
            if progress:
                progress(-1, "ログ取得中...")
            with ThreadPoolExecutor(max_workers=3) as executor:
                fut_casts = executor.submit(
                    self.ff_client.fetch_casts,
                    code,
                    fight,
                    actor_id,
                    stop_event,
                    None,
                )
                fut_timeline = executor.submit(
                    self.ff_client.fetch_actor_timeline_events,
                    code,
                    fight,
                    actor_id,
                    True,
                    stop_event,
                    None,
                )
                fut_damage = executor.submit(
                    self.ff_client.fetch_damage_events,
                    code,
                    fight,
                    actor_id,
                    True,
                    stop_event,
                    None,
                )
                casts = fut_casts.result()
                timeline_events = fut_timeline.result()
                damage = fut_damage.result()
            sim_log(
                f"[flow] fetch_done casts={len(casts)} timeline={len(timeline_events)} damage={len(damage)}"
            )
            if progress:
                progress(-1, "ログ後処理中...")
            damage_filtered = filter_damage_local(damage)
            damage_table = None
            damage_table_adps = None
            if fight_id is not None:
                try:
                    # Use raid table (contains per-actor NDPS/RDPS rows) to avoid per-ability rows.
                    with ThreadPoolExecutor(max_workers=2) as table_exec:
                        fut_summary = table_exec.submit(
                            self.ff_client.fetch_damage_done_table,
                            code,
                            fight_id,
                            None,
                            start_time,
                            end_time,
                            "summary",
                        )
                        fut_adps = table_exec.submit(
                            self.ff_client.fetch_damage_done_table,
                            code,
                            fight_id,
                            None,
                            start_time,
                            end_time,
                            "adps",
                        )
                        damage_table = {"raid": fut_summary.result()}
                        damage_table_adps = {"raid": fut_adps.result()}
                except Exception as e:
                    damage_table = {"error": str(e)}
            sim_log(
                f"[flow] table_fetch done raid={'yes' if damage_table else 'no'} adps={'yes' if damage_table_adps else 'no'}"
            )
            action_data: Dict[int, object] = {}
            status_data: Dict[int, object] = {}
            if damage_table_adps and isinstance(damage_table_adps, dict):
                table_for_ids = None
                if isinstance(damage_table_adps.get("actor"), dict):
                    table_for_ids = damage_table_adps.get("actor")
                elif isinstance(damage_table_adps.get("raid"), dict):
                    table_for_ids = damage_table_adps.get("raid")
                if table_for_ids:
                    action_ids = self._extract_action_ids_from_table(table_for_ids)
                    if action_ids:
                        action_data.update(self.xivapi_client.fetch_actions(action_ids))
            event_action_ids = self._extract_action_ids_from_events(casts, timeline_events, damage_filtered)
            status_ids = self._extract_status_ids_from_timeline(timeline_events)
            missing = [aid for aid in event_action_ids if aid not in action_data] if event_action_ids else []
            if missing or status_ids:
                if progress:
                    progress(-1, "辞書データ取得中...")
                with ThreadPoolExecutor(max_workers=2) as dict_exec:
                    fut_actions = (
                        dict_exec.submit(self.xivapi_client.fetch_actions, missing)
                        if missing
                        else None
                    )
                    fut_status = (
                        dict_exec.submit(self.xivapi_client.fetch_statuses, status_ids)
                        if status_ids
                        else None
                    )
                    if fut_actions:
                        action_data.update(fut_actions.result() or {})
                    if fut_status:
                        status_data.update(fut_status.result() or {})
            if action_data:
                sample_actions = list(action_data.keys())[:10]
                sim_log(
                    f"[flow] xivapi_actions fetched={len(action_data)} sample={sample_actions}"
                )
            if status_data:
                sample_status = list(status_data.keys())[:10]
                sim_log(
                    f"[flow] xivapi_statuses fetched={len(status_data)} sample={sample_status}"
                )
            sim_log(
                f"[simdps] ids action_event={len(event_action_ids)} status_timeline={len(status_ids)}"
            )
            if progress:
                progress(-1, "ログ集計中...")
            with ThreadPoolExecutor(max_workers=2) as executor:
                fut_damage = executor.submit(
                    optimizer.summarize_damage,
                    damage_filtered,
                    job,
                    action_data=action_data,
                )
                fut_timeline = executor.submit(
                    optimizer.summarize_timeline_damage,
                    casts,
                    damage_filtered,
                    timeline_events,
                    job,
                    actor_id,
                    action_data,
                    status_data,
                    fight_end,
                )
                damage_summary = fut_damage.result()
                timeline_summary = fut_timeline.result()
            return {
                "casts": casts,
                "timeline": timeline_events,
                "damage": damage_filtered,
                "damage_summary": damage_summary,
                "timeline_summary": timeline_summary,
                "damage_table": damage_table,
                "damage_table_adps": damage_table_adps,
                "action_data": action_data,
                "status_data": status_data,
                "enemy_npcs": enemy_npcs,
                "request_context": {
                    "report_code": code,
                    "fight_id": fight_id,
                    "actor_id": actor_id,
                },
            }

        self.start_worker(task, self._after_casts, lock_fflogs_context=True)

    def _after_casts(self, payload) -> None:
        if isinstance(payload, dict):
            context = payload.get("request_context") or {}
            report_code = context.get("report_code")
            if report_code and not self._fflogs_context_matches(
                report_code,
                context.get("fight_id"),
                context.get("actor_id"),
            ):
                logger.info(
                    "Discarded stale FFLogs casts result for report %s fight %s actor %s",
                    report_code,
                    context.get("fight_id"),
                    context.get("actor_id"),
                )
                return
        casts = payload.get("casts", []) if isinstance(payload, dict) else payload
        timeline = payload.get("timeline", []) if isinstance(payload, dict) else []
        damage = payload.get("damage", []) if isinstance(payload, dict) else []
        damage_summary = payload.get("damage_summary") if isinstance(payload, dict) else None
        timeline_summary = payload.get("timeline_summary") if isinstance(payload, dict) else None
        self.damage_table = payload.get("damage_table") if isinstance(payload, dict) else None
        self.damage_table_adps = payload.get("damage_table_adps") if isinstance(payload, dict) else None
        if isinstance(payload, dict):
            if "action_data" in payload:
                self.action_data = payload.get("action_data") or {}
            if "status_data" in payload:
                self.status_data = payload.get("status_data") or {}
        self.casts = casts or []
        self.timeline_events = timeline or []
        enemy_npcs = payload.get("enemy_npcs") if isinstance(payload, dict) else None
        if enemy_npcs:
            self.enemy_npcs = enemy_npcs
        self.damage_events = damage or []
        self.damage_summary = (
            damage_summary
            if isinstance(damage_summary, dict)
            else optimizer.summarize_damage(
                self.damage_events,
                self.current_gearset.job or "",
                action_data=self.action_data,
            )
        )
        if not isinstance(timeline_summary, dict):
            fight_end = None
            if self.selected_fight:
                fight_end = self.selected_fight.get("endTime", self.selected_fight.get("end_time"))
            timeline_summary = optimizer.summarize_timeline_damage(
                self.casts,
                self.damage_events,
                self.timeline_events,
                self.current_gearset.job or "",
                actor_id=self.selected_actor.get("id") if self.selected_actor else None,
                action_data=self.action_data,
                status_data=self.status_data,
                fight_end_ts=fight_end,
            )
        # "自己バフのみ" は NDPS を基準にスケーリング（時系列モデルに適用）
        self.damage_summary_self = (
            self._build_ndps_summary(timeline_summary)
            or timeline_summary
            or self._build_adps_summary()
        )
        self._update_simdps_baseline_data()
        self._refresh_log_gcd_profile()
        sim_log(
            f"[simdps] timeline casts={len(self.casts)} timeline_events={len(self.timeline_events)} "
            f"actions_cached={len(self.action_data)} statuses_cached={len(self.status_data)}"
        )
        self._debug_log_damage_summary()
        if self.damage_summary:
            total = int(self.damage_summary.get("total_damage", 0))
            self.progress_label.setText(
                f"キャスト{len(self.casts)}件 / ダメージ{total} を読み込みました"
            )
        else:
            self.progress_label.setText(f"キャストを読み込みました（{len(self.casts)}件）")

    def _debug_log_damage_summary(self) -> None:
        if not self.damage_summary:
            return
        source_ids = {}
        for ev in self.damage_events or []:
            src = ev.get("sourceID")
            if src is None:
                src = ev.get("sourceId")
            if src is None:
                src = ev.get("sourceid")
            if src is None:
                continue
            source_ids[src] = source_ids.get(src, 0) + 1
        fight_ms = 0
        if self.selected_fight:
            start_time = self.selected_fight.get("startTime", self.selected_fight.get("start_time", 0))
            end_time = self.selected_fight.get("endTime", self.selected_fight.get("end_time", 0))
            fight_ms = end_time - start_time
        total_amount = float(self.damage_summary.get("total_amount") or self.damage_summary.get("total_damage") or 0.0)
        total_absorbed = float(self.damage_summary.get("total_absorbed") or 0.0)
        total_overkill = float(self.damage_summary.get("total_overkill") or 0.0)
        min_ts = self.damage_summary.get("min_ts")
        max_ts = self.damage_summary.get("max_ts")
        active_ms = None
        if min_ts is not None and max_ts is not None and max_ts >= min_ts:
            active_ms = max_ts - min_ts
        raw_dps_fight = total_amount / (fight_ms / 1000.0) if fight_ms > 0 else 0.0
        raw_dps_active = (
            total_amount / (active_ms / 1000.0)
            if active_ms and active_ms > 0
            else 0.0
        )
        total_with_abs = total_amount + total_absorbed
        total_with_over = total_amount + total_overkill
        total_with_all = total_amount + total_absorbed + total_overkill
        sim_log(
            f"[simdps] total_amount={total_amount:.1f} absorbed={total_absorbed:.1f} overkill={total_overkill:.1f} "
            f"total+abs={total_with_abs:.1f} total+over={total_with_over:.1f} total+all={total_with_all:.1f}"
        )
        sim_log(
            f"[simdps] fight_ms={fight_ms} active_ms={active_ms} min_ts={min_ts} max_ts={max_ts} "
            f"raw_dps_fight={raw_dps_fight:.1f} raw_dps_active={raw_dps_active:.1f}"
        )
        if self.damage_table is not None:
            if isinstance(self.damage_table, dict) and self.damage_table.get("error"):
                sim_log(f"[simdps] damage_table_error={self.damage_table.get('error')}")
            else:
                table_actor = None
                table_raid = None
                if isinstance(self.damage_table, dict) and (
                    "actor" in self.damage_table or "raid" in self.damage_table
                ):
                    table_actor = self.damage_table.get("actor")
                    table_raid = self.damage_table.get("raid")
                else:
                    table_raid = self.damage_table

                def log_table(tag: str, table: dict) -> None:
                    if not isinstance(table, dict):
                        return
                    entries = self._extract_damage_table_entries(table)
                    keys = sorted(list(table.keys()))
                    sim_log(f"[simdps] damage_table[{tag}] keys={keys}")
                    combat_time = table.get("combatTime")
                    total_time = table.get("totalTime")
                    downtime = table.get("damageDowntime")
                    sim_log(
                        f"[simdps] damage_table[{tag}] combatTime={combat_time} totalTime={total_time} damageDowntime={downtime}"
                    )
                    sim_log(f"[simdps] damage_table[{tag}] entries={len(entries)}")
                    if entries:
                        sample = entries[0]
                        if isinstance(sample, dict):
                            sample_keys = list(sample.keys())[:12]
                            sim_log(f"[simdps] damage_table[{tag}] entry_keys={sample_keys}")

                if table_actor:
                    log_table("actor", table_actor)
                if table_raid:
                    log_table("raid", table_raid)

                actor_id = self.selected_actor.get("id") if self.selected_actor else None
                actor_guid = self.selected_actor.get("guid") if self.selected_actor else None
                actor_name = self.selected_actor.get("name") if self.selected_actor else None
                if self.selected_actor:
                    sim_log(
                        f"[simdps] actor id={actor_id} guid={actor_guid} name={actor_name} type={self.selected_actor.get('type')}"
                    )

                table_for_entry = table_raid if table_raid else table_actor
                entries = self._extract_damage_table_entries(table_for_entry or {})
                entry = None
                if actor_id is not None:
                    for e in entries:
                        if isinstance(e, dict) and (
                            e.get("id") == actor_id
                            or e.get("actor") == actor_id
                            or e.get("guid") == actor_id
                        ):
                            entry = e
                            break
                if entry is None and actor_guid is not None:
                    for e in entries:
                        if isinstance(e, dict) and (
                            e.get("guid") == actor_guid
                            or e.get("actor") == actor_guid
                        ):
                            entry = e
                            break
                if entry is None and actor_name:
                    for e in entries:
                        if isinstance(e, dict):
                            if e.get("name") == actor_name or e.get("actorName") == actor_name:
                                entry = e
                                break
                if entry is None and entries:
                    entry = entries[0]
                if isinstance(entry, dict):
                    dps = entry.get("dps")
                    total = entry.get("total") or entry.get("amount")
                    active_time = entry.get("activeTime") or entry.get("activeTimeMs")
                    rdps = entry.get("totalRDPS")
                    rdps_taken = entry.get("totalRDPSTaken")
                    rdps_given = entry.get("totalRDPSGiven")
                    ndps = entry.get("totalNDPS")
                    rdps_per_sec = None
                    if rdps is not None and isinstance(table_for_entry, dict):
                        combat_time = table_for_entry.get("combatTime") or 0
                        if combat_time:
                            try:
                                rdps_per_sec = float(rdps) / (float(combat_time) / 1000.0)
                            except Exception:
                                rdps_per_sec = None
                    sim_log(
                        f"[simdps] damage_table dps={dps} total={total} active={active_time} "
                        f"rdps={rdps} rdps_taken={rdps_taken} rdps_given={rdps_given} ndps={ndps} rdps_ps={rdps_per_sec}"
                    )
        if self.damage_table_adps is not None:
            table = None
            if isinstance(self.damage_table_adps, dict) and "raid" in self.damage_table_adps:
                table = self.damage_table_adps.get("raid")
            elif isinstance(self.damage_table_adps, dict):
                table = self.damage_table_adps
            if isinstance(table, dict):
                entries = self._extract_damage_table_entries(table)
                keys = sorted(list(table.keys()))
                sim_log(f"[simdps] adps_table keys={keys}")
                sim_log(f"[simdps] adps_table entries={len(entries)}")
                if entries:
                    sample = entries[0]
                    if isinstance(sample, dict):
                        sample_keys = list(sample.keys())[:12]
                        sim_log(f"[simdps] adps_table entry_keys={sample_keys}")
                actor_id = self.selected_actor.get("id") if self.selected_actor else None
                actor_guid = self.selected_actor.get("guid") if self.selected_actor else None
                actor_name = self.selected_actor.get("name") if self.selected_actor else None
                entry = None
                for e in entries:
                    if not isinstance(e, dict):
                        continue
                    if actor_id is not None and (e.get("id") == actor_id or e.get("actor") == actor_id):
                        entry = e
                        break
                if entry is None and actor_guid is not None:
                    for e in entries:
                        if isinstance(e, dict) and (e.get("guid") == actor_guid or e.get("actor") == actor_guid):
                            entry = e
                            break
                    if entry is None and actor_name:
                        for e in entries:
                            if isinstance(e, dict):
                                if e.get("name") == actor_name or e.get("actorName") == actor_name:
                                    entry = e
                                    break

                if isinstance(entry, dict):
                    total = entry.get("total") or entry.get("amount")
                    total_adps = entry.get("totalADPS") or entry.get("totalADPSRaw") or entry.get("totalADPSDone")
                    active_time = entry.get("activeTime") or entry.get("activeTimeMs")
                    adps_per_sec = None
                    combat_time = table.get("combatTime") or 0
                    if total_adps is not None and combat_time:
                        try:
                            adps_per_sec = float(total_adps) / (float(combat_time) / 1000.0)
                        except Exception:
                            adps_per_sec = None
                    sim_log(
                        f"[simdps] adps_table total={total} total_adps={total_adps} active={active_time} adps_ps={adps_per_sec}"
                    )
        if source_ids:
            actor_id = self.selected_actor.get("id") if self.selected_actor else None
            top_sources = sorted(source_ids.items(), key=lambda kv: kv[1], reverse=True)[:5]
            sim_log(f"[simdps] source_ids top={top_sources} actor_id={actor_id}")
        target_stats = {}
        for ev in self.damage_events or []:
            tid = ev.get("targetID") or ev.get("targetId") or ev.get("targetid")
            if tid is None:
                continue
            tname = None
            target = ev.get("target")
            if isinstance(target, dict):
                tname = target.get("name")
            elif isinstance(target, str):
                tname = target
            key = (int(tid), tname or "")
            entry = target_stats.get(key)
            amount = ev.get("amount") or 0
            if entry:
                entry["damage"] += float(amount)
                entry["count"] += 1
            else:
                target_stats[key] = {"damage": float(amount), "count": 1}
        if target_stats:
            top_targets = sorted(target_stats.items(), key=lambda kv: kv[1]["damage"], reverse=True)[:5]
            for (tid, tname), info in top_targets:
                sim_log(
                    f"[simdps] target {tid} {tname} dmg={info['damage']:.1f} count={info['count']}"
                )
        buckets = self.damage_summary.get("buckets") or {}
        bucket_counts = self.damage_summary.get("bucket_counts") or {}
        total_bucket = sum(buckets.values()) or 1.0
        for (atk, is_dot), dmg in sorted(buckets.items(), key=lambda x: x[1], reverse=True):
            cnt = bucket_counts.get((atk, is_dot), 0)
            pct = dmg / total_bucket * 100.0
            sim_log(f"[simdps] bucket {atk} dot={is_dot} dmg={dmg:.1f} ({pct:.1f}%) count={cnt}")
        unknown = self.damage_summary.get("unknown_actions") or {}
        top = []
        if unknown:
            unknown_total = sum(v["damage"] for v in unknown.values()) or 0.0
            sim_log(f"[simdps] unknown_total={unknown_total:.1f} ({unknown_total/total_bucket*100:.1f}%)")
            top = sorted(unknown.items(), key=lambda kv: kv[1]["damage"], reverse=True)[:20]
        for (aid, name), info in top:
            sim_log(f"[simdps] unknown {aid} {name} dmg={info['damage']:.1f} count={info['count']}")

    def _simdps_effective_duration_ms(self, fight_ms: int) -> int:
        if fight_ms <= 0:
            return fight_ms
        if not isinstance(self.damage_table, dict):
            return fight_ms
        table = None
        if isinstance(self.damage_table.get("raid"), dict):
            table = self.damage_table.get("raid")
        elif isinstance(self.damage_table.get("actor"), dict):
            table = self.damage_table.get("actor")
        else:
            table = self.damage_table
        table = self._normalize_table_dict(table)
        if not isinstance(table, dict) or not table:
            return fight_ms

        def _to_int_ms(v) -> Optional[int]:
            try:
                n = int(float(v))
            except Exception:
                return None
            return n if n > 0 else None

        candidates: List[Tuple[str, int]] = []
        entry = self._find_actor_entry(table)
        if isinstance(entry, dict):
            # Prioritize FFLogs actor durations requested by UI behavior:
            # combatTime -> activeTime (ms) -> fallback values.
            for key in ("combatTime", "activeTime", "activeTimeMs"):
                ms = _to_int_ms(entry.get(key))
                if ms is not None:
                    candidates.append((f"entry.{key}", ms))
        for key in ("combatTime", "activeTime", "activeTimeMs", "totalTime"):
            ms = _to_int_ms(table.get(key))
            if ms is not None:
                candidates.append((f"table.{key}", ms))
        if not candidates:
            return fight_ms
        source, effective = candidates[0]
        min_allowed = int(fight_ms * 0.4)
        max_allowed = int(fight_ms * 1.2)
        if effective < min_allowed or effective > max_allowed:
            return fight_ms
        if effective != fight_ms:
            sim_log(
                f"[simdps] duration_override fight_ms={fight_ms} effective_ms={effective} source={source}"
            )
        return effective

    def _update_simdps_baseline_data(self) -> None:
        gear = self._simdps_baseline_gearset or self.current_gearset
        if not gear:
            return
        if self._simdps_baseline_gearset and not self._gearset_items_ready(gear):
            return
        raw_stats, items = self._compute_raw_stats_with_melds(gear)
        if not items:
            # Keep waiting until at least one item is selected and resolvable.
            if self._gearset_has_selected_items(gear):
                sim_log(
                    "[simdps] baseline snapshot deferred: selected items are not resolved yet"
                )
            else:
                sim_log(
                    "[simdps] baseline snapshot deferred: gearset has no selected items"
                )
            return
        food = None
        if gear.food_id:
            food = self._find_food_by_id(gear.food_id)
        self._simdps_baseline_raw_stats = raw_stats
        self._simdps_baseline_items = items
        self._simdps_baseline_food = food
        if self._simdps_baseline_party is None:
            self._simdps_baseline_party = self.party_bonus.value()
        if self._simdps_baseline_race is None:
            self._simdps_baseline_race = DEFAULT_RACE

    def _baseline_formula_gcd(self) -> Optional[float]:
        gear = self._simdps_baseline_gearset
        raw_stats = self._simdps_baseline_raw_stats
        if not self._simdps_baseline_exact or gear is None or raw_stats is None or not gear.job:
            return None
        level_value = self._effective_calc_level()
        food = self._simdps_baseline_food
        comp = xivmath.build_computed_stats(
            gear.job,
            raw_stats,
            self._get_job_mods(gear.job),
            food.bonuses if food else None,
            int(self._simdps_baseline_party or 0),
            0,
            0,
            3.0,
            race=self._simdps_baseline_race,
            level=level_value,
        )
        speed = comp.spellspeed if gear.job in SPELL_SPEED_JOBS else comp.skillspeed
        return optimizer.calc_gcd_seconds(speed, gear.job, level=level_value)

    def _refresh_log_gcd_profile(self) -> None:
        actor_id = self.selected_actor.get("id") if self.selected_actor else None
        self._log_gcd_estimate = estimate_log_gcd(
            self.casts or [],
            self.action_data or {},
            actor_id=int(actor_id) if actor_id is not None else None,
        )
        baseline_gcd = self._baseline_formula_gcd()
        self._log_gcd_constraint = build_log_gcd_constraint(
            self._log_gcd_estimate,
            baseline_gcd,
        )
        self._refresh_log_gcd_ui()
        estimate = self._log_gcd_estimate
        sim_log(
            f"[gcd] observed={estimate.seconds} confidence={estimate.confidence} "
            f"samples={estimate.sample_count} raw_median_ms={estimate.raw_median_ms} "
            f"tier_share={estimate.tier_share:.3f} baseline={baseline_gcd} "
            f"constraint={'on' if self._log_gcd_constraint else 'off'}"
        )

    def _refresh_log_gcd_ui(self) -> None:
        if not hasattr(self, "log_gcd_status_label"):
            return
        estimate = self._log_gcd_estimate
        mode = self.calc_mode.currentData() if hasattr(self, "calc_mode") else "simdps_self"
        usable = mode in {"simdps", "simdps_self"} and self._log_gcd_constraint is not None
        self.chk_log_gcd_constraint.setEnabled(usable)
        if estimate is None:
            self.log_gcd_status_label.setText("ログGCD: 未取得")
            self.log_gcd_status_label.setToolTip("キャスト取得後に実測GCDを推定します")
            return
        confidence_labels = {"high": "高", "medium": "中", "low": "低", "unavailable": "不可"}
        confidence = confidence_labels.get(estimate.confidence, estimate.confidence)
        seconds = f"{estimate.seconds:.2f}秒" if estimate.seconds is not None else "推定不可"
        baseline_name = self._simdps_baseline_name or "未設定"
        self.log_gcd_status_label.setText(
            f"ログGCD: {seconds} ({confidence}, n={estimate.sample_count})"
        )
        if self._log_gcd_constraint is not None:
            tooltip = (
                f"基準セット: {baseline_name}\n"
                f"基準理論GCD: {self._log_gcd_constraint.baseline_formula_seconds:.3f}秒"
            )
        elif not self._simdps_baseline_exact:
            tooltip = "ログ識別子が一致する保存セットを右クリックし、ログ基準装備に設定してください"
        else:
            tooltip = estimate.reason or "実測GCDの信頼度または基準値との比率が不足しています"
        if estimate.raw_median_ms is not None:
            tooltip += (
                f"\nログ間隔中央値: {estimate.raw_median_ms / 1000.0:.3f}秒"
                f"\n表示GCD帯の支持率: {estimate.tier_share:.1%}"
            )
        self.log_gcd_status_label.setToolTip(tooltip)
        self.chk_log_gcd_constraint.setToolTip(tooltip)

    def _active_log_gcd_constraint(self, mode: str) -> Optional[LogGcdConstraint]:
        if mode not in {"simdps", "simdps_self"}:
            return None
        if not self.chk_log_gcd_constraint.isChecked():
            return None
        return self._log_gcd_constraint

    def _resolve_simdps_baseline(
        self,
        fallback_raw: Dict[int, int],
        fallback_items: Dict[str, object],
        fallback_food: Optional[object],
    ) -> Tuple[Dict[int, int], Dict[str, object], Optional[object], int, str]:
        if self._simdps_baseline_gearset and self._gearset_items_ready(self._simdps_baseline_gearset):
            base_gear = self._simdps_baseline_gearset
            base_raw, base_items = self._compute_raw_stats_with_melds(base_gear)
            if base_items:
                base_food = self._find_food_by_id(base_gear.food_id)
                self._simdps_baseline_raw_stats = base_raw
                self._simdps_baseline_items = base_items
                self._simdps_baseline_food = base_food
            else:
                if self._gearset_has_selected_items(base_gear):
                    sim_log(
                        "[simdps] baseline resolve deferred: selected items are not resolved yet"
                    )
                else:
                    sim_log(
                        "[simdps] baseline resolve deferred: baseline gearset has no selected items"
                    )
        # Recover from an empty/missing baseline once, then keep it stable.
        baseline_missing = (
            self._simdps_baseline_raw_stats is None
            or self._simdps_baseline_items is None
            or len(self._simdps_baseline_items) == 0
        )
        if baseline_missing and fallback_items:
            self._simdps_baseline_raw_stats = dict(fallback_raw)
            self._simdps_baseline_items = dict(fallback_items)
            self._simdps_baseline_food = fallback_food
            sim_log(
                "[simdps] baseline recovered from current set "
                f"weapon={getattr(fallback_items.get('weapon'), 'item_id', None)}"
            )
        base_raw = (
            self._simdps_baseline_raw_stats
            if self._simdps_baseline_raw_stats is not None
            else fallback_raw
        )
        base_items = (
            self._simdps_baseline_items
            if self._simdps_baseline_items is not None
            else fallback_items
        )
        base_food = self._simdps_baseline_food if self._simdps_baseline_food is not None else fallback_food
        base_party = (
            self._simdps_baseline_party
            if self._simdps_baseline_party is not None
            else self.party_bonus.value()
        )
        base_race = self._simdps_baseline_race or DEFAULT_RACE
        if self._simdps_baseline_raw_stats is None or self._simdps_baseline_items is None:
            if fallback_items:
                sim_log("[simdps] baseline resolve fallback to current stats/items")
            else:
                sim_log("[simdps] baseline unresolved: waiting for selectable gear items")
        return base_raw, base_items, base_food, int(base_party), base_race

    def _schedule_auto_score_update(self) -> None:
        if self._applying_gearset:
            return
        if self._saved_sets_reordering:
            return
        if self._auto_calc_suspended > 0 or self._is_populating:
            self._pending_score_after_populate = True
            return
        if self.active_worker:
            self._pending_score_after_worker = True
            return
        self._auto_calc_timer.stop()
        self._auto_calc_timer.start(350)

    def _build_preview_signature(
        self,
        mode: str,
        job: str,
        raw_stats: Dict[int, int],
        selected_items: Dict[str, object],
        fight_ms: int,
        summary: Optional[Dict[str, object]],
        party_synergies: Optional[Dict[str, bool]] = None,
    ) -> Tuple:
        main_stat_id = optimizer.MAIN_STAT_BY_JOB.get(job, 4)
        main_stat_val = int(raw_stats.get(main_stat_id, 0))
        gear_sig: List[Tuple[str, Optional[int], Tuple[Tuple[int, int], ...]]] = []
        for slot in GEAR_SLOTS:
            sel = self.current_gearset.items.get(slot)
            item_id = sel.item_id if sel else None
            materia_sig: Tuple[Tuple[int, int], ...] = ()
            if sel and sel.materia:
                materia_sig = tuple((int(m.base_param), int(m.grade)) for m in sel.materia if m)
            relic_sig = tuple(
                sorted(
                    (int(stat_id), int(value))
                    for stat_id, value in self._selection_relic_stats(sel).items()
                    if int(value or 0) > 0
                )
            ) if sel else ()
            gear_sig.append((slot, item_id, materia_sig, relic_sig))
        weapon = selected_items.get("weapon")
        weapon_id = getattr(weapon, "item_id", None) if weapon else None
        summary_total = float(summary.get("total_amount") or summary.get("total_damage") or 0.0) if summary else 0.0
        summary_actions = len(summary.get("ability_buckets") or {}) if summary else 0
        if party_synergies is None:
            party_synergies = self._selected_party_synergies()
        synergy_sig = tuple(sorted(k for k, v in party_synergies.items() if v))
        return (
            mode,
            job,
            int(self._effective_calc_level()),
            weapon_id,
            main_stat_val,
            int(raw_stats.get(27, 0)),
            int(raw_stats.get(22, 0)),
            int(raw_stats.get(44, 0)),
            int(raw_stats.get(45, 0)),
            int(raw_stats.get(46, 0)),
            int(self.party_bonus.value()),
            self._crit_rate_adjust_percent(),
            self._dhit_rate_adjust_percent(),
            self.current_gearset.food_id,
            float(self.current_gearset.target_gcd or 2.5),
            int(fight_ms),
            int(summary_total),
            int(summary_actions),
            synergy_sig,
            tuple(gear_sig),
        )

    def _update_score_preview(self) -> None:
        if self._applying_gearset:
            return
        if self.active_worker:
            self._pending_score_after_worker = True
            return
        if self._is_populating:
            self._pending_score_after_populate = True
            return
        job = self.current_gearset.job
        if not job:
            self._set_pending_saved_score_recalculation_waiting("ジョブ情報がありません。")
            return
        mode = self.calc_mode.currentData() or "simdps_self"
        if mode == "dmg100p" and not self.jobs_data:
            self._set_pending_saved_score_recalculation_waiting("装備データを読み込み中です。")
            return
        if mode in {"simdps", "simdps_self"} and not self.damage_summary:
            self._set_pending_saved_score_recalculation_waiting(
                "ファイトとアクターを選択して「キャスト取得」を実行してください。"
            )
            return

        self._sync_ui_to_gearset()
        if self._simdps_baseline_raw_stats is None or self._simdps_baseline_items is None:
            self._update_simdps_baseline_data()
        food = self._find_food_by_id(self.current_gearset.food_id)
        raw_stats, selected_items = self._compute_raw_stats_with_melds(self.current_gearset)
        baseline_raw, baseline_items, baseline_food, baseline_party, baseline_race = self._resolve_simdps_baseline(
            raw_stats,
            selected_items,
            food,
        )
        party_synergies = self._selected_party_synergies()

        fight_ms = 0
        if self.selected_fight:
            start_time = self.selected_fight.get("startTime", self.selected_fight.get("start_time", 0))
            end_time = self.selected_fight.get("endTime", self.selected_fight.get("end_time", 0))
            fight_ms = end_time - start_time

        if mode in {"simdps", "simdps_self"}:
            summary = self.damage_summary_self if mode == "simdps_self" else self.damage_summary
            if fight_ms <= 0 or not summary:
                self._set_pending_saved_score_recalculation_waiting(
                    "ファイトとアクターを選択して「キャスト取得」を実行してください。"
                )
                return
            sim_fight_ms = self._simdps_effective_duration_ms(fight_ms)
            preview_sig = self._build_preview_signature(
                mode, job, raw_stats, selected_items, sim_fight_ms, summary, party_synergies
            )
            if self._last_preview_signature == preview_sig:
                return
            self._last_preview_signature = preview_sig
            weapon = selected_items.get("weapon")
            weapon_id = getattr(weapon, "item_id", None) if weapon else None
            main_stat_id = optimizer.MAIN_STAT_BY_JOB.get(job, 4)
            main_stat_label = MAIN_STAT_LABELS.get(main_stat_id, f"stat{main_stat_id}")
            sim_log(
                "[simdps] preview stats "
                f"weapon={weapon_id} {main_stat_label}={raw_stats.get(main_stat_id, 0)} crit={raw_stats.get(27, 0)} "
                f"dhit={raw_stats.get(22, 0)} det={raw_stats.get(44, 0)} sps={raw_stats.get(46, 0)}"
            )
            dps, expected_dps, _gcd = optimizer.evaluate_score_pair(
                raw_stats,
                job,
                self.casts,
                sim_fight_ms,
                self.current_gearset.target_gcd,
                damage_summary=summary,
                job_mods=self._get_job_mods(job),
                food=food,
                party_bonus=self.party_bonus.value(),
                baseline_raw_stats=baseline_raw,
                baseline_items=baseline_items,
                selected_items=selected_items,
                baseline_food=baseline_food,
                baseline_party_bonus=baseline_party,
                baseline_race=baseline_race,
                party_synergies=party_synergies,
                race=self.current_gearset.race,
                mode=mode,
                level=self.current_gearset.level,
                # Auto preview is called frequently; keep it lightweight even in debug mode.
                debug=False,
                **self._eval_rate_adjust_kwargs(),
            )
            sim_log(
                f"[simdps] preview result mode={mode} dps={dps:.4f} gcd={_gcd:.3f} "
                f"baseline_weapon={getattr((baseline_items or {}).get('weapon'), 'item_id', None)} "
                f"current_weapon={weapon_id}"
            )
            self._apply_eval_result(mode, float(dps), float(_gcd), float(expected_dps))
            return

        preview_sig = self._build_preview_signature(
            mode, job, raw_stats, selected_items, fight_ms, None, party_synergies
        )
        if self._last_preview_signature == preview_sig:
            return
        self._last_preview_signature = preview_sig
        dmg100, expected_dmg100, _gcd = optimizer.evaluate_score_pair(
            raw_stats,
            job,
            self.casts,
            fight_ms,
            self.current_gearset.target_gcd,
            job_mods=self._get_job_mods(job),
            food=food,
            party_bonus=self.party_bonus.value(),
            baseline_raw_stats=baseline_raw,
            baseline_items=baseline_items,
            selected_items=selected_items,
            baseline_food=baseline_food,
            baseline_party_bonus=baseline_party,
            baseline_race=baseline_race,
            party_synergies=party_synergies,
            mode="dmg100p",
            race=self.current_gearset.race,
            level=self.current_gearset.level,
            **self._eval_rate_adjust_kwargs(),
        )
        self._apply_eval_result(mode, float(dmg100), float(_gcd), float(expected_dmg100))

    def _build_adps_summary(self) -> Optional[Dict[str, object]]:
        table_container = self.damage_table_adps
        if not isinstance(table_container, dict):
            return None
        table = None
        if "actor" in table_container:
            table = table_container.get("actor")
        elif "raid" in table_container:
            table = table_container.get("raid")
        else:
            table = table_container
        if not isinstance(table, dict):
            return None
        entries = self._extract_damage_table_entries(table)
        if not entries:
            return None
        actor_id = self.selected_actor.get("id") if self.selected_actor else None
        actor_guid = self.selected_actor.get("guid") if self.selected_actor else None
        actor_name = self.selected_actor.get("name") if self.selected_actor else None
        entry = None
        for e in entries:
            if not isinstance(e, dict):
                continue
            if actor_id is not None and (e.get("id") == actor_id or e.get("actor") == actor_id):
                entry = e
                break
        if entry is None and actor_guid is not None:
            for e in entries:
                if isinstance(e, dict) and (e.get("guid") == actor_guid or e.get("actor") == actor_guid):
                    entry = e
                    break
        if entry is None and actor_name:
            for e in entries:
                if isinstance(e, dict):
                    if e.get("name") == actor_name or e.get("actorName") == actor_name:
                        entry = e
                        break
        if entry is None:
            return None

        abilities = entry.get("damageAbilities") or entry.get("abilities") or []
        if not isinstance(abilities, list) or not abilities:
            return None

        # Build ability stats from damage events to split DoT vs direct.
        stats_by_id: Dict[int, dict] = {}
        stats_by_name: Dict[str, dict] = {}
        for ev in self.damage_events or []:
            amount = ev.get("amount")
            if amount is None or amount <= 0:
                continue
            ability = ev.get("ability") or {}
            aid = ability.get("gameID") or ability.get("guid") or ability.get("id")
            name = str(ability.get("name") or "")
            is_dot = bool(ev.get("tick") or ev.get("isTick"))
            atype = ability.get("type") or "Unknown"
            lower = name.lower()
            if lower in {"auto attack", "auto-attack", "attack", "攻撃", "オートアタック"}:
                atype = "Auto-attack"
            if aid is not None:
                rec = stats_by_id.get(int(aid))
                if not rec:
                    rec = {"total": 0.0, "dot": 0.0, "types": {}}
                    stats_by_id[int(aid)] = rec
                rec["total"] += float(amount)
                if is_dot:
                    rec["dot"] += float(amount)
                rec["types"][atype] = rec["types"].get(atype, 0) + 1
            if name:
                key = name.lower()
                rec = stats_by_name.get(key)
                if not rec:
                    rec = {"total": 0.0, "dot": 0.0, "types": {}}
                    stats_by_name[key] = rec
                rec["total"] += float(amount)
                if is_dot:
                    rec["dot"] += float(amount)
                rec["types"][atype] = rec["types"].get(atype, 0) + 1

        def pick_type(rec: dict) -> str:
            if not rec:
                return "Unknown"
            types = rec.get("types") or {}
            if not types:
                return "Unknown"
            return sorted(types.items(), key=lambda kv: kv[1], reverse=True)[0][0]

        buckets: Dict[Tuple[str, bool], float] = {}
        bucket_counts: Dict[Tuple[str, bool], int] = {}
        ability_buckets: Dict[Tuple[int, str, bool], float] = {}
        ability_bucket_counts: Dict[Tuple[int, str, bool], int] = {}
        ability_names: Dict[int, str] = {}
        total_amount = 0.0
        for ab in abilities:
            if not isinstance(ab, dict):
                continue
            total = ab.get("total") or ab.get("amount") or ab.get("damage")
            if total is None:
                continue
            aid = ab.get("guid") or ab.get("id") or ab.get("ability")
            try:
                aid_int = int(aid) if aid is not None else 0
            except Exception:
                aid_int = 0
            name = str(ab.get("name") or ab.get("ability") or ab.get("abilityName") or "")
            rec = None
            if aid_int and aid_int in stats_by_id:
                rec = stats_by_id[aid_int]
            elif name:
                rec = stats_by_name.get(name.lower())
            atype = pick_type(rec)
            if atype == "Unknown" and aid_int:
                action = self.action_data.get(aid_int) if isinstance(self.action_data, dict) else None
                if action and getattr(action, "attack_type", None):
                    atype = action.attack_type
            if atype == "Unknown":
                atype = "Spell" if (self.current_gearset.job in SPELL_SPEED_JOBS) else "Weaponskill"
            if aid_int and name:
                ability_names[aid_int] = name
            dot_ratio = 0.0
            if rec and rec.get("total"):
                dot_ratio = rec.get("dot", 0.0) / max(1e-6, rec.get("total", 0.0))
            total_val = float(total)
            if dot_ratio > 0.0:
                dot_amt = total_val * dot_ratio
                direct_amt = total_val - dot_amt
                buckets[(atype, True)] = buckets.get((atype, True), 0.0) + dot_amt
                buckets[(atype, False)] = buckets.get((atype, False), 0.0) + direct_amt
                bucket_counts[(atype, True)] = bucket_counts.get((atype, True), 0) + int(ab.get("hits") or ab.get("count") or 1)
                bucket_counts[(atype, False)] = bucket_counts.get((atype, False), 0) + int(ab.get("hits") or ab.get("count") or 1)
                ability_buckets[(aid_int, atype, True)] = ability_buckets.get((aid_int, atype, True), 0.0) + dot_amt
                ability_buckets[(aid_int, atype, False)] = ability_buckets.get((aid_int, atype, False), 0.0) + direct_amt
                ability_bucket_counts[(aid_int, atype, True)] = ability_bucket_counts.get((aid_int, atype, True), 0) + int(ab.get("hits") or ab.get("count") or 1)
                ability_bucket_counts[(aid_int, atype, False)] = ability_bucket_counts.get((aid_int, atype, False), 0) + int(ab.get("hits") or ab.get("count") or 1)
            else:
                buckets[(atype, False)] = buckets.get((atype, False), 0.0) + total_val
                bucket_counts[(atype, False)] = bucket_counts.get((atype, False), 0) + int(ab.get("hits") or ab.get("count") or 1)
                ability_buckets[(aid_int, atype, False)] = ability_buckets.get((aid_int, atype, False), 0.0) + total_val
                ability_bucket_counts[(aid_int, atype, False)] = ability_bucket_counts.get((aid_int, atype, False), 0) + int(ab.get("hits") or ab.get("count") or 1)
            total_amount += total_val

        min_ts = None
        max_ts = None
        for ev in self.damage_events or []:
            ts = ev.get("timestamp")
            if ts is None:
                ts = ev.get("time")
            if ts is None:
                continue
            min_ts = ts if min_ts is None else min(min_ts, ts)
            max_ts = ts if max_ts is None else max(max_ts, ts)

        return {
            "total_damage": total_amount,
            "total_hits": int(sum(bucket_counts.values())),
            "buckets": buckets,
            "bucket_counts": bucket_counts,
            "ability_buckets": ability_buckets,
            "ability_bucket_counts": ability_bucket_counts,
            "ability_names": ability_names,
            "total_amount": total_amount,
            "total_absorbed": 0.0,
            "total_overkill": 0.0,
            "min_ts": min_ts,
            "max_ts": max_ts,
            "unknown_actions": {},
        }

    def _update_live_saved_set_preview(
        self,
        mode: str,
        score: float,
        gcd: float,
        expected_score: Optional[float] = None,
    ) -> None:
        if self._saved_sets_reordering:
            return
        if not hasattr(self, "saved_sets_table"):
            return
        row = self.saved_sets_table.currentRow()
        if row < 0:
            return
        entry_item = self.saved_sets_table.item(row, SAVED_COL_NAME)
        entry = entry_item.data(Qt.UserRole) if entry_item else None
        if not isinstance(entry, dict):
            return
        entry_id = entry.get("id")
        if entry_id is None:
            return
        target = next(
            (
                saved
                for saved in self.saved_sets
                if isinstance(saved, dict) and saved.get("id") == entry_id
            ),
            None,
        )
        if target is None:
            return
        is_locked = bool(entry.get("locked", False))
        mode_item = self.saved_sets_table.item(row, SAVED_COL_MODE)
        score_item = self.saved_sets_table.item(row, SAVED_COL_SCORE)
        expected_score_item = self.saved_sets_table.item(row, SAVED_COL_EXPECTED_SCORE)
        gcd_item = self.saved_sets_table.item(row, SAVED_COL_GCD)
        if expected_score is None:
            current_eval = self._evaluate_current_gearset_scores(mode)
            expected_score = current_eval[1] if current_eval else score
        new_mode = self.calc_mode.currentData() or mode
        stats = self._compute_saved_stats(
            self.current_gearset,
            self.current_gearset.food_id,
            self.party_bonus.value(),
        )
        if is_locked and not self._saved_score_context_matches_current(target, new_mode, stats):
            saved_mode = str(target.get("mode") or "simdps")
            saved_score_valid, saved_message = self._saved_score_validation(target)
            saved_score = target.get("score")
            saved_expected = self._saved_expected_score_value(target)
            if mode_item:
                mode_item.setText(
                    "XiVGear（Dmg/100p）" if saved_mode == "dmg100p" else "試算DPS（logs基準）"
                )
            for cell, value in ((score_item, saved_score), (expected_score_item, saved_expected)):
                if not cell:
                    continue
                cell.setText(self._format_saved_score(saved_mode, value) if saved_score_valid else "要再計算")
                cell.setToolTip("" if saved_score_valid else saved_message)
            if gcd_item:
                saved_gcd = target.get("gcd")
                try:
                    saved_gcd_value = float(saved_gcd)
                except (TypeError, ValueError):
                    saved_gcd_value = 0.0
                gcd_item.setText(f"{saved_gcd_value:.3f}s" if math.isfinite(saved_gcd_value) and saved_gcd_value > 0 else "-")
            return
        if mode_item:
            mode_item.setText("XiVGear（Dmg/100p）" if new_mode == "dmg100p" else "試算DPS（logs基準）")
        if score_item:
            score_item.setText(self._format_saved_score(new_mode, score))
        if expected_score_item:
            expected_score_item.setText(self._format_saved_score(new_mode, expected_score))
        if gcd_item:
            gcd_item.setText(f"{gcd:.3f}s")

        if stats:
            main_stat_val = self._saved_stats_main_value(stats, self.current_gearset.job)
            for col, key in (
                (SAVED_COL_WD, "wd"),
                (SAVED_COL_HP, "hp"),
                (SAVED_COL_CRT, "crit"),
                (SAVED_COL_DHT, "dhit"),
                (SAVED_COL_DET, "det"),
                (SAVED_COL_SPS, "sps"),
            ):
                cell = self.saved_sets_table.item(row, col)
                if cell:
                    cell.setText(str(stats.get(key, "-")))
            main_cell = self.saved_sets_table.item(row, SAVED_COL_MAIN)
            if main_cell:
                main_cell.setText(str(main_stat_val) if main_stat_val is not None else "-")
        food_cell = self.saved_sets_table.item(row, SAVED_COL_FOOD)
        if food_cell:
            food_cell.setText(self._food_label_by_id(self.current_gearset.food_id))
        # 選択中セットは表示のみでなく、現在の構成と評価値で自動上書きする。
        changed = False
        if target.get("mode") != new_mode:
            target["mode"] = new_mode
            changed = True
        old_score = target.get("score")
        if self._saved_numeric_changed(old_score, score):
            target["score"] = float(score)
            changed = True
        old_expected_score = target.get("expected_score")
        if self._saved_numeric_changed(old_expected_score, expected_score):
            target["expected_score"] = float(expected_score)
            changed = True
        old_gcd = target.get("gcd")
        if self._saved_numeric_changed(old_gcd, gcd):
            target["gcd"] = float(gcd)
            changed = True
        if is_locked:
            if stats and target.get("stats") != stats:
                target["stats"] = stats
                target["stats_version"] = STATS_VERSION
                changed = True
            score_meta = self._build_score_meta_for_entry(target, new_mode)
            if score_meta is None:
                if target.pop("score_meta", None) is not None:
                    changed = True
            elif target.get("score_meta") != score_meta:
                target["score_meta"] = score_meta
                changed = True
            if changed:
                target["saved_at"] = utc_now_iso()
                self._schedule_saved_sets_flush(immediate=False)
                if isinstance(entry, dict):
                    entry.update(target)
                    if entry_item:
                        entry_item.setData(Qt.UserRole, entry)
            score_valid, message = self._saved_score_validation(target)
            for cell, value in ((score_item, score), (expected_score_item, expected_score)):
                if not cell:
                    continue
                cell.setText(self._format_saved_score(new_mode, value) if score_valid else "要再計算")
                cell.setToolTip("" if score_valid else message)
            return
        gear_dict = self.current_gearset.to_dict()
        new_food_id = self.current_gearset.food_id
        new_party_bonus = self.party_bonus.value()
        new_ui_context = self._capture_saved_set_ui_context(self.current_gearset.job)
        if target.get("food_id") != new_food_id:
            target["food_id"] = new_food_id
            changed = True
        if target.get("party_bonus") != new_party_bonus:
            target["party_bonus"] = new_party_bonus
            changed = True
        if target.get("ui_context") != new_ui_context:
            target["ui_context"] = new_ui_context
            changed = True
        if target.get("gearset") != gear_dict:
            target["gearset"] = gear_dict
            changed = True
        if stats and target.get("stats") != stats:
            target["stats"] = stats
            target["stats_version"] = STATS_VERSION
            changed = True
        report_code = extract_report_code(self.input_report_code.text())
        if target.get("report_code") != report_code:
            target["report_code"] = report_code
            changed = True
        fight_id = self.selected_fight.get("id") if self.selected_fight else None
        if target.get("fight_id") != fight_id:
            target["fight_id"] = fight_id
            changed = True
        actor_id = self.selected_actor.get("id") if self.selected_actor else None
        if target.get("actor_id") != actor_id:
            target["actor_id"] = actor_id
            changed = True
        score_meta = self._build_score_meta_for_entry(target, new_mode)
        if score_meta is None:
            if target.pop("score_meta", None) is not None:
                changed = True
        elif target.get("score_meta") != score_meta:
            target["score_meta"] = score_meta
            changed = True
        if changed:
            target["saved_at"] = utc_now_iso()
            self._schedule_saved_sets_flush(immediate=False)
            if isinstance(entry, dict):
                entry.update(target)
                if entry_item:
                    entry_item.setData(Qt.UserRole, entry)
        score_valid, message = self._saved_score_validation(target)
        for cell, value in ((score_item, score), (expected_score_item, expected_score)):
            if not cell:
                continue
            cell.setText(self._format_saved_score(new_mode, value) if score_valid else "要再計算")
            cell.setToolTip("" if score_valid else message)

    def _find_actor_entry(self, table: dict) -> Optional[dict]:
        entries = self._extract_damage_table_entries(table)
        if not entries:
            return None
        actor_id = self.selected_actor.get("id") if self.selected_actor else None
        actor_guid = self.selected_actor.get("guid") if self.selected_actor else None
        actor_name = self.selected_actor.get("name") if self.selected_actor else None
        actor_name_norm = actor_name.strip().lower() if isinstance(actor_name, str) else None

        def norm_id(val: object) -> Optional[int]:
            try:
                if val is None:
                    return None
                return int(val)
            except Exception:
                return None

        actor_id_norm = norm_id(actor_id)
        actor_guid_norm = norm_id(actor_guid)

        def is_ability_entry(e: dict) -> bool:
            return any(
                key in e
                for key in (
                    "abilityIcon",
                    "abilityName",
                    "ability",
                    "abilityID",
                    "abilityId",
                )
            )

        ability_like = False
        for e in entries[:5]:
            if isinstance(e, dict) and is_ability_entry(e):
                ability_like = True
                break
        entry = None
        if actor_id_norm is not None:
            for e in entries:
                if not isinstance(e, dict):
                    continue
                if norm_id(e.get("id")) == actor_id_norm:
                    entry = e
                    break
        if entry is None and actor_guid_norm is not None:
            for e in entries:
                if not isinstance(e, dict):
                    continue
                if norm_id(e.get("guid")) == actor_guid_norm:
                    entry = e
                    break
        if entry is None and actor_name_norm:
            for e in entries:
                if not isinstance(e, dict):
                    continue
                name = e.get("name") or e.get("actorName")
                if isinstance(name, str) and name.strip().lower() == actor_name_norm:
                    entry = e
                    break
        if entry is None and not ability_like and actor_id_norm is not None:
            for e in entries:
                if not isinstance(e, dict):
                    continue
                if norm_id(e.get("actor")) == actor_id_norm:
                    entry = e
                    break
        return entry

    def _build_ndps_summary(self, base_summary: Optional[Dict[str, object]] = None) -> Optional[Dict[str, object]]:
        summary = base_summary if base_summary is not None else self.damage_summary
        if not summary or not isinstance(self.damage_table, dict):
            return None
        table_raid = self._normalize_table_dict(self.damage_table.get("raid"))
        table_actor_raw = self.damage_table.get("actor") if "actor" in self.damage_table else self.damage_table
        table_actor = self._normalize_table_dict(table_actor_raw)
        entry = None
        if isinstance(table_raid, dict):
            entry = self._find_actor_entry(table_raid)
        if entry is None and isinstance(table_actor, dict):
            entry = self._find_actor_entry(table_actor)
        if not isinstance(entry, dict):
            return None
        total_ndps = None
        key_used = None
        for key in ("totalNDPS", "totalNDPSRaw", "totalNDPSDone", "ndps"):
            if key in entry and entry.get(key) is not None:
                total_ndps = entry.get(key)
                key_used = key
                break
        if total_ndps is None:
            return None
        try:
            total_ndps_val = float(total_ndps)
        except Exception:
            return None
        total_val = entry.get("total")
        rdps_taken = entry.get("totalRDPSTaken")
        derived_ndps = None
        try:
            if total_val is not None and rdps_taken is not None:
                derived_ndps = float(total_val) - float(rdps_taken)
        except Exception:
            derived_ndps = None
        total_raw = float(summary.get("total_amount") or summary.get("total_damage") or 0.0)
        if total_raw <= 0:
            return None
        combat_time = None
        if isinstance(table_actor, dict):
            combat_time = table_actor.get("combatTime") or table_actor.get("totalTime")
        if combat_time is None:
            table_raid = self._normalize_table_dict(self.damage_table.get("raid"))
            if isinstance(table_raid, dict):
                combat_time = table_raid.get("combatTime") or table_raid.get("totalTime")
        sim_log(
            f"[simdps] ndps_raw key={key_used} value={total_ndps_val:.3f} total_raw={total_raw:.1f} derived_ndps={derived_ndps}",
        )
        if derived_ndps is not None and derived_ndps > 0:
            # Prefer derived NDPS (total - rdps_taken) when it looks reasonable.
            if total_ndps_val <= 0 or total_ndps_val < derived_ndps * 0.1 or total_ndps_val > derived_ndps * 10.0:
                total_ndps_val = derived_ndps
                sim_log(
                    f"[simdps] ndps use_derived total_ndps={total_ndps_val:.1f}"
                )
        if combat_time:
            try:
                combat_time_val = float(combat_time)
            except Exception:
                combat_time_val = None
            if combat_time_val and total_ndps_val < total_raw:
                scaled_total = total_ndps_val * combat_time_val / 1000.0
                # Only scale if it still fits within raw total (per-second NDPS case).
                if scaled_total <= total_raw * 1.2:
                    total_ndps_val = scaled_total
                    sim_log(
                        f"[simdps] ndps total looks per-sec; scaled by combatTime={combat_time_val}"
                    )
        scale = total_ndps_val / total_raw
        sim_log(
            f"[simdps] ndps_scale total_ndps={total_ndps_val:.1f} total_raw={total_raw:.1f} scale={scale:.6f}",
        )
        buckets = {}
        for key, val in (summary.get("buckets") or {}).items():
            buckets[key] = float(val) * scale
        bucket_counts = dict(summary.get("bucket_counts") or {})
        ability_buckets = {}
        for key, val in (summary.get("ability_buckets") or {}).items():
            ability_buckets[key] = float(val) * scale
        ability_bucket_counts = dict(summary.get("ability_bucket_counts") or {})
        ability_names = dict(summary.get("ability_names") or {})
        unknown_actions = {}
        for key, info in (summary.get("unknown_actions") or {}).items():
            unknown_actions[key] = {
                "damage": float(info.get("damage", 0.0)) * scale,
                "count": info.get("count", 0),
            }
        return {
            "total_damage": total_raw * scale,
            "total_hits": summary.get("total_hits", 0),
            "buckets": buckets,
            "bucket_counts": bucket_counts,
            "ability_buckets": ability_buckets,
            "ability_bucket_counts": ability_bucket_counts,
            "ability_names": ability_names,
            "total_amount": total_raw * scale,
            "total_absorbed": 0.0,
            "total_overkill": 0.0,
            "min_ts": summary.get("min_ts"),
            "max_ts": summary.get("max_ts"),
            "unknown_actions": unknown_actions,
        }

    def _clear_layout(self, layout: QHBoxLayout) -> None:
        while layout.count():
            item = layout.takeAt(0)
            widget = item.widget()
            if widget:
                widget.setParent(None)

    def _normalize_table_dict(self, table: object) -> dict:
        current = table
        for _ in range(5):
            if not isinstance(current, dict):
                return {}
            if isinstance(current.get("table"), dict):
                current = current.get("table")
                continue
            if isinstance(current.get("data"), dict):
                current = current.get("data")
                continue
            break
        return current if isinstance(current, dict) else {}

    def _extract_damage_table_entries(self, table: dict) -> List[dict]:
        table = self._normalize_table_dict(table)
        if not isinstance(table, dict):
            return []
        for key in ("entries", "data", "series", "actors", "targets"):
            val = table.get(key)
            if isinstance(val, list):
                return val
        return []

    def _extract_action_ids_from_table(self, table: dict) -> List[int]:
        entries = self._extract_damage_table_entries(table)
        if not entries:
            return []
        actor_id = self.selected_actor.get("id") if self.selected_actor else None
        actor_guid = self.selected_actor.get("guid") if self.selected_actor else None
        actor_name = self.selected_actor.get("name") if self.selected_actor else None
        entry = None
        for e in entries:
            if not isinstance(e, dict):
                continue
            if actor_id is not None and (e.get("id") == actor_id or e.get("actor") == actor_id):
                entry = e
                break
        if entry is None and actor_guid is not None:
            for e in entries:
                if isinstance(e, dict) and (e.get("guid") == actor_guid or e.get("actor") == actor_guid):
                    entry = e
                    break
        if entry is None and actor_name:
            for e in entries:
                if isinstance(e, dict):
                    if e.get("name") == actor_name or e.get("actorName") == actor_name:
                        entry = e
                        break
        if entry is None:
            # Some FFLogs table views return ability rows directly.
            direct_ids = []
            for e in entries:
                if not isinstance(e, dict):
                    continue
                aid = e.get("guid") or e.get("id") or e.get("ability")
                if aid:
                    try:
                        direct_ids.append(int(aid))
                    except Exception:
                        continue
            return sorted(set(direct_ids))
        abilities = entry.get("damageAbilities") or entry.get("abilities") or []
        if not isinstance(abilities, list):
            return []
        ids = []
        for ab in abilities:
            if not isinstance(ab, dict):
                continue
            aid = ab.get("guid") or ab.get("id") or ab.get("ability")
            if aid:
                try:
                    ids.append(int(aid))
                except Exception:
                    continue
        return sorted(set(ids))

    def _extract_action_ids_from_events(self, casts: List[dict], timeline: List[dict], damage: List[dict]) -> List[int]:
        ids = []

        def _add_from_event(ev: dict) -> None:
            ability = ev.get("ability") or {}
            candidates = [
                ability.get("gameID"),
                ability.get("guid"),
                ability.get("id"),
                ev.get("abilityGameID"),
                ev.get("abilityGuid"),
                ev.get("abilityID"),
            ]
            for raw in candidates:
                if not raw:
                    continue
                try:
                    ids.append(int(raw))
                except Exception:
                    continue

        for ev in casts or []:
            _add_from_event(ev)
        for ev in timeline or []:
            _add_from_event(ev)
        for ev in damage or []:
            _add_from_event(ev)
        return sorted(set(ids))

    def _extract_status_ids_from_timeline(self, events: List[dict]) -> List[int]:
        if not events:
            return []
        keep_types = {
            "applybuff",
            "refreshbuff",
            "removebuff",
            "removebuffstack",
            "applydebuff",
            "refreshdebuff",
            "removedebuff",
            "removedebuffstack",
        }
        ids = []
        for ev in events:
            if ev.get("type") not in keep_types:
                continue
            ability = ev.get("ability") or {}
            candidates = [
                ability.get("gameID"),
                ability.get("guid"),
                ability.get("id"),
                ev.get("abilityGameID"),
                ev.get("abilityGuid"),
                ev.get("abilityID"),
            ]
            for raw in candidates:
                if not raw:
                    continue
                try:
                    ids.append(int(raw))
                except Exception:
                    continue
        return sorted(set(ids))

    def _sorted_relic_stat_ids(
        self,
        job: Optional[str],
        stat_caps: Optional[Dict[int, int]] = None,
    ) -> List[int]:
        allowed = set(optimizer.allowed_meld_stats(job or "")) if job else set(RELIC_STAT_ORDER)
        if stat_caps is not None:
            allowed &= {int(stat_id) for stat_id, value in stat_caps.items() if int(value or 0) > 0}
        ordered = [stat_id for stat_id in RELIC_STAT_ORDER if stat_id in allowed]
        extras = sorted(allowed.difference(ordered))
        return ordered + extras

    def _selection_relic_stats(self, selection: Optional[ItemSelection]) -> Dict[int, int]:
        raw_stats = getattr(selection, "relic_stats", {}) or {}
        if not isinstance(raw_stats, dict):
            return {}
        normalized: Dict[int, int] = {}
        for raw_stat_id, raw_value in raw_stats.items():
            try:
                stat_id = int(raw_stat_id)
                value = int(raw_value or 0)
            except Exception:
                continue
            if stat_id <= 0 or value <= 0:
                continue
            normalized[stat_id] = value
        return normalized

    def _is_manderville_weapon_item(self, item: Optional[ItemRecord]) -> bool:
        if not item:
            return False
        if str(getattr(item, "slot", "")) not in {"weapon", "offhand"}:
            return False
        if int(getattr(item, "materia_slots", 0) or 0) != 0:
            return False
        names = [
            str(getattr(item, "name", "") or ""),
            str(getattr(item, "name_ja", "") or ""),
        ]
        return any(
            name.startswith(prefix)
            for name in names
            for prefix in MANDERVILLE_NAME_PREFIXES
            if prefix
        )

    def _is_phantom_weapon_item(self, item: Optional[ItemRecord]) -> bool:
        if not item or str(getattr(item, "slot", "")) not in {"weapon", "offhand"}:
            return False
        names = [
            str(getattr(item, "name", "") or ""),
            str(getattr(item, "name_ja", "") or ""),
        ]
        return any(
            name.startswith(prefix)
            for name in names
            for prefix in PHANTOM_NAME_PREFIXES
            if prefix
        )

    def _is_search_special_weapon_item(
        self,
        item: Optional[ItemRecord],
        job: Optional[str],
    ) -> bool:
        if self._is_phantom_weapon_item(item):
            return True
        return self._relic_model_for_item(item, job) is not None

    def _gear_search_relic_stat_variants(
        self,
        config: Optional[Dict[str, object]],
    ) -> List[Dict[int, int]]:
        if not config:
            return []
        allowed_stats = [int(stat_id) for stat_id in list(config.get("allowed_stats", []) or [])]
        if not allowed_stats:
            return []
        variants: set[Tuple[Tuple[int, int], ...]] = set()
        kind = str(config.get("kind") or "")
        if kind == "manderville":
            fixed_values = [int(value) for value in list(config.get("fixed_values", []) or [])]
            if len(fixed_values) < 3:
                return []
            primary_value = fixed_values[0]
            tertiary_value = fixed_values[2]
            for primary_stats in combinations(allowed_stats, 2):
                for tertiary_stat in allowed_stats:
                    if tertiary_stat in primary_stats:
                        continue
                    stats = {
                        int(primary_stats[0]): primary_value,
                        int(primary_stats[1]): primary_value,
                        int(tertiary_stat): tertiary_value,
                    }
                    variants.add(tuple(sorted(stats.items())))
        elif kind == "resistance":
            total_cap = int(config.get("total_cap", 0) or 0)
            stat_caps = {
                int(stat_id): int(value)
                for stat_id, value in dict(config.get("stat_caps", {}) or {}).items()
                if int(value or 0) > 0
            }
            if total_cap <= 0 or not stat_caps:
                return []
            usable_stats = [stat_id for stat_id in allowed_stats if stat_id in stat_caps]

            def add_filled_variants(fixed_stats: Dict[int, int]) -> None:
                remaining_total = total_cap - sum(fixed_stats.values())
                remaining_stats = [
                    stat_id for stat_id in usable_stats if stat_id not in fixed_stats
                ]
                for stat_order in permutations(remaining_stats):
                    remaining = remaining_total
                    stats = dict(fixed_stats)
                    for stat_id in stat_order:
                        value = min(stat_caps[stat_id], remaining)
                        if value > 0:
                            stats[stat_id] = value
                            remaining -= value
                        if remaining <= 0:
                            break
                    if remaining <= 0:
                        variants.add(tuple(sorted(stats.items())))

            add_filled_variants({})
            allocation_step = 36
            for pivot_stat in usable_stats:
                pivot_cap = min(stat_caps[pivot_stat], total_cap)
                for pivot_value in range(allocation_step, pivot_cap, allocation_step):
                    add_filled_variants({pivot_stat: pivot_value})

            for subset_size in range(2, len(usable_stats) + 1):
                for stat_subset in combinations(usable_stats, subset_size):
                    if sum(stat_caps[stat_id] for stat_id in stat_subset) < total_cap:
                        continue
                    for stat_order in permutations(stat_subset):
                        remaining = total_cap
                        stats = {stat_id: 0 for stat_id in stat_subset}
                        while remaining > 0:
                            progressed = False
                            for stat_id in stat_order:
                                if stats[stat_id] >= stat_caps[stat_id]:
                                    continue
                                stats[stat_id] += 1
                                remaining -= 1
                                progressed = True
                                if remaining <= 0:
                                    break
                            if not progressed:
                                break
                        if remaining <= 0:
                            variants.add(
                                tuple(
                                    sorted(
                                        (stat_id, value)
                                        for stat_id, value in stats.items()
                                        if value > 0
                                    )
                                )
                            )
        return [dict(entries) for entries in sorted(variants)]

    def _manderville_fixed_values_for_item(self, item: Optional[ItemRecord]) -> Tuple[int, int, int]:
        if not item:
            return MANDERVILLE_FIXED_STAT_VALUES
        names = [
            str(getattr(item, "name", "") or ""),
            str(getattr(item, "name_ja", "") or ""),
        ]
        final_prefixes = ("Mandervillous", "マンダヴィラス")
        if any(
            name.startswith(prefix)
            for name in names
            for prefix in final_prefixes
            if prefix
        ):
            return MANDERVILLOUS_FIXED_STAT_VALUES
        return MANDERVILLE_FIXED_STAT_VALUES

    def _special_weapon_kind_text(self, config: Optional[Dict[str, object]]) -> str:
        kind = str((config or {}).get("kind") or "")
        if kind == "manderville":
            return "MW"
        if kind == "resistance":
            return "RW"
        return "特殊武器"

    def _special_weapon_dialog_title(self, slot: str, config: Optional[Dict[str, object]]) -> str:
        kind = str((config or {}).get("kind") or "")
        slot_label = SLOT_LABELS.get(slot, slot)
        if kind == "manderville":
            return f"{slot_label} のマンダヴィル補正"
        if kind == "resistance":
            return f"{slot_label} のレジスタンス補正"
        return f"{slot_label} の特殊武器補正"

    def _special_weapon_group_key(self, item: Optional[ItemRecord], job: Optional[str]) -> str:
        if self._is_phantom_weapon_item(item):
            return "phantom"
        config = self._relic_model_for_item(item, job)
        kind = str((config or {}).get("kind") or "").strip().lower()
        return kind or "normal"

    def _relic_model_for_item(self, item: Optional[ItemRecord], job: Optional[str]) -> Optional[Dict[str, object]]:
        if not item or not job:
            return None
        cache_key = (int(getattr(item, "item_id", 0) or 0), str(job))
        cached = self._relic_model_cache.get(cache_key)
        if cached is not None or cache_key in self._relic_model_cache:
            return cached
        if str(getattr(item, "slot", "")) not in {"weapon", "offhand"}:
            self._relic_model_cache[cache_key] = None
            return None
        if self._is_manderville_weapon_item(item):
            config = {
                "kind": "manderville",
                "item_ilvl": int(getattr(item, "ilvl", 0) or 0),
                "fixed_values": list(self._manderville_fixed_values_for_item(item)),
                "allowed_stats": self._sorted_relic_stat_ids(job),
            }
            self._relic_model_cache[cache_key] = config
            return config
        if not self.base_params or not self.item_levels:
            self._relic_model_cache[cache_key] = None
            return None
        if int(getattr(item, "materia_slots", 0) or 0) != 0:
            self._relic_model_cache[cache_key] = None
            return None
        ilvl = int(getattr(item, "ilvl", 0) or 0)
        base_total_cap = RELIC_TOTAL_CAP_BY_ILVL.get(ilvl)
        if not base_total_cap:
            self._relic_model_cache[cache_key] = None
            return None
        main_stat_id = self._main_stat_id_for_job(job)
        present_stats = {
            int(stat_id)
            for stat_id, value in (getattr(item, "base_params_hq", {}) or {}).items()
            if int(value or 0) > 0
        }
        if present_stats and not present_stats.issubset({main_stat_id, 3}):
            self._relic_model_cache[cache_key] = None
            return None
        crit_bp = self.base_params.get(27)
        occ_slot = getattr(item, "occ_slot", None) or getattr(item, "slot", "")
        slot_scale = getattr(crit_bp, "slots", {}).get(occ_slot) if crit_bp else None
        if slot_scale is None:
            self._relic_model_cache[cache_key] = None
            return None
        total_cap = int(round(float(base_total_cap) * (float(slot_scale) / 140.0)))
        stat_caps_raw = optimizer.compute_item_stat_caps_for_il(
            item,
            self.base_params,
            self.item_levels,
            job,
            ilvl,
        )
        if not stat_caps_raw:
            self._relic_model_cache[cache_key] = None
            return None
        stat_caps: Dict[int, int] = {}
        for stat_id in self._sorted_relic_stat_ids(job):
            cap_val = int(stat_caps_raw.get(stat_id, 0) or 0)
            if cap_val > 0:
                stat_caps[int(stat_id)] = cap_val
        if not stat_caps:
            self._relic_model_cache[cache_key] = None
            return None
        config = {
            "kind": "resistance",
            "item_ilvl": ilvl,
            "total_cap": total_cap,
            "stat_caps": stat_caps,
            "allowed_stats": self._sorted_relic_stat_ids(job, stat_caps),
        }
        self._relic_model_cache[cache_key] = config
        return config

    def _effective_manderville_stats_from_config(
        self,
        raw_stats: Dict[int, int],
        config: Optional[Dict[str, object]],
    ) -> Dict[int, int]:
        if not config:
            return {}
        allowed_stats = [int(stat_id) for stat_id in list(config.get("allowed_stats", []) or [])]
        if not allowed_stats:
            return {}
        fixed_values = list(config.get("fixed_values", []) or [])
        primary_value = int(fixed_values[0]) if len(fixed_values) >= 1 else MANDERVILLE_PRIMARY_STAT_VALUE
        tertiary_value = int(fixed_values[2]) if len(fixed_values) >= 3 else MANDERVILLE_TERTIARY_STAT_VALUE
        primary_stats = [
            stat_id
            for stat_id in allowed_stats
            if int(raw_stats.get(stat_id, 0) or 0) == primary_value
        ]
        tertiary_stats = [
            stat_id
            for stat_id in allowed_stats
            if int(raw_stats.get(stat_id, 0) or 0) == tertiary_value
        ]
        effective: Dict[int, int] = {}
        for stat_id in primary_stats[:2]:
            effective[int(stat_id)] = primary_value
        for stat_id in tertiary_stats:
            if int(stat_id) in effective:
                continue
            effective[int(stat_id)] = tertiary_value
            break
        return effective

    def _manderville_selection_slots(
        self,
        selection: Optional[ItemSelection],
        config: Optional[Dict[str, object]],
    ) -> Tuple[Optional[int], Optional[int], Optional[int]]:
        effective_stats = self._effective_manderville_stats_from_config(
            self._selection_relic_stats(selection),
            config,
        )
        allowed_stats = [int(stat_id) for stat_id in list((config or {}).get("allowed_stats", []) or [])]
        fixed_values = list((config or {}).get("fixed_values", []) or [])
        primary_value = int(fixed_values[0]) if len(fixed_values) >= 1 else MANDERVILLE_PRIMARY_STAT_VALUE
        tertiary_value = int(fixed_values[2]) if len(fixed_values) >= 3 else MANDERVILLE_TERTIARY_STAT_VALUE
        primary_stats = [
            stat_id
            for stat_id in allowed_stats
            if int(effective_stats.get(stat_id, 0) or 0) == primary_value
        ]
        tertiary_stat = next(
            (
                stat_id
                for stat_id in allowed_stats
                if int(effective_stats.get(stat_id, 0) or 0) == tertiary_value
            ),
            None,
        )
        first = primary_stats[0] if len(primary_stats) >= 1 else None
        second = primary_stats[1] if len(primary_stats) >= 2 else None
        return first, second, tertiary_stat

    def _effective_relic_stats_from_config(
        self,
        selection: Optional[ItemSelection],
        config: Optional[Dict[str, object]],
    ) -> Dict[int, int]:
        if not config:
            return {}
        raw_stats = self._selection_relic_stats(selection)
        if not raw_stats:
            return {}
        if str(config.get("kind") or "") == "manderville":
            return self._effective_manderville_stats_from_config(raw_stats, config)
        remaining_total = int(config.get("total_cap", 0) or 0)
        stat_caps = config.get("stat_caps", {}) or {}
        effective: Dict[int, int] = {}
        for stat_id in config.get("allowed_stats", []):
            try:
                requested = int(raw_stats.get(int(stat_id), 0) or 0)
            except Exception:
                continue
            if requested <= 0:
                continue
            per_stat_cap = int(stat_caps.get(int(stat_id), 0) or 0)
            applied = min(requested, per_stat_cap, remaining_total)
            if applied <= 0:
                continue
            effective[int(stat_id)] = applied
            remaining_total -= applied
            if remaining_total <= 0:
                break
        return effective

    def _effective_relic_stats_for_selection(
        self,
        selection: Optional[ItemSelection],
        item: Optional[ItemRecord],
        job: Optional[str],
    ) -> Dict[int, int]:
        config = self._relic_model_for_item(item, job)
        return self._effective_relic_stats_from_config(selection, config)

    def _item_with_relic_stats(
        self,
        item: ItemRecord,
        selection: Optional[ItemSelection],
        job: Optional[str],
    ) -> Tuple[ItemRecord, Optional[Dict[str, object]], Dict[int, int]]:
        config = self._relic_model_for_item(item, job)
        if not config:
            return item, None, {}
        relic_stats = self._effective_relic_stats_from_config(selection, config)
        if not relic_stats:
            return item, config, {}
        base_stats = dict(item.base_params or {})
        hq_stats = dict(item.base_params_hq or {})
        for stat_id, value in relic_stats.items():
            base_stats[stat_id] = int(base_stats.get(stat_id, 0) or 0) + int(value)
            hq_stats[stat_id] = int(hq_stats.get(stat_id, 0) or 0) + int(value)
        relic_item = ItemRecord(
            item_id=item.item_id,
            name=item.name,
            name_ja=item.name_ja,
            jobs=list(item.jobs),
            ilvl=int(item.ilvl),
            slot=item.slot,
            materia_slots=int(item.materia_slots or 0),
            overmeld=bool(item.overmeld),
            base_params=base_stats,
            base_params_hq=hq_stats,
            damage_phys=item.damage_phys,
            damage_mag=item.damage_mag,
            delay_ms=item.delay_ms,
            occ_slot=item.occ_slot,
            unique=bool(item.unique),
            icon_url=item.icon_url,
        )
        return relic_item, config, relic_stats

    def _effective_item_for_selection(
        self,
        item: ItemRecord,
        selection: Optional[ItemSelection],
        job: Optional[str],
        sync_il_override: object = _USE_CURRENT_SYNC,
    ) -> Tuple[ItemRecord, bool, Optional[Dict[str, object]], Dict[int, int]]:
        relic_item, relic_config, relic_stats = self._item_with_relic_stats(item, selection, job)
        effective_item, synced = self._apply_level_sync_to_item(
            relic_item,
            job,
            sync_il_override=sync_il_override,
        )
        return effective_item, synced, relic_config, relic_stats

    def _relic_stats_summary_text(
        self,
        selection: Optional[ItemSelection],
        item: Optional[ItemRecord],
        job: Optional[str],
    ) -> str:
        config = self._relic_model_for_item(item, job)
        if not config:
            return ""
        effective_stats = self._effective_relic_stats_for_selection(selection, item, job)
        prefix = self._special_weapon_kind_text(config)
        if str(config.get("kind") or "") == "manderville":
            if not effective_stats:
                return f"{prefix} 未設定"
            parts = [
                f"{STAT_ABBR.get(int(stat_id), str(stat_id))}{int(value)}"
                for stat_id, value in effective_stats.items()
                if int(value or 0) > 0
            ]
            return f"{prefix} {' / '.join(parts)}"
        used_total = sum(int(v) for v in effective_stats.values())
        total_cap = int(config.get("total_cap", 0) or 0)
        if not effective_stats:
            return f"{prefix} 未設定 (0/{total_cap})"
        parts = [
            f"{STAT_ABBR.get(int(stat_id), str(stat_id))}{int(value)}"
            for stat_id, value in effective_stats.items()
            if int(value or 0) > 0
        ]
        return f"{prefix} {' / '.join(parts)} ({used_total}/{total_cap})"

    def _update_slot_materia_display(self, slot: str) -> None:
        layout = getattr(self, "slot_materia_layouts", {}).get(slot)
        if layout is None:
            return
        self._clear_layout(layout)
        sel = self.current_gearset.items.get(slot)
        if not sel or not sel.item_id:
            layout.addWidget(QLabel("装備未選択"))
            layout.addStretch(1)
            return
        item = self.items_by_id.get(sel.item_id)
        if not item:
            layout.addWidget(QLabel("装備不明"))
            layout.addStretch(1)
            return
        effective_item, synced, relic_config, _relic_stats = self._effective_item_for_selection(
            item,
            sel,
            self.current_gearset.job,
        )
        if relic_config:
            relic_summary = QLabel(self._relic_stats_summary_text(sel, item, self.current_gearset.job))
            relic_summary.setToolTip("特殊武器のサブステータス設定")
            layout.addWidget(relic_summary)
            btn_relic = QPushButton(SPECIAL_WEAPON_EDIT_BUTTON_LABEL)
            btn_relic.setToolTip("特殊武器のサブステータスを編集")
            btn_relic.clicked.connect(lambda _checked=False, s=slot: self._open_relic_stat_editor(s))
            layout.addWidget(btn_relic)
        slots_total = optimizer.total_meld_slots_for_item(effective_item)
        if slots_total <= 0:
            if not relic_config:
                layout.addWidget(QLabel("レベルシンク中はマテリア無効" if synced else "スロットなし"))
            elif synced:
                layout.addWidget(QLabel("レベルシンク中はマテリア無効"))
            layout.addStretch(1)
            return
        self._ensure_materia_slots(sel, slots_total)
        guaranteed = optimizer.guaranteed_slots_for_item(effective_item)
        for idx in range(slots_total):
            meld = sel.materia[idx] if idx < len(sel.materia) else None
            btn = QToolButton()
            btn.setToolButtonStyle(Qt.ToolButtonTextBesideIcon)
            btn.setIconSize(QSize(24, 24))
            if meld and meld.base_param > 0 and meld.grade > 0:
                grade = self._materia_grade(meld.base_param, meld.grade)
                value = grade.value if grade else self._materia_value(meld.base_param, meld.grade)
                abbr = STAT_ABBR.get(meld.base_param, f"{meld.base_param}")
                btn.setText(f"{value} {abbr}")
                if grade and grade.icon_url:
                    icon = self._get_materia_icon(grade.icon_url)
                    if icon:
                        btn.setIcon(icon)
                    else:
                        self._pending_icon_buttons.setdefault(grade.icon_url, []).append(btn)
            else:
                btn.setText("空き")
            if idx >= guaranteed:
                btn.setToolTip("禁断スロット")
            btn.clicked.connect(lambda _checked=False, s=slot, i=idx: self._open_materia_picker(s, i))
            btn.setStyleSheet("QToolButton { background-color: #1f242a; border: 1px solid #3a424c; border-radius: 10px; padding: 2px 6px; }"
                              "QToolButton:hover { background-color: #2b323a; }")
            layout.addWidget(btn)
        layout.addStretch(1)

    def _ensure_materia_slots(self, sel: ItemSelection, slots_total: int, trim: bool = False) -> None:
        if len(sel.materia) > slots_total:
            sel.materia = sel.materia[:slots_total]
        while len(sel.materia) < slots_total:
            sel.materia.append(MateriaSlotSelection(base_param=0, grade=0))
        if trim:
            return

    def _materia_grade(self, base_param: int, grade: int) -> Optional[MateriaGrade]:
        cat = self.materia_catalog.get(base_param)
        if not cat:
            return None
        for g in cat.grades:
            if g.grade == grade:
                return g
        return None

    def _get_materia_icon(self, url: Optional[str]) -> Optional[QIcon]:
        if not self._icon_display_enabled():
            return None
        if not url:
            return None
        cached = self._materia_icon_cache.get(url)
        if cached:
            return cached
        disk_icon = self._load_icon_from_disk(url)
        if disk_icon:
            return disk_icon
        self._queue_icon_fetch(url)
        return None

    def _icon_cache_path(self, url: str) -> Path:
        key = hashlib.sha1(url.encode("utf-8")).hexdigest()
        return self._icon_cache_dir / f"{key}.png"

    def _load_icon_from_disk(self, url: str) -> Optional[QIcon]:
        try:
            path = self._icon_cache_path(url)
            if not path.exists():
                return None
            pixmap = QPixmap(str(path))
            if pixmap.isNull():
                return None
            icon = QIcon(pixmap)
            self._materia_icon_cache[url] = icon
            return icon
        except Exception:
            return None

    def _queue_icon_fetch(self, url: str) -> None:
        if not self._icon_display_enabled():
            return
        if url in self._icon_fetching:
            return
        self._icon_fetching.add(url)

        def task(stop_event=None, progress=None, _url=url):
            resp = httpx.get(_url, timeout=10)
            resp.raise_for_status()
            return resp.content

        worker = Worker(task)
        self._icon_workers[url] = worker
        worker.signals.finished.connect(
            lambda data, _url=url: self._on_icon_fetched(_url, data),
            Qt.QueuedConnection,
        )
        worker.signals.error.connect(
            lambda _trace, _url=url: self._on_icon_failed(_url),
            Qt.QueuedConnection,
        )
        self.icon_thread_pool.start(worker)

    def _on_icon_fetched(self, url: str, data: Optional[bytes]) -> None:
        self._icon_fetching.discard(url)
        self._icon_workers.pop(url, None)
        if not data:
            return
        try:
            self._icon_cache_dir.mkdir(parents=True, exist_ok=True)
            path = self._icon_cache_path(url)
            if not path.exists():
                with path.open("wb") as f:
                    f.write(data)
            pixmap = QPixmap()
            pixmap.loadFromData(data)
            if pixmap.isNull():
                try:
                    if path.exists():
                        path.unlink()
                except Exception:
                    pass
                self._on_icon_failed(url)
                return
            icon = QIcon(pixmap)
            self._materia_icon_cache[url] = icon
            pending = self._pending_icon_buttons.pop(url, [])
            for btn in pending:
                btn.setIcon(icon)
            pending_cells = self._pending_item_icon_cells.pop(url, [])
            for table, row, col in pending_cells:
                try:
                    if table is None or row < 0 or col < 0 or row >= table.rowCount():
                        continue
                    cell = table.item(row, col)
                    if not cell:
                        continue
                    if cell.data(Qt.UserRole + 2) != url:
                        continue
                    cell.setIcon(icon)
                except Exception:
                    continue
        except Exception:
            return

    def _on_icon_failed(self, url: str) -> None:
        self._icon_fetching.discard(url)
        self._icon_workers.pop(url, None)
        self._pending_item_icon_cells.pop(url, None)
        self._prefetched_item_icon_urls.discard(url)

    def _prefetch_materia_icons(self) -> None:
        if not self._icon_display_enabled():
            return
        if self._prefetch_icons_started:
            return
        if not self.materia_catalog:
            return
        self._prefetch_icons_started = True
        urls = [
            grade.icon_url
            for cat in self.materia_catalog.values()
            for grade in cat.grades
            if grade.icon_url
        ]
        unique_urls = list(dict.fromkeys(urls))
        for url in unique_urls:
            if url in self._materia_icon_cache:
                continue
            if self._load_icon_from_disk(url):
                continue
            self._queue_icon_fetch(url)

    def _prefetch_item_icons(self, items: List[object]) -> None:
        if not self._icon_display_enabled():
            return
        if not items:
            return
        urls: List[str] = []
        for item in items:
            url = getattr(item, "icon_url", None)
            if url:
                urls.append(url)
        self._prefetch_item_icon_urls(urls)

    def _prefetch_item_icon_urls(self, urls: List[str]) -> None:
        if not self._icon_display_enabled():
            return
        if not urls:
            return
        for url in dict.fromkeys(urls):
            if url in self._prefetched_item_icon_urls:
                continue
            self._prefetched_item_icon_urls.add(url)
            if url in self._materia_icon_cache:
                continue
            if self._load_icon_from_disk(url):
                continue
            self._queue_icon_fetch(url)

    def _open_materia_picker(self, slot: str, slot_idx: int) -> None:
        sel = self.current_gearset.items.get(slot)
        if not sel or not sel.item_id:
            return
        item = self.items_by_id.get(sel.item_id)
        if not item:
            return
        effective_item, synced = self._apply_level_sync_to_item(item, self.current_gearset.job)
        slots_total = optimizer.total_meld_slots_for_item(effective_item)
        if synced and slots_total <= 0:
            QMessageBox.information(self, "マテリア無効", "レベルシンク中の装備にはマテリアを装着できません。")
            return
        if slot_idx >= slots_total:
            return
        allowed_stats = optimizer.allowed_meld_stats(self.current_gearset.job or "")
        options: List[Tuple[int, MateriaGrade]] = []
        for stat_id, cat in self.materia_catalog.items():
            if stat_id not in allowed_stats:
                continue
            options.extend(
                (stat_id, grade)
                for grade in optimizer.allowed_grades_for_slot(effective_item, cat.grades, slot_idx)
            )
        if not options:
            QMessageBox.information(self, "マテリアなし", "このスロットに装着可能なマテリアがありません。")
            return
        options.sort(key=lambda x: (STAT_ABBR.get(x[0], str(x[0])), -x[1].value))

        dialog = QDialog(self)
        dialog.setWindowTitle("マテリアを選択")
        dialog_layout = QVBoxLayout(dialog)
        info = QLabel("クリックで差し替え / 右下の未選択で外す")
        dialog_layout.addWidget(info)
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        container = QWidget()
        grid = QGridLayout()
        container.setLayout(grid)
        scroll.setWidget(container)
        dialog_layout.addWidget(scroll)

        def apply_selection(base_param: int, grade: int) -> None:
            self._ensure_materia_slots(sel, slots_total)
            sel.materia[slot_idx] = MateriaSlotSelection(base_param=base_param, grade=grade)
            self.current_gearset.items[slot] = sel
            dialog.accept()

        def clear_selection() -> None:
            self._ensure_materia_slots(sel, slots_total)
            sel.materia[slot_idx] = MateriaSlotSelection(base_param=0, grade=0)
            self.current_gearset.items[slot] = sel
            dialog.accept()

        cols = 5
        row = 0
        col = 0
        for stat_id, grade in options:
            btn = QToolButton()
            btn.setToolButtonStyle(Qt.ToolButtonTextUnderIcon)
            btn.setIconSize(QSize(28, 28))
            icon = self._get_materia_icon(grade.icon_url)
            if icon:
                btn.setIcon(icon)
            abbr = STAT_ABBR.get(stat_id, f"{stat_id}")
            btn.setText(f"{grade.value} {abbr}")
            btn.clicked.connect(lambda _checked=False, s=stat_id, g=grade.grade: apply_selection(s, g))
            grid.addWidget(btn, row, col)
            col += 1
            if col >= cols:
                col = 0
                row += 1

        btn_clear = QPushButton("未選択")
        btn_clear.clicked.connect(clear_selection)
        dialog_layout.addWidget(btn_clear)
        dialog.exec()
        self._refresh_slot_selected_display(slot)
        self._schedule_auto_score_update()

    def _open_relic_stat_editor(self, slot: str) -> None:
        sel = self.current_gearset.items.get(slot)
        if not sel or not sel.item_id:
            return
        item = self.items_by_id.get(sel.item_id)
        if not item:
            return
        relic_config = self._relic_model_for_item(item, self.current_gearset.job)
        if not relic_config:
            QMessageBox.information(self, "編集不可", "この装備は手動サブステータス設定に対応していません。")
            return
        current_raw = self._selection_relic_stats(sel)
        total_cap = int(relic_config.get("total_cap", 0) or 0)
        stat_caps = relic_config.get("stat_caps", {}) or {}
        stat_ids = list(relic_config.get("allowed_stats", []) or [])
        kind = str(relic_config.get("kind") or "")

        if kind == "manderville":
            dialog = QDialog(self)
            dialog.setWindowTitle(self._special_weapon_dialog_title(slot, relic_config))
            dialog.setMinimumWidth(380)
            dialog_layout = QVBoxLayout(dialog)
            item_name = display_name_with_fallback(getattr(item, "name_ja", None), item.name)
            item_label = QLabel(f"[IL{int(item.ilvl or 0)}] {item_name}")
            item_label.setWordWrap(True)
            dialog_layout.addWidget(item_label)
            help_label = QLabel(
                "第1・第2ステータスは293、第3ステータスは72固定です。3つの異なるサブステータスを選択してください。"
            )
            help_label.setWordWrap(True)
            dialog_layout.addWidget(help_label)
            form = QFormLayout()
            combo_first = QComboBox(dialog)
            combo_second = QComboBox(dialog)
            combo_third = QComboBox(dialog)
            fixed_values = list(relic_config.get("fixed_values", []) or [])
            primary_value = int(fixed_values[0]) if len(fixed_values) >= 1 else MANDERVILLE_PRIMARY_STAT_VALUE
            tertiary_value = int(fixed_values[2]) if len(fixed_values) >= 3 else MANDERVILLE_TERTIARY_STAT_VALUE
            current_first, current_second, current_third = self._manderville_selection_slots(sel, relic_config)
            help_label.setText(
                f"第1・第2ステータスは{primary_value}、第3ステータスは{tertiary_value}固定です。"
                " 3つの異なるサブステータスを選択してください。"
            )
            form.addRow(f"第1ステータス ({primary_value})", combo_first)
            form.addRow(f"第2ステータス ({primary_value})", combo_second)
            form.addRow(f"第3ステータス ({tertiary_value})", combo_third)
            dialog_layout.addLayout(form)
            status_label = QLabel()
            status_label.setWordWrap(True)
            dialog_layout.addWidget(status_label)

            def _current_combo_values() -> Tuple[Optional[int], Optional[int], Optional[int]]:
                return (
                    combo_first.currentData(),
                    combo_second.currentData(),
                    combo_third.currentData(),
                )

            def _refresh_manderville_combo_options() -> None:
                current_values = _current_combo_values()
                combos = [combo_first, combo_second, combo_third]
                for idx, combo in enumerate(combos):
                    selected_value = current_values[idx]
                    excluded = {
                        int(value)
                        for pos, value in enumerate(current_values)
                        if pos != idx and value is not None
                    }
                    with QSignalBlocker(combo):
                        combo.clear()
                        combo.addItem("未選択", None)
                        for stat_id in stat_ids:
                            stat_id_int = int(stat_id)
                            if stat_id_int in excluded and stat_id_int != selected_value:
                                continue
                            combo.addItem(STAT_ABBR.get(stat_id_int, str(stat_id_int)), stat_id_int)
                        combo.setCurrentIndex(max(0, combo.findData(selected_value)))
                selected_values = [value for value in _current_combo_values() if value is not None]
                if not selected_values:
                    status_label.setText("未設定")
                    status_label.setStyleSheet("")
                    return
                if len(selected_values) != 3:
                    status_label.setText("3つすべてのサブステータスを選択してください。")
                    status_label.setStyleSheet("color: #e5c07b;")
                    return
                if len(set(selected_values)) != 3:
                    status_label.setText("同じサブステータスは重複選択できません。")
                    status_label.setStyleSheet("color: #e06c75;")
                    return
                status_label.setText(
                    " / ".join(
                        [
                            f"{STAT_ABBR.get(int(selected_values[0]), str(selected_values[0]))}{primary_value}",
                            f"{STAT_ABBR.get(int(selected_values[1]), str(selected_values[1]))}{primary_value}",
                            f"{STAT_ABBR.get(int(selected_values[2]), str(selected_values[2]))}{tertiary_value}",
                        ]
                    )
                )
                status_label.setStyleSheet("color: #98c379;")

            for combo in (combo_first, combo_second, combo_third):
                combo.currentIndexChanged.connect(_refresh_manderville_combo_options)
            _refresh_manderville_combo_options()

            buttons = QDialogButtonBox(QDialogButtonBox.Save | QDialogButtonBox.Cancel, parent=dialog)
            btn_reset = buttons.addButton("リセット", QDialogButtonBox.ResetRole)

            def _reset_values() -> None:
                for combo in (combo_first, combo_second, combo_third):
                    combo.setCurrentIndex(0)

            def _save_manderville_values() -> None:
                selected_values = list(_current_combo_values())
                chosen_ids = [value for value in selected_values if value is not None]
                if chosen_ids and len(chosen_ids) != 3:
                    QMessageBox.warning(dialog, "入力不足", "3つすべてのサブステータスを選択してください。")
                    return
                if len(chosen_ids) != len(set(chosen_ids)):
                    QMessageBox.warning(dialog, "重複選択", "同じサブステータスは重複選択できません。")
                    return
                if not chosen_ids:
                    new_stats = {}
                else:
                    new_stats = {
                        int(selected_values[0]): primary_value,
                        int(selected_values[1]): primary_value,
                        int(selected_values[2]): tertiary_value,
                    }
                sel.relic_stats = new_stats
                self.current_gearset.items[slot] = sel
                self._raw_stats_cache.clear()
                self._refresh_slot_selected_display(slot)
                self._persist_current_gearset_to_selected_saved_set()
                self._schedule_auto_score_update()
                dialog.accept()

            btn_reset.clicked.connect(_reset_values)
            buttons.accepted.connect(_save_manderville_values)
            buttons.rejected.connect(dialog.reject)
            dialog_layout.addWidget(buttons)
            dialog.exec()
            return

        dialog = QDialog(self)
        dialog.setWindowTitle(self._special_weapon_dialog_title(slot, relic_config))
        dialog.setMinimumWidth(360)
        dialog_layout = QVBoxLayout(dialog)
        item_name = display_name_with_fallback(getattr(item, "name_ja", None), item.name)
        item_label = QLabel(f"[IL{int(item.ilvl or 0)}] {item_name}")
        item_label.setWordWrap(True)
        dialog_layout.addWidget(item_label)
        help_label = QLabel(
            "サブステータスを手動入力します。各ステータスは個別上限を超えず、合計値は総量上限以内に収めてください。"
        )
        help_label.setWordWrap(True)
        dialog_layout.addWidget(help_label)
        form = QFormLayout()
        spin_boxes: Dict[int, QSpinBox] = {}
        for stat_id in stat_ids:
            spin = QSpinBox(dialog)
            cap_val = int(stat_caps.get(int(stat_id), 0) or 0)
            spin.setRange(0, max(0, cap_val))
            spin.setValue(max(0, min(cap_val, int(current_raw.get(int(stat_id), 0) or 0))))
            spin.setSingleStep(1)
            spin.setAccelerated(True)
            spin_boxes[int(stat_id)] = spin
            form.addRow(f"{STAT_ABBR.get(int(stat_id), str(stat_id))} (max {cap_val})", spin)
        dialog_layout.addLayout(form)
        status_label = QLabel()
        status_label.setWordWrap(True)
        dialog_layout.addWidget(status_label)

        def _update_status() -> None:
            used = sum(spin.value() for spin in spin_boxes.values())
            remaining = total_cap - used
            if remaining < 0:
                status_label.setText(f"総量上限 {total_cap} を {abs(remaining)} 超過しています。")
                status_label.setStyleSheet("color: #e06c75;")
            else:
                status_label.setText(f"使用量 {used} / {total_cap}  残り {remaining}")
                status_label.setStyleSheet("color: #98c379;")

        for spin in spin_boxes.values():
            spin.valueChanged.connect(_update_status)
        _update_status()

        buttons = QDialogButtonBox(QDialogButtonBox.Save | QDialogButtonBox.Cancel, parent=dialog)
        btn_reset = buttons.addButton("リセット", QDialogButtonBox.ResetRole)

        def _reset_values() -> None:
            for spin in spin_boxes.values():
                spin.setValue(0)

        def _save_values() -> None:
            used = sum(spin.value() for spin in spin_boxes.values())
            if used > total_cap:
                QMessageBox.warning(
                    dialog,
                    "上限超過",
                    f"サブステータス合計が総量上限 {total_cap} を超えています。",
                )
                return
            new_stats = {
                int(stat_id): int(spin.value())
                for stat_id, spin in spin_boxes.items()
                if int(spin.value()) > 0
            }
            sel.relic_stats = new_stats
            self.current_gearset.items[slot] = sel
            self._raw_stats_cache.clear()
            self._refresh_slot_selected_display(slot)
            self._persist_current_gearset_to_selected_saved_set()
            self._schedule_auto_score_update()
            dialog.accept()

        btn_reset.clicked.connect(_reset_values)
        buttons.accepted.connect(_save_values)
        buttons.rejected.connect(dialog.reject)
        dialog_layout.addWidget(buttons)
        dialog.exec()

    def _apply_melds_to_item_stats(self, item, melds: List[MateriaSlotSelection]) -> Dict[int, int]:
        slot = getattr(item, "slot", "")
        sel = None
        for slot_name, candidate_sel in (self.current_gearset.items or {}).items():
            if int(getattr(candidate_sel, "item_id", 0) or 0) != int(getattr(item, "item_id", 0) or 0):
                continue
            if slot_name == slot or (slot_name.startswith("ring") and slot == "ring"):
                sel = candidate_sel
                break
        effective_item, synced, _relic_config, _relic_stats = self._effective_item_for_selection(
            item,
            sel,
            self.current_gearset.job,
        )
        stats = dict(effective_item.base_params_hq)
        if synced:
            return stats
        if not melds:
            return stats
        per_item: Dict[int, int] = {}
        for meld in melds:
            if not meld or meld.base_param <= 0 or meld.grade <= 0:
                continue
            value = self._materia_value(meld.base_param, meld.grade)
            per_item[meld.base_param] = per_item.get(meld.base_param, 0) + value
        for stat_id, total_val in per_item.items():
            cap = optimizer.remaining_cap_for_item(item, stat_id, self.cap_table)
            applied = min(total_val, cap)
            if applied <= 0:
                continue
            stats[stat_id] = stats.get(stat_id, 0) + applied
        return stats

    def _refresh_slot_selected_display(self, slot: str) -> None:
        table = self.slot_tables.get(slot)
        job = self.current_gearset.job
        if not table or not job:
            return
        row_map = self.slot_row_index.get(slot)
        if not row_map:
            self._refresh_slot_table_stats(slot)
            return
        speed_stat = 46 if job in SPELL_SPEED_JOBS else 45
        extra_stat = 19 if job in {"PLD", "WAR", "DRK", "GNB"} else 6 if job in {"WHM", "SCH", "AST", "SGE"} else None
        sel = self.current_gearset.items.get(slot)
        selected_id = sel.item_id if sel else None
        prev_id = self._last_selected_items.get(slot)

        def update_row(item_id: Optional[int], use_melds: bool) -> None:
            if not item_id:
                return
            row = row_map.get(item_id)
            if row is None:
                return
            if self._is_compressed_table_row(table, row):
                return
            item = self.items_by_id.get(item_id)
            if not item:
                return
            effective_item, _synced, _relic_config, _relic_stats = self._effective_item_for_selection(
                item,
                sel,
                self.current_gearset.job,
            )
            stats = self._apply_melds_to_item_stats(item, sel.materia) if use_melds and sel else effective_item.base_params_hq
            self._set_table_text(table, row, 2, str(effective_item.materia_slots))
            self._set_table_text(table, row, 3, str(stats.get(27, 0)))
            self._set_table_text(table, row, 4, str(stats.get(22, 0)))
            self._set_table_text(table, row, 5, str(stats.get(44, 0)))
            self._set_table_text(table, row, 6, str(stats.get(speed_stat, 0)))
            extra_val = stats.get(extra_stat, 0) if extra_stat else 0
            self._set_table_text(table, row, 7, str(extra_val) if extra_stat else "-")

        table.blockSignals(True)
        try:
            if prev_id and prev_id != selected_id:
                update_row(prev_id, False)
            if selected_id:
                update_row(selected_id, True)
        finally:
            table.blockSignals(False)

        self._last_selected_items[slot] = selected_id
        self._update_slot_materia_display(slot)

    def _ensure_il_filter_for_gearset(
        self,
        gear: Gearset,
        ui_context: Optional[dict] = None,
        *,
        immediate: bool = False,
    ) -> None:
        if not gear.job:
            return
        items = self.items_by_job.get(gear.job, [])
        if not items:
            return
        new_min = None
        new_max = None
        context = ui_context if isinstance(ui_context, dict) else None
        if context and context.get("job") and str(context.get("job")) != str(gear.job):
            context = None
        if context is not None:
            try:
                raw_min = context.get("item_il_min")
                raw_max = context.get("item_il_max")
                if raw_min is not None and raw_max is not None:
                    new_min = max(1, int(raw_min))
                    new_max = max(new_min, int(raw_max))
            except Exception:
                new_min = None
                new_max = None
        if new_min is None or new_max is None:
            new_min, new_max = self._default_il_range_for_job(gear.job, items)
        cur_min = self.item_il_min.value()
        cur_max = self.item_il_max.value()
        if new_min == cur_min and new_max == cur_max:
            return
        self.item_il_min.blockSignals(True)
        self.item_il_max.blockSignals(True)
        try:
            self.item_il_min.setValue(new_min)
            self.item_il_max.setValue(new_max)
        finally:
            self.item_il_min.blockSignals(False)
            self.item_il_max.blockSignals(False)
        self.populate_items(gear.job, immediate=immediate)

    def _refresh_slot_table_stats(self, slot: str) -> None:
        table = self.slot_tables.get(slot)
        job = self.current_gearset.job
        if not table or not job:
            return
        speed_stat = 46 if job in SPELL_SPEED_JOBS else 45
        speed_label = "SpS" if job in SPELL_SPEED_JOBS else "SkS"
        extra_stat = 19 if job in {"PLD", "WAR", "DRK", "GNB"} else 6 if job in {"WHM", "SCH", "AST", "SGE"} else None
        extra_label = "TEN" if extra_stat == 19 else "PIE" if extra_stat == 6 else "-"
        table.setHorizontalHeaderLabels(["IL", "装備名", "枠", "CRT", "DHT", "DET", speed_label, extra_label])
        sel = self.current_gearset.items.get(slot)
        selected_id = sel.item_id if sel else None
        table.blockSignals(True)
        table.setUpdatesEnabled(False)
        table.viewport().setUpdatesEnabled(False)
        try:
            for row in range(table.rowCount()):
                cell = table.item(row, 0)
                if not cell:
                    continue
                if self._is_compressed_table_row(table, row):
                    continue
                item_id = cell.data(Qt.UserRole)
                if not item_id:
                    continue
                item = self.items_by_id.get(item_id)
                if not item:
                    continue
                display_sel = sel if selected_id == item_id and sel else None
                effective_item, _synced, _relic_config, _relic_stats = self._effective_item_for_selection(
                    item,
                    display_sel,
                    self.current_gearset.job,
                )
                if selected_id == item_id and sel:
                    stats = self._apply_melds_to_item_stats(item, sel.materia)
                else:
                    stats = effective_item.base_params_hq
                self._set_table_text(table, row, 2, str(effective_item.materia_slots))
                self._set_table_text(table, row, 3, str(stats.get(27, 0)))
                self._set_table_text(table, row, 4, str(stats.get(22, 0)))
                self._set_table_text(table, row, 5, str(stats.get(44, 0)))
                self._set_table_text(table, row, 6, str(stats.get(speed_stat, 0)))
                extra_val = stats.get(extra_stat, 0) if extra_stat else 0
                self._set_table_text(table, row, 7, str(extra_val) if extra_stat else "-")
        finally:
            table.blockSignals(False)
            table.setUpdatesEnabled(True)
            table.viewport().setUpdatesEnabled(True)

    def _refresh_all_slot_displays(self) -> None:
        for slot in self.slot_tables.keys():
            self._refresh_slot_selected_display(slot)

    # ---- Gear data handlers ----
    def _gear_jobs_to_refresh(self) -> List[str]:
        jobs = {str(job) for job in self.items_by_job if job}
        current_job = self.current_gearset.job
        combo_job = self.job_combo.currentData() if hasattr(self, "job_combo") else None
        if current_job:
            jobs.add(str(current_job))
        if combo_job:
            jobs.add(str(combo_job))
        for entry in self.saved_sets or []:
            gearset_data = entry.get("gearset") if isinstance(entry, dict) else None
            saved_job = gearset_data.get("job") if isinstance(gearset_data, dict) else None
            if saved_job:
                jobs.add(str(saved_job))
        return sorted(jobs)

    def on_fetch_gear_data(self) -> None:
        force = self.chk_force_gear.isChecked()
        jobs_to_refresh = self._gear_jobs_to_refresh() if force else []

        def task(progress=None, stop_event=None):
            return self.gear_data_service.fetch(
                force=force,
                jobs_to_refresh=jobs_to_refresh,
                progress=progress,
                stop_event=stop_event,
            )

        self.start_worker(
            task,
            lambda res: self._after_gear_data(res, from_cache=bool(res.get("from_cache"))),
            lock_job_context=True,
        )

    def _after_gear_data(self, result: dict, from_cache: bool = False) -> None:
        self.base_params = result.get("bp", {})
        self.materia_catalog = result.get("materia", {})
        self.foods = [f for f in (result.get("food", []) or []) if optimizer.is_combat_food(f)]
        self.jobs_data = result.get("jobs", {})
        self.item_levels = result.get("levels", {})
        refreshed_items = result.get("items_by_job") or {}
        if isinstance(refreshed_items, dict) and refreshed_items:
            for refreshed_job, items in refreshed_items.items():
                self.items_by_job[str(refreshed_job)] = list(items or [])
            self.items_by_id = {
                item.item_id: item
                for items in self.items_by_job.values()
                for item in items
                if getattr(item, "item_id", None) is not None
            }
        self._rebuild_food_lookup_cache()
        self._job_mods_cache.clear()
        self._relic_model_cache.clear()
        self._display_sync_item_cache.clear()
        self._saved_stats_cache.clear()
        self._raw_stats_cache.clear()
        job = self.current_gearset.job
        if job and job in self.items_by_job:
            self.cap_table = optimizer.build_cap_table(
                self.items_by_job[job],
                self.base_params,
                self.item_levels,
                job,
            )
            if refreshed_items:
                self._init_il_filter_for_job(job, self.items_by_job[job], force=True)
                self.populate_items(job)
        self.refresh_food_combo()
        self._refresh_saved_sets_table()
        QTimer.singleShot(0, self._ensure_initial_job_items_loaded)
        # Delay broad materia prefetch so visible gear icons are fetched first.
        QTimer.singleShot(1500, self._prefetch_materia_icons)
        if from_cache:
            self.progress_label.setText("装備データをキャッシュから読み込みました。")
        else:
            if result.get("forced") and hasattr(self, "chk_force_gear"):
                self.chk_force_gear.setChecked(False)
            refreshed_count = len(refreshed_items) if isinstance(refreshed_items, dict) else 0
            suffix = f"、ジョブ別装備 {refreshed_count}件" if refreshed_count else ""
            QMessageBox.information(
                self,
                "完了",
                f"基礎ステ・マテリア・食事・ジョブ・ItemLevel{suffix}をキャッシュしました。",
            )

    def _ensure_initial_job_items_loaded(self) -> None:
        if self._applying_gearset or self._is_populating:
            QTimer.singleShot(120, self._ensure_initial_job_items_loaded)
            return
        job = self.job_combo.currentData() if hasattr(self, "job_combo") else None
        if not job:
            job = self.current_gearset.job
        if not job:
            return
        if job in self.items_by_job and self.items_by_job.get(job):
            self._init_il_filter_for_job(job, self.items_by_job.get(job, []), force=True)
            self.populate_items(job)
            return
        if self.active_worker:
            QTimer.singleShot(200, self._ensure_initial_job_items_loaded)
            return

        def task(progress=None, stop_event=None):
            return self.xiv_client.fetch_items_for_jobs([job], force=False, progress=progress, stop_event=stop_event)

        self.start_worker(
            task,
            lambda items: self._after_items(job, items),
            silent_if_busy=True,
            lock_job_context=True,
        )

    def on_job_changed(self) -> None:
        if self._applying_gearset:
            return
        job = self.job_combo.currentData()
        self.current_gearset.job = job
        self._current_export_item_ids = {}
        self._refresh_saved_sets_table()
        if not job:
            return
        if job in self.items_by_job:
            if self.base_params and self.item_levels:
                self.cap_table = optimizer.build_cap_table(
                    self.items_by_job.get(job, []),
                    self.base_params,
                    self.item_levels,
                    job,
                )
                self._raw_stats_cache.clear()
            self._init_il_filter_for_job(job, self.items_by_job.get(job, []), force=True)
            self.populate_items(job)
            return

        def task(progress=None, stop_event=None):
            items = self.xiv_client.fetch_items_for_jobs([job], force=False, progress=progress, stop_event=stop_event)
            return items

        self.start_worker(
            task,
            lambda items: self._after_items(job, items),
            lock_job_context=True,
        )

    def _default_il_range_for_job(self, job: str, items: List) -> Tuple[int, int]:
        if not items:
            return 1, 9999
        max_ilvl_all = max((int(it.ilvl or 0) for it in items), default=0)
        weapon_ilvl = max(
            (int(it.ilvl or 0) for it in items if getattr(it, "slot", "") == "weapon"),
            default=max_ilvl_all,
        )
        if max_ilvl_all <= 0 and weapon_ilvl <= 0:
            return 1, 9999
        if self._level_sync_enabled():
            sync_il = int(self._level_sync_il_value() or weapon_ilvl or max_ilvl_all)
            il_min = max(1, sync_il - 10)
            il_max = max(1, max_ilvl_all)
        else:
            # Use overall max IL to avoid capping non-weapon slots when weapons lag behind.
            il_max = max(1, max_ilvl_all)
            il_min = max(1, il_max - 25)
        if il_min > il_max:
            il_min = max(1, il_max - 10)
        return il_min, il_max

    def _init_il_filter_for_job(self, job: str, items: List, force: bool = False) -> None:
        if (not force) and job in self._il_filter_initialized_jobs:
            return
        if not items:
            return
        min_ilvl, max_ilvl = self._default_il_range_for_job(job, items)
        self.item_il_min.blockSignals(True)
        self.item_il_max.blockSignals(True)
        try:
            self.item_il_max.setValue(max_ilvl)
            self.item_il_min.setValue(min_ilvl)
        finally:
            self.item_il_min.blockSignals(False)
            self.item_il_max.blockSignals(False)
        self._il_filter_initialized_jobs.add(job)

    def _after_items(self, job: str, items: List) -> None:
        self.items_by_job[job] = items
        for item in items:
            self.items_by_id[item.item_id] = item
        self._relic_model_cache.clear()
        self._display_sync_item_cache.clear()
        self._saved_stats_cache.clear()
        self._raw_stats_cache.clear()
        current_job = self.job_combo.currentData() if hasattr(self, "job_combo") else self.current_gearset.job
        if current_job != job:
            logger.info("Stored stale job result for %s without applying it to current job %s", job, current_job)
            QTimer.singleShot(0, self._ensure_initial_job_items_loaded)
            return
        self.cap_table = optimizer.build_cap_table(
            items,
            self.base_params,
            self.item_levels,
            job,
        )
        self._init_il_filter_for_job(job, items, force=True)
        self.populate_items(job)
        if self._simdps_baseline_gearset and self._gearset_items_ready(self._simdps_baseline_gearset):
            self._update_simdps_baseline_data()
        if self._pending_gearset and self._pending_gearset.job == job:
            gear = self._pending_gearset
            self._pending_gearset = None
            self._apply_gearset_to_ui(gear)

    def on_il_filter_changed(self) -> None:
        job = self.job_combo.currentData()
        if job:
            self.populate_items(job)
        self._sync_selected_saved_set_ui_context()

    def _compress_slot_items_for_display(
        self,
        choices: List[ItemRecord],
        job: str,
        speed_stat: int,
        extra_stat: Optional[int],
    ) -> List[Dict[str, object]]:
        sorted_items = sorted(
            choices,
            key=lambda i: (-i.ilvl, display_name_with_fallback(getattr(i, "name_ja", None), i.name)),
        )
        if not sorted_items:
            return []

        if not self._level_sync_enabled():
            return [
                {
                    "item_id": int(item.item_id),
                    "member_ids": [int(item.item_id)],
                    "il_text": str(item.ilvl),
                    "name_text": display_name_with_fallback(getattr(item, "name_ja", None), item.name),
                    "icon_url": getattr(item, "icon_url", None),
                    "slots_text": str(item.materia_slots),
                    "crt": int(item.base_params_hq.get(27, 0)),
                    "dht": int(item.base_params_hq.get(22, 0)),
                    "det": int(item.base_params_hq.get(44, 0)),
                    "speed": int(item.base_params_hq.get(speed_stat, 0)),
                    "extra": int(item.base_params_hq.get(extra_stat, 0)) if extra_stat else None,
                }
                for item in sorted_items
            ]

        sync_il = int(self._level_sync_il_value() or 0)
        near_min = max(1, sync_il - 10)
        near_max = sync_il + 10
        forced_high_sync_min_il = SYNC_SUBSTAT_CAP_START_IL.get(sync_il)

        def _synced_display_item(item: ItemRecord) -> ItemRecord:
            cache_key = (int(item.item_id or 0), str(job or ""), sync_il)
            cached = self._display_sync_item_cache.get(cache_key)
            if cached is not None:
                return cached
            effective_item, _synced = self._apply_level_sync_to_item(item, job)
            self._display_sync_item_cache[cache_key] = effective_item
            return effective_item

        def _row_from_item(
            item: ItemRecord,
            effective_item: ItemRecord,
            *,
            il_text: str,
            name_text: str,
            member_ids: List[int],
        ) -> Dict[str, object]:
            normalized_member_ids = self._dedupe_item_ids(member_ids)
            return {
                "item_id": int(item.item_id),
                "member_ids": normalized_member_ids,
                "il_text": il_text,
                "name_text": name_text,
                "icon_url": getattr(item, "icon_url", None),
                "slots_text": str(effective_item.materia_slots),
                "crt": int(effective_item.base_params_hq.get(27, 0)),
                "dht": int(effective_item.base_params_hq.get(22, 0)),
                "det": int(effective_item.base_params_hq.get(44, 0)),
                "speed": int(effective_item.base_params_hq.get(speed_stat, 0)),
                "extra": int(effective_item.base_params_hq.get(extra_stat, 0)) if extra_stat else None,
            }

        rows: List[Dict[str, object]] = []
        high_sync_groups: Dict[Tuple[int, int, int, int, int, str], Dict[str, object]] = {}
        allowed_stats = optimizer.allowed_meld_stats(job)
        cap_stats = set(optimizer.MELDABLE_STATS).intersection(allowed_stats)

        for item in sorted_items:
            ilvl = int(item.ilvl or 0)
            effective_item = _synced_display_item(item)

            # Always show near-sync window rows as-is.
            if near_min <= ilvl <= near_max:
                rows.append(
                    _row_from_item(
                        item,
                        effective_item,
                        il_text=str(ilvl),
                        name_text=display_name_with_fallback(getattr(item, "name_ja", None), item.name),
                        member_ids=[int(item.item_id)],
                    )
                )
                continue

            # Hide below window.
            if ilvl < near_min:
                continue

            # Above window:
            # - only fully-capped substats are kept, and later merged into 1 row
            if ilvl > near_max:
                qualifies_for_high_group = False
                group_min_il = ilvl
                if forced_high_sync_min_il is not None:
                    if ilvl < forced_high_sync_min_il:
                        continue
                    qualifies_for_high_group = True
                    group_min_il = int(forced_high_sync_min_il)
                else:
                    caps = optimizer.compute_item_stat_caps_for_il(
                        item,
                        self.base_params,
                        self.item_levels,
                        job,
                        sync_il,
                    )
                    base_stats = item.base_params_hq or {}
                    present_substats = []
                    for stat_id in cap_stats:
                        val = int(base_stats.get(stat_id, 0))
                        cap_val = caps.get(stat_id)
                        if val > 0 and cap_val is not None:
                            present_substats.append((stat_id, int(cap_val)))
                    if not present_substats:
                        continue
                    fully_capped = all(
                        int(effective_item.base_params_hq.get(stat_id, 0)) >= int(cap_val)
                        for stat_id, cap_val in present_substats
                    )
                    if not fully_capped:
                        continue
                    qualifies_for_high_group = True
                if not qualifies_for_high_group:
                    continue
                group_key = (
                    int(effective_item.base_params_hq.get(27, 0)),
                    int(effective_item.base_params_hq.get(22, 0)),
                    int(effective_item.base_params_hq.get(44, 0)),
                    int(effective_item.base_params_hq.get(speed_stat, 0)),
                    int(effective_item.base_params_hq.get(extra_stat, 0)) if extra_stat else 0,
                    self._special_weapon_group_key(item, job),
                )
                group = high_sync_groups.get(group_key)
                if group is None:
                    high_sync_groups[group_key] = {
                        "rep": item,
                        "effective": effective_item,
                        "member_ids": [int(item.item_id)],
                        "min_il": int(group_min_il),
                    }
                else:
                    item_id = int(item.item_id)
                    if item_id not in group["member_ids"]:
                        group["member_ids"].append(item_id)
                    group["min_il"] = min(int(group["min_il"]), int(group_min_il))

        if high_sync_groups:
            high_rows: List[Dict[str, object]] = []
            groups = list(high_sync_groups.values())
            groups.sort(
                key=lambda g: (
                    -int(g["min_il"]),
                    display_name_with_fallback(
                        getattr(g["rep"], "name_ja", None),
                        g["rep"].name,
                    ),
                )
            )
            for group in groups:
                rep = group["rep"]
                effective_rep = group["effective"]
                member_ids = self._dedupe_item_ids(group["member_ids"])
                min_il = int(group["min_il"])
                special_kind = (
                    "PW"
                    if self._is_phantom_weapon_item(rep)
                    else self._special_weapon_kind_text(self._relic_model_for_item(rep, job))
                )
                if len(member_ids) <= 1:
                    name_text = display_name_with_fallback(getattr(rep, "name_ja", None), rep.name)
                else:
                    if special_kind in {"RW", "MW"}:
                        name_text = f"IL{min_il}以上{special_kind} ({len(member_ids)}件)"
                    else:
                        name_text = f"IL{min_il}以上の装備 ({len(member_ids)}件)"
                high_rows.append(
                    _row_from_item(
                        rep,
                        effective_rep,
                        il_text=f"{min_il}+",
                        name_text=name_text,
                        member_ids=member_ids,
                    )
                )
            return high_rows + rows
        return rows

    def populate_items(self, job: str, immediate: bool = False) -> None:
        il_min = self.item_il_min.value()
        il_max = self.item_il_max.value()
        key = (
            job,
            il_min,
            il_max,
            bool(self._level_sync_enabled()),
            int(self._level_sync_il_value() or 0),
            int(self._selected_sync_level_value() or 0),
        )
        if self._is_populating:
            self._pending_populate = key
            return
        if self._last_populate_key == key:
            # If tables already populated, avoid full redraw.
            if all(table.rowCount() > 1 for table in self.slot_tables.values()):
                return
        self._is_populating = True
        self._populate_immediate_mode = bool(immediate)
        self._auto_calc_suspended += 1
        self._pending_populate = None
        self._last_populate_key = key
        items = self.items_by_job.get(job, [])
        self._last_populated_job = job
        by_slot: Dict[str, List] = {s: [] for s in ["weapon", "offhand", "head", "body", "hands", "legs", "feet", "earrings", "necklace", "bracelet", "ring"]}
        for item in items:
            if item.ilvl < il_min or item.ilvl > il_max:
                continue
            slot = item.slot
            if slot == "ring":
                by_slot["ring"].append(item)
            elif slot in by_slot:
                by_slot[slot].append(item)
        speed_stat = 46 if job in SPELL_SPEED_JOBS else 45
        speed_label = "SpS" if job in SPELL_SPEED_JOBS else "SkS"
        extra_stat = 19 if job in {"PLD", "WAR", "DRK", "GNB"} else 6 if job in {"WHM", "SCH", "AST", "SGE"} else None
        extra_label = "TEN" if extra_stat == 19 else "PIE" if extra_stat == 6 else "-"

        self._populate_queue = []
        display_rows_by_match_slot: Dict[str, List[Dict[str, object]]] = {}
        visible_item_icon_urls: List[str] = []
        try:
            for slot, table in self.slot_tables.items():
                match_slot = "ring" if slot.startswith("ring") else slot
                choices = by_slot.get(match_slot, [])
                table.blockSignals(True)
                table.setUpdatesEnabled(False)
                table.viewport().setUpdatesEnabled(False)
                row_map: Dict[int, int] = {}
                table.setColumnCount(8)
                table.setHorizontalHeaderLabels(["IL", "装備名", "枠", "CRT", "DHT", "DET", speed_label, extra_label])
                if match_slot in display_rows_by_match_slot:
                    display_rows = display_rows_by_match_slot[match_slot]
                else:
                    try:
                        display_rows = self._compress_slot_items_for_display(choices, job, speed_stat, extra_stat)
                    except Exception:
                        logger.exception("Display compression failed for slot %s", slot)
                        display_rows = []
                        for item in sorted(
                            choices,
                            key=lambda i: (-i.ilvl, display_name_with_fallback(getattr(i, "name_ja", None), i.name)),
                        ):
                            effective_item, _synced = self._apply_level_sync_to_item(item, job)
                            display_rows.append(
                                {
                                    "item_id": int(item.item_id),
                                    "member_ids": [int(item.item_id)],
                                    "il_text": str(item.ilvl),
                                    "name_text": display_name_with_fallback(getattr(item, "name_ja", None), item.name),
                                    "icon_url": getattr(item, "icon_url", None),
                                    "slots_text": str(effective_item.materia_slots),
                                    "crt": int(effective_item.base_params_hq.get(27, 0)),
                                    "dht": int(effective_item.base_params_hq.get(22, 0)),
                                    "det": int(effective_item.base_params_hq.get(44, 0)),
                                    "speed": int(effective_item.base_params_hq.get(speed_stat, 0)),
                                    "extra": int(effective_item.base_params_hq.get(extra_stat, 0)) if extra_stat else None,
                                }
                            )
                    display_rows_by_match_slot[match_slot] = display_rows
                table.setRowCount(len(display_rows) + 1)
                if self._icon_display_enabled():
                    for row_data in display_rows:
                        url = row_data.get("icon_url")
                        if url:
                            visible_item_icon_urls.append(str(url))
                self._set_table_item(table, 0, 0, "-", None)
                self._set_table_item(table, 0, 1, "-- 未選択 --", None)
                self._set_table_item(table, 0, 2, "-", None)
                self._set_table_item(table, 0, 3, "-", None)
                self._set_table_item(table, 0, 4, "-", None)
                self._set_table_item(table, 0, 5, "-", None)
                self._set_table_item(table, 0, 6, "-", None)
                self._set_table_item(table, 0, 7, "-", None)
                self.slot_row_index[slot] = row_map
                self._populate_queue.append(
                    {
                        "slot": slot,
                        "table": table,
                        "items": display_rows,
                        "row_map": row_map,
                        "speed_stat": speed_stat,
                        "extra_stat": extra_stat,
                        "chunk": 120,
                        "cursor": 0,
                    }
                )
        except Exception:
            self._is_populating = False
            if self._auto_calc_suspended > 0:
                self._auto_calc_suspended -= 1
            for table in self.slot_tables.values():
                table.blockSignals(False)
                table.setUpdatesEnabled(True)
                table.viewport().setUpdatesEnabled(True)
            raise
        if self._icon_display_enabled():
            if self._item_icon_prefetch_visible_only():
                QTimer.singleShot(0, lambda urls=visible_item_icon_urls: self._prefetch_item_icon_urls(urls))
            else:
                QTimer.singleShot(0, lambda rows=items: self._prefetch_item_icons(rows))
        if self._populate_immediate_mode:
            while self._populate_queue:
                self._populate_next_chunk()
        else:
            QTimer.singleShot(0, self._populate_next_chunk)

    def _populate_next_chunk(self) -> None:
        if not self._populate_queue:
            self._is_populating = False
            self._populate_immediate_mode = False
            if self._auto_calc_suspended > 0:
                self._auto_calc_suspended -= 1
            self._resize_populated_tables()
            for slot in self.slot_tables.keys():
                self._refresh_slot_selected_display(slot)
            self.progress_label.setText(
                f"{self.current_gearset.job} 用の装備一覧を読み込みました"
                if self.current_gearset.job
                else "装備一覧を読み込みました"
            )
            if self._pending_score_after_populate:
                self._pending_score_after_populate = False
                self._schedule_auto_score_update()
            if self._pending_populate:
                pending = self._pending_populate
                job = pending[0] if len(pending) >= 1 else None
                il_min = int(pending[1]) if len(pending) >= 3 else self.item_il_min.value()
                il_max = int(pending[2]) if len(pending) >= 3 else self.item_il_max.value()
                self.item_il_min.blockSignals(True)
                self.item_il_max.blockSignals(True)
                try:
                    self.item_il_min.setValue(il_min)
                    self.item_il_max.setValue(il_max)
                finally:
                    self.item_il_min.blockSignals(False)
                    self.item_il_max.blockSignals(False)
                self._pending_populate = None
                if job:
                    self.populate_items(str(job), immediate=self._populate_immediate_mode)
            return

        entry = self._populate_queue[0]
        table = entry["table"]
        items = entry["items"]
        row_map = entry["row_map"]
        extra_stat = entry["extra_stat"]
        cursor = entry["cursor"]
        end = min(cursor + entry["chunk"], len(items))
        for idx in range(cursor, end):
            row = idx + 1
            row_data = items[idx]
            item_id = int(row_data["item_id"])
            member_ids = [int(v) for v in row_data.get("member_ids", [])]
            group_size = len(member_ids)
            self._set_table_item(table, row, 0, str(row_data["il_text"]), item_id)
            self._set_table_item(
                table,
                row,
                1,
                str(row_data["name_text"]),
                item_id,
                icon_url=row_data.get("icon_url"),
            )
            self._set_table_item(table, row, 2, str(row_data["slots_text"]), item_id)
            self._set_table_item(table, row, 3, str(row_data["crt"]), item_id)
            self._set_table_item(table, row, 4, str(row_data["dht"]), item_id)
            self._set_table_item(table, row, 5, str(row_data["det"]), item_id)
            self._set_table_item(table, row, 6, str(row_data["speed"]), item_id)
            extra_val = row_data["extra"] if extra_stat else None
            self._set_table_item(table, row, 7, str(extra_val) if extra_stat else "-", item_id)
            for col in range(8):
                cell = table.item(row, col)
                if cell:
                    cell.setData(Qt.UserRole + 1, group_size)
                    cell.setData(Qt.UserRole + 3, member_ids)
            excluded_ids = self._slot_excluded_item_id_set(entry["slot"])
            row_excluded = bool(member_ids) and all(mapped_id in excluded_ids for mapped_id in member_ids)
            self._set_row_excluded_style(table, row, row_excluded)
            for mapped_id in member_ids:
                row_map[int(mapped_id)] = row
        entry["cursor"] = end
        if end >= len(items):
            slot = entry["slot"]
            if slot not in self._tables_to_resize:
                self._tables_to_resize.append(slot)
            current_sel = self.current_gearset.items.get(slot)
            if current_sel and current_sel.item_id:
                self._select_table_row(table, current_sel.item_id)
                self._last_selected_items[slot] = current_sel.item_id
            else:
                self._select_table_row(table, None)
                self._last_selected_items[slot] = None
            self._refresh_slot_exclusion_visuals(slot)
            table.blockSignals(False)
            table.setUpdatesEnabled(True)
            table.viewport().setUpdatesEnabled(True)
            self._populate_queue.pop(0)
            if self._populate_immediate_mode and not self._populate_queue:
                self._populate_next_chunk()
                return
        if not self._populate_immediate_mode:
            QTimer.singleShot(0, self._populate_next_chunk)

    def _resize_populated_tables(self) -> None:
        if not self._tables_to_resize:
            return
        for slot in list(self._tables_to_resize):
            table = self.slot_tables.get(slot)
            if not table:
                continue
            if not self._table_sized.get(slot):
                table.resizeColumnsToContents()
                self._table_sized[slot] = True
        self._tables_to_resize.clear()

    def _set_table_item(
        self,
        table: QTableWidget,
        row: int,
        col: int,
        text: str,
        item_id: Optional[int],
        icon_url: Optional[str] = None,
    ) -> None:
        item = QTableWidgetItem(text)
        item.setData(Qt.UserRole, item_id)
        if self._icon_display_enabled() and icon_url and col == 1:
            item.setData(Qt.UserRole + 2, icon_url)
            icon = self._get_materia_icon(icon_url)
            if icon:
                item.setIcon(icon)
            else:
                self._pending_item_icon_cells.setdefault(icon_url, []).append((table, row, col))
        table.setItem(row, col, item)

    def _is_compressed_table_row(self, table: QTableWidget, row: int) -> bool:
        cell = table.item(row, 0)
        if not cell:
            return False
        try:
            return int(cell.data(Qt.UserRole + 1) or 0) > 1
        except Exception:
            return False

    def _compressed_row_member_ids(self, table: QTableWidget, row: int) -> List[int]:
        cell = table.item(row, 0)
        if not cell:
            return []
        raw_ids = cell.data(Qt.UserRole + 3)
        if not isinstance(raw_ids, list):
            return []
        return self._dedupe_item_ids(raw_ids)

    def _grouped_slot_items(self, member_ids: List[int]) -> List[ItemRecord]:
        rows: List[ItemRecord] = []
        seen: set = set()
        for item_id in member_ids:
            if item_id in seen:
                continue
            seen.add(item_id)
            item = self.items_by_id.get(int(item_id))
            if item:
                rows.append(item)
        rows.sort(
            key=lambda item: (
                -int(item.ilvl or 0),
                display_name_with_fallback(getattr(item, "name_ja", None), item.name),
            )
        )
        return rows

    def _apply_grouped_slot_item_choice(self, slot: str, item_id: int) -> bool:
        try:
            resolved_item_id = int(item_id or 0)
        except Exception:
            return False
        if resolved_item_id <= 0:
            return False
        item = self.items_by_id.get(resolved_item_id)
        if not item:
            return False
        duplicate_slot = self._duplicate_unique_ring_slot(slot, resolved_item_id)
        if duplicate_slot is not None:
            other_label = SLOT_LABELS.get(duplicate_slot, duplicate_slot)
            QMessageBox.information(
                self,
                "ユニーク装備",
                f"この装備は unique のため、{other_label} と重複して設定できません。",
            )
            return False
        self._clear_optimal_variant_tabs()
        sel = self.current_gearset.items.get(slot) or ItemSelection()
        if int(sel.item_id or 0) == resolved_item_id:
            self._clear_export_item_override(slot)
            self._sync_selected_saved_set_ui_context()
            return True
        sel.item_id = resolved_item_id
        sel.materia = []
        sel.relic_stats = {}
        self.current_gearset.items[slot] = sel
        self._clear_export_item_override(slot)
        table = self.slot_tables.get(slot)
        if table is not None:
            self._select_table_row(table, resolved_item_id)
        self._raw_stats_cache.clear()
        self._refresh_slot_selected_display(slot)
        self._persist_current_gearset_to_selected_saved_set()
        self._sync_selected_saved_set_ui_context()
        self._schedule_auto_score_update()
        self.progress_label.setText(
            f"{SLOT_LABELS.get(slot, slot)} の装備を更新しました。"
        )
        return True

    def _show_grouped_slot_items_dialog(self, slot: str, member_ids: List[int]) -> None:
        items = self._grouped_slot_items(member_ids)
        if not items:
            return
        title = SLOT_LABELS.get(slot, slot)
        dialog = QDialog(self)
        dialog.setWindowTitle(f"{title} のまとめ装備一覧")
        dialog.resize(560, min(680, 180 + len(items) * 28))

        layout = QVBoxLayout(dialog)
        info_label = QLabel(
            f"この行には {len(items)} 件の装備が含まれます。表示中のサブステと枠は、レベルシンク後の共通値です。"
        )
        info_label.setWordWrap(True)
        layout.addWidget(info_label)

        item_list = QListWidget(dialog)
        if hasattr(item_list, "setUniformItemSizes"):
            item_list.setUniformItemSizes(True)
        item_list.setSelectionMode(QAbstractItemView.SingleSelection)
        item_list.setContextMenuPolicy(Qt.CustomContextMenu)
        item_list.customContextMenuRequested.connect(
            lambda pos, s=slot, lst=item_list: self._on_grouped_items_context_menu(s, lst, pos)
        )
        excluded_ids = self._slot_excluded_item_id_set(slot)
        current_item_id = int(getattr((self.current_gearset.items or {}).get(slot), "item_id", 0) or 0)
        current_row = -1
        for item in items:
            label = f"[IL{int(item.ilvl or 0)}] {display_name_with_fallback(getattr(item, 'name_ja', None), item.name)}"
            list_item = QListWidgetItem(label)
            list_item.setData(Qt.UserRole, int(item.item_id))
            icon = self._get_materia_icon(getattr(item, "icon_url", None))
            if icon:
                list_item.setIcon(icon)
            self._set_grouped_list_item_excluded_style(list_item, int(item.item_id) in excluded_ids)
            item_list.addItem(list_item)
            if current_row < 0 and int(item.item_id) == current_item_id:
                current_row = item_list.count() - 1
        if current_row < 0 and item_list.count() > 0:
            current_row = 0
        if current_row >= 0:
            item_list.setCurrentRow(current_row)
        item_list.itemDoubleClicked.connect(
            lambda list_item, s=slot, dlg=dialog: (
                self._apply_grouped_slot_item_choice(s, int(list_item.data(Qt.UserRole) or 0))
                and dlg.accept()
            )
        )
        layout.addWidget(item_list)

        buttons = QDialogButtonBox(QDialogButtonBox.Close, parent=dialog)
        btn_use = buttons.addButton("この装備を使用", QDialogButtonBox.ActionRole)
        btn_use.clicked.connect(
            lambda _checked=False, s=slot, lst=item_list, dlg=dialog: (
                self._apply_grouped_slot_item_choice(
                    s,
                    int((lst.currentItem().data(Qt.UserRole) if lst.currentItem() else 0) or 0),
                )
                and dlg.accept()
            )
        )
        buttons.rejected.connect(dialog.reject)
        buttons.accepted.connect(dialog.accept)
        layout.addWidget(buttons)
        dialog.exec()

    def _show_excluded_slot_items_dialog(self, slot: str) -> None:
        excluded_ids = self._slot_excluded_item_ids(slot)
        if not excluded_ids:
            return
        title = SLOT_LABELS.get(slot, slot)
        dialog = QDialog(self)
        dialog.setWindowTitle(f"{title} の除外装備一覧")
        dialog.resize(560, min(680, 180 + len(excluded_ids) * 28))

        layout = QVBoxLayout(dialog)
        info_label = QLabel(
            "除外を解除する装備を右クリックしてください。"
        )
        info_label.setWordWrap(True)
        layout.addWidget(info_label)

        item_list = QListWidget(dialog)
        if hasattr(item_list, "setUniformItemSizes"):
            item_list.setUniformItemSizes(True)
        item_list.setSelectionMode(QAbstractItemView.SingleSelection)
        item_list.setContextMenuPolicy(Qt.CustomContextMenu)
        item_list.customContextMenuRequested.connect(
            lambda pos, s=slot, lst=item_list: self._on_excluded_items_context_menu(
                s,
                lst,
                pos,
            )
        )
        for item_id in excluded_ids:
            item = self.items_by_id.get(int(item_id))
            if item is None:
                label = f"装備ID {int(item_id)}（装備データ未読込）"
            else:
                item_name = display_name_with_fallback(
                    getattr(item, "name_ja", None),
                    item.name,
                )
                label = f"[IL{int(item.ilvl or 0)}] {item_name}"
            list_item = QListWidgetItem(label)
            list_item.setData(Qt.UserRole, int(item_id))
            item_list.addItem(list_item)
        if item_list.count() > 0:
            item_list.setCurrentRow(0)
        layout.addWidget(item_list)

        buttons = QDialogButtonBox(QDialogButtonBox.Close, parent=dialog)
        buttons.rejected.connect(dialog.reject)
        buttons.accepted.connect(dialog.accept)
        layout.addWidget(buttons)
        dialog.exec()

    def _on_excluded_items_context_menu(
        self,
        slot: str,
        item_list: QListWidget,
        pos,
    ) -> None:
        item = item_list.itemAt(pos)
        if not item:
            return
        try:
            item_id = int(item.data(Qt.UserRole) or 0)
        except Exception:
            return
        if item_id <= 0 or item_id not in self._slot_excluded_item_id_set(slot):
            return
        self._toggle_slot_item_exclusion(slot, [item_id], exclude=False)
        row = item_list.row(item)
        if row >= 0:
            item_list.takeItem(row)

    def _set_grouped_list_item_excluded_style(self, list_item: QListWidgetItem, excluded: bool) -> None:
        font = list_item.font()
        if font.strikeOut() != excluded:
            font.setStrikeOut(excluded)
            list_item.setFont(font)

    def _on_grouped_items_context_menu(self, slot: str, item_list: QListWidget, pos) -> None:
        item = item_list.itemAt(pos)
        if not item:
            return
        raw_item_id = item.data(Qt.UserRole)
        try:
            item_id = int(raw_item_id or 0)
        except Exception:
            return
        if item_id <= 0:
            return
        menu = QMenu(item_list)
        action_use = menu.addAction("この装備を使用")
        action_search = menu.addAction("FF14公式DBで検索")
        is_excluded = item_id in self._slot_excluded_item_id_set(slot)
        action_exclude = menu.addAction("検索時除外を解除" if is_excluded else "検索時除外")
        chosen = menu.exec(item_list.viewport().mapToGlobal(pos))
        if chosen is action_use:
            if self._apply_grouped_slot_item_choice(slot, item_id):
                item_list.setCurrentItem(item)
        elif chosen is action_search:
            self._open_official_db_search_for_item(item_id)
        elif chosen is action_exclude:
            self._toggle_slot_item_exclusion(slot, [item_id], exclude=not is_excluded)
            self._set_grouped_list_item_excluded_style(item, not is_excluded)

    def _table_min_height(self, table: QTableWidget, rows: int) -> int:
        header_h = table.horizontalHeader().height()
        if header_h <= 0:
            header_h = table.fontMetrics().height() + 12
        row_h = table.verticalHeader().defaultSectionSize()
        if row_h <= 0:
            row_h = table.fontMetrics().height() + 10
        frame = table.frameWidth() * 2
        return int(header_h + row_h * rows + frame + 6)

    def _set_table_text(self, table: QTableWidget, row: int, col: int, text: str) -> None:
        item = table.item(row, col)
        if item:
            item.setText(text)
        else:
            table.setItem(row, col, QTableWidgetItem(text))

    def _table_row_item_id(self, table: QTableWidget, row: int) -> Optional[int]:
        cell = table.item(row, 0)
        if not cell:
            return None
        raw_item_id = cell.data(Qt.UserRole)
        try:
            item_id = int(raw_item_id or 0)
        except Exception:
            return None
        return item_id or None

    def _open_official_db_search_for_item(self, item_id: int) -> None:
        item = self.items_by_id.get(int(item_id))
        if not item:
            QMessageBox.warning(self, "検索不可", "装備情報を取得できませんでした。")
            return
        item_name = display_name_with_fallback(getattr(item, "name_ja", None), item.name)
        if not item_name:
            QMessageBox.warning(self, "検索不可", "装備名を取得できませんでした。")
            return
        search_url = (
            "https://jp.finalfantasyxiv.com/lodestone/playguide/db/search/?q="
            f"{quote_plus(item_name)}"
        )
        if not QDesktopServices.openUrl(QUrl(search_url)):
            QMessageBox.warning(self, "起動失敗", "ブラウザで公式DBを開けませんでした。")

    def _level_sync_enabled(self) -> bool:
        return bool(hasattr(self, "chk_level_sync") and self.chk_level_sync.isChecked())

    def _selected_sync_level_value(self) -> int:
        combo = getattr(self, "level_sync_level_combo", None)
        if combo is None:
            return int(xivmath.CURRENT_MAX_LEVEL)
        value = combo.currentData()
        if value is None:
            value = combo.currentText()
        return int(xivmath.normalize_supported_level(value))

    def _effective_calc_level(self) -> int:
        if not self._level_sync_enabled():
            return int(xivmath.CURRENT_MAX_LEVEL)
        return self._selected_sync_level_value()

    def _level_sync_il_value(self) -> Optional[int]:
        if not self._level_sync_enabled():
            return None
        if not hasattr(self, "level_sync_il"):
            return None
        return int(self.level_sync_il.value())

    def on_level_sync_changed(self, *_args) -> None:
        enabled = self._level_sync_enabled()
        if hasattr(self, "level_sync_il"):
            self.level_sync_il.setEnabled(enabled)
        if hasattr(self, "level_sync_level_combo"):
            self.level_sync_level_combo.setEnabled(enabled)
        if hasattr(self, "current_gearset") and self.current_gearset is not None:
            self.current_gearset.level = self._effective_calc_level()
        job = self.job_combo.currentData() if hasattr(self, "job_combo") else None
        if job and job in self.items_by_job:
            self._init_il_filter_for_job(job, self.items_by_job.get(job, []), force=True)
            self.populate_items(job)
        self._sync_selected_saved_set_ui_context()
        self.on_save_auth(silent=True)
        self._refresh_all_slot_displays()
        self._schedule_auto_score_update()

    def _apply_level_sync_to_item(
        self,
        item: ItemRecord,
        job: Optional[str],
        sync_il_override: object = _USE_CURRENT_SYNC,
    ) -> Tuple[ItemRecord, bool]:
        sync_il = (
            self._level_sync_il_value()
            if sync_il_override is _USE_CURRENT_SYNC
            else sync_il_override
        )
        if not sync_il or not job:
            return item, False
        if not item or int(item.ilvl or 0) <= sync_il:
            return item, False
        ilvl_row = self.item_levels.get(sync_il) or {}
        caps = optimizer.compute_item_stat_caps_for_il(
            item,
            self.base_params,
            self.item_levels,
            job,
            sync_il,
        )
        synced_stats = dict(item.base_params_hq or {})
        for stat_id, cap_val in caps.items():
            cur_val = synced_stats.get(stat_id)
            if cur_val is None:
                continue
            synced_stats[stat_id] = min(int(cur_val), int(cap_val))

        damage_phys = item.damage_phys
        damage_mag = item.damage_mag
        delay_ms = item.delay_ms
        sync_phys = ilvl_row.get("physicalDamage")
        sync_mag = ilvl_row.get("magicalDamage")
        sync_delay = ilvl_row.get("delay")
        if isinstance(sync_phys, (int, float)) and damage_phys is not None:
            damage_phys = min(int(damage_phys), int(sync_phys))
        if isinstance(sync_mag, (int, float)) and damage_mag is not None:
            damage_mag = min(int(damage_mag), int(sync_mag))
        if isinstance(sync_delay, (int, float)) and delay_ms is not None and int(sync_delay) > 0:
            delay_ms = min(int(delay_ms), int(sync_delay))

        synced_item = ItemRecord(
            item_id=item.item_id,
            name=item.name,
            name_ja=item.name_ja,
            jobs=list(item.jobs),
            ilvl=min(int(item.ilvl), int(sync_il)),
            slot=item.slot,
            materia_slots=0,
            overmeld=False,
            base_params=dict(synced_stats),
            base_params_hq=dict(synced_stats),
            damage_phys=damage_phys,
            damage_mag=damage_mag,
            delay_ms=delay_ms,
            occ_slot=item.occ_slot,
            unique=item.unique,
            icon_url=item.icon_url,
        )
        return synced_item, True

    def _resolved_selected_items(
        self,
        gearset: Gearset,
        sync_il_override: object = _USE_CURRENT_SYNC,
    ) -> Tuple[Dict[str, object], set]:
        selected_items: Dict[str, object] = {}
        no_meld_slots: set = set()
        seen_unique: set = set()
        for slot, sel in gearset.items.items():
            if not sel or not sel.item_id:
                continue
            item = self.items_by_id.get(sel.item_id)
            if not item:
                continue
            item_id = int(getattr(item, "item_id", 0) or 0)
            if bool(getattr(item, "unique", False)) and item_id in seen_unique:
                continue
            if bool(getattr(item, "unique", False)):
                seen_unique.add(item_id)
            effective_item, synced, _relic_config, _relic_stats = self._effective_item_for_selection(
                item,
                sel,
                gearset.job,
                sync_il_override=sync_il_override,
            )
            selected_items[slot] = effective_item
            if synced:
                no_meld_slots.add(slot)
        return selected_items, no_meld_slots

    def _select_table_row(self, table: QTableWidget, item_id: Optional[int]) -> None:
        if item_id is None:
            if table.rowCount() > 0:
                if table.currentRow() == 0 and self._is_table_row_visible(table, 0):
                    return
                table.setCurrentCell(0, 0)
                # Keep the placeholder row selected, but reveal the first real option
                # so wide IL ranges do not look empty.
                if table.rowCount() > 1:
                    first_item = table.item(1, 0)
                    if first_item is not None and not self._is_table_row_visible(table, 1):
                        table.scrollToItem(first_item, QAbstractItemView.PositionAtTop)
            return
        # fast path via row index
        for slot, slot_table in self.slot_tables.items():
            if slot_table is table:
                row_map = self.slot_row_index.get(slot, {})
                row = row_map.get(item_id)
                if row is not None:
                    current_row = table.currentRow()
                    if current_row == row:
                        current_cell = table.item(row, 0)
                        if current_cell is not None and current_cell.data(Qt.UserRole) == item_id:
                            return
                    needs_scroll = not self._is_table_row_visible(table, row)
                    table.setCurrentCell(row, 0)
                    target = table.item(row, 0)
                    if target is not None and needs_scroll:
                        table.scrollToItem(target, QAbstractItemView.PositionAtCenter)
                    return
                break
        for row in range(table.rowCount()):
            cell = table.item(row, 0)
            if cell and cell.data(Qt.UserRole) == item_id:
                if table.currentRow() == row:
                    return
                needs_scroll = not self._is_table_row_visible(table, row)
                table.setCurrentCell(row, 0)
                if needs_scroll:
                    table.scrollToItem(cell, QAbstractItemView.PositionAtCenter)
                return

    def _is_table_row_visible(self, table: QTableWidget, row: int) -> bool:
        if row < 0 or row >= table.rowCount():
            return False
        model = table.model()
        if model is None:
            return False
        index = model.index(row, 0)
        if not index.isValid():
            return False
        rect = table.visualRect(index)
        if not rect.isValid() or rect.isEmpty():
            return False
        return table.viewport().rect().intersects(rect)

    def _table_has_item(self, table: QTableWidget, item_id: Optional[int]) -> bool:
        if item_id is None:
            return False
        for slot, slot_table in self.slot_tables.items():
            if slot_table is table:
                row_map = self.slot_row_index.get(slot, {})
                if item_id in row_map:
                    return True
                break
        for row in range(table.rowCount()):
            cell = table.item(row, 0)
            if cell and cell.data(Qt.UserRole) == item_id:
                return True
        return False

    def _resolve_optimize_food_candidates(self) -> Tuple[List[object], Optional[object]]:
        food_id = self.current_gearset.food_id
        if bool(getattr(self.current_gearset, "food_simulation", False)):
            il_min = self.food_il_min.value()
            il_max = self.food_il_max.value()

            def in_range(food) -> bool:
                if food.level_item is None:
                    return True
                return il_min <= food.level_item <= il_max

            foods = optimizer.highest_item_level_combat_foods(
                [f for f in self.foods if in_range(f)]
            )
            relevant_stats = set(optimizer.allowed_meld_stats(self.current_gearset.job or ""))
            main_stat_id = optimizer.MAIN_STAT_BY_JOB.get(self.current_gearset.job or "")
            if main_stat_id is not None:
                relevant_stats.add(main_stat_id)
            relevant_stats.add(3)  # VIT/HPも同一以上の食事だけを優越候補とする
            foods = optimizer.non_dominated_combat_foods(
                foods,
                relevant_stats,
            )
            foods.sort(key=lambda f: (-(f.level_item or 0), f.food_id or 0))
        elif food_id:
            resolved_food = self._find_food_by_id(food_id)
            foods = [resolved_food] if resolved_food and optimizer.is_combat_food(resolved_food) else []
        else:
            foods = [None]
        food_for_baseline = self._find_food_by_id(food_id)
        return foods, food_for_baseline

    def _filtered_items_by_slot(self, job: str) -> Dict[str, List[ItemRecord]]:
        il_min = self.item_il_min.value()
        il_max = self.item_il_max.value()
        by_slot: Dict[str, List[ItemRecord]] = {
            "weapon": [],
            "offhand": [],
            "head": [],
            "body": [],
            "hands": [],
            "legs": [],
            "feet": [],
            "earrings": [],
            "necklace": [],
            "bracelet": [],
            "ring": [],
        }
        for item in self.items_by_job.get(job, []):
            ilvl = int(getattr(item, "ilvl", 0) or 0)
            if ilvl < il_min or ilvl > il_max:
                continue
            slot = getattr(item, "slot", "")
            if slot in by_slot:
                by_slot[slot].append(item)
        return by_slot

    def _gear_search_item_signature(self, item: ItemRecord) -> Tuple[object, ...]:
        stat_entries = tuple(
            sorted(
                (int(stat_id), int(value))
                for stat_id, value in (item.base_params_hq or {}).items()
                if int(value or 0) != 0
            )
        )
        signature: List[object] = [
            str(item.slot),
            int(item.materia_slots or 0),
            int(item.damage_phys or 0),
            int(item.damage_mag or 0),
            int(item.delay_ms or 0),
            bool(item.unique),
            stat_entries,
        ]
        if item.slot == "ring" and bool(item.unique):
            signature.append(int(item.item_id))
        return tuple(signature)

    def _prefer_gear_search_candidate(
        self,
        candidate: ItemRecord,
        current_best: ItemRecord,
        preferred_ids: set,
    ) -> bool:
        candidate_pref = int(candidate.item_id) in preferred_ids
        current_pref = int(current_best.item_id) in preferred_ids
        if candidate_pref != current_pref:
            return candidate_pref
        candidate_key = (
            int(candidate.ilvl or 0),
            optimizer.total_meld_slots_for_item(candidate),
            -int(candidate.item_id),
        )
        current_key = (
            int(current_best.ilvl or 0),
            optimizer.total_meld_slots_for_item(current_best),
            -int(current_best.item_id),
        )
        return candidate_key > current_key

    def _build_gear_search_candidates(self, job: str) -> Tuple[Dict[str, List[ItemRecord]], List[str]]:
        filtered = self._filtered_items_by_slot(job)
        speed_stat = 46 if job in SPELL_SPEED_JOBS else 45
        extra_stat = 19 if job in {"PLD", "WAR", "DRK", "GNB"} else 6 if job in {"WHM", "SCH", "AST", "SGE"} else None
        preferred_ids: set = set()

        def add_preferred_ids(gear: Optional[Gearset]) -> None:
            if not gear or gear.job != job:
                return
            for sel in (gear.items or {}).values():
                item_id = int(getattr(sel, "item_id", 0) or 0) if sel else 0
                if item_id > 0:
                    preferred_ids.add(item_id)

        add_preferred_ids(self.current_gearset)
        add_preferred_ids(self._simdps_baseline_gearset)
        for entry in self.saved_sets:
            if not isinstance(entry, dict):
                continue
            gear_data = entry.get("gearset")
            if not isinstance(gear_data, dict):
                continue
            try:
                add_preferred_ids(Gearset.from_dict(gear_data))
            except Exception:
                continue

        relic_profile_cache: Dict[int, Tuple[Dict[int, int], Dict[int, int]]] = {}

        def resistance_effective_profile(
            raw_item: ItemRecord,
            relic_config: Optional[Dict[str, object]],
        ) -> Tuple[Dict[int, int], Dict[int, int]]:
            item_id = int(raw_item.item_id)
            cached = relic_profile_cache.get(item_id)
            if cached is not None:
                return cached
            if str((relic_config or {}).get("kind") or "") != "resistance":
                relic_profile_cache[item_id] = ({}, {})
                return relic_profile_cache[item_id]
            base_effective, _synced, _config, _stats = self._effective_item_for_selection(
                raw_item,
                None,
                job,
            )
            base_stats = dict(base_effective.base_params_hq or {})
            effective_caps: Dict[int, int] = {}
            total_cap = int((relic_config or {}).get("total_cap", 0) or 0)
            stat_caps = dict((relic_config or {}).get("stat_caps", {}) or {})
            for stat_id in list((relic_config or {}).get("allowed_stats", []) or []):
                stat_id = int(stat_id)
                requested = min(total_cap, int(stat_caps.get(stat_id, 0) or 0))
                if requested <= 0:
                    continue
                capped_effective, _synced, _config, _stats = self._effective_item_for_selection(
                    raw_item,
                    ItemSelection(item_id=item_id, relic_stats={stat_id: requested}),
                    job,
                )
                effective_caps[stat_id] = max(
                    0,
                    int(capped_effective.base_params_hq.get(stat_id, 0) or 0)
                    - int(base_stats.get(stat_id, 0) or 0),
                )
            relic_profile_cache[item_id] = (base_stats, effective_caps)
            return relic_profile_cache[item_id]

        def mark_relic_candidate(
            effective_item: ItemRecord,
            raw_item: ItemRecord,
            relic_config: Optional[Dict[str, object]],
            relic_stats: Dict[int, int],
        ) -> None:
            if relic_stats:
                setattr(effective_item, "_gear_search_relic_stats", dict(relic_stats))
            kind = str((relic_config or {}).get("kind") or "")
            if kind != "resistance":
                return
            base_stats, effective_caps = resistance_effective_profile(raw_item, relic_config)
            setattr(effective_item, "_gear_search_relic_kind", kind)
            setattr(effective_item, "_gear_search_relic_config", copy.deepcopy(relic_config))
            setattr(effective_item, "_gear_search_relic_base_stats", dict(base_stats))
            setattr(effective_item, "_gear_search_relic_effective_caps", dict(effective_caps))

        slot_sources = [
            ("weapon", "weapon"),
            ("offhand", "offhand"),
            ("head", "head"),
            ("body", "body"),
            ("hands", "hands"),
            ("legs", "legs"),
            ("feet", "feet"),
            ("earrings", "earrings"),
            ("necklace", "necklace"),
            ("bracelet", "bracelet"),
            ("ring1", "ring"),
            ("ring2", "ring"),
        ]
        candidates: Dict[str, List[ItemRecord]] = {}
        for slot, source in slot_sources:
            current_sel = (self.current_gearset.items or {}).get(slot) or ItemSelection()
            excluded_ids = {
                int(v) for v in list(getattr(current_sel, "excluded_item_ids", []) or []) if int(v or 0) > 0
            }
            if bool(getattr(current_sel, "lock_item", False)):
                locked_item = self.items_by_id.get(int(current_sel.item_id or 0)) if current_sel.item_id else None
                if locked_item is None:
                    candidates[slot] = []
                    continue
                effective_item, _synced, relic_config, relic_stats = self._effective_item_for_selection(
                    locked_item,
                    current_sel,
                    job,
                )
                mark_relic_candidate(
                    effective_item,
                    locked_item,
                    relic_config,
                    relic_stats,
                )
                candidates[slot] = [effective_item]
                continue
            choices = filtered.get(source, [])
            try:
                display_rows = self._compress_slot_items_for_display(choices, job, speed_stat, extra_stat)
            except Exception:
                display_rows = [
                    {
                        "item_id": int(item.item_id),
                        "member_ids": [int(item.item_id)],
                    }
                    for item in choices
                ]
            displayed_ids = {
                int(member_id)
                for row_data in display_rows
                for member_id in row_data.get("member_ids", [])
                if int(member_id or 0) > 0
            }
            for item in choices:
                item_id = int(getattr(item, "item_id", 0) or 0)
                if item_id <= 0 or item_id in displayed_ids:
                    continue
                if not self._is_search_special_weapon_item(item, job):
                    continue
                display_rows.append(
                    {
                        "item_id": item_id,
                        "member_ids": [item_id],
                    }
                )
                displayed_ids.add(item_id)
            best_by_signature: Dict[Tuple[object, ...], ItemRecord] = {}
            seen_ids: set = set()
            for row_data in display_rows:
                member_ids = [int(v) for v in row_data.get("member_ids", []) if int(v or 0) > 0]
                if not member_ids:
                    item_id = int(row_data.get("item_id") or 0)
                    if item_id > 0:
                        member_ids = [item_id]
                for item_id in member_ids:
                    if item_id in seen_ids:
                        continue
                    if item_id in excluded_ids:
                        continue
                    raw_item = self.items_by_id.get(item_id)
                    if not raw_item:
                        continue
                    selection_override = current_sel if int(getattr(current_sel, "item_id", 0) or 0) == item_id else None
                    selection_variants: List[Optional[ItemSelection]] = [selection_override]
                    relic_config = self._relic_model_for_item(raw_item, job)
                    for relic_stats in self._gear_search_relic_stat_variants(relic_config):
                        selection_variants.append(
                            ItemSelection(
                                item_id=item_id,
                                relic_stats=relic_stats,
                            )
                        )
                    seen_relic_variants: set[Tuple[Tuple[int, int], ...]] = set()
                    for selection_variant in selection_variants:
                        relic_variant_key = tuple(
                            sorted(
                                (int(stat_id), int(value))
                                for stat_id, value in (
                                    getattr(selection_variant, "relic_stats", {}) or {}
                                ).items()
                                if int(value or 0) > 0
                            )
                        )
                        if relic_variant_key in seen_relic_variants:
                            continue
                        seen_relic_variants.add(relic_variant_key)
                        effective_item, _synced, _relic_config, relic_stats = self._effective_item_for_selection(
                            raw_item,
                            selection_variant,
                            job,
                        )
                        mark_relic_candidate(
                            effective_item,
                            raw_item,
                            _relic_config,
                            relic_stats,
                        )
                        signature = self._gear_search_item_signature(effective_item)
                        current_best = best_by_signature.get(signature)
                        if current_best is None or self._prefer_gear_search_candidate(
                            effective_item,
                            current_best,
                            preferred_ids,
                        ):
                            best_by_signature[signature] = effective_item
                    seen_ids.add(item_id)
            slot_candidates = list(best_by_signature.values())
            slot_candidates.sort(
                key=lambda item: (
                    -int(item.ilvl or 0),
                    -optimizer.total_meld_slots_for_item(item),
                    display_name_with_fallback(getattr(item, "name_ja", None), item.name),
                    int(item.item_id),
                )
            )
            candidates[slot] = slot_candidates

        has_any_offhand = any(getattr(item, "slot", "") == "offhand" for item in self.items_by_job.get(job, []))
        required_slots = [slot for slot in GEAR_SLOTS if slot != "offhand"]
        if has_any_offhand:
            required_slots.append("offhand")
        missing = [slot for slot in required_slots if not candidates.get(slot)]
        return candidates, missing

    def _gearset_within_candidate_pool(
        self,
        gear: Optional[Gearset],
        candidate_items_by_slot: Dict[str, List[ItemRecord]],
    ) -> bool:
        if not gear or not gear.job:
            return False
        for slot, sel in (gear.items or {}).items():
            if not sel or not sel.item_id:
                continue
            slot_candidates = candidate_items_by_slot.get(slot) or []
            if not any(int(getattr(item, "item_id", 0) or 0) == int(sel.item_id) for item in slot_candidates):
                return False
        return True

    def _gear_search_seed_candidates(
        self,
        job: str,
        candidate_items_by_slot: Dict[str, List[ItemRecord]],
    ) -> List[Tuple[Gearset, Dict[str, object], set]]:
        seeds: List[Tuple[Gearset, Dict[str, object], set]] = []
        seen: set = set()
        current_level = self._effective_calc_level()
        current_target_gcd = self.current_gearset.target_gcd
        current_race = self.current_gearset.race
        current_food_id = self.current_gearset.food_id
        current_food_simulation = bool(
            getattr(self.current_gearset, "food_simulation", False)
        )
        active_items = self.current_gearset.items or {}

        def add_seed(gear: Optional[Gearset]) -> None:
            if not gear or gear.job != job:
                return
            cloned = Gearset.from_dict(gear.to_dict())
            # Re-evaluate saved sets under the active search conditions.
            cloned.level = current_level
            cloned.target_gcd = current_target_gcd
            cloned.race = current_race
            cloned.food_id = current_food_id
            cloned.food_simulation = current_food_simulation
            for slot in GEAR_SLOTS:
                active_sel = active_items.get(slot) or ItemSelection()
                target_sel = (cloned.items or {}).get(slot) or ItemSelection()
                target_sel.lock_item = bool(getattr(active_sel, "lock_item", False))
                target_sel.lock_materia = bool(getattr(active_sel, "lock_materia", False))
                target_sel.excluded_item_ids = list(getattr(active_sel, "excluded_item_ids", []) or [])
                if target_sel.lock_item:
                    previous_item_id = target_sel.item_id
                    target_sel.item_id = active_sel.item_id
                    target_sel.relic_stats = dict(self._selection_relic_stats(active_sel))
                    if target_sel.lock_materia:
                        target_sel.materia = list(active_sel.materia or [])
                    elif previous_item_id != active_sel.item_id:
                        target_sel.materia = []
                cloned.items[slot] = target_sel
            if not self._gearset_items_ready(cloned):
                return
            if not self._gearset_within_candidate_pool(cloned, candidate_items_by_slot):
                return
            selected_items, no_meld_slots = self._resolved_selected_items(cloned)
            if not selected_items:
                return
            key = tuple(
                (
                    slot,
                    sel.item_id if sel else None,
                    tuple((m.base_param, m.grade) for m in ((sel.materia or []) if sel else [])),
                    tuple(
                        sorted(
                            (int(stat_id), int(value))
                            for stat_id, value in self._selection_relic_stats(sel).items()
                            if int(value or 0) > 0
                        )
                    ) if sel else (),
                )
                for slot, sel in sorted((cloned.items or {}).items())
            )
            if key in seen:
                return
            seen.add(key)
            seeds.append((cloned, selected_items, no_meld_slots))

        add_seed(self.current_gearset)
        add_seed(self._simdps_baseline_gearset)
        for entry in self.saved_sets:
            if not isinstance(entry, dict):
                continue
            gear_data = entry.get("gearset")
            if not isinstance(gear_data, dict):
                continue
            try:
                saved_gear = Gearset.from_dict(gear_data)
            except Exception:
                continue
            add_seed(saved_gear)
        return seeds

    def _gear_search_constrained_candidates(
        self,
        candidate_items_by_slot: Dict[str, List[ItemRecord]],
        gear: Gearset,
        fixed_slots: set[str],
        sync_il_override: object = _USE_CURRENT_SYNC,
        allow_ui_fallback: bool = True,
    ) -> Tuple[Dict[str, List[ItemRecord]], List[str]]:
        constrained: Dict[str, List[ItemRecord]] = {}
        missing: List[str] = []
        for slot in GEAR_SLOTS:
            if slot in fixed_slots:
                sel = (gear.items or {}).get(slot)
                if not sel or not sel.item_id:
                    missing.append(slot)
                    constrained[slot] = []
                    continue
                slot_candidates = list(candidate_items_by_slot.get(slot) or [])
                selected_relic_key = tuple(
                    sorted(
                        (int(stat_id), int(value))
                        for stat_id, value in self._selection_relic_stats(sel).items()
                        if int(value or 0) > 0
                    )
                )
                same_id_candidates = [
                    candidate
                    for candidate in slot_candidates
                    if int(getattr(candidate, "item_id", 0) or 0) == int(sel.item_id)
                ]
                item = next(
                    (
                        candidate
                        for candidate in same_id_candidates
                        if tuple(
                            sorted(
                                (int(stat_id), int(value))
                                for stat_id, value in dict(
                                    getattr(candidate, "_gear_search_relic_stats", {}) or {}
                                ).items()
                                if int(value or 0) > 0
                            )
                        ) == selected_relic_key
                    ),
                    None,
                )
                if item is None and same_id_candidates and all(
                    not getattr(candidate, "_gear_search_relic_kind", "")
                    and not getattr(candidate, "_gear_search_relic_stats", {})
                    for candidate in same_id_candidates
                ):
                    item = same_id_candidates[0]
                if item is not None:
                    constrained[slot] = [item]
                    continue
                if not allow_ui_fallback:
                    missing.append(slot)
                    constrained[slot] = []
                    continue
                item = self.items_by_id.get(int(sel.item_id))
                if item is None:
                    missing.append(slot)
                    constrained[slot] = []
                    continue
                effective_item, _synced, _relic_config, _relic_stats = self._effective_item_for_selection(
                    item,
                    sel,
                    gear.job,
                    sync_il_override=sync_il_override,
                )
                constrained[slot] = [effective_item]
            else:
                constrained[slot] = list(candidate_items_by_slot.get(slot) or [])
        return constrained, missing

    def _dedupe_optimized_results(
        self,
        results: List[Tuple[Gearset, float, float]],
        limit: int = 3,
    ) -> List[Tuple[Gearset, float, float]]:
        deduped: List[Tuple[Gearset, float, float]] = []
        seen = set()
        for gs, score, gcd in sorted(results, key=lambda entry: (-float(entry[1]), float(entry[2]))):
            key = tuple(
                (
                    slot,
                    sel.item_id if sel else None,
                    tuple((m.base_param, m.grade) for m in ((sel.materia or []) if sel else [])),
                    tuple(
                        sorted(
                            (int(stat_id), int(value))
                            for stat_id, value in self._selection_relic_stats(sel).items()
                            if int(value or 0) > 0
                        )
                    ) if sel else (),
                )
                for slot, sel in sorted((gs.items or {}).items())
            )
            if key in seen:
                continue
            seen.add(key)
            deduped.append((gs, score, gcd))
            if len(deduped) >= limit:
                break
        return deduped

    @staticmethod
    def _gear_search_focus_signature(gear: Gearset) -> Tuple:
        """Return the conditions that can change a fixed-side gear search."""

        signature = []
        for slot in GEAR_SLOTS:
            selection = (gear.items or {}).get(slot)
            if selection is None:
                signature.append((slot, None, (), False, False, ()))
                continue
            lock_item = bool(getattr(selection, "lock_item", False))
            lock_materia = bool(getattr(selection, "lock_materia", False))
            relic_stats = tuple(
                sorted(
                    (int(stat_id), int(value))
                    for stat_id, value in dict(
                        getattr(selection, "relic_stats", {}) or {}
                    ).items()
                    if int(value or 0) > 0
                )
            )
            fixed_materia = (
                tuple(
                    (int(meld.base_param), int(meld.grade))
                    for meld in (selection.materia or [])
                )
                if lock_item and lock_materia
                else ()
            )
            signature.append(
                (
                    slot,
                    int(selection.item_id) if selection.item_id else None,
                    relic_stats,
                    lock_item,
                    lock_materia,
                    fixed_materia,
                )
            )
        return tuple(signature)

    def refresh_food_combo(self) -> None:
        il_min = self.food_il_min.value()
        il_max = self.food_il_max.value()
        current_food_id = self.food_combo.currentData()
        self.food_combo.blockSignals(True)
        self.food_combo.clear()
        self.food_combo.addItem("食事なし（固定）", None)
        self.food_combo.addItem("食事をシミュレーション", FOOD_SIMULATION_DATA)

        def in_range(f):
            if f.level_item is None:
                return True
            return il_min <= f.level_item <= il_max

        foods = [f for f in self.foods if in_range(f) and optimizer.is_combat_food(f)]
        foods.sort(key=lambda f: (-(f.level_item or 0), display_name_with_fallback(getattr(f, "name_ja", None), f.name)))
        for f in foods:
            name = display_name_with_fallback(getattr(f, "name_ja", None), f.name)
            level = f.level_item if f.level_item is not None else "?"
            self.food_combo.addItem(f"[IL{level}] {name}", f.food_id)
        if current_food_id is not None:
            idx = self.food_combo.findData(current_food_id)
            if idx != -1:
                self.food_combo.setCurrentIndex(idx)
        self.food_combo.blockSignals(False)

    def _sync_food_selection_to_gearset(self) -> Optional[int]:
        selected = self.food_combo.currentData()
        simulate = selected == FOOD_SIMULATION_DATA
        self.current_gearset.food_simulation = simulate
        if not simulate:
            self.current_gearset.food_id = self._resolve_food_id(selected)
        return self.current_gearset.food_id

    def _on_food_combo_changed(self, _index: int = -1) -> None:
        if getattr(self, "_applying_gearset", False):
            return
        self._sync_food_selection_to_gearset()
        self._update_optimize_button_text()
        self._schedule_auto_score_update()
        self._sync_selected_saved_set_ui_context()

    def _ensure_food_combo_item(self, food_id: Optional[int]) -> None:
        if food_id is None or not hasattr(self, "food_combo"):
            return
        resolved_food_id = self._resolve_food_id(food_id)
        if resolved_food_id is None:
            return
        if self.food_combo.findData(resolved_food_id) != -1:
            return
        food = self._find_food_by_id(resolved_food_id)
        if not food:
            return
        name = display_name_with_fallback(getattr(food, "name_ja", None), food.name)
        level = food.level_item if food.level_item is not None else "?"
        self.food_combo.addItem(f"[IL{level}] {name}", food.food_id)

    def _sync_ui_to_gearset(self) -> None:
        for slot, table in self.slot_tables.items():
            sel = self.current_gearset.items.get(slot) or ItemSelection()
            sel.lock_item = self._slot_item_lock_enabled(slot)
            sel.lock_materia = self._slot_materia_lock_enabled(slot)
            row = table.currentRow()
            if row < 0:
                self.current_gearset.items[slot] = sel
                continue
            item_cell = table.item(row, 0)
            if not item_cell:
                self.current_gearset.items[slot] = sel
                continue
            item_id = item_cell.data(Qt.UserRole)
            if item_id is None and sel.item_id is not None:
                # Avoid clearing selection when the UI row hasn't caught up yet.
                self.current_gearset.items[slot] = sel
                continue
            if sel.item_id is not None:
                # Gearset is authoritative; only accept the table value when it matches.
                # Manual changes are handled by on_slot_table_selected.
                if not self._table_has_item(table, sel.item_id):
                    # Keep existing selection if the UI list is filtered out.
                    self.current_gearset.items[slot] = sel
                    continue
                if item_id != sel.item_id:
                    self.current_gearset.items[slot] = sel
                    continue
            else:
                sel.item_id = item_id
                if item_id is None:
                    sel.materia = []
                    sel.relic_stats = {}
            self.current_gearset.items[slot] = sel
        self.current_gearset.target_gcd = self.input_target_gcd.value()
        self._sync_food_selection_to_gearset()
        self.current_gearset.race = self._current_race()
        self.current_gearset.level = self._effective_calc_level()

    def _compute_raw_stats_with_melds(self, gearset: Gearset) -> Tuple[Dict[int, int], Dict[str, object]]:
        key_slots = []
        for slot_name in GEAR_SLOTS:
            sel = (gearset.items or {}).get(slot_name) or ItemSelection()
            mats = tuple((m.base_param, m.grade) for m in (sel.materia or []))
            relic_sig = tuple(
                sorted(
                    (int(stat_id), int(value))
                    for stat_id, value in self._selection_relic_stats(sel).items()
                    if int(value or 0) > 0
                )
            )
            key_slots.append((slot_name, int(sel.item_id or 0), mats, relic_sig))
        cache_key = (
            str(gearset.job or ""),
            int(gearset.level or 0),
            bool(self._level_sync_enabled()),
            int(self._level_sync_il_value() or 0),
            tuple(key_slots),
        )
        cached = self._raw_stats_cache.get(cache_key)
        if cached is not None:
            cached_stats, cached_items = cached
            return dict(cached_stats), dict(cached_items)
        selected_items, no_meld_slots = self._resolved_selected_items(gearset)
        base_stats = optimizer.aggregate_base_stats(selected_items)
        combined_stats = base_stats.copy()
        for slot, sel in gearset.items.items():
            if not sel or not sel.materia:
                continue
            if slot in no_meld_slots:
                continue
            item = selected_items.get(slot)
            if not item:
                continue
            per_item: Dict[int, int] = {}
            for meld in sel.materia:
                if not meld or meld.base_param <= 0 or meld.grade <= 0:
                    continue
                value = self._materia_value(meld.base_param, meld.grade)
                per_item[meld.base_param] = per_item.get(meld.base_param, 0) + value
            for stat_id, total_val in per_item.items():
                cap = optimizer.remaining_cap_for_item(item, stat_id, self.cap_table)
                applied = min(total_val, cap)
                if applied <= 0:
                    continue
                combined_stats[stat_id] = combined_stats.get(stat_id, 0) + applied
        if len(self._raw_stats_cache) >= 128:
            self._raw_stats_cache.clear()
        self._raw_stats_cache[cache_key] = (dict(combined_stats), dict(selected_items))
        return combined_stats, selected_items

    def _selected_saved_set_locked(self) -> bool:
        if not hasattr(self, "saved_sets_table"):
            return False
        row = self.saved_sets_table.currentRow()
        if row < 0:
            return False
        entry_item = self.saved_sets_table.item(row, SAVED_COL_NAME)
        entry = entry_item.data(Qt.UserRole) if entry_item else None
        return isinstance(entry, dict) and bool(entry.get("locked", False))

    def _show_locked_materia_message(self) -> None:
        QMessageBox.information(self, "ロック中", "ロック中のためマテリア更新できません。")

    def on_optimize(self) -> None:
        if self._selected_saved_set_locked():
            self._show_locked_materia_message()
            self.progress_label.setText("ロック中のためマテリア最適化は実行しませんでした。")
            return
        job = self.current_gearset.job
        if not job:
            QMessageBox.warning(self, "ジョブ未選択", "先にジョブを選択してください。")
            return
        if not self.materia_catalog or not self.foods:
            QMessageBox.warning(self, "データ未取得", "マテリアと食事データを取得してください。")
            return
        if not self.base_params or not self.item_levels or not self.jobs_data:
            QMessageBox.warning(self, "データ未取得", "装備データ取得（強制再取得）で基礎ステ/ItemLevel/ジョブを取得してください。")
            return
        if not self.cap_table:
            QMessageBox.warning(self, "装備未取得", "先にジョブの装備一覧を読み込んでください。")
            return
        mode = self.calc_mode.currentData() or "simdps_self"
        if mode == "dmg100p" and not self.jobs_data:
            QMessageBox.warning(self, "ジョブ未取得", "装備データ取得でジョブ情報を取得してください。")
            return

        self._sync_ui_to_gearset()
        if not self._validate_simulation_fixed_slots():
            self.progress_label.setText("固定条件が不正なためシミュレーションを実行しませんでした。")
            return
        foods, food_for_baseline = self._resolve_optimize_food_candidates()
        if not foods:
            QMessageBox.warning(self, "食事なし", "条件に合う戦闘向け食事がありません。")
            return
        baseline_raw_stats, baseline_items = self._compute_raw_stats_with_melds(self.current_gearset)
        baseline_raw_stats, baseline_items, baseline_food, baseline_party, baseline_race = self._resolve_simdps_baseline(
            baseline_raw_stats,
            baseline_items,
            food_for_baseline,
        )
        party_synergies = self._selected_party_synergies()
        eval_rate_adjust_kwargs = self._eval_rate_adjust_kwargs()

        fight_ms = 0
        if self.selected_fight:
            start_time = self.selected_fight.get("startTime", self.selected_fight.get("start_time", 0))
            end_time = self.selected_fight.get("endTime", self.selected_fight.get("end_time", 0))
            fight_ms = end_time - start_time
        fight_ms_eval = fight_ms
        if mode in {"simdps", "simdps_self"}:
            summary = self.damage_summary_self if mode == "simdps_self" else self.damage_summary
            if fight_ms <= 0 or not summary:
                QMessageBox.warning(
                    self,
                    "ログ未取得",
                    "試算DPSにはダメージログが必要です。\nファイトとアクターを選択して「キャスト取得」を実行してください。",
                )
                return
            fight_ms_eval = self._simdps_effective_duration_ms(fight_ms)
            try:
                total_amt = float(summary.get("total_amount") or summary.get("total_damage") or 0.0)
                bucket_sum = sum((summary.get("buckets") or {}).values())
                action_buckets = summary.get("ability_buckets") or {}
                action_bucket_count = len(action_buckets)
                buffed_bucket_count = 0
                for k in action_buckets.keys():
                    if isinstance(k, tuple) and len(k) >= 8:
                        dmg_mult, crit_bonus, dh_bonus, fcrit, fdh = k[3], k[4], k[5], k[6], k[7]
                        if (
                            abs(float(dmg_mult) - 1.0) > 1e-9
                            or abs(float(crit_bonus)) > 1e-9
                            or abs(float(dh_bonus)) > 1e-9
                            or bool(fcrit)
                            or bool(fdh)
                        ):
                            buffed_bucket_count += 1
                sim_log(
                    f"[calc] mode={mode} total_amount={total_amt:.1f} bucket_sum={bucket_sum:.1f} "
                    f"action_buckets={action_bucket_count} buffed_buckets={buffed_bucket_count} fight_ms={fight_ms_eval}"
                )
            except Exception:
                pass

        self.last_optimize_mode = mode
        gearset_snapshot = Gearset.from_dict(self.current_gearset.to_dict())
        items_by_id_snapshot = dict(self.items_by_id)
        materia_catalog_snapshot = dict(self.materia_catalog)
        foods_snapshot = list(foods)
        casts_snapshot = copy.deepcopy(self.casts)
        cap_table_snapshot = dict(self.cap_table)
        damage_summary_snapshot = copy.deepcopy(
            self.damage_summary_self if mode == "simdps_self" else self.damage_summary
        )
        gcd_constraint_snapshot = self._active_log_gcd_constraint(mode)
        job_mods_snapshot = self._get_job_mods(job)
        party_bonus_snapshot = int(self.party_bonus.value())
        level_sync_ilvl_snapshot = self._level_sync_il_value()
        optimization_worker_count_snapshot = self._optimization_worker_count()
        baseline_raw_stats = dict(baseline_raw_stats or {})
        baseline_items = dict(baseline_items or {})
        party_synergies = dict(party_synergies or {})
        if self._gear_search_enabled():
            gear_candidates, missing_slots = self._build_gear_search_candidates(job)
            if missing_slots:
                slot_labels = "、".join(optimizer.SLOT_LABELS.get(slot, slot) for slot in missing_slots)
                QMessageBox.warning(
                    self,
                    "装備候補不足",
                    f"IL 範囲内に候補がない部位があります。\n{slot_labels}",
                )
                return
            self._last_optimize_used_gear_search = True
            seed_candidates = self._gear_search_seed_candidates(job, gear_candidates)
            gear_candidates_snapshot = {
                slot: list(items)
                for slot, items in gear_candidates.items()
            }
            seed_candidates_snapshot = [
                (
                    Gearset.from_dict(seed_gearset.to_dict()),
                    dict(seed_items),
                    set(seed_no_meld),
                )
                for seed_gearset, seed_items, seed_no_meld in seed_candidates
            ]

            def _run_gear_search_task(
                optimization_session,
                progress=None,
                stop_event=None,
            ):
                def _search_progress(pct: int, message: str) -> None:
                    if not progress:
                        return
                    mapped = int((max(0, min(100, int(pct))) / 100.0) * 80)
                    progress(mapped, message)

                results = optimizer.search_gearsets(
                    gearset_snapshot,
                    gear_candidates_snapshot,
                    items_by_id_snapshot,
                    materia_catalog_snapshot,
                    foods_snapshot,
                    casts_snapshot,
                    fight_ms_eval,
                    cap_table_snapshot,
                    damage_summary=damage_summary_snapshot,
                    job_mods=job_mods_snapshot,
                    party_bonus=party_bonus_snapshot,
                    baseline_raw_stats=baseline_raw_stats,
                    baseline_items=baseline_items,
                    baseline_food=baseline_food,
                    gcd_constraint=gcd_constraint_snapshot,
                    baseline_party_bonus=baseline_party,
                    baseline_race=baseline_race,
                    party_synergies=party_synergies,
                    **eval_rate_adjust_kwargs,
                    mode=mode,
                    level_sync_ilvl=level_sync_ilvl_snapshot,
                    progress=_search_progress,
                    stop_event=stop_event,
                    finalize_progress=False,
                    optimization_session=optimization_session,
                )
                merged = list(results or [])

                seed_requests = []
                for seed_index, (
                    seed_gearset,
                    seed_items,
                    seed_no_meld,
                ) in enumerate(seed_candidates_snapshot):
                    cache_key = optimizer.optimization_request_key(
                        seed_gearset,
                        seed_items,
                        seed_no_meld,
                    )
                    seed_requests.append(
                        optimizer.OptimizationRequest(
                            request_id=seed_index,
                            cache_key=cache_key,
                            gearset=seed_gearset,
                            selected_items=seed_items,
                            no_meld_slots=seed_no_meld,
                        )
                    )

                def _seed_progress(
                    completed: int,
                    total: int,
                    elapsed: float,
                    eta: Optional[float],
                ) -> None:
                    if not progress:
                        return
                    detail_pct = 100 if total <= 0 else int(
                        (completed / max(1, total)) * 100
                    )
                    eta_text = ""
                    if eta is not None:
                        eta_text = f"、残り約{max(0, int(round(eta)))}秒"
                    progress(
                        80 + int(detail_pct * 5 / 100),
                        encode_progress_message(
                            (
                                f"既知装備を再評価中 {completed}/{total} "
                                f"({optimization_session.worker_count}並列、"
                                f"経過{int(elapsed)}秒{eta_text})"
                            ),
                            detail_value=detail_pct,
                            detail_message="既知装備再評価",
                        ),
                    )

                seed_results = optimization_session.optimize_batch(
                    seed_requests,
                    stop_event=stop_event,
                    progress=_seed_progress,
                )
                if stop_event and stop_event.is_set():
                    return []
                for request in seed_requests:
                    seed_variants = list(
                        optimization_session.cached_variants(request.cache_key)
                    )
                    if seed_variants:
                        merged.extend(
                            self._top_tied_optimized_results(seed_variants, mode)
                        )
                        continue
                    seed_best = seed_results.get(request.cache_key)
                    if seed_best is not None:
                        merged.append(seed_best)

                focus_slot_groups = [
                    {"weapon", "offhand", "head", "body", "hands", "legs", "feet"},
                    {"earrings", "necklace", "bracelet", "ring1", "ring2"},
                ]
                focused_seeds = []
                focused_signatures = set()
                for entry in sorted(
                    merged,
                    key=lambda result: (-float(result[1]), float(result[2])),
                ):
                    focus_signature = self._gear_search_focus_signature(entry[0])
                    if focus_signature in focused_signatures:
                        continue
                    focused_signatures.add(focus_signature)
                    focused_seeds.append(entry)
                    if len(focused_seeds) >= 2:
                        break
                for base_index, (focused_gear, _focused_score, _focused_gcd) in enumerate(focused_seeds, 1):
                    refined_gear = focused_gear
                    for focus_index, fixed_slots in enumerate(focus_slot_groups, 1):
                        if stop_event and stop_event.is_set():
                            return []
                        constrained_candidates, missing_focus = self._gear_search_constrained_candidates(
                            gear_candidates_snapshot,
                            refined_gear,
                            fixed_slots,
                            sync_il_override=level_sync_ilvl_snapshot,
                            allow_ui_fallback=False,
                        )
                        if missing_focus:
                            continue
                        focused_search_number = (
                            (base_index - 1) * len(focus_slot_groups) + focus_index
                        )
                        focused_search_total = max(
                            1,
                            len(focused_seeds) * len(focus_slot_groups),
                        )

                        def _focused_progress(
                            pct: int,
                            message: str,
                            *,
                            search_number: int = focused_search_number,
                        ) -> None:
                            if not progress:
                                return
                            search_fraction = (
                                (search_number - 1) + max(0, min(100, int(pct))) / 100.0
                            ) / focused_search_total
                            progress(
                                85 + int(search_fraction * 14),
                                message,
                            )

                        focused_results = optimizer.search_gearsets(
                            refined_gear,
                            constrained_candidates,
                            items_by_id_snapshot,
                            materia_catalog_snapshot,
                            foods_snapshot,
                            casts_snapshot,
                            fight_ms_eval,
                            cap_table_snapshot,
                            damage_summary=damage_summary_snapshot,
                            job_mods=job_mods_snapshot,
                            party_bonus=party_bonus_snapshot,
                            baseline_raw_stats=baseline_raw_stats,
                            baseline_items=baseline_items,
                            baseline_food=baseline_food,
                            gcd_constraint=gcd_constraint_snapshot,
                            baseline_party_bonus=baseline_party,
                            baseline_race=baseline_race,
                            party_synergies=party_synergies,
                            **eval_rate_adjust_kwargs,
                            mode=mode,
                            level_sync_ilvl=level_sync_ilvl_snapshot,
                            progress=_focused_progress,
                            stop_event=stop_event,
                            finalize_progress=False,
                            optimization_session=optimization_session,
                        )
                        if not focused_results:
                            continue
                        merged.extend(self._top_tied_optimized_results(focused_results, mode))
                        refined_gear = focused_results[0][0]
                        if progress:
                            progress(
                                85 + int(
                                    (focused_search_number / focused_search_total) * 14
                                ),
                                encode_progress_message(
                                    f"片側固定の再探索中 {base_index}-{focus_index}",
                                    detail_value=int(
                                        (focused_search_number / focused_search_total) * 100
                                    ),
                                    detail_message="片側固定再探索",
                                ),
                            )
                if progress:
                    progress(
                        100,
                        encode_progress_message(
                            "装備検索を含む最適化が完了しました",
                            detail_value=100,
                            detail_message="完了",
                        ),
                    )
                return self._dedupe_optimized_results(merged, limit=8)

            def task(progress=None, stop_event=None):
                worker_count = optimization_worker_count_snapshot
                if progress:
                    progress(
                        0,
                        encode_progress_message(
                            f"最適化ワーカーを起動中（{worker_count}並列）",
                            detail_value=0,
                            detail_message="並列処理準備",
                        ),
                    )
                worker_context = optimizer.OptimizationWorkerContext(
                    items_by_id=items_by_id_snapshot,
                    materia_catalog=materia_catalog_snapshot,
                    foods=foods_snapshot,
                    casts=casts_snapshot,
                    fight_duration_ms=fight_ms_eval,
                    cap_table=cap_table_snapshot,
                    damage_summary=damage_summary_snapshot,
                    baseline_raw_stats=baseline_raw_stats,
                    baseline_items=baseline_items,
                    baseline_gcd=None,
                    gcd_constraint=gcd_constraint_snapshot,
                    job_mods=job_mods_snapshot,
                    baseline_food=baseline_food,
                    party_bonus=party_bonus_snapshot,
                    baseline_party_bonus=baseline_party,
                    mode=mode,
                    baseline_race=baseline_race,
                    party_synergies=party_synergies,
                    crit_rate_offset=float(eval_rate_adjust_kwargs.get("crit_rate_offset", 0.0)),
                    dhit_rate_offset=float(eval_rate_adjust_kwargs.get("dhit_rate_offset", 0.0)),
                )
                with optimizer.OptimizationSession(
                    worker_context,
                    worker_count=worker_count,
                ) as optimization_session:
                    return _run_gear_search_task(
                        optimization_session,
                        progress=progress,
                        stop_event=stop_event,
                    )

            if self.start_worker(task, self._after_optimize):
                self.update_progress(
                    0,
                    encode_progress_message(
                        "装備検索を開始しています...",
                        detail_value=0,
                        detail_message="開始準備",
                    ),
                )
            return

        self._last_optimize_used_gear_search = False
        selected_items_for_opt, no_meld_slots_opt = self._resolved_selected_items(
            gearset_snapshot,
            sync_il_override=level_sync_ilvl_snapshot,
        )

        def task(progress=None, stop_event=None):
            return optimizer.optimize(
                gearset_snapshot,
                items_by_id_snapshot,
                materia_catalog_snapshot,
                foods_snapshot,
                casts_snapshot,
                fight_ms_eval,
                cap_table_snapshot,
                damage_summary=damage_summary_snapshot,
                job_mods=job_mods_snapshot,
                party_bonus=party_bonus_snapshot,
                baseline_raw_stats=baseline_raw_stats,
                baseline_items=baseline_items,
                baseline_food=baseline_food,
                gcd_constraint=gcd_constraint_snapshot,
                baseline_party_bonus=baseline_party,
                baseline_race=baseline_race,
                party_synergies=party_synergies,
                **eval_rate_adjust_kwargs,
                selected_items_override=selected_items_for_opt,
                no_meld_slots=no_meld_slots_opt,
                mode=mode,
                progress=progress,
                stop_event=stop_event,
            )

        if self.start_worker(task, self._after_optimize):
            self.update_progress(
                0,
                encode_progress_message(
                    "マテリア最適化を開始しています...",
                    detail_value=0,
                    detail_message="開始準備",
                ),
            )

    def on_calculate(self) -> None:
        job = self.current_gearset.job
        if not job:
            QMessageBox.warning(self, "ジョブ未選択", "先にジョブを選択してください。")
            return
        if not self.materia_catalog:
            QMessageBox.warning(self, "データ未取得", "マテリアデータを取得してください。")
            return
        mode = self.calc_mode.currentData() or "simdps_self"
        if mode == "dmg100p" and not self.jobs_data:
            QMessageBox.warning(self, "ジョブ未取得", "装備データ取得でジョブ情報を取得してください。")
            return

        self._sync_ui_to_gearset()
        food = self._find_food_by_id(self.current_gearset.food_id)
        raw_stats, selected_items = self._compute_raw_stats_with_melds(self.current_gearset)
        if self._simdps_baseline_raw_stats is None or self._simdps_baseline_items is None:
            self._update_simdps_baseline_data()
        baseline_raw, baseline_items, baseline_food, baseline_party, baseline_race = self._resolve_simdps_baseline(
            raw_stats,
            selected_items,
            food,
        )
        party_synergies = self._selected_party_synergies()

        fight_ms = 0
        if self.selected_fight:
            start_time = self.selected_fight.get("startTime", self.selected_fight.get("start_time", 0))
            end_time = self.selected_fight.get("endTime", self.selected_fight.get("end_time", 0))
            fight_ms = end_time - start_time
        fight_ms_eval = fight_ms
        if mode in {"simdps", "simdps_self"}:
            summary = self.damage_summary_self if mode == "simdps_self" else self.damage_summary
            if fight_ms <= 0 or not summary:
                QMessageBox.warning(
                    self,
                    "ログ未取得",
                    "試算DPSにはダメージログが必要です。\nファイトとアクターを選択して「キャスト取得」を実行してください。",
                )
                return
            fight_ms_eval = self._simdps_effective_duration_ms(fight_ms)

        eval_kwargs = {
            "job_mods": self._get_job_mods(job),
            "food": food,
            "party_bonus": self.party_bonus.value(),
            "baseline_raw_stats": baseline_raw,
            "baseline_items": baseline_items,
            "selected_items": selected_items,
            "baseline_food": baseline_food,
            "baseline_party_bonus": baseline_party,
            "baseline_race": baseline_race,
            "party_synergies": party_synergies,
            "race": self.current_gearset.race,
            "mode": mode,
            "level": self.current_gearset.level,
            **self._eval_rate_adjust_kwargs(),
        }

        selected_entry = next(
            (
                entry
                for entry in self.saved_sets
                if isinstance(entry, dict)
                and entry.get("id") == self._current_loaded_saved_set_id
            ),
            None,
        )
        self._begin_saved_score_recalculation(selected_entry)

        if mode == "dmg100p":
            score, expected_score, gcd = optimizer.evaluate_score_pair(
                raw_stats,
                job,
                self.casts,
                fight_ms_eval,
                self.current_gearset.target_gcd,
                **eval_kwargs,
            )
            self._apply_eval_result(mode, float(score), float(gcd), float(expected_score))
        elif mode in {"simdps", "simdps_self"}:
            summary = self.damage_summary_self if mode == "simdps_self" else self.damage_summary
            score, expected_score, gcd = optimizer.evaluate_score_pair(
                raw_stats,
                job,
                self.casts,
                fight_ms_eval,
                self.current_gearset.target_gcd,
                damage_summary=summary,
                debug=sim_debug_enabled(),
                **eval_kwargs,
            )
            self._apply_eval_result(mode, float(score), float(gcd), float(expected_score))
            if mode == "simdps_self":
                sim_log(f"[calc] mode={mode} result={score:.2f} gcd={gcd}")
        else:
            score, expected_score, gcd = optimizer.evaluate_score_pair(
                raw_stats,
                job,
                self.casts,
                fight_ms_eval,
                self.current_gearset.target_gcd,
                **eval_kwargs,
            )
            self._apply_eval_result(mode, float(score), float(gcd), float(expected_score))
        for slot in self.slot_tables.keys():
            self._refresh_slot_selected_display(slot)

    def _after_optimize(self, results) -> None:
        if not results:
            self._clear_optimal_variant_tabs()
            detail = ""
            if self._level_sync_enabled():
                detail = "\nレベルシンク中は同期された装備のマテリアが無効になります。"
            if self._last_optimize_used_gear_search:
                detail += "\n装備シミュレーションでは現在の IL 範囲内の候補のみ探索します。"
            QMessageBox.information(self, "結果なし", f"条件を満たす組み合わせが見つかりませんでした。{detail}")
            return
        mode = self.last_optimize_mode or "simdps_self"
        variant_entries = self._build_optimal_variant_entries(list(results), mode)
        active_entry = variant_entries[0] if variant_entries else None
        best = active_entry.get("gearset") if active_entry is not None else results[0][0]
        if not isinstance(best, Gearset):
            best = results[0][0]
        self._pending_saved_set_ui_context = self._capture_saved_set_ui_context(best.job)
        self._apply_gearset_to_ui(best)
        if self._last_optimize_used_gear_search:
            self.progress_label.setText("最適な装備セットを反映しました。")
        else:
            self.progress_label.setText("最適解を反映しました。")
        for slot in self.slot_tables.keys():
            self._refresh_slot_selected_display(slot)
        if active_entry is None:
            expected_score = float(results[0][1])
            current_eval = self._evaluate_current_gearset_scores(mode)
            score_value = float(results[0][1])
            gcd_value = float(results[0][2])
            if current_eval is not None:
                score_value = float(current_eval[0])
                expected_score = float(current_eval[1])
                gcd_value = float(current_eval[2])
            self._apply_eval_result(mode, score_value, gcd_value, expected_score)
            self._clear_optimal_variant_tabs()
            return
        self._apply_eval_result(
            mode,
            float(active_entry["score"]),
            float(active_entry["gcd"]),
            float(active_entry["expected_score"]),
        )
        self._set_optimal_variant_tabs(variant_entries, selected_index=0)


    def _materia_value(self, base_param: int, grade: int) -> int:
        if base_param <= 0 or grade <= 0:
            return 0
        cat = self.materia_catalog.get(base_param)
        if cat:
            for g in cat.grades:
                if g.grade == grade:
                    return g.value
        return 0

    def _get_job_mods(self, job: str) -> Dict[str, int]:
        cached = self._job_mods_cache.get(job)
        if cached is not None:
            return dict(cached)
        rec = self.jobs_data.get(job)
        if not rec:
            return {}
        mods = {
            "strength": rec.modifier_strength,
            "dexterity": rec.modifier_dexterity,
            "intelligence": rec.modifier_intelligence,
            "mind": rec.modifier_mind,
            "vitality": rec.modifier_vitality,
            "hp": rec.modifier_hp,
        }
        self._job_mods_cache[job] = dict(mods)
        return mods

    def _shutdown_background_tasks(self) -> bool:
        if self.active_worker:
            self.active_worker.cancel()
        if self._saved_stats_worker:
            self._saved_stats_worker.cancel()
        for worker in list(self._icon_workers.values()):
            worker.cancel()
        deadline = time.monotonic() + 30.0
        main_timeout_ms = max(0, int((deadline - time.monotonic()) * 1000))
        main_done = self.thread_pool.waitForDone(main_timeout_ms)
        icon_timeout_ms = max(0, int((deadline - time.monotonic()) * 1000))
        icons_done = self.icon_thread_pool.waitForDone(icon_timeout_ms)
        if not main_done or not icons_done:
            logger.warning(
                "Background workers did not stop before shutdown (main=%s, icons=%s)",
                main_done,
                icons_done,
            )
            return False
        for client in (self.ff_client, self.xivapi_client, self.xiv_client):
            try:
                client.close()
            except Exception:
                logger.exception("Failed to close HTTP client %s", type(client).__name__)
        return True

    def closeEvent(self, event) -> None:
        self._closing = True
        save_errors: List[str] = []
        if not self._flush_saved_sets():
            save_errors.append("保存セット")
        if not self.on_save_auth(silent=True):
            save_errors.append("認証・画面設定")
        if not self._shutdown_background_tasks():
            self._closing = False
            event.ignore()
            QMessageBox.warning(
                self,
                "終了待機",
                "バックグラウンド処理を停止できませんでした。処理終了後にもう一度閉じてください。",
            )
            return
        if save_errors:
            QMessageBox.warning(
                self,
                "保存失敗",
                f"終了時に保存できなかった項目があります: {', '.join(save_errors)}",
            )
        super().closeEvent(event)


def main() -> None:
    ensure_runtime_dirs()
    ensure_config_files()
    app = QApplication([])
    app.setStyleSheet(
        """
        QWidget { background-color: #1b1f23; color: #dfe6ee; }
        QLabel { padding-right: 4px; }
        QLineEdit, QComboBox, QSpinBox, QDoubleSpinBox, QTextEdit, QListWidget, QTableWidget {
            background-color: #11161b; border: 1px solid #2b323a; padding: 4px;
        }
        QHeaderView::section { padding: 4px 8px; }
        QTableWidget::item { padding: 2px 8px; }
        QSpinBox, QDoubleSpinBox { padding-right: 18px; }
        QSpinBox::up-button, QDoubleSpinBox::up-button {
            subcontrol-origin: border;
            subcontrol-position: top right;
            width: 16px;
            border-left: 1px solid #2b323a;
        }
        QSpinBox::down-button, QDoubleSpinBox::down-button {
            subcontrol-origin: border;
            subcontrol-position: bottom right;
            width: 16px;
            border-left: 1px solid #2b323a;
        }
        QGroupBox { border: 1px solid #2b323a; margin-top: 8px; }
        QGroupBox::title { subcontrol-origin: margin; left: 8px; padding: 0 4px; }
        QPushButton { background-color: #2b323a; border: 1px solid #3a424c; padding: 4px 8px; }
        QPushButton:hover { background-color: #3a424c; }
        QProgressBar { background-color: #11161b; border: 1px solid #2b323a; text-align: center; }
        QProgressBar::chunk { background-color: #3c8dbc; }
        """
    )
    win = MainWindow()
    win.show()
    app.exec()


if __name__ == "__main__":
    main()
