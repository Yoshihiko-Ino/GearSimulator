from __future__ import annotations

import traceback
import threading
from typing import Any, Callable

from PySide6.QtCore import QObject, QRunnable, Signal


class WorkerSignals(QObject):
    finished = Signal(object)
    error = Signal(str)
    progress = Signal(int, str)
    cancelled = Signal()


class Worker(QRunnable):
    def __init__(self, fn: Callable, *args, **kwargs) -> None:
        super().__init__()
        self.fn = fn
        self.args = args
        self.kwargs = kwargs
        self.signals = WorkerSignals()
        self.stop_event = threading.Event()

    def cancel(self) -> None:
        self.stop_event.set()

    def run(self) -> None:
        try:
            result = self.fn(*self.args, stop_event=self.stop_event, **self.kwargs)
            self.signals.finished.emit(result)
        except Exception:
            tb = traceback.format_exc()
            self.signals.error.emit(tb)

