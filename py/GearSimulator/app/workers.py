import traceback
import threading
from typing import Callable

try:
    from PySide6.QtCore import QObject, QRunnable, Signal
except ModuleNotFoundError:
    class _BoundSignal:
        def __init__(self) -> None:
            self._callbacks = []

        def connect(self, callback) -> None:
            self._callbacks.append(callback)

        def emit(self, *args, **kwargs) -> None:
            for callback in list(self._callbacks):
                callback(*args, **kwargs)

    class _SignalDescriptor:
        def __init__(self, *_args, **_kwargs) -> None:
            self._name = ""

        def __set_name__(self, _owner, name: str) -> None:
            self._name = f"__signal_{name}"

        def __get__(self, instance, _owner):
            if instance is None:
                return self
            signal = instance.__dict__.get(self._name)
            if signal is None:
                signal = _BoundSignal()
                instance.__dict__[self._name] = signal
            return signal

    class QObject:
        pass

    class QRunnable:
        def __init__(self, *_args, **_kwargs) -> None:
            pass

    def Signal(*_args, **_kwargs):
        return _SignalDescriptor()


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
            if self.stop_event.is_set():
                self.signals.cancelled.emit()
                return
            self.signals.finished.emit(result)
        except Exception:
            if self.stop_event.is_set():
                self.signals.cancelled.emit()
                return
            tb = traceback.format_exc()
            self.signals.error.emit(tb)
