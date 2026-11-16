# -*- coding: utf-8 -*-
"""后台任务执行器 — 把阻塞调用（DB/渲染/LLM）从 UI 线程挪到工作线程

用法:
    runner = TaskRunner(fn, arg1, arg2)
    runner.succeeded.connect(on_done)   # on_done(result)
    runner.failed.connect(on_error)     # on_error(str)
    runner.start()

铁律: fn 内必须新建工作线程对象（AnalyticsRepo / VariantFactory 等），
      get_db() 走 threading.local()，禁止跨线程复用 UI 线程的 repo。
"""
from PyQt6.QtCore import QThread, pyqtSignal


class TaskRunner(QThread):
    """后台跑 fn(*args, **kwargs)，发 succeeded(object) / failed(str)"""
    succeeded = pyqtSignal(object)
    failed = pyqtSignal(str)

    def __init__(self, fn, *args, **kwargs):
        super().__init__()
        self._fn = fn
        self._args = args
        self._kwargs = kwargs

    def run(self):
        try:
            result = self._fn(*self._args, **self._kwargs)
            self.succeeded.emit(result)
        except Exception as e:
            self.failed.emit(str(e))
