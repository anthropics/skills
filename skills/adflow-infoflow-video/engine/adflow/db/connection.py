"""
SQLite 数据库连接管理
- 线程本地连接（每线程独立连接，WAL 模式）
- 自动建表
- 上下文管理器支持事务
"""

import atexit
import sqlite3
import os
import threading
from pathlib import Path


class Database:
    """SQLite 数据库管理器"""

    def __init__(self, db_path: str):
        self.db_path = db_path
        self._conn: sqlite3.Connection | None = None

    @property
    def conn(self) -> sqlite3.Connection:
        if self._conn is None:
            raise RuntimeError("数据库未连接，请先调用 connect() 或使用 with 语句")
        return self._conn

    def connect(self) -> "Database":
        """建立连接并启用 WAL 模式"""
        os.makedirs(os.path.dirname(self.db_path), exist_ok=True)
        self._conn = sqlite3.connect(self.db_path)
        self._conn.execute("PRAGMA journal_mode=WAL")
        self._conn.execute("PRAGMA foreign_keys=ON")
        self._conn.row_factory = sqlite3.Row
        return self

    def init_schema(self) -> None:
        """执行 schema.sql 建表 + 老库补列迁移"""
        schema_path = Path(__file__).parent / "schema.sql"
        with open(schema_path, "r", encoding="utf-8") as f:
            self.conn.executescript(f.read())
        self._migrate()
        self.conn.commit()

    def _migrate(self) -> None:
        """老库补缺失列（幂等：列已存在则跳过）。"""
        self._ensure_column("materials", "phash", "phash TEXT NOT NULL DEFAULT ''")
        # 方向分类（老库默认 unknown，导入/补算按钮会回填）
        self._ensure_column(
            "materials", "orientation",
            "orientation TEXT NOT NULL DEFAULT 'unknown'")

    def _ensure_column(self, table: str, column: str, ddl: str) -> None:
        cols = {r["name"] for r in self.conn.execute(f"PRAGMA table_info({table})")}
        if column not in cols:
            self.conn.execute(f"ALTER TABLE {table} ADD COLUMN {ddl}")

    def close(self) -> None:
        if self._conn:
            self._conn.close()
            self._conn = None

    def __enter__(self) -> "Database":
        self.connect()
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.close()
        return False


# ============================================================
# 线程本地工厂 — 每个线程独立连接，避免 SQLite 跨线程错误
# ============================================================

_thread_local = threading.local()
_db_path: str | None = None
_created: list[Database] = []  # 所有已建立的连接，退出时统一关闭


def get_db(db_path: str | None = None) -> Database:
    """获取当前线程的数据库实例（线程隔离）"""
    global _db_path
    if db_path is not None:
        _db_path = db_path
    elif _db_path is None:
        from adflow.config_loader import config
        _db_path = config.db_path

    # 每个线程创建自己的连接
    if not hasattr(_thread_local, "db") or _thread_local.db is None:
        _thread_local.db = Database(_db_path)
        _thread_local.db.connect()
        _thread_local.db.init_schema()
        _created.append(_thread_local.db)
    return _thread_local.db


def _close_all_connections() -> None:
    """退出时关闭所有线程本地连接（checkpoint WAL + 释放句柄）"""
    for db in _created:
        try:
            db.close()
        except Exception:
            pass


atexit.register(_close_all_connections)


def reset_db_instance() -> None:
    """重置数据库实例（测试用）"""
    global _db_path
    if hasattr(_thread_local, "db") and _thread_local.db:
        _thread_local.db.close()
    _thread_local.db = None
    _db_path = None
