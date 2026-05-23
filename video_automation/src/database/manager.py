import sqlite3
import os
import json
from datetime import datetime
from pathlib import Path


class DatabaseManager:
    def __init__(self, db_path: str = "automation.db"):
        self.db_path = db_path
        self._init_db()

    def _conn(self) -> sqlite3.Connection:
        conn = sqlite3.connect(self.db_path)
        conn.row_factory = sqlite3.Row
        return conn

    def _init_db(self):
        with self._conn() as conn:
            conn.executescript("""
                CREATE TABLE IF NOT EXISTS videos (
                    id          INTEGER PRIMARY KEY AUTOINCREMENT,
                    niche       TEXT NOT NULL,
                    platform    TEXT NOT NULL,
                    title       TEXT,
                    description TEXT,
                    tags        TEXT,
                    file_path   TEXT,
                    status      TEXT DEFAULT 'pending',
                    created_at  TEXT DEFAULT (datetime('now')),
                    metadata    TEXT
                );

                CREATE TABLE IF NOT EXISTS uploads (
                    id          INTEGER PRIMARY KEY AUTOINCREMENT,
                    video_id    INTEGER REFERENCES videos(id),
                    platform    TEXT NOT NULL,
                    platform_id TEXT,
                    url         TEXT,
                    status      TEXT DEFAULT 'pending',
                    error       TEXT,
                    uploaded_at TEXT DEFAULT (datetime('now'))
                );

                CREATE TABLE IF NOT EXISTS topics (
                    id          INTEGER PRIMARY KEY AUTOINCREMENT,
                    niche       TEXT NOT NULL,
                    topic       TEXT NOT NULL,
                    source      TEXT,
                    used        INTEGER DEFAULT 0,
                    created_at  TEXT DEFAULT (datetime('now'))
                );
            """)

    # ── Videos ──────────────────────────────────────────────────────────────

    def save_video(
        self,
        niche: str,
        platform: str,
        title: str,
        description: str,
        tags: list[str],
        file_path: str,
        metadata: dict | None = None,
    ) -> int:
        with self._conn() as conn:
            cur = conn.execute(
                """INSERT INTO videos (niche, platform, title, description, tags, file_path, status, metadata)
                   VALUES (?, ?, ?, ?, ?, ?, 'ready', ?)""",
                (
                    niche,
                    platform,
                    title,
                    description,
                    json.dumps(tags),
                    file_path,
                    json.dumps(metadata or {}),
                ),
            )
            return cur.lastrowid

    def update_video_status(self, video_id: int, status: str):
        with self._conn() as conn:
            conn.execute("UPDATE videos SET status=? WHERE id=?", (status, video_id))

    def get_pending_videos(self) -> list[dict]:
        with self._conn() as conn:
            rows = conn.execute(
                "SELECT * FROM videos WHERE status='ready' ORDER BY created_at"
            ).fetchall()
            return [dict(r) for r in rows]

    def videos_created_today(self) -> int:
        with self._conn() as conn:
            row = conn.execute(
                "SELECT COUNT(*) as n FROM videos WHERE date(created_at)=date('now')"
            ).fetchone()
            return row["n"]

    # ── Uploads ─────────────────────────────────────────────────────────────

    def save_upload(
        self,
        video_id: int,
        platform: str,
        platform_id: str = "",
        url: str = "",
        status: str = "success",
        error: str = "",
    ) -> int:
        with self._conn() as conn:
            cur = conn.execute(
                """INSERT INTO uploads (video_id, platform, platform_id, url, status, error)
                   VALUES (?, ?, ?, ?, ?, ?)""",
                (video_id, platform, platform_id, url, status, error),
            )
            return cur.lastrowid

    # ── Topics ───────────────────────────────────────────────────────────────

    def save_topic(self, niche: str, topic: str, source: str = ""):
        with self._conn() as conn:
            conn.execute(
                "INSERT OR IGNORE INTO topics (niche, topic, source) VALUES (?,?,?)",
                (niche, topic, source),
            )

    def mark_topic_used(self, topic_id: int):
        with self._conn() as conn:
            conn.execute("UPDATE topics SET used=1 WHERE id=?", (topic_id,))

    # ── Stats ────────────────────────────────────────────────────────────────

    def get_stats(self) -> dict:
        with self._conn() as conn:
            total = conn.execute("SELECT COUNT(*) as n FROM videos").fetchone()["n"]
            today = self.videos_created_today()
            uploads = conn.execute(
                "SELECT COUNT(*) as n FROM uploads WHERE status='success'"
            ).fetchone()["n"]
            by_niche = conn.execute(
                "SELECT niche, COUNT(*) as n FROM videos GROUP BY niche"
            ).fetchall()
            return {
                "total_videos": total,
                "today": today,
                "successful_uploads": uploads,
                "by_niche": {r["niche"]: r["n"] for r in by_niche},
            }
