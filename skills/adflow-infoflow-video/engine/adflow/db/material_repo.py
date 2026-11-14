"""
素材仓库 CRUD
- 导入 / 查询 / 更新 / 删除素材
- 标签管理
- 使用记录查询
"""

import json
import hashlib
import uuid
from datetime import datetime
from typing import Optional

from adflow.models import MaterialRecord, MaterialUsageLog
from adflow.db.connection import get_db


class MaterialRepo:
    """素材仓库"""

    def __init__(self):
        self.db = get_db()

    # ---- 素材 CRUD ----

    def insert(self, material: MaterialRecord) -> str:
        """插入素材，自动生成 material_id"""
        if not material.material_id:
            material.material_id = uuid.uuid4().hex[:12]
        if not material.imported_at:
            material.imported_at = datetime.now().isoformat()

        self.db.conn.execute("""
            INSERT INTO materials (
                material_id, file_path, original_filename,
                duration_ms, fps, width, height, file_size_bytes, md5_hash, phash,
                orientation,
                scene, shot_type, camera_movement, emotion, product_visibility,
                has_person, person_count, person_role, person_feature,
                has_dialogue, has_bgm, lighting, pace, quality_flags,
                material_category, tags, auto_quality_score,
                source_project, imported_at, notes,
                use_count_total, use_count_30d, last_used_at,
                cooldown_hours, performance_score,
                ctr_avg, cvr_avg, retention_3s_avg, retention_5s_avg
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?,
                      ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, (
            material.material_id, material.file_path, material.original_filename,
            material.duration_ms, material.fps, material.width, material.height,
            material.file_size_bytes, material.md5_hash, material.phash,
            material.orientation,
            material.scene, material.shot_type, material.camera_movement,
            material.emotion, material.product_visibility,
            int(material.has_person), material.person_count,
            material.person_role, material.person_feature,
            int(material.has_dialogue), int(material.has_bgm),
            material.lighting, material.pace, material.quality_flags,
            material.material_category, material.tags, material.auto_quality_score,
            material.source_project, material.imported_at, material.notes,
            material.use_count_total, material.use_count_30d, material.last_used_at,
            material.cooldown_hours, material.performance_score,
            material.ctr_avg, material.cvr_avg,
            material.retention_3s_avg, material.retention_5s_avg,
        ))
        self.db.conn.commit()
        return material.material_id

    def get_by_id(self, material_id: str) -> Optional[MaterialRecord]:
        """按 ID 查询素材"""
        row = self.db.conn.execute(
            "SELECT * FROM materials WHERE material_id = ?", (material_id,)
        ).fetchone()
        return self._row_to_material(row) if row else None

    def get_all(self, limit: int = 200, offset: int = 0) -> list[MaterialRecord]:
        """获取素材列表（limit=0 表示不设上限，返回全部）"""
        if limit and limit > 0:
            rows = self.db.conn.execute(
                "SELECT * FROM materials ORDER BY imported_at DESC LIMIT ? OFFSET ?",
                (limit, offset),
            ).fetchall()
        else:
            rows = self.db.conn.execute(
                "SELECT * FROM materials ORDER BY imported_at DESC",
            ).fetchall()
        return [self._row_to_material(r) for r in rows]

    def count(self) -> int:
        row = self.db.conn.execute("SELECT COUNT(*) as cnt FROM materials").fetchone()
        return row["cnt"] if row else 0

    def get_used_counts(self) -> dict[str, int]:
        """返回 {material_id: use_count_total}，仅含使用次数 > 0 的素材（跨任务永久去重用）"""
        rows = self.db.conn.execute(
            "SELECT material_id, use_count_total FROM materials WHERE use_count_total > 0"
        ).fetchall()
        return {r["material_id"]: r["use_count_total"] for r in rows}

    def search_by_tags(self, tags: list[str], limit: int = 50) -> list[MaterialRecord]:
        """按自由标签搜索素材（OR 逻辑）"""
        if not tags:
            return self.get_all(limit)
        placeholders = ",".join("?" * len(tags))
        rows = self.db.conn.execute(f"""
            SELECT DISTINCT m.* FROM materials m
            LEFT JOIN material_tags t ON m.material_id = t.material_id
            WHERE t.tag_name IN ({placeholders})
            ORDER BY m.performance_score DESC
            LIMIT ?
        """, (*tags, limit)).fetchall()
        return [self._row_to_material(r) for r in rows]

    def get_by_md5(self, md5_hash: str) -> Optional[MaterialRecord]:
        """MD5 去重查询"""
        row = self.db.conn.execute(
            "SELECT * FROM materials WHERE md5_hash = ?", (md5_hash,)
        ).fetchone()
        return self._row_to_material(row) if row else None

    def update_tags(self, material_id: str, tags: list[str]) -> None:
        """更新自由标签"""
        tags_json = json.dumps(tags, ensure_ascii=False)
        self.db.conn.execute(
            "UPDATE materials SET tags = ? WHERE material_id = ?",
            (tags_json, material_id),
        )
        # 同步 material_tags 表
        self.db.conn.execute(
            "DELETE FROM material_tags WHERE material_id = ?", (material_id,)
        )
        for tag in tags:
            self.db.conn.execute(
                "INSERT OR IGNORE INTO material_tags (material_id, tag_name) VALUES (?, ?)",
                (material_id, tag),
            )
        self.db.conn.commit()

    def update_auto_tags(self, material_id: str, **tag_fields) -> None:
        """批量更新自动打标字段"""
        allowed = {
            "scene", "shot_type", "camera_movement", "emotion",
            "product_visibility", "has_person", "person_count",
            "person_role", "person_feature", "has_dialogue", "has_bgm",
            "lighting", "pace", "quality_flags", "material_category",
            "auto_quality_score",
        }
        updates = {k: v for k, v in tag_fields.items() if k in allowed}
        if not updates:
            return
        # bool → int
        for k in ("has_person", "has_dialogue", "has_bgm"):
            if k in updates:
                updates[k] = int(updates[k])
        set_clause = ", ".join(f"{k} = ?" for k in updates)
        values = list(updates.values()) + [material_id]
        self.db.conn.execute(
            f"UPDATE materials SET {set_clause} WHERE material_id = ?", values
        )
        self.db.conn.commit()

    def set_phash_batch(self, items: list[tuple[str, str]]) -> None:
        """批量写入素材 pHash（items: [(phash, material_id), ...]，一次事务）"""
        if not items:
            return
        self.db.conn.executemany(
            "UPDATE materials SET phash = ? WHERE material_id = ?", items
        )
        self.db.conn.commit()

    def set_orientation_batch(self, items: list[tuple[str, str]]) -> None:
        """批量写入方向分类（items: [(orientation, material_id), ...]）"""
        if not items:
            return
        self.db.conn.executemany(
            "UPDATE materials SET orientation = ? WHERE material_id = ?", items
        )
        self.db.conn.commit()

    def delete(self, material_id: str) -> None:
        """删除素材（仅删除数据库记录，不删文件）"""
        self.db.conn.execute("DELETE FROM materials WHERE material_id = ?", (material_id,))
        self.db.conn.commit()

    def delete_all(self) -> None:
        """清空全部素材（仅删除数据库记录，不删文件）"""
        self.db.conn.execute("DELETE FROM material_tags")
        self.db.conn.execute("DELETE FROM material_usage_log")
        self.db.conn.execute("DELETE FROM materials")
        self.db.conn.commit()

    def get_available_for_shot(
        self, required_scene: str = "", required_emotion: str = "",
        required_product_vis: str = "", limit: int = 30,
    ) -> list[MaterialRecord]:
        """按分镜需求筛选可用的候选素材"""
        conditions = ["1=1"]
        params: list = []
        if required_scene:
            conditions.append("scene = ?")
            params.append(required_scene)
        if required_emotion:
            conditions.append("emotion = ?")
            params.append(required_emotion)
        if required_product_vis:
            conditions.append("product_visibility = ?")
            params.append(required_product_vis)

        where = " AND ".join(conditions)
        # limit=0 表示不设上限：用完优先时候选池需覆盖全部素材，
        # 否则 performance_score 全相同时按 rowid 取前 N 会永久卡死冷门素材
        if limit and limit > 0:
            rows = self.db.conn.execute(
                f"SELECT * FROM materials WHERE {where} ORDER BY performance_score DESC LIMIT ?",
                (*params, limit),
            ).fetchall()
        else:
            rows = self.db.conn.execute(
                f"SELECT * FROM materials WHERE {where} ORDER BY performance_score DESC",
                (*params,),
            ).fetchall()
        return [self._row_to_material(r) for r in rows]

    # ---- 使用记录 ----

    def log_usage(self, usage: MaterialUsageLog) -> None:
        """记录素材使用"""
        self.db.conn.execute(
            "INSERT INTO material_usage_log (material_id, ad_variant_id, shot_position, used_at, account_id) "
            "VALUES (?, ?, ?, ?, ?)",
            (usage.material_id, usage.ad_variant_id, usage.shot_position,
             usage.used_at, usage.account_id),
        )
        # 更新素材使用计数
        self.db.conn.execute(
            "UPDATE materials SET use_count_total = use_count_total + 1, "
            "use_count_30d = use_count_30d + 1, last_used_at = ? "
            "WHERE material_id = ?",
            (usage.used_at, usage.material_id),
        )
        self.db.conn.commit()

    def get_recent_usage(
        self, account_id: str = "", window_size: int = 20
    ) -> list[MaterialUsageLog]:
        """获取最近的使用记录"""
        if account_id:
            rows = self.db.conn.execute(
                "SELECT * FROM material_usage_log WHERE account_id = ? "
                "ORDER BY id DESC LIMIT ?",
                (account_id, window_size),
            ).fetchall()
        else:
            rows = self.db.conn.execute(
                "SELECT * FROM material_usage_log ORDER BY id DESC LIMIT ?",
                (window_size,),
            ).fetchall()
        return [MaterialUsageLog(
            id=r["id"], material_id=r["material_id"],
            ad_variant_id=r["ad_variant_id"], shot_position=r["shot_position"],
            used_at=r["used_at"], account_id=r["account_id"],
        ) for r in rows]

    # ---- 辅助 ----

    @staticmethod
    def _row_to_material(row) -> MaterialRecord:
        """sqlite3.Row → MaterialRecord"""
        if row is None:
            return None
        return MaterialRecord(
            material_id=row["material_id"],
            file_path=row["file_path"],
            original_filename=row["original_filename"],
            duration_ms=row["duration_ms"],
            fps=row["fps"],
            width=row["width"],
            height=row["height"],
            file_size_bytes=row["file_size_bytes"],
            md5_hash=row["md5_hash"],
            phash=row["phash"],
            # orientation 列由 _migrate 保证存在，老库默认 'unknown'
            orientation=row["orientation"],
            scene=row["scene"],
            shot_type=row["shot_type"],
            camera_movement=row["camera_movement"],
            emotion=row["emotion"],
            product_visibility=row["product_visibility"],
            has_person=bool(row["has_person"]),
            person_count=row["person_count"],
            person_role=row["person_role"],
            person_feature=row["person_feature"],
            has_dialogue=bool(row["has_dialogue"]),
            has_bgm=bool(row["has_bgm"]),
            lighting=row["lighting"],
            pace=row["pace"],
            quality_flags=row["quality_flags"],
            material_category=row["material_category"],
            tags=row["tags"],
            auto_quality_score=row["auto_quality_score"],
            source_project=row["source_project"],
            imported_at=row["imported_at"],
            notes=row["notes"],
            use_count_total=row["use_count_total"],
            use_count_30d=row["use_count_30d"],
            last_used_at=row["last_used_at"],
            cooldown_hours=row["cooldown_hours"],
            performance_score=row["performance_score"],
            ctr_avg=row["ctr_avg"],
            cvr_avg=row["cvr_avg"],
            retention_3s_avg=row["retention_3s_avg"],
            retention_5s_avg=row["retention_5s_avg"],
        )

    @staticmethod
    def compute_md5(file_path: str) -> str:
        """计算文件 MD5"""
        hash_md5 = hashlib.md5()
        with open(file_path, "rb") as f:
            for chunk in iter(lambda: f.read(8192), b""):
                hash_md5.update(chunk)
        return hash_md5.hexdigest()
