# -*- coding: utf-8 -*-
"""爆款标注 + 因子快照 CRUD — 遵循项目裸SQL模式"""

import json
from datetime import datetime
from typing import Optional

from adflow.db.connection import get_db
from adflow.analytics.factor_types import (
    HitRecord, VideoFactors,
    RhythmFactors, EmotionFactors, VisualFactors,
    CopyFactors, VoiceFactors, StructureFactors,
)

# 标签枚举（写入与查询两侧统一，避免中英文不一致致训练集永远为空）
LABEL_HIT = "爆款"
LABEL_NORMAL = "一般"
LABEL_FLOP = "低效"
TRAIN_LABELS = (LABEL_HIT, LABEL_NORMAL, LABEL_FLOP)


class AnalyticsRepo:
    """爆款因子数据仓库"""

    def __init__(self):
        self.db = get_db()

    # ═══════════════════════════════════
    # 标注 CRUD
    # ═══════════════════════════════════

    def insert_label(self, rec: HitRecord) -> int:
        """写入爆款标注，返回 rowid"""
        now = datetime.now().isoformat()
        cur = self.db.conn.execute("""
            INSERT INTO hit_labels (
                video_path, video_source, source_task_id, copy_text,
                impressions, clicks, conversions, ctr, cvr, cost,
                play_3s_rate, play_full_rate, like_count, share_count, comment_count,
                label, label_source, label_notes, labeled_at, created_at
            ) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
        """, (
            rec.video_path, rec.video_source, rec.source_task_id, rec.copy_text,
            rec.impressions, rec.clicks, rec.conversions,
            rec.ctr, rec.cvr, rec.cost,
            rec.play_3s_rate, rec.play_full_rate,
            rec.like_count, rec.share_count, rec.comment_count,
            rec.label, rec.label_source, rec.label_notes,
            now, now,
        ))
        self.db.conn.commit()
        return cur.lastrowid

    def update_label(self, label_id: int, **kwargs) -> None:
        """更新标注字段"""
        allowed = {"label", "label_notes", "copy_text",
                   "impressions", "clicks", "conversions",
                   "ctr", "cvr", "cost", "play_3s_rate", "play_full_rate",
                   "like_count", "share_count", "comment_count"}
        sets = []
        vals = []
        for k, v in kwargs.items():
            if k in allowed:
                sets.append(f"{k}=?")
                vals.append(v)
        if not sets:
            return
        sets.append("labeled_at=?")
        vals.append(datetime.now().isoformat())
        vals.append(label_id)
        self.db.conn.execute(
            f"UPDATE hit_labels SET {', '.join(sets)} WHERE id=?",
            vals,
        )
        self.db.conn.commit()

    def get_labels(self, label: str = "", limit: int = 100) -> list[HitRecord]:
        """查询标注记录"""
        if label:
            rows = self.db.conn.execute(
                "SELECT * FROM hit_labels WHERE label=? ORDER BY created_at DESC LIMIT ?",
                (label, limit),
            ).fetchall()
        else:
            rows = self.db.conn.execute(
                "SELECT * FROM hit_labels ORDER BY created_at DESC LIMIT ?",
                (limit,),
            ).fetchall()
        return [self._row_to_hit(r) for r in rows]

    def get_labels_with_factors(self, limit: int = 200
                                ) -> list[HitRecord]:
        """查询已标注且有关联因子的记录（供训练用）"""
        rows = self.db.conn.execute("""
            SELECT h.*, f.factor_vector, f.rhythm_factors, f.emotion_factors,
                   f.visual_factors, f.copy_factors, f.voice_factors,
                   f.structure_factors
            FROM hit_labels h
            JOIN factor_snapshots f ON f.hit_label_id = h.id
            WHERE h.label IN (?, ?, ?)
            ORDER BY h.created_at DESC
            LIMIT ?
        """, (*TRAIN_LABELS, limit)).fetchall()
        return [self._row_to_hit(r, with_factors=True) for r in rows]

    # ═══════════════════════════════════
    # 因子快照 CRUD
    # ═══════════════════════════════════

    def insert_factors(self, hit_label_id, factors: VideoFactors) -> int:
        """写入因子快照"""
        now = datetime.now().isoformat()
        fd = factors.to_dict()
        cur = self.db.conn.execute("""
            INSERT INTO factor_snapshots (
                hit_label_id, source_type, source_task_id,
                rhythm_factors, emotion_factors, visual_factors,
                copy_factors, voice_factors, structure_factors,
                factor_vector, extracted_at
            ) VALUES (?,?,?,?,?,?,?,?,?,?,?)
        """, (
            hit_label_id, factors.source_type, factors.source_task_id,
            json.dumps(fd.get("rhythm", {}), ensure_ascii=False),
            json.dumps(fd.get("emotion", {}), ensure_ascii=False),
            json.dumps(fd.get("visual", {}), ensure_ascii=False),
            json.dumps(fd.get("copy", {}), ensure_ascii=False),
            json.dumps(fd.get("voice", {}), ensure_ascii=False),
            json.dumps(fd.get("structure", {}), ensure_ascii=False),
            json.dumps(factors.to_vector()),
            now,
        ))
        self.db.conn.commit()
        return cur.lastrowid

    # ═══════════════════════════════════
    # 批量导入（CSV/Excel 投放数据 → 自动匹配视频文件）
    # ═══════════════════════════════════

    def batch_import_csv(self, csv_path: str, video_dir: str = "",
                         label_default: str = "normal") -> dict:
        """从CSV批量导入投放数据，按文件名自动匹配视频。

        支持的列名（中英文均可）:
          文件名/filename/视频 → 匹配 video_path
          CTR/点击率, CVR/转化率, 曝光/impressions, 点击/clicks,
          转化/conversions, 消耗/cost, 3s完播/play_3s_rate,
          完播/play_full_rate, 点赞/like_count, 分享/share_count,
          评论/comment_count, 标签/label

        Returns: {"total": N, "inserted": N, "updated": N, "skipped": N,
                  "errors": [...]}
        """
        import csv
        import os as _os

        result = {"total": 0, "inserted": 0, "updated": 0,
                  "skipped": 0, "errors": []}

        # 读CSV（自动检测分隔符）
        try:
            with open(csv_path, "r", encoding="utf-8-sig") as f:
                sample = f.read(1024)
                f.seek(0)
                dialect = csv.Sniffer().sniff(sample, delimiters=",\t;|")
                reader = csv.DictReader(f, dialect=dialect)
                rows = list(reader)
        except Exception as e:
            result["errors"].append(f"读取CSV失败: {e}")
            return result

        if not rows:
            result["errors"].append("CSV为空")
            return result

        # 列名映射
        col_map = self._map_csv_columns(rows[0].keys())
        if "filename" not in col_map:
            result["errors"].append(
                "未找到文件名列，请确保CSV包含：文件名/filename/视频")
            return result

        now = datetime.now().isoformat()

        for row in rows:
            result["total"] += 1
            try:
                filename = (row.get(col_map["filename"]) or "").strip()
                if not filename:
                    result["skipped"] += 1
                    continue

                # 匹配视频文件
                video_path = self._find_video(filename, video_dir)

                # 提取各字段
                copy_text = self._csv_val(row, col_map, "copy_text", "")
                # 标签中英文统一转中文；有标签列但单元格为空→留空（未标注，不默认"一般"以免污染训练集）
                if "label" in col_map:
                    raw_label = self._csv_val(row, col_map, "label", "")
                    label_map = {"hit": "爆款", "normal": "一般", "flop": "低效"}
                    label_cn = label_map.get(raw_label.strip().lower(), raw_label.strip())
                else:
                    label_cn = label_default

                rec = HitRecord(
                    video_path=video_path,
                    video_source="csv_import",
                    copy_text=copy_text,
                    impressions=self._csv_int(row, col_map, "impressions"),
                    clicks=self._csv_int(row, col_map, "clicks"),
                    conversions=self._csv_int(row, col_map, "conversions"),
                    ctr=self._csv_float(row, col_map, "ctr"),
                    cvr=self._csv_float(row, col_map, "cvr"),
                    cost=self._csv_float(row, col_map, "cost"),
                    play_3s_rate=self._csv_float(row, col_map, "play_3s_rate"),
                    play_full_rate=self._csv_float(row, col_map, "play_full_rate"),
                    like_count=self._csv_int(row, col_map, "like_count"),
                    share_count=self._csv_int(row, col_map, "share_count"),
                    comment_count=self._csv_int(row, col_map, "comment_count"),
                    label=label_cn,
                    label_notes=self._csv_val(row, col_map, "label_notes", f"CSV导入: {filename}"),
                )

                # Upsert: 已有同路径记录则更新
                existing = self._find_by_video_path(video_path)
                if existing:
                    self.update_label(existing.id,
                                      label=rec.label,
                                      impressions=rec.impressions,
                                      clicks=rec.clicks,
                                      conversions=rec.conversions,
                                      ctr=rec.ctr, cvr=rec.cvr, cost=rec.cost,
                                      play_3s_rate=rec.play_3s_rate,
                                      play_full_rate=rec.play_full_rate,
                                      like_count=rec.like_count,
                                      share_count=rec.share_count,
                                      comment_count=rec.comment_count,
                                      label_notes=rec.label_notes)
                    result["updated"] += 1
                else:
                    rec.labeled_at = now
                    rec.created_at = now
                    self.insert_label(rec)
                    result["inserted"] += 1

            except Exception as e:
                result["errors"].append(f"第{result['total']}行: {e}")

        return result

    # ── CSV导入辅助 ──

    @staticmethod
    def _map_csv_columns(headers: list) -> dict:
        """列名→标准字段映射（中英文兼容）"""
        mapping = {}
        for h in headers:
            h_lower = h.strip().lower()
            if any(kw in h_lower for kw in ("文件名", "filename", "视频", "video_name")):
                mapping["filename"] = h
            elif any(kw in h_lower for kw in ("ctr", "点击率")):
                mapping["ctr"] = h
            elif any(kw in h_lower for kw in ("cvr", "转化率")):
                mapping["cvr"] = h
            elif any(kw in h_lower for kw in ("曝光", "impression", "展示")):
                mapping["impressions"] = h
            elif any(kw in h_lower for kw in ("点击", "click")):
                mapping["clicks"] = h
            elif any(kw in h_lower for kw in ("转化", "conversion")):
                mapping["conversions"] = h
            elif any(kw in h_lower for kw in ("消耗", "cost", "花费", "金额")):
                mapping["cost"] = h
            elif any(kw in h_lower for kw in ("3s", "3秒", "前三秒", "前3秒")):
                mapping["play_3s_rate"] = h
            elif any(kw in h_lower for kw in ("完播", "播放完成", "full")):
                mapping["play_full_rate"] = h
            elif any(kw in h_lower for kw in ("点赞", "like")):
                mapping["like_count"] = h
            elif any(kw in h_lower for kw in ("分享", "share", "转发")):
                mapping["share_count"] = h
            elif any(kw in h_lower for kw in ("评论", "comment")):
                mapping["comment_count"] = h
            elif any(kw in h_lower for kw in ("文案", "copy_text", "脚本", "文案内容")):
                mapping["copy_text"] = h
            elif any(kw in h_lower for kw in ("备注", "notes", "note")):
                mapping["label_notes"] = h
            elif any(kw in h_lower for kw in ("标签", "label", "标注", "是否爆款")):
                mapping["label"] = h
        return mapping

    @staticmethod
    def _find_video(filename: str, video_dir: str) -> str:
        """按文件名匹配视频路径"""
        import os as _os
        # 去掉扩展名再匹配
        name_no_ext = _os.path.splitext(filename)[0]
        exts = [".mp4", ".mov", ".avi", ".webm", ".mkv"]

        search_dirs = [video_dir] if video_dir else ["hit_videos", "materials", "output", "."]
        for d in search_dirs:
            if not _os.path.isdir(d):
                continue
            # 精确匹配
            full = _os.path.join(d, filename)
            if _os.path.exists(full):
                return _os.path.abspath(full)
            # 模糊匹配（不同扩展名）
            for ext in exts:
                full2 = _os.path.join(d, name_no_ext + ext)
                if _os.path.exists(full2):
                    return _os.path.abspath(full2)
            # 递归搜索一层
            try:
                for entry in _os.listdir(d):
                    entry_path = _os.path.join(d, entry)
                    if _os.path.isfile(entry_path):
                        if entry == filename:
                            return _os.path.abspath(entry_path)
                        ename = _os.path.splitext(entry)[0]
                        if ename == name_no_ext:
                            return _os.path.abspath(entry_path)
            except PermissionError:
                pass

        # 找不到就返回推测路径
        return _os.path.abspath(_os.path.join(
            video_dir or "materials", filename))

    def _find_by_video_path(self, path: str):
        """按视频路径查已有记录"""
        row = self.db.conn.execute(
            "SELECT * FROM hit_labels WHERE video_path=? LIMIT 1",
            (path,),
        ).fetchone()
        return self._row_to_hit(row) if row else None

    def get_label_by_video_path(self, path: str) -> Optional[HitRecord]:
        """按视频路径查标注（供 GUI 因子快照关联正确视频）"""
        return self._find_by_video_path(path)

    @staticmethod
    def _csv_val(row, col_map, key, default=""):
        col = col_map.get(key)
        return row.get(col, default) if col else default

    @staticmethod
    def _csv_int(row, col_map, key) -> int:
        try:
            return int(float(AnalyticsRepo._csv_val(row, col_map, key, "0")))
        except (ValueError, TypeError):
            return 0

    @staticmethod
    def _csv_float(row, col_map, key) -> float:
        try:
            return float(AnalyticsRepo._csv_val(row, col_map, key, "0"))
        except (ValueError, TypeError):
            return 0.0

    # ═══════════════════════════════════
    # 训练数据提取
    # ═══════════════════════════════════

    def get_training_data(self, limit: int = 500
                          ) -> tuple[list[list[float]], list[float]]:
        """提取 (X, y) 供 XGBoost 训练。

        Returns:
            X: 特征矩阵 (n_samples × 30)
            y: 标签向量 (hit=1, normal/flop=0)
        """
        rows = self.db.conn.execute("""
            SELECT h.label, f.factor_vector
            FROM hit_labels h
            JOIN factor_snapshots f ON f.hit_label_id = h.id
            WHERE h.label IN (?, ?, ?)
              AND f.factor_vector != '[]'
            ORDER BY h.created_at DESC
            LIMIT ?
        """, (*TRAIN_LABELS, limit)).fetchall()

        X, y = [], []
        for r in rows:
            try:
                vec = json.loads(r["factor_vector"])
            except (json.JSONDecodeError, TypeError):
                continue
            if len(vec) < 10:  # 向量不完整
                continue
            # 补齐到30维
            while len(vec) < 30:
                vec.append(0.0)
            X.append(vec[:30])
            y.append(1.0 if r["label"] == LABEL_HIT else 0.0)

        return X, y

    # ═══════════════════════════════════
    # 行→对象转换
    # ═══════════════════════════════════

    @staticmethod
    def _row_to_hit(row, with_factors: bool = False) -> HitRecord:
        rec = HitRecord(
            id=row["id"],
            video_path=row["video_path"],
            video_source=row["video_source"],
            source_task_id=row["source_task_id"],
            impressions=row["impressions"],
            clicks=row["clicks"],
            conversions=row["conversions"],
            ctr=row["ctr"],
            cvr=row["cvr"],
            cost=row["cost"],
            play_3s_rate=row["play_3s_rate"],
            play_full_rate=row["play_full_rate"],
            like_count=row["like_count"],
            share_count=row["share_count"],
            comment_count=row["comment_count"],
            label=row["label"],
            label_source=row["label_source"],
            label_notes=row["label_notes"],
            labeled_at=row["labeled_at"],
            created_at=row["created_at"],
        )
        if with_factors and row["factor_vector"]:
            try:
                rec.factors = AnalyticsRepo._row_to_factors(row)
            except Exception:
                pass
        return rec

    @staticmethod
    def _row_to_factors(row) -> VideoFactors:
        """sqlite3.Row → VideoFactors"""
        row = {k: row[k] for k in row.keys()}  # sqlite3.Row 无 .get()，转 dict 以复用取值逻辑
        def _parse_json(val, default):
            if isinstance(val, str):
                try:
                    return json.loads(val)
                except (json.JSONDecodeError, TypeError):
                    return default
            return val or default

        return VideoFactors(
            source_type=row.get("source_type", ""),
            source_task_id=row.get("source_task_id", ""),
            rhythm=RhythmFactors(
                **_parse_json(row.get("rhythm_factors"), {}),
            ),
            emotion=EmotionFactors(
                **_parse_json(row.get("emotion_factors"), {}),
            ),
            visual=VisualFactors(
                **_parse_json(row.get("visual_factors"), {}),
            ),
            copy=CopyFactors(
                **_parse_json(row.get("copy_factors"), {}),
            ),
            voice=VoiceFactors(
                **_parse_json(row.get("voice_factors"), {}),
            ),
            structure=StructureFactors(
                **_parse_json(row.get("structure_factors"), {}),
            ),
        )
