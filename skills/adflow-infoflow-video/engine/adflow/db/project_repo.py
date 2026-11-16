"""
项目与任务仓库 CRUD
- 产品档案管理
- 出片任务管理
- 策略 / 脚本 / 变体 数据查询
"""

import json
import uuid
from datetime import datetime
from typing import Optional

from adflow.models import (
    ProductProfile, ProjectTask, CreativeStrategy,
    StoryboardScript, StoryboardShot, AdVariant, EditTimeline, ShotMatchResult,
)
from adflow.db.connection import get_db


class ProjectRepo:
    """项目与任务仓库"""

    def __init__(self):
        self.db = get_db()

    # ---- 产品档案 ----

    def insert_product(self, product: ProductProfile) -> str:
        if not product.product_id:
            product.product_id = uuid.uuid4().hex[:10]
        if not product.created_at:
            product.created_at = datetime.now().isoformat()
        product.updated_at = datetime.now().isoformat()

        self.db.conn.execute("""
            INSERT INTO products (product_id, name, category, key_selling_points,
                target_audience, pain_points, brand_tone, prohibited_words,
                avg_price_range, competitors, notes, created_at, updated_at)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, (
            product.product_id, product.name, product.category,
            product.key_selling_points, product.target_audience,
            product.pain_points, product.brand_tone, product.prohibited_words,
            product.avg_price_range, product.competitors,
            product.notes, product.created_at, product.updated_at,
        ))
        self.db.conn.commit()
        return product.product_id

    def get_product(self, product_id: str) -> Optional[ProductProfile]:
        row = self.db.conn.execute(
            "SELECT * FROM products WHERE product_id = ?", (product_id,)
        ).fetchone()
        return self._row_to_product(row) if row else None

    # ---- 出片任务 ----

    def insert_task(self, task: ProjectTask) -> str:
        if not task.task_id:
            task.task_id = uuid.uuid4().hex[:10]
        if not task.created_at:
            task.created_at = datetime.now().isoformat()

        self.db.conn.execute("""
            INSERT INTO project_tasks (task_id, product_id, platform, account_id,
                target_duration_ms, variant_count, status, strategy_id,
                created_at, completed_at, notes)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, (
            task.task_id, task.product_id, task.platform, task.account_id,
            task.target_duration_ms, task.variant_count, task.status,
            task.strategy_id, task.created_at, task.completed_at, task.notes,
        ))
        self.db.conn.commit()
        return task.task_id

    def get_task(self, task_id: str) -> Optional[ProjectTask]:
        row = self.db.conn.execute(
            "SELECT * FROM project_tasks WHERE task_id = ?", (task_id,)
        ).fetchone()
        return self._row_to_task(row) if row else None

    def get_all_tasks(self, limit: int = 50) -> list[ProjectTask]:
        rows = self.db.conn.execute(
            "SELECT * FROM project_tasks ORDER BY created_at DESC LIMIT ?", (limit,)
        ).fetchall()
        return [self._row_to_task(r) for r in rows]

    def update_task_status(self, task_id: str, status: str) -> None:
        completed_at = datetime.now().isoformat() if status in ("done", "failed") else ""
        self.db.conn.execute(
            "UPDATE project_tasks SET status = ?, completed_at = ? WHERE task_id = ?",
            (status, completed_at, task_id),
        )
        self.db.conn.commit()

    def update_task_strategy(self, task_id: str, strategy_id: str) -> None:
        self.db.conn.execute(
            "UPDATE project_tasks SET strategy_id = ? WHERE task_id = ?",
            (strategy_id, task_id),
        )
        self.db.conn.commit()

    # ---- 创意策略 ----

    def insert_strategy(self, strategy: CreativeStrategy) -> str:
        if not strategy.strategy_id:
            strategy.strategy_id = uuid.uuid4().hex[:10]
        if not strategy.created_at:
            strategy.created_at = datetime.now().isoformat()

        self.db.conn.execute("""
            INSERT INTO creative_strategies (strategy_id, task_id, narrative_type,
                hook_type, pace_style, tone, key_message, target_emotion,
                reasoning, source_signals, created_at)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, (
            strategy.strategy_id, strategy.task_id, strategy.narrative_type,
            strategy.hook_type, strategy.pace_style, strategy.tone,
            strategy.key_message, strategy.target_emotion,
            strategy.reasoning, strategy.source_signals, strategy.created_at,
        ))
        self.db.conn.commit()
        return strategy.strategy_id

    def get_strategy_by_task(self, task_id: str) -> Optional[CreativeStrategy]:
        row = self.db.conn.execute(
            "SELECT * FROM creative_strategies WHERE task_id = ? ORDER BY created_at DESC",
            (task_id,),
        ).fetchone()
        return self._row_to_strategy(row) if row else None

    # ---- 分镜脚本 ----

    def insert_script(self, script: StoryboardScript) -> str:
        if not script.script_id:
            script.script_id = uuid.uuid4().hex[:10]
        if not script.created_at:
            script.created_at = datetime.now().isoformat()

        try:
            self.db.conn.execute("""
                INSERT INTO storyboard_scripts (script_id, task_id, strategy_id,
                    cta_text, total_duration_ms, variant_index, created_at)
                VALUES (?, ?, ?, ?, ?, ?, ?)
            """, (
                script.script_id, script.task_id, script.strategy_id,
                script.cta_text, script.total_duration_ms,
                script.variant_index, script.created_at,
            ))

            # 逐镜写入
            for shot in script.shots:
                self.db.conn.execute("""
                    INSERT INTO storyboard_shots (script_id, shot_index, role,
                        duration_ms, description, camera_direction,
                        narration_text,
                        required_product_visibility, required_scene,
                        required_emotion, fallback_notes)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """, (
                    script.script_id, shot.shot_index, shot.role,
                    shot.duration_ms, shot.description, shot.camera_direction,
                    shot.narration_text,
                    shot.required_product_visibility, shot.required_scene,
                    shot.required_emotion, shot.fallback_notes,
                ))

            self.db.conn.commit()
        except Exception:
            self.db.conn.rollback()
            raise
        return script.script_id

    def get_script(self, script_id: str) -> Optional[StoryboardScript]:
        row = self.db.conn.execute(
            "SELECT * FROM storyboard_scripts WHERE script_id = ?", (script_id,)
        ).fetchone()
        if not row:
            return None
        shots = self._get_shots(script_id)
        return self._row_to_script(row, shots)

    def get_scripts_by_task(self, task_id: str) -> list[StoryboardScript]:
        rows = self.db.conn.execute(
            "SELECT * FROM storyboard_scripts WHERE task_id = ? ORDER BY variant_index",
            (task_id,),
        ).fetchall()
        result = []
        for r in rows:
            shots = self._get_shots(r["script_id"])
            result.append(self._row_to_script(r, shots))
        return result

    # ---- 变体 ----

    def insert_variant(self, variant: AdVariant) -> str:
        if not variant.variant_id:
            variant.variant_id = uuid.uuid4().hex[:10]
        if not variant.created_at:
            variant.created_at = datetime.now().isoformat()

        self.db.conn.execute("""
            INSERT INTO ad_variants (variant_id, task_id, script_id, timeline_id,
                output_file, variant_metadata, status, compliance_check_passed, created_at)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, (
            variant.variant_id, variant.task_id, variant.script_id,
            variant.timeline_id, variant.output_file, variant.variant_metadata,
            variant.status, int(variant.compliance_check_passed), variant.created_at,
        ))
        self.db.conn.commit()
        return variant.variant_id

    def get_variants_by_task(self, task_id: str) -> list[AdVariant]:
        rows = self.db.conn.execute(
            "SELECT * FROM ad_variants WHERE task_id = ? ORDER BY created_at",
            (task_id,),
        ).fetchall()
        return [self._row_to_variant(r) for r in rows]

    # ---- 时间线 ----

    def insert_timeline(self, timeline: EditTimeline) -> str:
        if not timeline.timeline_id:
            timeline.timeline_id = uuid.uuid4().hex[:10]

        self.db.conn.execute("""
            INSERT INTO edit_timelines (timeline_id, script_id, shots, bgm_file,
                subtitle_tracks, cta_overlay, variant_metadata)
            VALUES (?, ?, ?, ?, ?, ?, ?)
        """, (
            timeline.timeline_id, timeline.script_id,
            json.dumps([vars(s) for s in timeline.shots], ensure_ascii=False),
            timeline.bgm_file,
            timeline.subtitle_tracks, timeline.cta_overlay,
            timeline.variant_metadata,
        ))
        self.db.conn.commit()
        return timeline.timeline_id

    def get_timeline(self, timeline_id: str) -> Optional[EditTimeline]:
        """按 ID 读回时间线（shots 反序列化，variant_metadata 含重渲染信息）"""
        row = self.db.conn.execute(
            "SELECT * FROM edit_timelines WHERE timeline_id = ?",
            (timeline_id,),
        ).fetchone()
        return self._row_to_timeline(row) if row else None

    @staticmethod
    def _row_to_timeline(row) -> EditTimeline:
        shots = [ShotMatchResult(**s) for s in json.loads(row["shots"] or "[]")]
        return EditTimeline(
            timeline_id=row["timeline_id"],
            script_id=row["script_id"],
            shots=shots,
            bgm_file=row["bgm_file"] or "",
            subtitle_tracks=row["subtitle_tracks"] or "",
            cta_overlay=row["cta_overlay"] or "",
            variant_metadata=row["variant_metadata"] or "",
        )

    # ---- 辅助 ----

    def _get_shots(self, script_id: str) -> list[StoryboardShot]:
        rows = self.db.conn.execute(
            "SELECT * FROM storyboard_shots WHERE script_id = ? ORDER BY shot_index",
            (script_id,),
        ).fetchall()
        return [StoryboardShot(
            id=r["id"], script_id=r["script_id"], shot_index=r["shot_index"],
            role=r["role"], duration_ms=r["duration_ms"], description=r["description"],
            camera_direction=r["camera_direction"], narration_text=r["narration_text"],
            required_product_visibility=r["required_product_visibility"],
            required_scene=r["required_scene"],
            required_emotion=r["required_emotion"],
            fallback_notes=r["fallback_notes"],
        ) for r in rows]

    @staticmethod
    def _row_to_product(row) -> ProductProfile:
        return ProductProfile(
            product_id=row["product_id"], name=row["name"], category=row["category"],
            key_selling_points=row["key_selling_points"],
            target_audience=row["target_audience"], pain_points=row["pain_points"],
            brand_tone=row["brand_tone"], prohibited_words=row["prohibited_words"],
            avg_price_range=row["avg_price_range"], competitors=row["competitors"],
            notes=row["notes"], created_at=row["created_at"], updated_at=row["updated_at"],
        )

    @staticmethod
    def _row_to_task(row) -> ProjectTask:
        return ProjectTask(
            task_id=row["task_id"], product_id=row["product_id"],
            platform=row["platform"], account_id=row["account_id"],
            target_duration_ms=row["target_duration_ms"],
            variant_count=row["variant_count"], status=row["status"],
            strategy_id=row["strategy_id"], created_at=row["created_at"],
            completed_at=row["completed_at"], notes=row["notes"],
        )

    @staticmethod
    def _row_to_strategy(row) -> CreativeStrategy:
        signals = {}
        try:
            signals = json.loads(row["source_signals"] or "{}")
        except (json.JSONDecodeError, TypeError):
            signals = {}
        return CreativeStrategy(
            strategy_id=row["strategy_id"], task_id=row["task_id"],
            narrative_type=row["narrative_type"], hook_type=row["hook_type"],
            pace_style=row["pace_style"], tone=row["tone"],
            key_message=row["key_message"], target_emotion=row["target_emotion"],
            reasoning=row["reasoning"], source_signals=row["source_signals"],
            specific_angle=signals.get("specific_angle", ""),
            target_scenario=signals.get("target_scenario", ""),
            opening_style=signals.get("opening_style", ""),
            emotion_arc=signals.get("emotion_arc", ""),
            differentiation_hints=json.dumps(
                signals.get("differentiation_hints", []), ensure_ascii=False),
            created_at=row["created_at"],
        )

    @staticmethod
    def _row_to_script(row, shots: list[StoryboardShot]) -> StoryboardScript:
        return StoryboardScript(
            script_id=row["script_id"], task_id=row["task_id"],
            strategy_id=row["strategy_id"], shots=shots,
            cta_text=row["cta_text"],
            total_duration_ms=row["total_duration_ms"],
            variant_index=row["variant_index"], created_at=row["created_at"],
        )

    @staticmethod
    def _row_to_variant(row) -> AdVariant:
        return AdVariant(
            variant_id=row["variant_id"], task_id=row["task_id"],
            script_id=row["script_id"], timeline_id=row["timeline_id"],
            output_file=row["output_file"], variant_metadata=row["variant_metadata"],
            status=row["status"],
            compliance_check_passed=bool(row["compliance_check_passed"]),
            created_at=row["created_at"],
        )
