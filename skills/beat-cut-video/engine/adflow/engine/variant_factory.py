"""
变体工厂
- 同一套脚本 × 不同素材 × 不同 BGM
- 批量生产多个视频变体
- 智能过滤不合理组合
"""

import os
import json
import logging
from dataclasses import dataclass

logger = logging.getLogger("adflow.render")
from datetime import datetime

from adflow.models import (
    StoryboardScript, EditTimeline, AdVariant,
    MaterialRecord,
)
from adflow.engine.editor import VideoEditor, ClipSegment, EditJob
from adflow.engine.subtitle_renderer import SubtitleBlock
from adflow.config_loader import config


def _daily_output_path(output_dir: str, name_prefix: str = "") -> str:
    """生成按日期组织的输出路径: output/0729/0729-N.mp4

    name_prefix 非空时改为前缀命名: output/0729/{name_prefix}01.mp4（序号两位补零）。
    自动检测当天已有文件数，递增编号。
    """
    today = datetime.now().strftime("%m%d")
    day_dir = os.path.join(output_dir, today)
    os.makedirs(day_dir, exist_ok=True)

    if name_prefix:
        # 前缀命名：统计当天该前缀已有文件数 → 序号从 01 递增
        existing = [f for f in os.listdir(day_dir)
                    if f.startswith(name_prefix) and f.endswith(".mp4")]
        next_num = len(existing) + 1
        return os.path.join(day_dir, f"{name_prefix}{next_num:02d}.mp4")

    # 统计当天已有文件数 → 编号从 N+1 开始
    existing = [f for f in os.listdir(day_dir)
                if f.startswith(today) and f.endswith(".mp4")]
    next_num = len(existing) + 1

    return os.path.join(day_dir, f"{today}-{next_num}.mp4")


@dataclass
class VariantConfig:
    """单个变体的参数组合"""
    variant_index: int = 0
    hook_material_id: str = ""       # 替换钩子镜头素材（空=不替换）
    bgm_file: str = ""               # 替换BGM
    subtitle_style: str = "default"  # 字幕样式


class VariantFactory:
    """变体工厂：1套脚本 → N个视频"""

    def __init__(self):
        self.editor = VideoEditor()
        self.output_dir = config.output_dir
        self.name_prefix = ""  # 视频命名前缀（""=默认日期命名；非空=前缀+序号，如「视频01」）

    def produce(
        self,
        script: StoryboardScript,
        base_timeline: EditTimeline,
        variants: list[VariantConfig],
        task_id: str,
        account_id: str = "",
        narration_file: str = "",
        segment_durations: list[int] | None = None,
        pause_durations: list[int] | None = None,
        shot_targets: list | None = None,
        digital_human_video: str = "",
        aspect_ratio: str = "portrait",
        subtitle_alignment: tuple = None,
    ) -> list[AdVariant]:
        """
        批量生产变体
        aspect_ratio: portrait竖屏 / landscape横屏（不再写死读 douyin 配置）
        subtitle_alignment: (字幕文本列表, 语音段[(起ms,止ms)]) — 爆款原声
        0 延迟对齐（文本=用户原文，时间戳=真实语音段），None=走常规字幕链路
        返回产出变体列表
        """
        os.makedirs(self.output_dir, exist_ok=True)
        results = []

        for vc_idx, vc in enumerate(variants):
            # 1. 克隆并修改 timeline
            timeline = self._apply_variant(base_timeline, vc)

            # 1.5 镜头顺序轻度打乱（防判重）：相邻同角色镜头按变体序换位，
            # 首尾（hook/cta）不动；换位不改各镜头时长，字幕时间不受影响
            self._shuffle_shot_order(
                timeline, shot_targets or script.shots, vc_idx)

            # 2. 构建 ClipSegment 列表（镜头目标 ≠ 口播句，narration 从镜头目标取）
            segments = self._timeline_to_segments(timeline, shot_targets or script.shots)

            # 3. 构建字幕（用分段合成的精确时间戳；爆款原声用 0 延迟对齐）
            subtitles = self._build_subtitles(
                script, narration_file, segment_durations or [],
                pause_durations or [], alignment=subtitle_alignment)

            # 4. 构建 EditJob（按日期组织输出）
            # 画幅由用户在出片页选择：竖屏 1080x1920 / 横屏 1920x1080
            if aspect_ratio == "landscape":
                out_w, out_h = 1920, 1080
            else:
                plat_cfg = config.platform_default("douyin")
                out_w, out_h = plat_cfg.get("resolution", [1080, 1920])
            output_path = _daily_output_path(self.output_dir, self.name_prefix)
            dh_cfg = config.get("digital_human", {}) or {}

            job = EditJob(
                segments=segments,
                output_path=output_path,
                bgm_file=vc.bgm_file if vc.bgm_file else base_timeline.bgm_file,
                narration_file=narration_file,
                narration_volume=0.7,
                subtitles=subtitles,
                target_width=out_w,
                target_height=out_h,
                smart_mix=True,       # CLIP启动时已预下载
                smart_mix_bpm=120.0,
                remove_voice=config.get("editing.remove_voice", False),
                normalize_loudness=config.get("editing.normalize_loudness", True),
                digital_human_video=digital_human_video,
                pip_position=dh_cfg.get("pip_position", "bottom_right"),
                pip_margin=int(dh_cfg.get("pip_margin", 20) or 20),
                pip_border_color=dh_cfg.get("pip_border_color", "white"),
                pip_border_width=int(dh_cfg.get("pip_border_width", 3) or 3),
                pip_scale=float(dh_cfg.get("pip_scale", 1 / 3) or 1 / 3),
            )

            # ── 后处理（调色+去重）滤镜链并入主渲染单次编码，省一次全量重编码 ──
            post_vf = self._build_post_vf(script, vc.variant_index)
            if post_vf:
                job.post_vf = post_vf
                job.crf = 20  # 与原二次编码 crf 20 一致，单次编码质量不降级

            # 5. 渲染
            try:
                self.editor.edit(job)

                # ── 导出 EDL（可复现剪辑决策）──
                edl_path = output_path.replace(".mp4", "_edl.json")
                _export_edl(edl_path, script, timeline, job, vc, segments, subtitles)

                # ── 导出独立 SRT（平台自动字幕 / SEO）──
                try:
                    from adflow.engine.subtitle_renderer import subtitles_to_srt
                    srt_path = output_path.replace(".mp4", ".srt")
                    with open(srt_path, "w", encoding="utf-8") as f:
                        f.write(subtitles_to_srt(subtitles))
                except Exception as e:
                    logger.debug("SRT 导出跳过: %s", e)

                # ── 渲染后自检（参考 video-use self-eval）──
                try:
                    from adflow.engine.render_checker import RenderChecker
                    checker = RenderChecker()
                    check_result = checker.check(
                        video_path=output_path,
                        expected_resolution=(job.target_width, job.target_height),
                        expected_duration_ms=script.total_duration_ms,
                        subtitle_count=len(subtitles),
                        edl_path=edl_path,
                    )
                    if not check_result.passed:
                        logger.warning(
                            "渲染自检: %.1f/10 %s",
                            check_result.score, check_result.issues[:3])
                except Exception as e:
                    logger.debug("渲染自检跳过: %s", e)

                # 记录素材使用（防重复 + 滑动窗口统计）
                # 丢弃的镜头（配音长度不够，未实际使用）不记录使用，下次变体优先选
                from adflow.engine.diversity import DiversityController
                dc = DiversityController()
                used_count = job.used_shot_count if job.used_shot_count > 0 else len(timeline.shots)
                for i, shot in enumerate(timeline.shots):
                    if i >= used_count:
                        break
                    if shot.material_id:
                        dc.log_usage(
                            material_id=shot.material_id,
                            variant_id="",
                            shot_position=getattr(shot, 'shot_index', 0),
                            account_id=account_id,
                        )

                variant = AdVariant(
                    task_id=task_id,
                    script_id=script.script_id,
                    timeline_id=timeline.timeline_id,
                    output_file=output_path,
                    variant_metadata=str({
                        "hook_material": vc.hook_material_id,
                        "bgm": os.path.basename(vc.bgm_file) if vc.bgm_file else "default",
                        "style": vc.subtitle_style,
                        "digital_human": os.path.basename(digital_human_video) if digital_human_video else "",
                    }),
                    status="pending_review",
                    compliance_check_passed=False,
                    created_at=datetime.now().isoformat(),
                )
                results.append(variant)
            except Exception as e:
                logging.getLogger("adflow.render").error(
                    f"变体 {vc.variant_index} 渲染失败: {e}", exc_info=True,
                )
                # 跳过失败的变体，继续下一个
                continue

        return results

    def _build_post_vf(self, script, variant_index: int) -> str:
        """收集调色 + 去重滤镜链，返回合并后的 FFmpeg -vf 串（空串=无需后处理）"""
        from adflow.engine.color_grade import ColorGradeEngine
        from adflow.engine.anti_dedup import AntiDedupEngine

        # 调色滤镜
        cg = ColorGradeEngine()
        cg_params = cg.params_from_config()
        if cg_params.is_empty:
            cg_params = cg.params_from_category(
                getattr(script, 'category', ''))
        vf_chain = cg.build_filter_chain(cg_params) if not cg_params.is_empty else ""

        # 去重滤镜
        dedup = AntiDedupEngine()
        dedup_enabled = dedup.cfg.get("enabled", True)
        dedup_params = AntiDedupEngine.generate_dedup_params(variant_index) if dedup_enabled else None
        dedup_vf = dedup.build_video_filter(dedup_params) if dedup_params else ""

        # 合并滤镜链
        return ",".join(f for f in [vf_chain, dedup_vf] if f)

    def generate_combinations(
        self,
        hook_materials: list[MaterialRecord],
        bgm_files: list[str],
        max_variants: int = 12,
    ) -> list[VariantConfig]:
        """
        生成变体组合：钩子素材 × BGM
        智能过滤：
        - 去重（完全相同跳过）
        - 最多 max_variants 个
        """
        combos = []
        idx = 0

        for hook in (hook_materials or [None]):
            for bgm in (bgm_files or [""]):
                if len(combos) >= max_variants:
                    break

                combo = VariantConfig(
                    variant_index=idx,
                    hook_material_id=hook.material_id if hook else "",
                    bgm_file=bgm,
                )
                combos.append(combo)
                idx += 1

            if len(combos) >= max_variants:
                break

        return combos

    @staticmethod
    def _apply_variant(base: EditTimeline, vc: VariantConfig) -> EditTimeline:
        """应用变体参数到时间线"""
        import copy
        timeline = copy.deepcopy(base)

        # 替换钩子镜头素材（仅当 DB 查到才替换，避免 id/file 不一致）
        if vc.hook_material_id:
            from adflow.db.material_repo import MaterialRepo
            repo = MaterialRepo()
            hook_mat = repo.get_by_id(vc.hook_material_id)
            if hook_mat:
                for shot in timeline.shots:
                    if shot.shot_index == 0:
                        shot.material_id = vc.hook_material_id
                        shot.material_file = hook_mat.file_path
                        shot.start_ms = 0
                        shot.end_ms = min(shot.end_ms - shot.start_ms,
                                          hook_mat.duration_ms)
                        shot.sub_ranges = None  # 换了素材，旧窗口作废
                        break
            else:
                logger.warning("钩子素材 %s 在数据库中不存在，跳过替换",
                               vc.hook_material_id)

        # 替换 BGM
        if vc.bgm_file:
            timeline.bgm_file = vc.bgm_file

        return timeline

    @staticmethod
    def _shuffle_shot_order(timeline: EditTimeline, shot_targets: list,
                            vc_idx: int) -> None:
        """镜头顺序轻度打乱（防判重）：相邻同角色镜头两两换位。

        换哪些对由 (script_id, vc_idx) 决定（确定性，可复现）；
        hook（首镜）和 cta（尾镜）不动；换位只改顺序不改时长。
        """
        import random as _random
        if vc_idx <= 0 or len(timeline.shots) < 3:
            return
        roles = {s.shot_index: s.role for s in shot_targets}
        shots = timeline.shots
        rng = _random.Random(f"order|{timeline.script_id}|{vc_idx}")
        i = 1  # 首镜头（hook）不动
        while i < len(shots) - 1:  # 尾镜头（cta）不动
            r1 = roles.get(shots[i].shot_index, "b_roll")
            r2 = roles.get(shots[i + 1].shot_index, "b_roll")
            if (r1 == r2 and r1 not in ("hook", "cta")
                    and rng.random() < 0.5):
                shots[i], shots[i + 1] = shots[i + 1], shots[i]
                i += 2  # 已换位的对不再参与
            else:
                i += 1

    @staticmethod
    def _timeline_to_segments(timeline: EditTimeline, shots: list) -> list[ClipSegment]:
        """时间线 → ClipSegment 列表（shots = 镜头目标列表，供峰值语义匹配）"""
        segments = []
        for shot in timeline.shots:
            if not shot.material_file:
                continue
            # 查找对应镜头的口播文案（供峰值语义匹配）
            narration = ""
            for s in shots:
                if s.shot_index == shot.shot_index:
                    narration = s.narration_text or ""
                    break
            segments.append(ClipSegment(
                file_path=shot.material_file,
                start_ms=shot.start_ms,
                end_ms=shot.end_ms,
                volume=1.0,
                narration_text=narration,
                is_hook=(shot.shot_index == 0),
                sub_ranges=getattr(shot, "sub_ranges", None),
            ))
        return segments

    @staticmethod
    def _build_subtitles(script: StoryboardScript,
                         narration_file: str = "",
                         segment_durations: list[int] | None = None,
                         pause_durations: list[int] | None = None,
                         alignment: tuple = None,
                         ) -> list[SubtitleBlock]:
        """语音同步字幕：LLM分段 → 每段独立配音 → 精确时间戳；CTA 段用 CTA 色"""
        # 1. 收集分段（CTA 口播也是普通字幕，只是用 CTA 色 style='cta'）
        from adflow.engine.resynth import collect_narration_segments
        all_segments, segment_roles = collect_narration_segments(script)
        segment_styles = ['cta' if r == 'cta' else 'default' for r in segment_roles]

        # 0. 爆款原声 0 延迟对齐：文本=用户原文断句，时间戳=真实语音段
        if alignment:
            texts, speech = alignment
            if texts and len(texts) == len(speech):
                cta_text = (script.cta_text or "").strip()
                return [SubtitleBlock(
                    text=t, start_ms=s, end_ms=e,
                    style=("cta" if t.strip() == cta_text else "default"))
                    for t, (s, e) in zip(texts, speech)]

        if not all_segments:
            return []

        # 2. 有精确分段时长 → 直接用（字幕覆盖纯语音，不含段间停顿）
        if segment_durations and len(segment_durations) == len(all_segments):
            subtitles = []
            t = 0
            for i, seg in enumerate(all_segments):
                total_dur = max(segment_durations[i], 300)  # 语音 + 停顿
                pause = (pause_durations[i]
                         if pause_durations and i < len(pause_durations) else 0)
                speech_dur = max(total_dur - pause, 300)  # 纯语音时长
                subtitles.append(SubtitleBlock(
                    text=seg, start_ms=t, end_ms=t + speech_dur,
                    style=segment_styles[i]))
                t += total_dur
            return subtitles

        # 2.5 静音检测对齐（音波「静音-语音-静音」，替代字数比例估算）
        if narration_file and os.path.exists(narration_file):
            try:
                from adflow.engine.subtitle_renderer import detect_speech_segments
                speech = detect_speech_segments(narration_file)
                if speech and len(speech) == len(all_segments):
                    return [SubtitleBlock(
                        text=all_segments[i], start_ms=s_start, end_ms=s_end,
                        style=segment_styles[i])
                        for i, (s_start, s_end) in enumerate(speech)]
            except Exception as e:
                logger.debug("静音检测对齐失败，回退字数估算: %s", e)

        # 3. 回退估算
        audio_dur_ms = 30000
        if narration_file and os.path.exists(narration_file):
            try:
                from moviepy import AudioFileClip
                nac = AudioFileClip(narration_file)
                audio_dur_ms = int(nac.duration * 1000)
                nac.close()
            except Exception:
                pass
        subtitles = []
        t = 0
        for i, seg in enumerate(all_segments):
            dur = max(int(len(seg) / max(len(''.join(all_segments)), 1) * audio_dur_ms), 300)
            subtitles.append(SubtitleBlock(
                text=seg, start_ms=t, end_ms=t + dur, style=segment_styles[i]))
            t += dur
        return subtitles


# ═══════════════════════════════════════
# EDL 导出 — 可复现的剪辑决策文件
# ═══════════════════════════════════════

def _export_edl(edl_path: str, script, timeline, job, variant_config,
                segments: list, subtitles: list) -> str:
    """导出 EDL JSON — 完整记录本次渲染的所有参数，可用于复现

    格式参考 video-use 的 edl.json 设计：
      - 每个镜头记录源文件、入出点、调色参数
      - 字幕记录文本+精确时间戳
      - 音频记录配音+BGM混合参数
    """
    from datetime import datetime

    edl = {
        "version": "1.0",
        "generated_at": datetime.now().isoformat(),
        "output_file": job.output_path,
        "metadata": {
            "script_id": script.script_id,
            "task_id": script.task_id,
            "variant_index": variant_config.variant_index,
        },
        "video": {
            "resolution": [job.target_width, job.target_height],
            "fps": job.fps,
            "codec": job.video_codec,
            "crf": job.crf,
        },
        "timeline": {
            "total_duration_ms": script.total_duration_ms,
            "segments": [],
        },
        "audio": {
            "narration_file": os.path.basename(job.narration_file) if job.narration_file else "",
            "narration_volume": job.narration_volume,
            "bgm_file": os.path.basename(job.bgm_file) if job.bgm_file else "",
            "bgm_volume": job.bgm_volume,
            "audio_codec": job.audio_codec,
        },
        "subtitles": [],
    }

    # 每个镜头的剪辑参数
    for i, seg in enumerate(segments):
        shot_entry = {
            "index": i,
            "source": seg.file_path,
            "start_ms": seg.start_ms,
            "end_ms": seg.end_ms,
            "volume": seg.volume,
        }
        # 关联脚本镜头
        if i < len(script.shots):
            shot = script.shots[i]
            shot_entry["role"] = shot.role
            shot_entry["narration_text"] = shot.narration_text
            shot_entry["duration_ms"] = shot.duration_ms
        edl["timeline"]["segments"].append(shot_entry)

    # 字幕块
    for sub in subtitles:
        edl["subtitles"].append({
            "text": sub.text,
            "start_ms": sub.start_ms,
            "end_ms": sub.end_ms,
            "style": getattr(sub, "style", "default"),
        })

    try:
        with open(edl_path, "w", encoding="utf-8") as f:
            json.dump(edl, f, ensure_ascii=False, indent=2)
        logging.getLogger("adflow.render").info("EDL 已导出: %s", edl_path)
    except Exception as e:
        logging.getLogger("adflow.render").warning("EDL 导出失败: %s", e)

    return edl_path
