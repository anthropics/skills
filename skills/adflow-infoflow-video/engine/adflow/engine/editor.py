"""
剪辑执行引擎
- 素材裁剪 + 拼接
- BGM 叠加
- 字幕叠加
- 多比例输出（9:16 / 16:9 / 1:1）
- 输出 H.264 MP4
"""

import os
import json
import logging
import subprocess
import tempfile
import uuid
from dataclasses import dataclass
from typing import Optional

from moviepy import (
    VideoFileClip, AudioFileClip, CompositeVideoClip, ColorClip,
    concatenate_videoclips,
)
from moviepy.audio.fx import AudioFadeIn, AudioFadeOut

from adflow.config_loader import config
from adflow.engine.subtitle_renderer import (
    SubtitleBlock, SubtitleStyle, build_subtitle_track,
)
from adflow.utils.ffmpeg_finder import get_ffmpeg_cmd, get_ffprobe_cmd
from adflow.utils.font_resolver import resolve_subtitle_font

logger = logging.getLogger("adflow.editor")


def _resolve_border_color(color) -> tuple:
    """把边框配色转 RGB tuple。moviepy 2.x 的 ColorClip 拒绝字符串颜色(如 'white')。

    支持颜色名('white')、hex('#ffffff')、'rgb(255,255,255)'；已是 tuple 直接透传。
    解析失败兜底白色——边框配色错误不应阻断出片。
    """
    if isinstance(color, (tuple, list)):
        return tuple(color[:3])
    try:
        from PIL import ImageColor

        return ImageColor.getrgb(color)
    except Exception:
        return (255, 255, 255)


# HDR 传输曲线（HLG / PQ）：转码时需 zscale 做色彩空间转换到 bt709，否则发灰
_HDR_TRANSFERS = ("arib-std-b67", "smpte2084", "smpte428", "smpte428-1")


def _is_hdr_transfer(color_transfer: str) -> bool:
    """是否为 HDR 传输曲线（HLG/PQ）"""
    return (color_transfer or "") in _HDR_TRANSFERS


@dataclass
class ClipSegment:
    """一个剪辑片段"""
    file_path: str
    start_ms: int = 0
    end_ms: int = 0           # 0 表示到末尾
    volume: float = 1.0       # 音量倍率（1.0=原声）
    narration_text: str = ""  # 对应口播文案（供峰值检测语义匹配）
    is_hook: bool = False     # 钩子镜头标记（强制峰值检测）
    # 子片段重组（防判重）：[(起ms, 止ms), ...] 素材内绝对时间；
    # 非空时按序拼接各子段成一个镜头，忽略 start_ms/end_ms 的裁剪
    sub_ranges: list = None


@dataclass
class EditJob:
    """一次剪辑任务的所有参数"""
    segments: list[ClipSegment]
    output_path: str
    bgm_file: str = ""
    bgm_volume: float = 0.15       # BGM 音量 -16dB（0-1，背景不抢戏）
    narration_file: str = ""        # AI 配音文件
    narration_volume: float = 0.7   # 配音音量（0-1，峰值留余量给 loudnorm）
    subtitles: list[SubtitleBlock] = None
    smart_mix: bool = False         # 智能混排（CLIP+动作+BGM卡点）
    smart_mix_bpm: float = 120.0    # 智能混排BPM
    remove_voice: bool = False      # 去除素材人声（通道相位抵消）
    normalize_loudness: bool = True # 响度标准化 -14 LUFS（短视频平台推荐）
    target_width: int = 1080
    target_height: int = 1920
    fps: int = 30
    video_codec: str = "libx264"
    audio_codec: str = "aac"
    crf: int = 23
    subtitle_style: SubtitleStyle = None
    used_shot_count: int = 0  # 实际使用的镜头数（配音/2.5s），丢弃的镜头不记录使用
    post_vf: str = ""  # 后处理滤镜链（调色+去重），非空则并入主渲染单次编码
    # ── 数字人画中画（可选，空=不叠加）──
    digital_human_video: str = ""       # 数字人说话视频路径
    pip_position: str = "bottom_right"  # top_left/top_right/bottom_left/bottom_right
    pip_margin: int = 20                # 距边缘像素
    pip_border_color: str = "white"     # 矩形边框颜色
    pip_border_width: int = 3           # 矩形边框宽度
    pip_scale: float = 1 / 3            # 宽高缩放比例（各 1/3 = 面积约 1/9）


class VideoEditor:
    """视频剪辑引擎"""

    def __init__(self):
        self.editing_cfg = config.editing_config
        self.sub_cfg = self.editing_cfg.get("subtitle", {})
        self._temp_files: list[str] = []  # 降级预处理的临时文件，导出后清理

    def edit(self, job: EditJob) -> str:
        """
        执行剪辑任务，返回输出文件路径
        """
        if not job.segments:
            raise ValueError("至少需要一个素材片段")

        # 确保输出目录存在
        os.makedirs(os.path.dirname(job.output_path), exist_ok=True)

        # 0. 智能混排（可选）
        if job.smart_mix and len(job.segments) > 2:
            try:
                from adflow.engine.smart_mixer import SmartMixer, ClipCandidate
                mixer = SmartMixer()
                candidates = []
                for i, seg in enumerate(job.segments):
                    dur_ms = (sum(max(e - s, 0) for s, e in seg.sub_ranges)
                              if seg.sub_ranges
                              else (seg.end_ms - seg.start_ms
                                    if seg.end_ms > seg.start_ms else 3000))
                    candidates.append(ClipCandidate(
                        file_path=seg.file_path,
                        duration_sec=dur_ms / 1000.0,
                        index=i,
                    ))
                total_dur = sum(c.duration_sec for c in candidates)
                # 自动检测 BGM 实际 BPM
                actual_bpm = job.smart_mix_bpm
                if job.bgm_file and os.path.exists(job.bgm_file):
                    actual_bpm = VideoEditor._detect_bpm(job.bgm_file)
                    if actual_bpm != job.smart_mix_bpm:
                        logging.getLogger("adflow.editor").info(
                            "BGM BPM: 检测=%.0f, 默认=%.0f", actual_bpm, job.smart_mix_bpm)
                ordered = mixer.plan(
                    candidates, target_duration_sec=total_dur,
                    bgm_bpm=actual_bpm,
                )
                new_segments = []
                for oc in ordered:
                    orig = job.segments[oc.index]
                    new_segments.append(orig)
                job.segments = new_segments
                logger.info(f"[Editor] 智能混排: {len(candidates)}→{len(new_segments)}片段")
            except Exception as e:
                logger.warning(f"[Editor] 智能混排跳过: {e}")

        # 1. 加载并裁剪各片段（同视频不重复）
        clips = []
        loaded_sources = set()
        for seg in job.segments:
            # 同一视频内不重复使用同一素材（窗口或子段组合任一不同即算不同用法）
            src_key = f"{seg.file_path}_{seg.start_ms}_{seg.end_ms}_{seg.sub_ranges}"
            if src_key in loaded_sources:
                logger.info(f"[Editor] 跳过重复: {os.path.basename(seg.file_path)}")
                continue
            loaded_sources.add(src_key)
            clip = self._load_and_trim(seg, job.target_width, job.target_height)
            if clip is not None:
                clips.append(clip)

        if not clips:
            raise RuntimeError("没有有效素材可以剪辑")

        # 2. 拼接
        if len(clips) == 1:
            final = clips[0]
        else:
            final = concatenate_videoclips(clips, method="compose")

        # 3. 配音为主时钟：视频太长就裁掉，不够就填充/慢放兜底
        if job.narration_file and os.path.exists(job.narration_file):
            try:
                nar_clip = AudioFileClip(job.narration_file)
                nar_dur = nar_clip.duration
                nar_clip.close()
                shot_dur = self.editing_cfg.get("shot_duration_ms", 2500) / 1000.0
                if nar_dur <= 0:
                    pass
                elif final.duration > nar_dur + 0.05:
                    # 视频比配音长 → 按镜头时长保留前 N 个完整镜头（不硬切）
                    target_n = max(1, round(nar_dur / shot_dur))
                    if target_n < len(clips):
                        from moviepy import concatenate_videoclips as _concat
                        final = _concat(clips[:target_n], method="compose")
                        job.used_shot_count = target_n  # 丢弃的镜头不记录使用
                        # 精确对齐配音：前 N 镜总长可能略超配音，裁掉多余（<一个镜头）
                        if final.duration > nar_dur + 0.05:
                            final = final.subclipped(0, nar_dur)
                    else:
                        final = final.subclipped(0, nar_dur)
                elif final.duration < nar_dur - 0.5:
                    # 视频比配音短 → 从素材库挑未用镜头填充（不重复、不拉伸）
                    gap = nar_dur - final.duration
                    extra_clips = self._fill_from_library(
                        job, gap, {seg.file_path for seg in job.segments})
                    if extra_clips:
                        from moviepy import concatenate_videoclips as _concat
                        clips = clips + extra_clips
                        final = _concat(clips, method="compose")
                # 兜底：视频仍比配音短（含 <0.5s 盲区）→ 慢放兜底（仅 1.5~2s 素材例外）
                if final.duration < nar_dur - 0.05:
                    final = self._slowdown_last_clip(clips, nar_dur)
            except Exception as e:
                logging.getLogger("adflow.editor").error(
                    "配音对齐失败，视频可能与配音长度不一致: %s", e)

        # 4. 处理音频（BGM 叠加 + 原声保留）
        final = self._mix_audio(final, job)

        # 5. 叠加数字人画中画（底）与字幕（顶），字幕始终在最上层
        final = self._overlay_pip(final, job)
        if job.subtitles:
            final = self._overlay_subtitles(final, job)

        # 6. 导出
        # 注意: loudnorm 滤镜与 MoviePy 内部 -c:a copy 冲突，
        # 响度标准化在音频混合阶段已通过音量参数控制
        try:
            ffmpeg_params = [
                "-crf", str(job.crf), "-pix_fmt", "yuv420p",
                "-movflags", "+faststart",
                "-g", "60",
                "-profile:v", "high", "-level", "4.1",
                "-colorspace", "bt709", "-color_primaries", "bt709",
                "-color_trc", "bt709",
                "-ar", "48000",
            ]
            if job.post_vf:
                # 调色+去重滤镜链并入主渲染单次编码，替代二次编码（省一次全量重编码）
                ffmpeg_params += ["-vf", job.post_vf]
            final.write_videofile(
                job.output_path,
                fps=job.fps,
                codec=job.video_codec,
                audio_codec=job.audio_codec,
                preset="medium",
                bitrate=None,
                threads=4,
                logger=None,
                ffmpeg_params=ffmpeg_params,
            )

            # 8. 后处理：人声移除（通道相位抵消）
            if job.remove_voice:
                self._remove_voice_from_video(job.output_path)

            # 9. 后处理：响度标准化（目标 -14 LUFS，短视频平台推荐）
            if job.normalize_loudness:
                self._normalize_loudness(job.output_path)

            return job.output_path
        finally:
            # 清理：无论导出成败都释放句柄、删除临时文件
            final.close()
            for c in clips:
                c.close()
            for p in self._temp_files:
                try:
                    os.remove(p)
                except OSError:
                    pass
            self._temp_files.clear()

    def _fill_from_library(self, job: EditJob, gap: float,
                           used_paths: set[str]) -> list[VideoFileClip]:
        """从素材库挑未使用镜头填充 gap（每个 2-3 秒，不重复）。

        从数据库查素材（而非扫磁盘），避免挑到「清空素材库」后磁盘残留的旧文件。
        """
        import random

        used_abs = {os.path.abspath(p) for p in used_paths}
        try:
            from adflow.db.material_repo import MaterialRepo
            records = MaterialRepo().get_all(limit=200)
        except Exception:
            return []
        available = [
            r.file_path for r in records
            if r.file_path and os.path.exists(r.file_path)
            and os.path.abspath(r.file_path) not in used_abs
        ]
        random.shuffle(available)

        extra: list[VideoFileClip] = []
        remaining = gap
        for f in available:
            if remaining <= 0.3:
                break
            seg = ClipSegment(
                file_path=f, start_ms=0, end_ms=2500,
                volume=1.0, narration_text="", is_hook=False)
            clip = self._load_and_trim(seg, job.target_width, job.target_height)
            if clip is None:
                continue
            if clip.duration > remaining:
                clip = clip.subclipped(0, remaining)
            extra.append(clip)
            remaining -= clip.duration
        return extra

    def _slowdown_last_clip(self, clips: list, target_dur: float):
        """慢放兜底：最后镜头素材 1.5~2s 且无更长素材时，慢放到 2s（唯一例外）"""
        from moviepy import concatenate_videoclips as _concat
        if not clips:
            return None
        last = clips[-1]
        # 只在素材 1.5~2s 之间才慢放（其余情况不慢放，不黑幕不变速）
        if not (1.5 <= last.duration <= 2.0):
            return _concat(clips, method="compose")
        prefix = sum(c.duration for c in clips[:-1])
        slow_to = min(2.0, target_dur - prefix)
        if slow_to <= last.duration:
            return _concat(clips, method="compose")
        new_last = last.with_duration(slow_to)
        final = _concat(clips[:-1] + [new_last], method="compose")
        return final

    def _load_and_trim(
        self, seg: ClipSegment, target_w: int, target_h: int
    ) -> Optional[VideoFileClip]:
        """加载素材，裁剪时间段，缩放到目标分辨率，自动回正旋转视频"""
        source_path = seg.file_path

        # ── 峰值检测：钩子镜头或从头开始的镜头，找最有冲击力的片段 ──
        # （子片段重组的镜头窗口是特意挑的，不再跑峰值）
        if seg.sub_ranges:
            pass
        elif seg.is_hook or (seg.start_ms == 0 and seg.end_ms > 3000):
            try:
                from adflow.engine.smart_mixer import SmartMixer
                peak_start, peak_end = SmartMixer.find_peak_segment(
                    source_path,
                    target_dur_sec=(seg.end_ms - seg.start_ms) / 1000.0,
                    semantic_prompt=seg.narration_text,
                )
                seg.start_ms = int(peak_start * 1000)
                seg.end_ms = int(peak_end * 1000)
            except Exception:
                pass  # 峰值检测失败，用原始时间

        # 检测方向（三层：元数据 + 宽高比 + 人脸），替代旧 VideoProbe + 硬编码 270
        try:
            from adflow.engine.video_orientation import VideoOrientationDetector
            orient = VideoOrientationDetector.detect(source_path, target_w, target_h)
            rotation = orient["rotation"]
            crop_region = orient["crop_region"]
            if rotation:
                logger.info(f"[Editor] 检测到旋转 {rotation}°: {os.path.basename(source_path)}")
        except Exception:
            rotation = 0
            crop_region = None

        # 所有需要缩放或旋转的素材统一走 FFmpeg 预处理
        downscaled_path = self._pre_downscale_if_needed(
            source_path, target_w, target_h, rotation=rotation, crop_region=crop_region)
        if downscaled_path:
            source_path = downscaled_path
            skip_resize = True
        else:
            skip_resize = False

        try:
            clip = VideoFileClip(source_path)
        except Exception as e:
            logger.warning(f"[Editor] 无法加载素材: {source_path} — {e}")
            return None

        # 时间段裁剪（镜头时长限制 ≤ 2.5s，铁律：2-3s 一个镜头）
        if seg.sub_ranges:
            # 子片段重组（防判重）：按 sub_ranges 顺序拼各子段成一个"新镜头"
            sub_clips = []
            for (s_ms, e_ms) in seg.sub_ranges:
                ts = s_ms / 1000.0
                te = min(e_ms / 1000.0, clip.duration)
                if te > ts:
                    sub_clips.append(clip.subclipped(ts, te))
            if not sub_clips:
                clip.close()
                return None
            clip = (sub_clips[0] if len(sub_clips) == 1
                    else concatenate_videoclips(sub_clips))
        elif seg.start_ms > 0 or seg.end_ms > 0:
            t_start = seg.start_ms / 1000.0
            t_end = seg.end_ms / 1000.0 if seg.end_ms > 0 else clip.duration
            shot_dur = self.editing_cfg.get("shot_duration_ms", 2500) / 1000.0
            t_end = min(t_end, clip.duration, t_start + shot_dur * 1.5)
            if t_end <= t_start:
                clip.close()
                return None
            clip = clip.subclipped(t_start, t_end)

        # ── 30ms 音频渐变消除段边界爆音（参考 video-use 硬规则 #3）──
        clip_dur = clip.duration
        if clip_dur > 0.1 and clip.audio is not None:
            try:
                clip = clip.with_effects([
                    AudioFadeIn(0.006),
                    AudioFadeOut(0.006),
                ])
            except Exception:
                pass  # 渐变失败不影响主流程

        # 缩放 + 裁剪到目标比例（已由 FFmpeg 处理过的跳过此步）
        if not skip_resize:
            clip = self._resize_to_target(clip, target_w, target_h)

        # 音量调整
        if seg.volume != 1.0:
            clip = clip.with_volume_scaled(seg.volume)

        return clip

    def _pre_downscale_if_needed(self, src: str, target_w: int, target_h: int,
                                 rotation: int = 0,
                                 crop_region: dict | None = None) -> str | None:
        """FFmpeg 预处理：缩放 + 旋转回正 + 居中裁剪。
        返回临时文件路径，源分辨率与目标一致且无旋转则返回 None"""
        try:
            probe = subprocess.run(
                [get_ffprobe_cmd(), "-v", "quiet", "-print_format", "json",
                 "-show_streams", src],
                capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=15,
            )
            if probe.returncode != 0 or not probe.stdout.strip():
                return None
            streams = json.loads(probe.stdout).get("streams", [])
            video_streams = [s for s in streams if s.get("codec_type") == "video"]
            if not video_streams:
                return None
            src_w = video_streams[0].get("width", 0)
            src_h = video_streams[0].get("height", 0)
            color_transfer = video_streams[0].get("color_transfer", "") or ""
            if not src_w or not src_h:
                return None

            # 宽高比容差 2% + 无旋转 + 无人脸裁剪 + 非 HDR → 跳过
            # （HDR 素材即使尺寸匹配也必须走 FFmpeg 做色彩空间转换，否则发灰）
            if (rotation == 0 and crop_region is None and
                    not _is_hdr_transfer(color_transfer) and
                    abs(src_w - target_w) <= target_w * 0.02 and
                    abs(src_h - target_h) <= target_h * 0.02):
                return None

            label = f"{src_w}x{src_h}"
            if rotation:
                label += f" 旋转{rotation}°"
            if _is_hdr_transfer(color_transfer):
                label += f" HDR({color_transfer})"
            logger.info(f"[Editor] {label} → {target_w}x{target_h} (FFmpeg)")
            return self._ffmpeg_downscale(
                src, target_w, target_h, rotation=rotation, crop_region=crop_region,
                color_transfer=color_transfer)
        except Exception as e:
            logger.warning(f"[Editor] 预降级失败，使用原文件: {e}")
            return None

    def _ffmpeg_downscale(self, src: str, target_w: int, target_h: int,
                          rotation: int = 0,
                          crop_region: dict | None = None,
                          color_transfer: str = "") -> str:
        """FFmpeg 旋转回正 + 填满画面（无黑边），返回临时文件路径"""
        filters = []
        # 旋转: 90→顺时针90°, 270→逆时针90°
        if rotation == 90:
            filters.append("transpose=1")
        elif rotation == 270:
            filters.append("transpose=2")
        elif rotation == 180:
            filters.append("transpose=2,transpose=2")

        if crop_region:
            # 人脸优先裁剪：scale 到填满尺寸 → 偏移裁剪（坐标=旋转后坐标系）
            filters.append(
                f"scale={crop_region['scaled_w']}:{crop_region['scaled_h']},"
                f"crop={crop_region['w']}:{crop_region['h']}:{crop_region['x']}:{crop_region['y']}"
            )
        else:
            # 缩放填满: increase=放大覆盖+居中裁剪（无黑边）；decrease 缩小留黑边会裁不出
            filters.append(
                f"scale={target_w}:{target_h}:force_original_aspect_ratio=increase,"
                f"crop={target_w}:{target_h}"
            )
        # HDR（HLG/PQ）→ SDR 色彩空间转换：只转色域(bt2020→bt709)与矩阵，不动传输曲线
        # （灰蒙是「颜色/色域」问题而非「亮度」问题：保留 HLG 亮度，仅还原饱和度）
        if _is_hdr_transfer(color_transfer):
            filters.append("zscale=p=bt709:m=bt709:r=tv,format=yuv420p")
        vf = ",".join(filters)

        tmp_dir = os.path.join(config.output_dir, "_temp")
        os.makedirs(tmp_dir, exist_ok=True)
        tmp_path = os.path.join(tmp_dir, f"ds_{uuid.uuid4().hex[:8]}.mp4")
        self._temp_files.append(tmp_path)

        result = subprocess.run(
            [get_ffmpeg_cmd(), "-y", "-noautorotate", "-i", src,
             "-vf", vf,
             "-c:v", "libx264", "-preset", "ultrafast", "-crf", "18",
             tmp_path],
            capture_output=True, timeout=120,
        )
        if result.returncode != 0:
            raise RuntimeError(f"FFmpeg 降级失败: {result.stderr.decode()[-200:]}")
        return tmp_path

    @staticmethod
    def _resize_to_target(clip: VideoFileClip, target_w: int, target_h: int) -> VideoFileClip:
        """等比缩放 + 居中裁剪到目标分辨率"""
        src_w, src_h = clip.size

        # 计算缩放比（按较大边适配）
        scale_w = target_w / src_w
        scale_h = target_h / src_h
        scale = max(scale_w, scale_h)

        new_w = int(src_w * scale)
        new_h = int(src_h * scale)
        clip = clip.resized((new_w, new_h))

        # 居中裁剪
        x_center = new_w / 2
        y_center = new_h / 2
        x1 = max(0, int(x_center - target_w / 2))
        y1 = max(0, int(y_center - target_h / 2))

        clip = clip.cropped(x1=x1, y1=y1, width=target_w, height=target_h)
        return clip

    @staticmethod
    def _detect_bpm(bgm_path: str) -> float:
        """用 librosa 检测 BGM 实际 BPM，失败返回 120"""
        try:
            import librosa
            y, sr = librosa.load(bgm_path, sr=None, duration=30)
            tempo, _ = librosa.beat.beat_track(y=y, sr=sr)
            bpm = float(tempo[0] if hasattr(tempo, '__len__') else tempo)
            return max(60, min(200, bpm))
        except Exception:
            return 120.0

    @staticmethod
    def _remove_voice_from_video(video_path: str) -> None:
        """后处理：用通道相位抵消去除视频中的人声（保留环境音）

        原理：人声通常在立体声中央（左右声道相同），
        L-R 可抵消中央声音，保留两侧的环境音。
        """
        import subprocess, tempfile, shutil
        from adflow.utils.ffmpeg_finder import get_ffmpeg_cmd

        tmp_path = video_path + ".temp.mp4"
        try:
            result = subprocess.run(
                [get_ffmpeg_cmd(), "-y",
                 "-i", video_path,
                 "-af", "pan=stereo|FL=FL-0.6*FR|FR=FR-0.6*FL,volume=0.7",
                 "-c:v", "copy",
                 tmp_path],
                capture_output=True, timeout=120,
            )
            if result.returncode == 0 and os.path.exists(tmp_path):
                shutil.move(tmp_path, video_path)
            else:
                logging.getLogger("adflow.editor").warning(
                    "人声移除失败，保留原音轨")
        except Exception as e:
            logging.getLogger("adflow.editor").warning(
                "人声移除异常: %s", e)

    @staticmethod
    def _normalize_loudness(video_path: str) -> None:
        """后处理：FFmpeg loudnorm 双遍响度标准化到 -14 LUFS（短视频平台推荐）"""
        import json
        import subprocess, shutil
        from adflow.utils.ffmpeg_finder import get_ffmpeg_cmd

        tmp_path = video_path + ".norm.mp4"
        try:
            # 第一遍：测量（不传 measured_* 时走动态归一化，偏差 2-4 LU）
            probe = subprocess.run(
                [get_ffmpeg_cmd(), "-i", video_path,
                 "-af", "loudnorm=I=-14:LRA=11:TP=-1.5:print_format=json",
                 "-f", "null", "-"],
                capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=120,
            )
            measured = {}
            for line in probe.stderr.splitlines():
                line = line.strip()
                if line.startswith("{") and "input_i" in line:
                    try:
                        measured = json.loads(line)
                    except Exception:
                        pass
                    break

            # 第二遍：线性归一化
            filter_str = "loudnorm=I=-14:LRA=11:TP=-1.5:linear=true"
            if measured:
                filter_str += (
                    f":measured_I={measured.get('input_i', '')}"
                    f":measured_TP={measured.get('input_tp', '')}"
                    f":measured_LRA={measured.get('input_lra', '')}"
                    f":measured_thresh={measured.get('input_thresh', '')}")
            result = subprocess.run(
                [get_ffmpeg_cmd(), "-y", "-i", video_path,
                 "-af", filter_str, "-c:v", "copy", tmp_path],
                capture_output=True, timeout=120,
            )
            if result.returncode == 0 and os.path.exists(tmp_path):
                shutil.move(tmp_path, video_path)
        except Exception as e:
            logging.getLogger("adflow.editor").debug(
                "响度标准化跳过: %s", e)

    def _mix_audio(self, video: VideoFileClip, job: EditJob) -> VideoFileClip:
        """音频混合：原声 + 配音（主导） + BGM（背景）"""
        total_duration = video.duration
        from moviepy import CompositeAudioClip

        audio_tracks = []

        # 原声保留（压低音量，垫底不抢配音）
        if video.audio is not None:
            audio_tracks.append(video.audio.with_volume_scaled(0.12))

        # AI 配音 / BGM — 长度不够就用原长度，CompositeAudioClip 会自动静音尾部
        if job.narration_file and os.path.exists(job.narration_file):
            try:
                narration = AudioFileClip(job.narration_file)
                narration = narration.with_volume_scaled(job.narration_volume)
                audio_tracks.append(narration)
            except Exception as e:
                logger.warning(f"[Editor] 配音加载失败: {e}")

        if job.bgm_file and os.path.exists(job.bgm_file):
            try:
                bgm = AudioFileClip(job.bgm_file)
                bgm = bgm.with_volume_scaled(job.bgm_volume)
                if bgm.duration > total_duration:
                    bgm = bgm.subclipped(0, total_duration)
                elif bgm.duration < total_duration:
                    # BGM 短于视频 → 循环拼接，避免后半段无声
                    from moviepy import concatenate_audioclips
                    loops = int(total_duration / bgm.duration) + 1
                    bgm = concatenate_audioclips([bgm] * loops).subclipped(
                        0, total_duration)
                audio_tracks.append(bgm)
            except Exception as e:
                logger.warning(f"[Editor] BGM 加载失败: {e}")

        if audio_tracks:
            video = video.with_audio(CompositeAudioClip(audio_tracks))

        return video

    def _overlay_subtitles(self, video: VideoFileClip, job: EditJob) -> CompositeVideoClip:
        """叠加字幕"""
        style = job.subtitle_style or SubtitleStyle(
            font=resolve_subtitle_font(self.sub_cfg.get("font", "")),
            font_size=self.sub_cfg.get("font_size", 48),
            color=self.sub_cfg.get("color", "white"),
            stroke_color=self.sub_cfg.get("stroke_color", "black"),
            stroke_width=self.sub_cfg.get("stroke_width", 2),
            fixed_y=self.sub_cfg.get("fixed_y", 0),
            safe_margin_bottom=self.sub_cfg.get("safe_margin_bottom", 120),
            safe_margin_sides=self.sub_cfg.get("safe_margin_sides", 80),
            # CTA 句颜色接 config：原版写死红色，红/暖色素材上红字看不见（像字幕缺了）
            cta_color=self.sub_cfg.get("cta_color", "white"),
        )

        subtitle_clips = build_subtitle_track(
            job.subtitles,
            video_width=job.target_width,
            video_height=job.target_height,
            video_duration_sec=video.duration,
            style=style,
        )

        if not subtitle_clips:
            return video

        composite = CompositeVideoClip([video] + subtitle_clips)
        return composite

    def _overlay_pip(self, video, job) -> CompositeVideoClip:
        """叠加数字人画中画（一期：矩形小窗带边框）。

        数字人视频缺失/加载失败 → 返回原 video（no-op，降级为无数字人）。
        """
        if not job.digital_human_video or not os.path.exists(job.digital_human_video):
            return video

        try:
            pip = VideoFileClip(job.digital_human_video)
        except Exception as e:
            logger.warning("[数字人] 画中画加载失败: %s", e)
            return video

        # 等比缩放（宽高各 pip_scale，面积约 pip_scale² = 1/9）
        pip = pip.resized(job.pip_scale)
        pip = pip.with_duration(min(pip.duration, video.duration))

        pip_w, pip_h = pip.size
        W, H = job.target_width, job.target_height
        margin = job.pip_margin

        anchors = {
            "top_left": (margin, margin),
            "top_right": (W - pip_w - margin, margin),
            "bottom_left": (margin, H - pip_h - margin),
            "bottom_right": (W - pip_w - margin, H - pip_h - margin),
        }
        x, y = anchors.get(job.pip_position, anchors["bottom_right"])
        pip = pip.with_position((x, y))

        # 矩形边框（一期无抠像，用 ColorClip 包一圈）
        if job.pip_border_width > 0:
            try:
                bw = job.pip_border_width
                border = ColorClip(
                    size=(pip_w + 2 * bw, pip_h + 2 * bw),
                    color=_resolve_border_color(job.pip_border_color),
                ).with_duration(pip.duration)
                border = border.with_position((x - bw, y - bw))
                return CompositeVideoClip([video, border, pip])
            except Exception as e:
                logger.warning("[数字人] 边框生成失败，退化无边框: %s", e)

        return CompositeVideoClip([video, pip])
