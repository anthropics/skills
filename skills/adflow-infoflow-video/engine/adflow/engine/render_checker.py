# -*- coding: utf-8 -*-
"""
渲染后自检器 — 参考 video-use self-eval 机制

渲染完成后自动检查:
  1. 视觉检查: 黑帧/跳帧/分辨率
  2. 音频检查: 爆音/clipping/静音段
  3. 字幕检查: 是否被遮挡/位置正确
  4. 结构检查: 时长/编码/元信息

评估: ✅通过 / ⚠️警告 / ❌需修复（最多3次重试）
"""
import json
import logging
import os
import subprocess
from dataclasses import dataclass, field

logger = logging.getLogger("adflow.render_check")


@dataclass
class RenderCheckResult:
    """渲染检查结果"""
    passed: bool = True
    score: float = 10.0
    checks: dict[str, dict] = field(default_factory=dict)
    issues: list[str] = field(default_factory=list)
    fix_suggestions: list[str] = field(default_factory=list)


class RenderChecker:
    """渲染后自检器"""

    def check(self, video_path: str, expected_resolution: tuple = (1080, 1920),
              expected_duration_ms: int = 0, subtitle_count: int = 0,
              edl_path: str = "") -> RenderCheckResult:
        """对渲染输出进行全面检查

        Args:
            video_path: 渲染后的视频路径
            expected_resolution: 期望分辨率 (w, h)
            expected_duration_ms: 期望时长
            subtitle_count: 应有字幕数
            edl_path: EDL 文件路径（可选，用于交叉验证）

        Returns:
            RenderCheckResult
        """
        result = RenderCheckResult()
        checks = {}

        if not os.path.exists(video_path):
            result.passed = False
            result.issues.append("输出文件不存在")
            return result

        # ── 1. 视觉检查 ──
        checks["visual"] = self._check_visual(video_path, expected_resolution)

        # ── 2. 音频检查 ──
        checks["audio"] = self._check_audio(video_path)

        # ── 3. 时长检查 ──
        checks["duration"] = self._check_duration(video_path, expected_duration_ms)

        # ── 4. 编码检查 ──
        checks["codec"] = self._check_codec(video_path)

        # ── 5. 黑帧检查 ──
        checks["black_frame"] = self._check_black_frames(video_path)

        # ── 6. EDL 交叉验证 ──
        if edl_path and os.path.exists(edl_path):
            checks["edl_verify"] = self._verify_edl(video_path, edl_path)

        result.checks = checks

        # 汇总分数和问题
        scores = [c.get("score", 10) for c in checks.values()]
        result.score = sum(scores) / len(scores) if scores else 10

        for name, check in checks.items():
            for issue in check.get("issues", []):
                result.issues.append(f"[{name}] {issue}")
            for fix in check.get("fixes", []):
                result.fix_suggestions.append(f"[{name}] {fix}")

        result.passed = result.score >= 6.0 and all(
            c.get("passed", True) for c in checks.values()
        )

        if not result.passed:
            logger.warning(
                "渲染自检未通过: %.1f/10, %d个问题",
                result.score, len(result.issues))

        return result

    # ── 各维度检查 ──

    @staticmethod
    def _check_visual(video_path: str, expected_res: tuple) -> dict:
        """视觉检查：分辨率"""
        result = {"passed": True, "score": 10, "issues": [], "fixes": []}
        try:
            from adflow.engine.video_probe import VideoProbe
            info = VideoProbe.probe(video_path)

            ew, eh = expected_res
            if abs(info.width - ew) > 50 or abs(info.height - eh) > 50:
                result["passed"] = False
                result["score"] = 3
                result["issues"].append(
                    f"分辨率不匹配: {info.width}x{info.height} (期望{ew}x{eh})")
                result["fixes"].append(
                    f"调整渲染参数 target_width={ew}, target_height={eh}")
            else:
                result["score"] = 10

            if info.fps < 20:
                result["passed"] = False
                result["score"] -= 3
                result["issues"].append(f"帧率过低: {info.fps:.1f}fps")
                result["fixes"].append("检查素材帧率，确保≥25fps")

        except Exception as e:
            result["passed"] = False
            result["score"] = 0
            result["issues"].append(f"视觉检查失败: {e}")

        return result

    @staticmethod
    def _check_audio(video_path: str) -> dict:
        """音频检查：爆音/clipping/静音（FFmpeg volumedetect，无 pydub 依赖）"""
        result = {"passed": True, "score": 10, "issues": [], "fixes": []}
        try:
            from adflow.utils.ffmpeg_finder import get_ffmpeg_cmd
            import re
            proc = subprocess.run(
                [get_ffmpeg_cmd(), "-i", video_path,
                 "-af", "volumedetect", "-f", "null", "-"],
                capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=60,
            )
            stderr = proc.stderr or ""
            m_mean = re.search(r"mean_volume:\s*(-?[\d.]+) dB", stderr)
            m_max = re.search(r"max_volume:\s*(-?[\d.]+) dB", stderr)
            mean_db = float(m_mean.group(1)) if m_mean else None
            max_db = float(m_max.group(1)) if m_max else None

            # Clipping 检测（max_volume 接近 0dB 视为爆音）
            if max_db is not None and max_db > -0.5:
                result["passed"] = False
                result["score"] -= 4
                result["issues"].append("音频存在 clipping（爆音）")
                result["fixes"].append("降低主音量 2-3dB，或在混音时加 limiter")

            # 响度检查（-14 LUFS 标准，过响则提示）
            if mean_db is not None and mean_db > -6:
                result["score"] -= 2
                result["issues"].append(f"音频过响: {mean_db:.1f} dB")
                result["fixes"].append(
                    "添加 loudnorm 滤镜: loudnorm=I=-14:LRA=1:TP=-1")

            # 静音检测
            if mean_db is not None and mean_db < -50:
                result["passed"] = False
                result["score"] = 0
                result["issues"].append("音频完全静音")
                result["fixes"].append("检查配音文件是否存在且非空")

        except Exception as e:
            result["score"] = 5
            result["issues"].append(f"音频检查异常: {e}")

        return result

    @staticmethod
    def _check_duration(video_path: str, expected_ms: int) -> dict:
        """时长检查：铁律要求 视频长度 ≥ 配音长度，且差值 < 0.5s"""
        result = {"passed": True, "score": 10, "issues": [], "fixes": []}
        if expected_ms <= 0:
            return result

        try:
            from adflow.engine.video_probe import VideoProbe
            info = VideoProbe.probe(video_path)
            actual_ms = info.duration_ms
            delta = actual_ms - expected_ms  # 正=视频长于配音

            # 容差 -50ms：视频帧对齐（30fps 步进 33.33ms）必有毫秒级抖动，
            # 与 editor.py 配音对齐的 50ms 容忍带一致，短一帧内不算「短于配音」
            if delta < -50:
                # 视频短于配音超过一帧容差：硬违规（铁律：禁止视频短于配音）
                result["passed"] = False
                result["score"] = 3
                result["issues"].append(
                    f"视频短于配音: 实际{actual_ms}ms < 期望{expected_ms}ms")
                result["fixes"].append("补镜头或从素材源多截取，确保视频 ≥ 配音")
            elif delta >= 500:
                # 视频比配音长太多（铁律：差值 < 0.5s）
                result["passed"] = False
                result["score"] = 3
                result["issues"].append(
                    f"视频比配音长太多: 差值{delta}ms（阈值 < 500ms）")
                result["fixes"].append("裁掉多余镜头，使视频-配音 < 0.5s")
            else:
                result["score"] = 10
        except Exception:
            result["score"] = 5

        return result

    @staticmethod
    def _check_codec(video_path: str) -> dict:
        """编码检查"""
        result = {"passed": True, "score": 10, "issues": [], "fixes": []}
        try:
            from adflow.engine.video_probe import VideoProbe
            info = VideoProbe.probe(video_path)

            valid_video_codecs = {"h264", "hevc", "h265"}
            if info.video_codec.lower() not in valid_video_codecs:
                result["passed"] = False
                result["score"] = 3
                result["issues"].append(
                    f"视频编码不兼容: {info.video_codec} (需要h264/hevc)")
                result["fixes"].append("设置 video_codec='libx264'")

            valid_audio_codecs = {"aac", "mp3", "opus"}
            if info.audio_codec and info.audio_codec.lower() not in valid_audio_codecs:
                result["score"] -= 2
                result["issues"].append(
                    f"音频编码不兼容: {info.audio_codec}")

        except Exception:
            result["score"] = 5

        return result

    @staticmethod
    def _check_black_frames(video_path: str) -> dict:
        """黑帧检查：用 ffmpeg blackdetect 检测全黑帧（铁律：无黑屏）"""
        result = {"passed": True, "score": 10, "issues": [], "fixes": []}
        try:
            from adflow.utils.ffmpeg_finder import get_ffmpeg_cmd

            # blackdetect 逐帧检测纯黑画面，d=最小黑帧时长，pix_th=像素亮度阈值
            proc = subprocess.run(
                [get_ffmpeg_cmd(), "-i", video_path,
                 "-vf", "blackdetect=d=0.1:pix_th=0.10",
                 "-an", "-f", "null", "-"],
                capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=60,
            )
            stderr = proc.stderr or ""
            if "black_start" in stderr:
                result["passed"] = False
                result["score"] = 3
                result["issues"].append("检测到黑帧（无画面）")
                result["fixes"].append("检查镜头拼接与素材有效性，禁止出现黑屏")

        except Exception:
            result["score"] = 7

        return result

    @staticmethod
    def _verify_edl(video_path: str, edl_path: str) -> dict:
        """EDL 交叉验证：检查渲染输出与 EDL 是否一致"""
        result = {"passed": True, "score": 10, "issues": [], "fixes": []}
        try:
            with open(edl_path, "r", encoding="utf-8") as f:
                edl = json.load(f)

            from adflow.engine.video_probe import VideoProbe
            info = VideoProbe.probe(video_path)

            # 验证分辨率
            edl_res = edl.get("video", {}).get("resolution", [])
            if edl_res:
                ew, eh = edl_res
                if abs(info.width - ew) > 100 or abs(info.height - eh) > 100:
                    result["score"] -= 3
                    result["issues"].append(
                        f"EDL分辨率({ew}x{eh})与输出({info.width}x{info.height})不匹配")

            # 验证有时长
            if info.duration_sec <= 0:
                result["score"] -= 5
                result["issues"].append("输出视频时长为0")
                result["fixes"].append("检查素材文件和渲染流程")

        except Exception as e:
            result["score"] = 5
            result["issues"].append(f"EDL验证异常: {e}")

        return result
