# -*- coding: utf-8 -*-
"""
素材去重微调引擎 — 7维度差异化，确保变体过平台去重检测

维度:
  1. 视频指纹 (pHash) — 裁剪/旋转/缩放微调
  2. 音频指纹 — 音高/语速/噪声微调
  3. 关键帧序列 (颜色直方图) — 调色改变
  4. OCR文本 — 文案差异化
  5. ASR语音 — 文案+音色差异化
  6. 编辑模式 — 剪切点+转场变化
  7. 元数据 — 帧率/分辨率微调

目标: 每个变体在 ≥4 个维度上不同于其他变体，综合相似度 < 0.70
"""
import logging
import os
import subprocess
from dataclasses import dataclass

logger = logging.getLogger("adflow.anti_dedup")


@dataclass
class DedupParams:
    """去重微调参数（每个变体一组，确定性生成）"""
    # 视频微调
    crop_offset: float = 0.0        # 裁剪比例 0~0.02
    rotation_deg: float = 0.0       # 旋转角度（已废弃=0）
    scale_factor: float = 1.0       # 缩放因子 1.0~1.02
    flip: bool = False              # 水平镜像翻转

    # 结构微调
    transition: str = "cut"         # cut/fade/dissolve/slide
    fps: float = 30.0

    @property
    def has_video_adjust(self) -> bool:
        return self.crop_offset > 0 or self.scale_factor != 1.0 or self.flip


class AntiDedupEngine:
    """多维度去重微调引擎"""

    # 微调参数池（素数取模确保各维度变化周期不同）
    CROP_MODES = [0.00, 0.005, 0.01, 0.015, 0.02]    # 最大2%，不切画面
    ROTATION_MODES = [0.0, 0.0, 0.0, 0.0, 0.0]        # 取消旋转（几乎无效+黑边）
    SCALE_MODES = [1.00, 1.005, 1.01, 1.015, 1.02]    # 微缩放5档
    FLIP_MODES = [False, True, False, True, False]       # 镜像翻转（最安全差异化）
    TRANSITION_MODES = ["cut", "fade", "dissolve", "slide", "cut"]
    FPS_MODES = [30.0, 29.97, 30.03, 30.0, 29.97]

    def __init__(self):
        from adflow.config_loader import config
        self.cfg = config.get("anti_dedup", {}) or {}

    @classmethod
    def generate_dedup_params(cls, variant_index: int) -> DedupParams:
        """根据变体序号确定性生成差异化参数"""
        return DedupParams(
            crop_offset=cls.CROP_MODES[variant_index % 5],
            rotation_deg=cls.ROTATION_MODES[variant_index % 5],
            scale_factor=cls.SCALE_MODES[variant_index % 5],
            flip=cls.FLIP_MODES[variant_index % 5],
            transition=cls.TRANSITION_MODES[variant_index % 5],
            fps=cls.FPS_MODES[variant_index % 5],
        )

    def build_video_filter(self, params: DedupParams,
                           src_w: int = 0, src_h: int = 0) -> str:
        """构建 FFmpeg 视频微调滤镜链（裁窗口后显式 scale 回源尺寸，分辨率不变）

        src_w/src_h = 源分辨率，默认取竖屏平台 1080x1920。显式 scale 回源尺寸可
        避免 FFmpeg 整数截断在多次 scale/crop 间累积（否则输出缩水 1~2px）。
        """
        if src_w <= 0 or src_h <= 0:
            from adflow.config_loader import config
            res = config.platform_default("douyin").get("resolution", [1080, 1920])
            src_w, src_h = res[0], res[1]
        W, H = src_w, src_h
        filters = []
        if params.crop_offset > 0:
            o = params.crop_offset
            # 裁掉边缘 o 比例后放大回源尺寸 —— 轻微偏移变焦
            filters.append(
                f"crop={W*(1-2*o):.1f}:{H*(1-2*o):.1f}:{W*o:.1f}:{H*o:.1f},"
                f"scale={W}:{H}")
        if params.rotation_deg > 0:
            rad = params.rotation_deg * 3.14159 / 180
            filters.append(f"rotate={rad:.4f}:fillcolor=black")
        if params.scale_factor != 1.0:
            s = params.scale_factor
            # 放大 s 倍后裁回源尺寸 —— 轻微变焦（整数 crop 精确还原，避免 1.005 失效）
            filters.append(f"scale={W*s:.1f}:{H*s:.1f},crop={W}:{H}:0:0")
        if params.flip:
            filters.append("hflip")
        return ",".join(filters)

    def apply_post_dedup(self, video_path: str, params: DedupParams,
                         output_path: str = "") -> str:
        """视频后处理去重微调（剪辑导出+调色后执行）"""
        if not params.has_video_adjust:
            return video_path

        from adflow.utils.ffmpeg_finder import get_ffmpeg_cmd

        if not output_path:
            base, ext = os.path.splitext(video_path)
            output_path = f"{base}_dedup{ext}"

        vf = self.build_video_filter(params)

        cmd = [get_ffmpeg_cmd(), "-y", "-i", video_path]
        if vf:
            cmd += ["-vf", vf]
        cmd += ["-c:v", "libx264", "-preset", "medium", "-crf", "20",
                "-r", str(params.fps), "-c:a", "copy", output_path]

        try:
            result = subprocess.run(cmd, capture_output=True, timeout=300)
            if result.returncode != 0:
                logger.error("去重微调失败: %s",
                             result.stderr.decode()[-300:])
                return video_path
            return output_path
        except Exception as e:
            logger.error("去重微调异常: %s", e)
            return video_path

    # ── 相似度检测 ──

    @staticmethod
    def compute_text_similarity(text_a: str, text_b: str) -> float:
        """文本相似度（字符集Jaccard）"""
        if not text_a or not text_b:
            return 0.0
        sa, sb = set(text_a), set(text_b)
        union = sa | sb
        return len(sa & sb) / len(union) if union else 0.0

    @staticmethod
    def compute_edit_similarity(script_a, script_b) -> float:
        """编辑模式相似度（镜头数+时长分布）"""
        shots_a, shots_b = len(script_a.shots), len(script_b.shots)
        if shots_a == 0 or shots_b == 0:
            return 0.0
        count_sim = 1 - abs(shots_a - shots_b) / max(shots_a, shots_b)
        da = [s.duration_ms for s in script_a.shots]
        db = [s.duration_ms for s in script_b.shots]
        mx = max(len(da), len(db))
        da += [0] * (mx - len(da))
        db += [0] * (mx - len(db))
        ta, tb = sum(da) or 1, sum(db) or 1
        diff = sum(abs(a/ta - b/tb) for a, b in zip(da, db)) / 2
        return count_sim * 0.4 + (1 - diff) * 0.6

    @staticmethod
    def compute_phash(video_path: str, num_frames: int = 8) -> list:
        """计算视频感知哈希序列"""
        try:
            import cv2
            import imagehash
            from PIL import Image
        except ImportError:
            return []

        cap = cv2.VideoCapture(video_path)
        if not cap.isOpened():
            return []
        total = int(cap.get(cv2.CAP_PROP_FRAME_COUNT))
        step = max(1, total // num_frames)
        hashes = []
        for i in range(0, total, step):
            if len(hashes) >= num_frames:
                break
            cap.set(cv2.CAP_PROP_POS_FRAMES, i)
            ret, frame = cap.read()
            if not ret:
                continue
            img = Image.fromarray(cv2.cvtColor(frame, cv2.COLOR_BGR2RGB))
            hashes.append(str(imagehash.phash(img)))
        cap.release()
        return hashes

    @staticmethod
    def check_similarity(video_a: str, video_b: str,
                         text_a: str = "", text_b: str = "") -> float:
        """综合相似度: pHash(0.4)+文本(0.3)+颜色直方图(0.3)"""
        # pHash
        pa = AntiDedupEngine.compute_phash(video_a)
        pb = AntiDedupEngine.compute_phash(video_b)
        phash_sim = 0.0
        if pa and pb:
            from difflib import SequenceMatcher
            matches = sum(1 for h1, h2 in zip(pa, pb)
                          if SequenceMatcher(None, h1, h2).ratio() > 0.8)
            phash_sim = matches / max(len(pa), len(pb))

        # 文本
        text_sim = AntiDedupEngine.compute_text_similarity(text_a, text_b)

        # 颜色直方图
        color_sim = AntiDedupEngine._color_hist_sim(video_a, video_b)

        return phash_sim * 0.4 + text_sim * 0.3 + color_sim * 0.3

    @staticmethod
    def _color_hist_sim(va: str, vb: str) -> float:
        try:
            import cv2
            import numpy as np
        except ImportError:
            return 0.0

        def _hist(vp):
            cap = cv2.VideoCapture(vp)
            if not cap.isOpened():
                return None
            total = int(cap.get(cv2.CAP_PROP_FRAME_COUNT))
            step = max(1, total // 5)
            hists = []
            for i in range(0, total, step):
                if len(hists) >= 5:
                    break
                cap.set(cv2.CAP_PROP_POS_FRAMES, i)
                ret, frame = cap.read()
                if not ret:
                    continue
                hist = cv2.calcHist([frame], [0, 1, 2], None, [8, 8, 8],
                                    [0, 256, 0, 256, 0, 256])
                cv2.normalize(hist, hist)
                hists.append(hist.flatten())
            cap.release()
            return np.mean(hists, axis=0) if hists else None

        ha = _hist(va)
        hb = _hist(vb)
        if ha is None or hb is None:
            return 0.0
        return float(cv2.compareHist(
            ha.astype(np.float32), hb.astype(np.float32), cv2.HISTCMP_CORREL))
