# -*- coding: utf-8 -*-
"""
视频方向智能检测器 — 三层检测 + 人脸优先智能裁剪

Layer 1: 元数据层 — FFprobe rotation 字段
Layer 2: 画面层 — 宽高比 + 手机录制特征
Layer 3: 内容层 — OpenCV 人脸检测确定画面重心

解决三个核心问题:
  1. 横拍竖看: 手机横拍但元数据 rotation=0 → 需要旋转90°
  2. 倒着拍: rotation=180 或画面颠倒 → 需要翻转180°
  3. 裁剪偏移: 横屏裁竖屏时裁掉了主体 → 人脸优先裁剪
"""
import logging
from typing import Optional

logger = logging.getLogger("adflow.orientation")


def classify_orientation(file_path: str) -> str:
    """导入时的快速方向分类（只用元数据+手机启发式，无人脸检测，毫秒级）

    返回:
      vertical      竖屏素材（含带 90/270 旋转元数据、回正后是竖屏的）
      landscape     真横屏素材
      phone_rotated 手机横拍竖看（画面内容其实是竖的，渲染时自动旋转回正）
      unknown       识别不了（探测失败）
    """
    try:
        from adflow.engine.video_probe import VideoProbe
        info = VideoProbe.probe(file_path)
    except Exception as e:
        logger.warning("方向探测失败 %s: %s", file_path, e)
        return "unknown"
    if not info or not getattr(info, "width", 0) or not getattr(info, "height", 0):
        return "unknown"
    rot = info.rotation or 0
    if rot in (90, 270):
        # 旋转元数据：交换宽高得到内容实际方向
        eff_w, eff_h = info.height, info.width
    else:
        # rotation=0 且宽>高：可能是手机横拍竖看（内容竖的存成横的）
        if info.width > info.height and rot == 0:
            if VideoOrientationDetector._detect_phone_landscape(file_path, info):
                return "phone_rotated"
        eff_w, eff_h = info.width, info.height
    # 180°上下颠倒：宽高不变，渲染时自动翻转回正，按宽高归类
    return "vertical" if eff_h >= eff_w else "landscape"


class VideoOrientationDetector:
    """视频方向智能检测器 — 三层检测 + 智能裁剪"""

    # 常见手机录制分辨率
    PHONE_RESOLUTIONS = {
        (1920, 1080), (1280, 720), (2160, 1080),
        (2560, 1440), (1440, 1080), (1280, 960),
        (1080, 1920), (720, 1280), (1080, 2160),
    }

    @classmethod
    def detect(cls, file_path: str,
               target_w: int = 1080, target_h: int = 1920) -> dict:
        """综合检测视频方向

        Returns:
            {
                "rotation": 0,                # 需要旋转的角度: 0/90/180/270
                "orientation": "portrait",     # 原始方向
                "effective_orientation": "portrait",  # 旋转后方向
                "needs_rotation": False,
                "needs_crop": True,
                "crop_strategy": "face",       # face/center
                "crop_region": {x, y, w, h} or None,
                "confidence": 0.95,
                "detection_layers": {...},
            }
        """
        from adflow.engine.video_probe import VideoProbe

        # ── Layer 1: 元数据检测 ──
        info = VideoProbe.probe(file_path)
        metadata_rotation = info.rotation or 0

        # ── Layer 2: 宽高比 + 手机录制特征 ──
        is_landscape = info.width > info.height
        target_portrait = target_h > target_w

        is_phone_landscape = False
        if is_landscape and target_portrait and metadata_rotation == 0:
            is_phone_landscape = cls._detect_phone_landscape(file_path, info)

        # 确定旋转角度
        if metadata_rotation in (90, 180, 270):
            rotation = metadata_rotation
        elif is_phone_landscape:
            rotation = 270  # 逆时针90°回正
        else:
            rotation = 0

        # 旋转后有效宽高
        if rotation in (90, 270):
            eff_w, eff_h = info.height, info.width
        else:
            eff_w, eff_h = info.width, info.height

        # ── Layer 3: 人脸检测 → 裁剪区域（受 video_orientation.face_detection 控制）──
        from adflow.config_loader import config
        crop_strategy = "center"
        crop_region = None
        face_center = None

        if eff_w != target_w or eff_h != target_h:
            # 非口播混剪设 face_detection=false 关闭人脸优先裁剪（Haar 对普通片段误检率↑，易裁偏）
            if config.get("video_orientation.face_detection", True):
                face_center = cls._detect_face_center(file_path)
            if face_center:
                crop_strategy = "face"
                crop_region = cls._crop_around_point(
                    eff_w, eff_h, target_w, target_h, face_center)
            else:
                crop_region = cls._crop_around_point(
                    eff_w, eff_h, target_w, target_h,
                    (eff_w / 2, eff_h / 2))

        return {
            "rotation": rotation,
            "orientation": "landscape" if is_landscape else "portrait",
            "effective_orientation": "portrait" if eff_h > eff_w else "landscape",
            "needs_rotation": rotation != 0,
            "needs_crop": crop_region is not None,
            "crop_strategy": crop_strategy,
            "crop_region": crop_region,
            "is_upside_down": rotation == 180,
            "is_phone_landscape": is_phone_landscape,
            "confidence": 0.9 if face_center else 0.7,
            "detection_layers": {
                "metadata": {"rotation": metadata_rotation, "source": "ffprobe"},
                "aspect": {
                    "is_landscape": is_landscape,
                    "ratio": round(info.width / max(info.height, 1), 2),
                },
                "content": {
                    "face_detected": face_center is not None,
                    "face_center": face_center,
                },
            },
        }

    @classmethod
    def _detect_phone_landscape(cls, file_path: str, info) -> bool:
        """检测是否是手机横拍竖看

        启发式规则:
          - 分辨率匹配常见手机尺寸
          - 帧率匹配手机 (30/60fps)
          - 格式为 MP4/MOV
        满足 ≥2 项即判定为手机横拍
        """
        is_phone_res = (info.width, info.height) in cls.PHONE_RESOLUTIONS
        is_phone_fps = info.fps in [29.97, 30, 59.94, 60]
        is_phone_format = file_path.lower().endswith(('.mp4', '.mov'))
        matches = sum([is_phone_res, is_phone_fps, is_phone_format])
        return matches >= 2

    @staticmethod
    def _detect_face_center(file_path: str) -> Optional[tuple[float, float]]:
        """用 OpenCV Haar Cascade 检测人脸中心

        采样第1秒和第3秒两帧，取最大人脸。
        """
        try:
            import cv2
        except ImportError:
            return None

        try:
            cap = cv2.VideoCapture(file_path)
            if not cap.isOpened():
                cap.release()
                return None

            best_center = None
            best_area = 0

            for sample_sec in [1.0, 3.0]:
                cap.set(cv2.CAP_PROP_POS_MSEC, int(sample_sec * 1000))
                ret, frame = cap.read()
                if not ret:
                    continue

                gray = cv2.cvtColor(frame, cv2.COLOR_BGR2GRAY)
                cascade_path = (
                    cv2.data.haarcascades + 'haarcascade_frontalface_default.xml')
                face_cascade = cv2.CascadeClassifier(cascade_path)
                faces = face_cascade.detectMultiScale(gray, 1.1, 4)

                for (x, y, w, h) in faces:
                    area = w * h
                    if area > best_area:
                        best_area = area
                        best_center = (x + w / 2, y + h / 2)

            cap.release()
            if best_center:
                logger.info("人脸检测成功: center=(%.0f, %.0f) area=%d",
                            best_center[0], best_center[1], best_area)
            return best_center

        except Exception as e:
            logger.debug("人脸检测失败: %s", e)
            return None

    @staticmethod
    def _crop_around_point(
        src_w: int, src_h: int,
        target_w: int, target_h: int,
        center: tuple[float, float],
    ) -> dict:
        """围绕给定中心计算裁剪区域"""
        scale = max(target_w / src_w, target_h / src_h)
        scaled_w = int(src_w * scale)
        scaled_h = int(src_h * scale)

        cx = center[0] * scale
        cy = center[1] * scale

        x = int(cx - target_w / 2)
        y = int(cy - target_h / 2)

        # 边界保护
        x = max(0, min(x, scaled_w - target_w))
        y = max(0, min(y, scaled_h - target_h))

        return {
            "x": x, "y": y,
            "w": target_w, "h": target_h,
            "scaled_w": scaled_w,
            "scaled_h": scaled_h,
        }

    @classmethod
    def classify(cls, file_path: str) -> str:
        """快速分类视频方向类型

        Returns:
            portrait_upright / portrait_rotated /
            landscape_upright / landscape_rotated / square
        """
        from adflow.engine.video_probe import VideoProbe
        info = VideoProbe.probe(file_path)

        if info.rotation in (90, 270):
            return "portrait_rotated" if info.width > info.height else "landscape_rotated"

        if abs(info.width - info.height) < 50:
            return "square"

        if info.width > info.height:
            if cls._detect_phone_landscape(file_path, info):
                return "landscape_rotated"
            return "landscape_upright"

        return "portrait_upright"

    @classmethod
    def batch_detect(cls, file_paths: list[str]) -> dict[str, dict]:
        """批量检测，返回 {file_path: result, ...}"""
        results = {}
        for fp in file_paths:
            try:
                results[fp] = cls.detect(fp)
            except Exception as e:
                results[fp] = {"error": str(e)}
        return results
