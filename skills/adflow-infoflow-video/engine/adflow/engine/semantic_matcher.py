"""文案-素材语义对齐 — 中文 CLIP 图文相似度

把分镜文案（narration_text）与素材画面映射到同一语义空间，
算余弦相似度，供 match_agent 增加「文案-画面语义对齐」评分。
"""

import logging
import os

import numpy as np

logger = logging.getLogger("adflow.semantic_matcher")

_MODEL_NAME = "OFA-Sys/chinese-clip-vit-base-patch16"

_model = None
_processor = None
_device = None

# 会话内缓存：素材图像特征（key=file_path）/ 文案文本特征（key=text）
_image_feature_cache: dict[str, np.ndarray] = {}
_text_feature_cache: dict[str, np.ndarray] = {}


def _ensure_loaded() -> bool:
    """加载中文 CLIP 到模块级缓存（首次自动下载 ~350MB）"""
    global _model, _processor, _device
    if _model is not None:
        return True
    try:
        os.environ.setdefault("HF_ENDPOINT", "https://hf-mirror.com")
        import torch
        from transformers import ChineseCLIPModel, ChineseCLIPProcessor

        _device = "cuda" if torch.cuda.is_available() else "cpu"
        try:
            _model = ChineseCLIPModel.from_pretrained(
                _MODEL_NAME, local_files_only=True).to(_device)
            _processor = ChineseCLIPProcessor.from_pretrained(
                _MODEL_NAME, local_files_only=True)
        except Exception:
            logger.info("首次使用，下载中文 CLIP 模型 (~350MB)...")
            _model = ChineseCLIPModel.from_pretrained(_MODEL_NAME).to(_device)
            _processor = ChineseCLIPProcessor.from_pretrained(_MODEL_NAME)
        logger.info("中文 CLIP 模型就绪 (device=%s)", _device)
        return True
    except ImportError:
        logger.warning("中文 CLIP 依赖缺失: pip install transformers torch")
        return False
    except Exception as e:
        logger.warning("中文 CLIP 加载失败: %s", str(e)[:120])
        return False


def encode_image(pil_image) -> np.ndarray | None:
    """图像 → L2 归一化特征向量"""
    if not _ensure_loaded():
        return None
    try:
        import torch
        inputs = _processor(images=pil_image, return_tensors="pt").to(_device)
        with torch.no_grad():
            feat = _model.get_image_features(**inputs)
        feat = feat / feat.norm(p=2, dim=-1, keepdim=True)
        return feat[0].cpu().numpy()
    except Exception as e:
        logger.debug("图像特征提取失败: %s", e)
        return None


def encode_text(text: str) -> np.ndarray | None:
    """文本 → L2 归一化特征向量（带缓存）"""
    if not _ensure_loaded():
        return None
    if text in _text_feature_cache:
        return _text_feature_cache[text]
    try:
        import torch
        inputs = _processor(text=[text], padding=True, return_tensors="pt").to(_device)
        with torch.no_grad():
            # ChineseCLIP 的 text_model 是 RoBERTa（无 pooler），
            # get_text_features 依赖的 pooler_output 为 None，改用 <s> token 的 hidden state
            out = _model.text_model(**inputs)
            pooled = out.last_hidden_state[:, 0, :]
            feat = _model.text_projection(pooled)
        feat = feat / feat.norm(p=2, dim=-1, keepdim=True)
        vec = feat[0].cpu().numpy()
        _text_feature_cache[text] = vec
        return vec
    except Exception as e:
        logger.debug("文本特征提取失败: %s", e)
        return None


def similarity(image_feat: np.ndarray, text_feat: np.ndarray) -> float:
    """余弦相似度 → 0-1"""
    cos = float(np.dot(image_feat, text_feat))
    return max(0.0, min(1.0, (cos + 1) / 2))


def image_feature_from_video(path: str) -> np.ndarray | None:
    """视频抽中间 1 帧 → 图像特征（带缓存）"""
    if path in _image_feature_cache:
        return _image_feature_cache[path]
    feat = _extract_mid_frame_feature(path)
    if feat is not None:
        _image_feature_cache[path] = feat
    return feat


def _extract_mid_frame_feature(path: str) -> np.ndarray | None:
    """cv2 抽中间帧 → encode_image"""
    try:
        import cv2
        cap = cv2.VideoCapture(path)
        total = int(cap.get(cv2.CAP_PROP_FRAME_COUNT))
        if total <= 0:
            cap.release()
            return None
        cap.set(cv2.CAP_PROP_POS_FRAMES, total // 2)
        ret, frame = cap.read()
        cap.release()
        if not ret:
            return None
        from PIL import Image
        return encode_image(Image.fromarray(cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)))
    except Exception as e:
        logger.debug("抽帧失败: %s", e)
        return None
