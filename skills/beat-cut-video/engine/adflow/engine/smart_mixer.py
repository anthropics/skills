# -*- coding: utf-8 -*-
"""
智能镜头混排引擎 — CLIP特征 + 动作衔接 + BGM卡点 + Beam Search

替换 editor.py 的纯顺序拼接，实现:
  ① 相似片段不连续出现（防视觉重复）
  ② 动作方向相近的片段优先衔接（减少跳跃感）
  ③ BGM 节拍点优先放置镜头切换点（节奏感强）
  ④ 多样性惩罚：同场景/同景别连续出现 → 大幅降权
"""
import logging
import os
from dataclasses import dataclass

import numpy as np

logger = logging.getLogger("adflow.smart_mixer")


@dataclass
class ClipCandidate:
    """混排候选片段"""
    file_path: str
    duration_sec: float = 3.0
    quality_score: float = 0.7     # 0-1
    scene: str = ""                 # 场景标签
    shot_type: str = ""             # 景别
    camera_movement: str = ""       # 运镜
    index: int = 0

    @property
    def edge_weight(self) -> float:
        """边缘权重：高质量 + 适中时长的片段优先"""
        dur_score = 1.0 if 2 <= self.duration_sec <= 6 else (
            0.5 if self.duration_sec < 2 else 0.7)
        return self.quality_score * 0.6 + dur_score * 0.4


def _cosine_sim(a: np.ndarray, b: np.ndarray) -> float:
    a = a / (np.linalg.norm(a) + 1e-8)
    b = b / (np.linalg.norm(b) + 1e-8)
    return float(np.dot(a, b))


# CLIP 模型模块级缓存（_clip_text_image_similarity 是 staticmethod，避免每次 from_pretrained）
_clip_model_cache = None
_clip_processor_cache = None
_clip_device_cache = None


class SmartMixer:
    """智能混排引擎"""

    def __init__(self):
        pass  # CLIP 模型统一走模块级全局缓存（见 preload_clip / _get_clip_features）

    # ── 主入口 ──

    def plan(
        self, candidates: list[ClipCandidate],
        target_duration_sec: float = 30.0,
        bgm_bpm: float = 120.0,
        beam_width: int = 15,
    ) -> list[ClipCandidate]:
        """规划最优镜头序列

        Args:
            candidates: 候选片段列表
            target_duration_sec: 目标总时长
            bgm_bpm: BGM BPM
            beam_width: Beam Search 宽度

        Returns:
            重排后的片段列表
        """
        n = len(candidates)
        if n <= 2:
            return candidates

        # Step 1: 特征提取
        features = self._extract_features(candidates)
        sim_matrix = self._build_similarity_matrix(features)

        # Step 2: 动作衔接（简化：基于标签）
        motion_scores = self._tag_motion_scores(candidates)

        # Step 3: 节拍时间点
        beat_times = [i * 60.0 / max(bgm_bpm, 1) for i in range(
            int(target_duration_sec * bgm_bpm / 60) + 1)]

        # Step 4: Beam Search
        ordered = self._beam_search(
            candidates, sim_matrix, motion_scores,
            beat_times, target_duration_sec, beam_width,
        )

        # Step 5: 质量过滤
        filtered = self._quality_filter(ordered)
        return filtered

    # ── 特征提取 ──

    def _extract_features(self, clips: list[ClipCandidate]) -> np.ndarray:
        """提取每个片段的特征向量"""
        features = []
        for clip in clips:
            feat = self._extract_one(clip)
            features.append(feat)
        return np.array(features)  # (N, D)

    def _extract_one(self, clip: ClipCandidate) -> np.ndarray:
        """提取单个片段的特征（优先 CLIP，回退颜色直方图）"""
        # 尝试 CLIP
        clf = self._get_clip_features(clip.file_path)
        if clf is not None:
            return clf

        # 回退：颜色直方图 + 标签编码
        return self._get_histogram_features(clip.file_path, clip)

    @classmethod
    def preload_clip(cls) -> bool:
        """加载CLIP模型到全局缓存（首次自动下载~400MB，后续秒加载）"""
        global _clip_model_cache, _clip_processor_cache, _clip_device_cache
        try:
            import os
            os.environ["HF_ENDPOINT"] = "https://hf-mirror.com"
            import torch
            from transformers import CLIPProcessor, CLIPModel
            device = "cuda" if torch.cuda.is_available() else "cpu"
            logger.info("加载 CLIP 模型... (device=%s)", device)
            # 优先本地缓存，首次运行时下载；结果写入全局缓存避免重复加载
            try:
                _clip_model_cache = CLIPModel.from_pretrained(
                    "openai/clip-vit-base-patch32", local_files_only=True).to(device)
                _clip_processor_cache = CLIPProcessor.from_pretrained(
                    "openai/clip-vit-base-patch32", local_files_only=True)
            except Exception:
                logger.info("首次使用，下载 CLIP 模型 (~400MB)...")
                _clip_model_cache = CLIPModel.from_pretrained(
                    "openai/clip-vit-base-patch32").to(device)
                _clip_processor_cache = CLIPProcessor.from_pretrained(
                    "openai/clip-vit-base-patch32")
            _clip_device_cache = device
            logger.info("CLIP 模型就绪")
            return True
        except ImportError:
            logger.warning("CLIP依赖缺失: pip install transformers torch")
            return False
        except Exception as e:
            logger.warning("CLIP预下载失败(将用颜色直方图回退): %s", str(e)[:100])
            return False

    @staticmethod
    def _clip_text_image_similarity(image, text: str) -> float:
        """CLIP 图文匹配度：画面与描述文本的语义相似度 0-1

        用于判断画面是否包含产品特写、使用动作等卖点元素。
        """
        global _clip_model_cache, _clip_processor_cache, _clip_device_cache
        try:
            import os
            os.environ.setdefault("HF_ENDPOINT", "https://hf-mirror.com")
            import torch
            import numpy as np
            from transformers import CLIPProcessor, CLIPModel
            from PIL import Image

            if _clip_model_cache is None:
                _clip_device_cache = "cuda" if torch.cuda.is_available() else "cpu"
                _clip_model_cache = CLIPModel.from_pretrained(
                    "openai/clip-vit-base-patch32", local_files_only=True).to(_clip_device_cache)
                _clip_processor_cache = CLIPProcessor.from_pretrained(
                    "openai/clip-vit-base-patch32", local_files_only=True)
            device = _clip_device_cache
            model = _clip_model_cache
            processor = _clip_processor_cache

            if isinstance(image, np.ndarray):
                pil_image = Image.fromarray(image)
            else:
                pil_image = image

            inputs = processor(
                text=[text], images=[pil_image],
                return_tensors="pt", padding=True).to(device)
            with torch.no_grad():
                outputs = model(**inputs)
            # cosine similarity scaled to 0-1
            sim = outputs.logits_per_image[0, 0].item()
            return max(0.0, min(1.0, (sim + 1) / 2))
        except Exception:
            return 0.5  # 失败回退中性分

    def _get_clip_features(self, path: str) -> np.ndarray | None:
        """CLIP ViT-B/32 特征（国内镜像+hf-mirror.com）"""
        global _clip_model_cache, _clip_processor_cache, _clip_device_cache
        try:
            import os
            os.environ.setdefault("HF_ENDPOINT", "https://hf-mirror.com")
            import torch
            from transformers import CLIPProcessor, CLIPModel

            if _clip_model_cache is None:
                _clip_device_cache = "cuda" if torch.cuda.is_available() else "cpu"
                model_name = "openai/clip-vit-base-patch32"
                _clip_model_cache = CLIPModel.from_pretrained(
                    model_name).to(_clip_device_cache)
                _clip_processor_cache = CLIPProcessor.from_pretrained(
                    model_name)
            device = _clip_device_cache
            model = _clip_model_cache
            processor = _clip_processor_cache

            import cv2
            cap = cv2.VideoCapture(path)
            total = int(cap.get(cv2.CAP_PROP_FRAME_COUNT))
            frames = []
            for pos in [0, total // 2, total - 1]:
                cap.set(cv2.CAP_PROP_POS_FRAMES, max(0, min(pos, total - 1)))
                ret, frame = cap.read()
                if ret:
                    frames.append(cv2.cvtColor(frame, cv2.COLOR_BGR2RGB))
            cap.release()

            if not frames:
                return None

            from PIL import Image
            images = [Image.fromarray(f) for f in frames]
            inputs = processor(
                images=images, return_tensors="pt").to(device)
            with torch.no_grad():
                emb = model.get_image_features(**inputs)
            return emb.mean(dim=0).cpu().numpy()

        except ImportError:
            return None
        except Exception as e:
            logger.debug("CLIP提取失败: %s", e)
            return None

    def _get_histogram_features(self, path: str,
                                 clip: ClipCandidate) -> np.ndarray:
        """颜色直方图 + 标签特征（无需GPU）"""
        import cv2
        cap = cv2.VideoCapture(path)
        total = int(cap.get(cv2.CAP_PROP_FRAME_COUNT))
        step = max(1, total // 5)
        hists = []
        for i in range(0, total, step):
            cap.set(cv2.CAP_PROP_POS_FRAMES, i)
            ret, frame = cap.read()
            if not ret:
                break
            hist = cv2.calcHist([frame], [0, 1, 2], None, [8, 8, 8],
                                [0, 256, 0, 256, 0, 256])
            cv2.normalize(hist, hist)
            hists.append(hist.flatten())
        cap.release()
        color_feat = np.mean(hists, axis=0) if hists else np.zeros(512)

        # 标签 one-hot 编码
        scenes = ["indoor", "outdoor", "product", "office", "kitchen"]
        tag_feat = np.zeros(len(scenes))
        for i, s in enumerate(scenes):
            if s in (clip.scene or "").lower():
                tag_feat[i] = 1.0

        return np.concatenate([color_feat[:256], tag_feat])

    # ── 相似度矩阵 ──

    def _build_similarity_matrix(self, features: np.ndarray) -> np.ndarray:
        """N×N 余弦相似度矩阵"""
        n = features.shape[0]
        sim = np.zeros((n, n))
        for i in range(n):
            for j in range(n):
                sim[i, j] = _cosine_sim(features[i], features[j])
        return sim

    # ── 动作衔接（基于标签） ──

    @staticmethod
    def _tag_motion_scores(clips: list[ClipCandidate]) -> list[dict]:
        """基于运镜标签计算动作衔接分"""
        scores = []
        for c in clips:
            movement = (c.camera_movement or "").lower()
            angle = 0.0
            if "left" in movement:
                angle = -0.5
            elif "right" in movement:
                angle = 0.5
            elif "up" in movement or "tilt" in movement:
                angle = 0.3
            elif "zoom" in movement:
                angle = 0.0
            mag = 0.5 if movement and movement != "static" else 0.1
            scores.append({"angle": angle, "magnitude": mag})
        return scores

    @staticmethod
    def _motion_continuity(a: dict, b: dict) -> float:
        """两个片段动作衔接分（方向越近越好）"""
        diff = abs(a["angle"] - b["angle"])
        diff = min(diff, 2 * np.pi - diff) if diff > np.pi else diff
        return 1.0 - diff / np.pi

    # ── Beam Search ──

    def _beam_search(
        self, clips: list[ClipCandidate],
        sim_matrix: np.ndarray,
        motion_scores: list[dict],
        beat_times: list[float],
        target_dur: float,
        beam_width: int = 15,
    ) -> list[ClipCandidate]:
        """Beam Search 最优序列"""
        n = len(clips)
        # beam: list of (score, seq_indices, total_dur)
        beam = [(0.0, [], 0.0)]

        for _ in range(n):
            new_beam = []
            for score, seq, dur in beam:
                used = set(seq)
                for ci in range(n):
                    if ci in used:
                        continue
                    cand = clips[ci]
                    new_dur = dur + cand.duration_sec

                    # 超时跳过
                    if new_dur > target_dur * 1.3:
                        continue

                    new_score = score + cand.edge_weight

                    # 相似度惩罚
                    if seq:
                        prev = seq[-1]
                        sim = sim_matrix[prev][ci]
                        new_score -= sim * 2.0

                    # 动作衔接
                    if seq:
                        mc = self._motion_continuity(
                            motion_scores[seq[-1]], motion_scores[ci])
                        new_score += mc * 0.4

                    # BGM 卡点加分
                    nearest = min(beat_times,
                                  key=lambda b: abs(b - dur))
                    beat_penalty = abs(dur + cand.duration_sec - nearest)
                    new_score -= beat_penalty * 0.05

                    # 多样性惩罚
                    if seq:
                        prev_clip = clips[seq[-1]]
                        # 同素材文件 → 强禁止
                        if prev_clip.file_path == cand.file_path:
                            new_score -= 10.0
                        # CLIP 相似度 > 0.6 → 大幅降权
                        if sim_matrix[seq[-1]][ci] > 0.6:
                            new_score -= 3.0
                        # 同场景连续 → 惩罚
                        if prev_clip.scene == cand.scene and cand.scene:
                            new_score -= 2.0
                        # 同景别连续 → 惩罚
                        if (prev_clip.shot_type == cand.shot_type
                                and cand.shot_type):
                            new_score -= 1.5

                    new_beam.append((new_score, seq + [ci], new_dur))

            if not new_beam:
                break
            new_beam.sort(key=lambda x: x[0], reverse=True)
            beam = new_beam[:beam_width]

        # 取最接近目标时长的序列
        best = min(beam, key=lambda x: abs(x[2] - target_dur))
        logger.info(
            "SmartMixer: %d片段 → %d镜头序列, 时长%.1fs, 得分%.2f",
            len(clips), len(best[1]), best[2], best[0])
        return [clips[i] for i in best[1]]

    # ── 峰值片段检测 ──

    @staticmethod
    def find_peak_segment(video_path: str, target_dur_sec: float = 3.0,
                          total_dur_sec: float = 0,
                          semantic_prompt: str = "") -> tuple[float, float]:
        """找到素材中最能表达卖点的片段

        评分维度:
          - 视觉兴趣 40%: 亮度方差 + 运动 + 色彩
          - 卖点语义 40%: CLIP 画面与卖点文本的匹配度
          - 人脸加分 20%: 人脸吸引注意但不喧宾夺主

        Returns:
            (peak_start_sec, peak_end_sec) 最佳片段起止时间
        """
        import cv2
        cap = cv2.VideoCapture(video_path)
        if not cap.isOpened():
            return (0.0, target_dur_sec)

        fps = cap.get(cv2.CAP_PROP_FPS)
        total_frames = int(cap.get(cv2.CAP_PROP_FRAME_COUNT))
        total_dur = total_frames / fps if fps > 0 else 10.0
        if total_dur_sec > 0:
            total_dur = min(total_dur, total_dur_sec)

        # 每 0.5 秒采样一帧评分
        window_size = int(fps * target_dur_sec)  # 目标窗口帧数
        sample_interval = max(1, int(fps * 0.5))
        frame_scores = []
        prev_frame = None

        # CLIP 语义评分缓存（每2秒算一次，避免太慢）
        clip_cache: dict[int, float] = {}
        if semantic_prompt:
            clip_sample_frames = list(range(0, total_frames - window_size,
                                            max(1, int(fps * 2))))

        for i in range(0, total_frames - window_size, sample_interval):
            cap.set(cv2.CAP_PROP_POS_FRAMES, i)
            ret, frame = cap.read()
            if not ret:
                break

            # 视觉兴趣分
            vis_score = SmartMixer._score_frame_interest(frame, prev_frame) / 10.0

            # 卖点语义分（CLIP，缓存最近的关键帧结果）
            sem_score = 0.5  # 默认中性
            if semantic_prompt:
                nearest = min(clip_sample_frames,
                             key=lambda x: abs(x - i))
                if nearest not in clip_cache:
                    cap.set(cv2.CAP_PROP_POS_FRAMES, nearest)
                    _, sem_frame = cap.read()
                    if sem_frame is not None:
                        clip_cache[nearest] = SmartMixer._clip_text_image_similarity(
                            cv2.cvtColor(sem_frame, cv2.COLOR_BGR2RGB),
                            semantic_prompt)
                    cap.set(cv2.CAP_PROP_POS_FRAMES, i)
                sem_score = clip_cache.get(nearest, 0.5)

            # 综合评分: 视觉 40% + 语义 40% + 人脸 20%
            score = vis_score * 0.4 + sem_score * 0.4 + vis_score * 0.2
            frame_scores.append((i / fps, score))
            prev_frame = frame

        cap.release()

        if not frame_scores:
            return (0.0, min(target_dur_sec, total_dur))

        # 找到评分最高的连续窗口
        best_start = 0.0
        best_score = 0.0
        for start_sec, _ in frame_scores:
            end_sec = start_sec + target_dur_sec
            if end_sec > total_dur:
                break
            # 窗口内平均分
            window_scores = [
                s for t, s in frame_scores
                if start_sec <= t <= end_sec
            ]
            avg = sum(window_scores) / len(window_scores) if window_scores else 0
            if avg > best_score:
                best_score = avg
                best_start = start_sec

        # 回退：取 20%-50% 位置（通常中间部分有内容）
        if best_start < 0.1:
            best_start = total_dur * 0.2

        peak_end = min(best_start + target_dur_sec, total_dur)
        logger.info("峰值检测: %.1fs-%.1fs (评分%.2f) from %s",
                     best_start, peak_end, best_score,
                     os.path.basename(video_path)[:20])
        return (best_start, peak_end)

    @staticmethod
    def _score_frame_interest(frame, prev_frame=None) -> float:
        """单帧视觉吸引力评分"""
        import cv2
        hsv = cv2.cvtColor(frame, cv2.COLOR_BGR2HSV)

        # 1. 亮度方差（有明暗对比 = 有趣）
        v_channel = hsv[:, :, 2]
        brightness_var = float(np.std(v_channel)) / 128.0
        brightness_score = min(1.0, brightness_var)

        # 2. 色彩饱和度
        s_channel = hsv[:, :, 1]
        sat_mean = float(np.mean(s_channel)) / 255.0
        sat_score = sat_mean * 0.5 + 0.3  # 不要太艳也不要太灰

        # 3. 运动幅度（帧差）
        motion_score = 0.3  # 默认中等
        if prev_frame is not None:
            diff = cv2.absdiff(
                cv2.cvtColor(frame, cv2.COLOR_BGR2GRAY),
                cv2.cvtColor(prev_frame, cv2.COLOR_BGR2GRAY))
            motion = float(np.mean(diff)) / 50.0
            motion_score = min(1.0, motion)

        # 4. 人脸检测加分（级联分类器缓存，只加载一次）
        face_score = 0.0
        try:
            if not hasattr(SmartMixer, '_face_cascade'):
                SmartMixer._face_cascade = cv2.CascadeClassifier(
                    cv2.data.haarcascades + 'haarcascade_frontalface_default.xml')
            cascade = SmartMixer._face_cascade
            gray = cv2.cvtColor(frame, cv2.COLOR_BGR2GRAY)
            faces = cascade.detectMultiScale(gray, 1.1, 3)
            if len(faces) > 0:
                face_score = min(0.4, len(faces) * 0.1)
        except Exception:
            pass

        # 加权综合
        return (brightness_score * 0.25 + sat_score * 0.20 +
                motion_score * 0.35 + face_score * 0.20)

    # ── 质量过滤 ──

    @staticmethod
    def _quality_filter(clips: list[ClipCandidate]) -> list[ClipCandidate]:
        """过滤低质量片段"""
        return [c for c in clips if c.quality_score >= 0.3]
