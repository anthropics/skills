# -*- coding: utf-8 -*-
"""
爆款文本分析器 — 参考 video-use 双层感知模型

核心理念: 先读文本（~12KB），再按需看图 → 大幅降低分析成本

默认使用本地 Qwen3:8b（5.2GB，40K上下文，支持thinking模式）
可通过 config.yaml → segmentation.model 切换

第一层: 文本索引（快）
  - 从爆款视频的文案/字幕/OCR提取文本
  - 建立词级时间戳索引
  - 分析文案结构（hook/problem/solution/cta）、情绪曲线、关键词密度
  - 仅在文本分析不足以判断时，才进入第二层

第二层: 视觉分析（按需）
  - 关键帧提取（仅在关键时间点）
  - 画面构成分析
  - 色调/风格分析
"""
import hashlib
import json
import logging
import os
from dataclasses import dataclass, field
from typing import Optional

logger = logging.getLogger("adflow.hit_text")


@dataclass
class TextAnalysisResult:
    """爆款文本分析结果"""
    hit_id: str = ""
    source: str = ""               # "captions" | "ocr" | "manual" | "unknown"

    # 文案结构
    full_text: str = ""
    text_length: int = 0
    word_count: int = 0             # 中文字数

    # 结构分析
    hook_text: str = ""             # 开头3秒文案
    hook_type: str = ""             # 痛点/反常识/场景/数据/悬念
    narrative_structure: str = ""   # 叙事结构类型
    cta_text: str = ""              # 行动号召文案

    # 情绪分析
    emotion_curve: str = ""         # "激昂→紧迫→温和" 情绪变化
    primary_emotion: str = "中性"
    emotion_intensity: float = 0.5  # 0-1

    # 语言特征
    oral_score: float = 0.5         # 口语化程度
    info_density: float = 0.5       # 信息密度
    keyword_density: dict = field(default_factory=dict)  # 关键词词频
    sentence_lengths: list[int] = field(default_factory=list)  # 句长分布

    # 时间线
    text_timeline: list[dict] = field(default_factory=list)
    # [{"text": "句1", "start_ms": 0, "end_ms": 3000}, ...]

    # 元信息
    analyzed_at: str = ""
    cache_key: str = ""


class HitTextAnalyzer:
    """爆款文本分析器 — 文本优先，视觉按需

    使用方式:
      analyzer = HitTextAnalyzer()
      result = analyzer.analyze("path/to/hit_video.mp4")
      # → 返回文本层面的完整分析，仅当需要时才做视觉分析
    """

    def __init__(self, cache_dir: str = ""):
        self.cache_dir = cache_dir or os.path.join(
            os.path.dirname(__file__), "..", "..", "data", "_hit_text_cache")
        os.makedirs(self.cache_dir, exist_ok=True)

    def analyze(self, video_path: str, existing_captions: str = "",
                hit_metadata: dict | None = None) -> TextAnalysisResult:
        """第一层：文本分析（快速，无需GPU）

        Args:
            video_path: 爆款视频路径
            existing_captions: 已有的字幕/文案（如有）
            hit_metadata: 已有元数据（标题、标签等）
        """
        cache_key = self._cache_key(video_path)
        result = self._load_cache(cache_key)
        if result is not None:
            return result

        result = TextAnalysisResult(
            hit_id=os.path.basename(video_path),
            cache_key=cache_key,
        )

        # 1. 收集所有可用的文本源
        texts = self._collect_texts(video_path, existing_captions, hit_metadata)

        if not texts:
            result.source = "unknown"
            result.full_text = ""
            logger.warning("无可用文本: %s", video_path)
            return result

        result.full_text = texts.get("narration", "")
        result.text_length = len(result.full_text)
        result.word_count = sum(1 for c in result.full_text if '一' <= c <= '鿿')

        # 2. 分析文案结构
        result.hook_text = self._extract_hook(result.full_text, texts)
        result.hook_type = self._classify_hook_type(result.hook_text)
        result.narrative_structure = self._detect_structure(result.full_text)
        result.cta_text = self._extract_cta(result.full_text)

        # 3. 情绪分析
        result.primary_emotion, result.emotion_curve = self._analyze_emotion(
            result.full_text)
        result.emotion_intensity = self._calc_intensity(result.full_text)

        # 4. 语言特征
        result.oral_score = self._score_oral(result.full_text)
        result.info_density = self._score_info_density(result.full_text)
        result.keyword_density = self._extract_keywords(result.full_text)
        result.sentence_lengths = self._sentence_lengths(result.full_text)

        # 5. 构建文本时间线
        if texts.get("timeline"):
            result.text_timeline = texts["timeline"]

        result.analyzed_at = self._now()
        result.source = texts.get("source", "unknown")

        # 缓存
        self._save_cache(cache_key, result)

        logger.info(
            "爆款文本分析: %d字, hook=%s, 情绪=%s, 口语=%.2f",
            result.word_count, result.hook_type,
            result.primary_emotion, result.oral_score)

        return result

    def build_reference_context(self, result: TextAnalysisResult,
                                max_chars: int = 500) -> str:
        """将分析结果构建为 Agent prompt 参考上下文（文本优先）"""
        lines = [
            "## 爆款参考（文本分析）",
            f"- 开头类型: {result.hook_type}",
            f"- 情绪基调: {result.primary_emotion}",
            f"- 叙事结构: {result.narrative_structure}",
            f"- 口语化: {result.oral_score:.0%} | 信息密度: {result.info_density:.0%}",
        ]

        if result.hook_text:
            lines.append(f"\n### 开头文案\n{result.hook_text[:80]}")

        if result.cta_text:
            lines.append(f"\n### CTA文案\n{result.cta_text}")

        if result.full_text:
            text_preview = result.full_text[:max_chars]
            lines.append(f"\n### 完整文案（前{max_chars}字）\n{text_preview}")

        lines.append(
            "\n请参考以上爆款的结构和情绪节奏，但不要直接复制。"
            "结合产品特点，找到差异化的创意切入点。"
        )
        return "\n".join(lines)

    # ── 内部方法 ──

    def _collect_texts(self, video_path: str, captions: str,
                       metadata: dict | None) -> dict:
        """收集所有可用的文本源"""
        texts = {}

        # 1. 已有字幕/文案（优先）
        if captions and captions.strip():
            texts["narration"] = captions
            texts["source"] = "captions"
            return texts

        # 2. 元数据中的标题/描述
        if metadata:
            title = metadata.get("title", "")
            desc = metadata.get("narration_text", "")
            if desc:
                texts["narration"] = desc
                texts["source"] = "metadata"
                return texts
            if title:
                texts["narration"] = title
                texts["source"] = "title"
                return texts

        # 3. 尝试从文件名提取（例如 "爆款_文案内容.mp4"）
        fname = os.path.splitext(os.path.basename(video_path))[0]
        if len(fname) > 5:
            # 清理文件名中的标记
            clean = fname.replace("_", " ").replace("-", " ").strip()
            if any('一' <= c <= '鿿' for c in clean):
                texts["narration"] = clean
                texts["source"] = "filename"

        return texts

    @staticmethod
    def _extract_hook(full_text: str, texts: dict) -> str:
        """提取开头3秒的文案"""
        if not full_text:
            return ""
        # 取前30字作为hook区域
        return full_text[:30]

    @staticmethod
    def _classify_hook_type(hook_text: str) -> str:
        """分类开头类型"""
        if not hook_text:
            return "未知"
        if any(w in hook_text for w in ["是不是", "有没有", "有没有觉得"]):
            return "痛点"
        if any(w in hook_text for w in ["90%", "80%", "竟然", "居然", "没想到"]):
            return "反常识"
        if any(w in hook_text for w in ["出门", "早上", "下班", "周末", "在家"]):
            return "场景"
        if any(c.isdigit() for c in hook_text):
            return "数据"
        if any(w in hook_text for w in ["秘密", "不知道", "看了三遍"]):
            return "悬念"
        if any(w in hook_text for w in ["别人", "普通", "一般", "vs"]):
            return "对比"
        return "通用"

    @staticmethod
    def _detect_structure(full_text: str) -> str:
        """检测叙事结构"""
        if not full_text:
            return "未知"
        # 简单启发式
        if "但是" in full_text or "可是" in full_text:
            return "转折式"
        if "第一" in full_text or "首先" in full_text:
            return "列举式"
        if "以前" in full_text or "之前" in full_text:
            return "前后对比"
        return "直述式"

    @staticmethod
    def _extract_cta(full_text: str) -> str:
        """提取CTA文案"""
        if not full_text:
            return ""
        cta_keywords = ["下单", "点击", "购买", "抢", "立即", "马上", "限时", "链接"]
        for kw in cta_keywords:
            idx = full_text.rfind(kw)
            if idx >= 0:
                start = max(0, idx - 5)
                end = min(len(full_text), idx + 20)
                return full_text[start:end]
        # 取最后50字作为CTA区域
        return full_text[-50:] if len(full_text) > 50 else ""

    @staticmethod
    def _analyze_emotion(text: str) -> tuple[str, str]:
        """情绪分析（关键词规则）"""
        emotion_keywords = {
            "激昂": ["震撼", "重磅", "疯抢", "爆款", "绝了", "太牛", "必入"],
            "紧迫": ["最后", "马上", "立刻", "仅剩", "倒计时", "手慢"],
            "温和": ["推荐", "分享", "好用", "喜欢", "温暖", "日常"],
            "惊讶": ["竟然", "居然", "没想到", "天哪", "不可思议"],
        }

        scores = {}
        for emotion, kws in emotion_keywords.items():
            scores[emotion] = sum(1 for kw in kws if kw in text)

        if not scores:
            return "中性", "中性"

        primary = max(scores, key=scores.get)
        # 简化情绪曲线
        top2 = sorted(scores, key=scores.get, reverse=True)[:2]
        curve = "→".join(top2) if len(top2) > 1 else primary

        return primary, curve

    @staticmethod
    def _calc_intensity(text: str) -> float:
        """计算情绪强度"""
        intense_words = ["!", "！", "绝了", "太牛", "冲", "抢", "疯",
                          "限时", "史低", "错过", "必入", "手慢"]
        if not text:
            return 0.0
        hits = sum(1 for w in intense_words if w in text)
        return min(1.0, hits / max(len(text) / 10, 1))

    @staticmethod
    def _score_oral(text: str) -> float:
        """口语化评分"""
        if not text:
            return 0.0
        oral_words = ["真的", "特别", "太", "超", "贼", "老", "绝了", "说实话"]
        written_words = ["因此", "然而", "此外", "综上所述", "总而言之", "值得注意"]

        oral_hits = sum(1 for w in oral_words if w in text)
        written_hits = sum(1 for w in written_words if w in text)
        score = 0.5 + oral_hits * 0.1 - written_hits * 0.15
        return max(0.0, min(1.0, score))

    @staticmethod
    def _score_info_density(text: str) -> float:
        """信息密度评分"""
        if not text:
            return 0.0
        import re
        # 有数字 → 信息密度高
        numbers = len(re.findall(r'\d+', text))
        # 有专有名词/品牌词 → 信息密度高
        # 废话标记
        waste = sum(1 for w in ["今天给大家", "希望大家", "点击下方"] if w in text)
        score = 0.5 + numbers * 0.08 - waste * 0.2
        return max(0.0, min(1.0, score))

    @staticmethod
    def _extract_keywords(text: str) -> dict:
        """提取关键词密度"""
        if not text:
            return {}
        import re
        # 简单: 提取2-4字高频词
        words = {}
        for i in range(len(text) - 1):
            for length in [2, 3, 4]:
                if i + length <= len(text):
                    w = text[i:i + length]
                    if all('一' <= c <= '鿿' for c in w):
                        words[w] = words.get(w, 0) + 1

        # 排序取前10
        sorted_words = sorted(words.items(), key=lambda x: x[1], reverse=True)
        return dict(sorted_words[:10])

    @staticmethod
    def _sentence_lengths(text: str) -> list[int]:
        """统计句子长度分布"""
        lengths = []
        current = 0
        for char in text:
            if char in "，。！？；：、":
                if current > 0:
                    lengths.append(current)
                current = 0
            else:
                current += 1
        if current > 0:
            lengths.append(current)
        return lengths

    # ── 缓存 ──

    @staticmethod
    def _cache_key(video_path: str) -> str:
        """生成缓存键（基于文件路径+修改时间+大小）"""
        try:
            stat = os.stat(video_path)
            raw = f"{video_path}_{stat.st_mtime}_{stat.st_size}"
            return hashlib.md5(raw.encode()).hexdigest()
        except OSError:
            return hashlib.md5(video_path.encode()).hexdigest()

    def _load_cache(self, cache_key: str) -> Optional[TextAnalysisResult]:
        """加载缓存"""
        cache_path = os.path.join(self.cache_dir, f"{cache_key}.json")
        if not os.path.exists(cache_path):
            return None
        try:
            with open(cache_path, "r", encoding="utf-8") as f:
                data = json.load(f)
            return TextAnalysisResult(**data)
        except Exception:
            return None

    def _save_cache(self, cache_key: str, result: TextAnalysisResult):
        """保存缓存（参考 video-use 规则 #9: 缓存不重复分析）"""
        cache_path = os.path.join(self.cache_dir, f"{cache_key}.json")
        try:
            from dataclasses import asdict
            with open(cache_path, "w", encoding="utf-8") as f:
                json.dump(asdict(result), f, ensure_ascii=False, indent=2)
        except Exception as e:
            logger.debug("文本分析缓存失败: %s", e)

    @staticmethod
    def _now() -> str:
        from datetime import datetime
        return datetime.now().isoformat()
