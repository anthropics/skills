# -*- coding: utf-8 -*-
"""
参考视频分析器 — 分析竞品/爆款视频，提取策略注入 Agent

参考 OpenMontage 的 reference-driven creation:
  用户贴一个视频链接 → 分析文案/节奏/场景/风格 → 生成差异化方案

分析维度:
  1. 文案层: 文本结构(hook/problem/solution/cta)、情绪曲线、关键词密度
  2. 节奏层: 镜头切换频率、时长分布、BPM
  3. 视觉层: 色调风格、景别分布、运镜方式
  4. 策略层: 受众洞察、差异化角度建议

输出: ReferenceContext → 直接注入 StrategyAgent + ScriptAgent prompt
"""
import hashlib
import json
import logging
import os
import time
from dataclasses import dataclass, field
from typing import Optional

logger = logging.getLogger("adflow.reference")


@dataclass
class ReferenceResult:
    """参考视频分析结果"""
    source: str = ""                     # 视频来源
    source_type: str = ""                # "url" | "local" | "hit_library"

    # 文案分析
    full_text: str = ""
    text_length: int = 0
    hook_text: str = ""                  # 开头文案
    hook_type: str = ""                  # 痛点/反常识/场景/数据/悬念
    narrative_structure: str = ""        # 转折式/列举式/前后对比/直述式
    cta_text: str = ""
    emotion_curve: str = ""              # "好奇→认同→渴望→行动"

    # 节奏分析
    shot_count: int = 0
    avg_shot_duration_sec: float = 0.0   # 平均镜头时长
    shot_pace: str = ""                  # "快节奏(<2s)" | "中速(2-4s)" | "舒缓(>4s)"
    bpm_estimate: float = 0.0            # BGM BPM 估算

    # 视觉分析
    dominant_colors: list[str] = field(default_factory=list)  # ["暖黄", "白", "绿"]
    color_temperature: str = ""          # "warm" | "cool" | "neutral"
    camera_style: str = ""               # "手持生活感" | "固定棚拍" | "航拍大片"
    shot_types: dict = field(default_factory=dict)  # {"closeup": 5, "medium": 3, ...}

    # 策略洞察
    target_audience: str = ""            # 推测的目标受众
    key_insight: str = ""                # 核心策略洞察（1句话）
    differentiation_angles: list[str] = field(default_factory=list)  # 差异化角度建议

    # 元信息
    confidence: float = 0.7              # 分析置信度
    analyzed_at: str = ""


class ReferenceAnalyzer:
    """参考视频分析器 — 对标 OpenMontage 的 reference-driven creation

    使用方式:
      analyzer = ReferenceAnalyzer()
      result = analyzer.analyze("https://<短视频平台域名>/video/xxx")
        # 或
      result = analyzer.analyze("/path/to/competitor_ad.mp4")

      # 构建 Agent 上下文
      context = analyzer.build_strategy_context(result)
      # → 注入 StrategyAgent.generate(style_context=context)
    """

    def __init__(self, cache_dir: str = ""):
        self.cache_dir = cache_dir or os.path.join(
            os.path.dirname(__file__), "..", "..", "data", "_reference_cache")
        os.makedirs(self.cache_dir, exist_ok=True)

    def analyze(
        self,
        source: str,
        source_type: str = "",
        existing_transcript: str = "",
        progress_callback=None,
    ) -> ReferenceResult:
        """分析参考视频

        Args:
            source: 视频 URL 或本地路径
            source_type: "url" | "local" | "hit_library"
            existing_transcript: 已有字幕/文案
            progress_callback: 进度回调
        """
        if not source_type:
            source_type = "local" if os.path.exists(source) else "url"

        # 缓存检查
        cache_key = self._cache_key(source)
        cached = self._load_cache(cache_key)
        if cached:
            return cached

        result = ReferenceResult(
            source=source,
            source_type=source_type,
        )

        self._report(progress_callback, f"分析参考视频: {source[:50]}...")

        # ── Layer 1: 文本分析 ──
        self._report(progress_callback, "Layer 1/3: 文案分析...")
        text_result = self._analyze_text(source, existing_transcript)
        result.full_text = text_result.get("full_text", "")
        result.text_length = len(result.full_text)
        result.hook_text = text_result.get("hook_text", "")
        result.hook_type = text_result.get("hook_type", "")
        result.narrative_structure = text_result.get("narrative_structure", "")
        result.cta_text = text_result.get("cta_text", "")
        result.emotion_curve = text_result.get("emotion_curve", "")

        # ── Layer 2: 节奏分析 ──
        self._report(progress_callback, "Layer 2/3: 节奏分析...")
        rhythm_result = self._analyze_rhythm(source)
        result.shot_count = rhythm_result.get("shot_count", 0)
        result.avg_shot_duration_sec = rhythm_result.get("avg_duration", 0)
        result.shot_pace = rhythm_result.get("pace", "")
        result.bpm_estimate = rhythm_result.get("bpm", 0)

        # ── Layer 3: 视觉分析 ──
        self._report(progress_callback, "Layer 3/3: 视觉分析...")
        visual_result = self._analyze_visual(source)
        result.dominant_colors = visual_result.get("dominant_colors", [])
        result.color_temperature = visual_result.get("temperature", "")
        result.camera_style = visual_result.get("camera_style", "")
        result.shot_types = visual_result.get("shot_types", {})

        # ── 策略洞察 ──
        result.target_audience = self._infer_audience(result)
        result.key_insight = self._extract_insight(result)
        result.differentiation_angles = self._generate_angles(result)
        result.confidence = self._calc_confidence(result)
        result.analyzed_at = time.strftime("%Y-%m-%d %H:%M:%S")

        # 缓存
        self._save_cache(cache_key, result)

        self._report(progress_callback,
                     f"分析完成: hook={result.hook_type}, "
                     f"节奏={result.shot_pace}, "
                     f"风格={result.camera_style}")

        return result

    def build_strategy_context(self, result: ReferenceResult,
                               product_category: str = "") -> str:
        """构建注入 StrategyAgent 的参考上下文"""
        lines = [
            "## 竞品参考视频分析（请参考其策略，但做差异化）",
            "",
            f"### 文案策略",
            f"- 开头类型: **{result.hook_type}** → 建议用不同的开头方式",
            f"- 叙事结构: {result.narrative_structure}",
            f"- 情绪曲线: {result.emotion_curve}",
        ]

        if result.hook_text:
            lines.append(f"- 参考开头: 「{result.hook_text[:50]}」")

        if result.cta_text:
            lines.append(f"- 参考CTA: 「{result.cta_text}」")

        lines.extend([
            "",
            f"### 节奏参考",
            f"- 镜头切换: {result.shot_pace} (平均{result.avg_shot_duration_sec:.1f}秒/镜)",
            f"- BGM BPM: ~{result.bpm_estimate:.0f}",
            "",
            f"### 视觉风格",
            f"- 色调: {result.color_temperature} ({', '.join(result.dominant_colors[:3])})",
            f"- 拍摄风格: {result.camera_style}",
            "",
            f"### 策略洞察",
            f"- 推测受众: {result.target_audience}",
            f"- 核心洞察: {result.key_insight}",
            "",
            f"### 差异化角度建议",
        ])

        for i, angle in enumerate(result.differentiation_angles[:3], 1):
            lines.append(f"{i}. {angle}")

        if product_category:
            lines.append(f"\n结合「{product_category}」品类特点，找到与竞品的差异点。")

        return "\n".join(lines)

    # ── 分析子模块 ──

    def _analyze_text(self, source: str, transcript: str = "") -> dict:
        """第一层：文本分析"""
        result = {}

        # 优先使用已有文案
        if transcript:
            result["full_text"] = transcript
        else:
            # 尝试从 hit_library 获取
            try:
                from adflow.analytics.hit_text_analyzer import HitTextAnalyzer
                analyzer = HitTextAnalyzer()
                hit_result = analyzer.analyze(source)
                result["full_text"] = hit_result.full_text
                result["hook_text"] = hit_result.hook_text
                result["hook_type"] = hit_result.hook_type
                result["narrative_structure"] = hit_result.narrative_structure
                result["cta_text"] = hit_result.cta_text
                result["emotion_curve"] = hit_result.emotion_curve
                return result
            except Exception as e:
                logger.debug("HitTextAnalyzer 不可用: %s", e)

        text = result.get("full_text", "")
        if not text:
            result["hook_text"] = ""
            result["hook_type"] = "未知"
            result["narrative_structure"] = "未知"
            result["cta_text"] = ""
            result["emotion_curve"] = "未知"
            return result

        # 规则分析（无 LLM 依赖）
        result["hook_text"] = text[:30] if len(text) > 30 else text
        result["hook_type"] = self._classify_hook(result["hook_text"])
        result["narrative_structure"] = self._detect_structure(text)
        result["cta_text"] = text[-50:] if len(text) > 50 else text
        result["emotion_curve"] = self._detect_emotion_curve(text)

        return result

    def _analyze_rhythm(self, source: str) -> dict:
        """第二层：节奏分析（场景切换检测）"""
        result = {
            "shot_count": 0,
            "avg_duration": 0,
            "pace": "未知",
            "bpm": 0,
        }

        if not os.path.exists(source):
            return result

        try:
            from adflow.engine.video_probe import VideoProbe
            info = VideoProbe.probe(source)

            total_sec = info.duration_sec
            if total_sec <= 0:
                return result

            # 使用 FFmpeg 检测场景切换
            import subprocess
            from adflow.utils.ffmpeg_finder import get_ffmpeg_cmd

            tmp_stats = source + "_scene_stats.txt"
            subprocess.run(
                [get_ffmpeg_cmd(), "-y", "-v", "quiet",
                 "-i", source,
                 "-vf", "select='gt(scene,0.3)',showinfo",
                 "-f", "null", "-"],
                capture_output=True, timeout=60,
            )

            # 简化：使用帧数估算
            # 连续画面变化 > 30% 视为场景切换
            frame_count = int(total_sec * info.fps)
            # 估算: 广告平均2-4秒一个镜头
            estimated_shots = max(1, int(total_sec / 3))
            avg_dur = total_sec / estimated_shots

            result["shot_count"] = estimated_shots
            result["avg_duration"] = round(avg_dur, 1)

            if avg_dur < 2:
                result["pace"] = "快节奏(<2s/镜)"
            elif avg_dur <= 4:
                result["pace"] = "中速(2-4s/镜)"
            else:
                result["pace"] = "舒缓(>4s/镜)"

            # BPM 估算（基于镜头切换频率）
            result["bpm"] = round(60 / max(avg_dur, 0.5))

        except Exception as e:
            logger.debug("节奏分析失败: %s", e)

        return result

    def _analyze_visual(self, source: str) -> dict:
        """第三层：视觉分析（色调、运镜）"""
        result = {
            "dominant_colors": [],
            "temperature": "unknown",
            "camera_style": "未知",
            "shot_types": {},
        }

        if not os.path.exists(source):
            return result

        try:
            # 提取关键帧进行色调分析
            from adflow.utils.ffmpeg_finder import get_ffmpeg_cmd
            import subprocess
            import tempfile

            tmp_dir = tempfile.mkdtemp(prefix="ref_frames_")
            subprocess.run(
                [get_ffmpeg_cmd(), "-y", "-v", "quiet",
                 "-i", source,
                 "-vf", "fps=1/3",  # 每3秒1帧
                 "-vframes", "5",
                 "-q:v", "2",
                 f"{tmp_dir}/frame_%02d.jpg"],
                capture_output=True, timeout=30,
            )

            # 尝试用 OpenCV 分析
            frame_colors = []
            for i in range(5):
                fp = os.path.join(tmp_dir, f"frame_{i+1:02d}.jpg")
                if not os.path.exists(fp):
                    break
                try:
                    import cv2
                    import numpy as np
                    img = cv2.imread(fp)
                    if img is not None:
                        avg_color = np.mean(img, axis=(0, 1))
                        frame_colors.append(avg_color)
                except ImportError:
                    break

            if frame_colors:
                avg = np.mean(frame_colors, axis=0)
                # BGR → 色温判断
                b, g, r = avg[0], avg[1], avg[2]
                if r > b + 20:
                    result["temperature"] = "warm"
                    result["dominant_colors"] = ["暖黄", "橙"]
                elif b > r + 20:
                    result["temperature"] = "cool"
                    result["dominant_colors"] = ["冷蓝", "白"]
                else:
                    result["temperature"] = "neutral"
                    result["dominant_colors"] = ["中性", "自然"]

            # 清理
            import shutil
            shutil.rmtree(tmp_dir, ignore_errors=True)

            # 运镜风格推断
            try:
                from adflow.engine.video_probe import VideoProbe
                info = VideoProbe.probe(source)
                # 手机竖拍 + 高帧率 → 可能手持
                if info.height > info.width and info.fps >= 30:
                    result["camera_style"] = "手持生活感（竖屏）"
                elif info.rotation != 0:
                    result["camera_style"] = "手持生活感"
                else:
                    result["camera_style"] = "固定棚拍/稳定器"
            except Exception:
                pass

        except Exception as e:
            logger.debug("视觉分析失败: %s", e)

        return result

    @staticmethod
    def _infer_audience(result: ReferenceResult) -> str:
        """推测目标受众"""
        text = result.full_text
        keywords = {
            "宝妈": ["宝宝", "婴儿", "奶粉", "辅食", "怀孕"],
            "白领": ["办公室", "上班", "加班", "职场", "开会", "下午茶"],
            "学生": ["考试", "宿舍", "学校", "考研", "学习"],
            "女性": ["护肤", "化妆", "美妆", "穿搭", "显瘦", "变美"],
            "男性": ["数码", "科技", "游戏", "运动", "健身"],
            "老年人": ["养生", "退休", "健康", "关节", "睡眠"],
        }
        for audience, kws in keywords.items():
            for kw in kws:
                if kw in text:
                    return audience
        return "泛人群"

    @staticmethod
    def _extract_insight(result: ReferenceResult) -> str:
        """提取核心策略洞察"""
        insights = []
        if result.hook_type == "痛点":
            insights.append("用'你也有这个困扰'的方式建立共情")
        elif result.hook_type == "反常识":
            insights.append("用认知冲突制造信息差吸引力")
        elif result.hook_type == "场景":
            insights.append("用真实生活场景降低广告感")
        elif result.hook_type == "数据":
            insights.append("用具体数字建立可信度")

        if result.shot_pace.startswith("快"):
            insights.append("快节奏营造紧迫感，适合冲动消费品类")

        if result.color_temperature == "warm":
            insights.append("暖色调营造亲和力和信任感")

        return "；".join(insights) if insights else "综合分析无特殊洞察"

    @staticmethod
    def _generate_angles(result: ReferenceResult) -> list[str]:
        """生成差异化角度建议"""
        angles = []

        # 反向思维：如果竞品用痛点，就用反常识
        hook_alternatives = {
            "痛点": ["反常识: 用数据打破认知", "场景: 用真实画面降低广告感"],
            "反常识": ["痛点: 更直接地戳用户焦虑", "对比: 前后效果可视化"],
            "场景": ["痛点: 把场景背后的困扰说出来", "悬念: 制造好奇勾子"],
            "数据": ["场景: 把数字变成真实体验", "反常识: 用更大的反差数据"],
            "悬念": ["痛点: 用结果吸引→展开痛点分析", "场景: 不断设问引导观看"],
        }
        alternatives = hook_alternatives.get(
            result.hook_type,
            ["痛点: 直接戳用户焦虑", "反常识: 打破认知的信息差"],
        )
        angles.extend(alternatives)

        angles.append("调整镜头节奏: 竞品"
                      f"{result.shot_pace}，可尝试相反的节奏风格")
        return angles

    @staticmethod
    def _calc_confidence(result: ReferenceResult) -> float:
        """计算分析置信度"""
        score = 0.5
        if result.full_text:
            score += 0.15
        if result.hook_type != "未知":
            score += 0.1
        if result.shot_count > 0:
            score += 0.1
        if result.camera_style != "未知":
            score += 0.1
        if result.dominant_colors:
            score += 0.05
        return min(1.0, score)

    @staticmethod
    def _classify_hook(text: str) -> str:
        if not text:
            return "未知"
        if any(w in text for w in ["是不是", "有没有", "有没有觉得"]):
            return "痛点"
        if any(w in text for w in ["90%", "80%", "竟然", "居然", "没想到", "其实"]):
            return "反常识"
        if any(w in text for w in ["出门", "早上", "下班", "周末", "在家", "夏天", "冬天"]):
            return "场景"
        if any(c.isdigit() for c in text):
            return "数据"
        if any(w in text for w in ["秘密", "不知道", "看了三遍", "差距"]):
            return "悬念"
        if any(w in text for w in ["别人", "普通", "一般", "vs"]):
            return "对比"
        return "直述"

    @staticmethod
    def _detect_structure(text: str) -> str:
        if not text:
            return "未知"
        if "但是" in text or "可是" in text or "不过" in text:
            return "转折式"
        if "第一" in text or "首先" in text:
            return "列举式"
        if "以前" in text or "之前" in text or "后来" in text:
            return "前后对比"
        return "直述式"

    @staticmethod
    def _detect_emotion_curve(text: str) -> str:
        emotions = []
        first_30 = text[:30]
        last_50 = text[-50:] if len(text) > 50 else text

        if any(w in first_30 for w in ["震撼", "竟然", "没想到", "绝了"]):
            emotions.append("惊讶")
        elif any(w in first_30 for w in ["是不是", "有没有"]):
            emotions.append("疑问")
        else:
            emotions.append("好奇")

        if any(w in last_50 for w in ["下单", "抢", "立即", "限时", "手慢"]):
            emotions.append("紧迫")
        else:
            emotions.append("渴望")

        emotions.append("行动")
        return "→".join(emotions[:3])

    # ── 缓存 ──

    def _cache_key(self, source: str) -> str:
        raw = source
        if os.path.exists(source):
            try:
                stat = os.stat(source)
                raw = f"{source}_{stat.st_mtime}_{stat.st_size}"
            except OSError:
                pass
        return hashlib.md5(raw.encode()).hexdigest()

    def _load_cache(self, key: str) -> Optional[ReferenceResult]:
        path = os.path.join(self.cache_dir, f"{key}.json")
        if not os.path.exists(path):
            return None
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
            return ReferenceResult(**data)
        except Exception:
            return None

    def _save_cache(self, key: str, result: ReferenceResult):
        from dataclasses import asdict
        path = os.path.join(self.cache_dir, f"{key}.json")
        try:
            with open(path, "w", encoding="utf-8") as f:
                json.dump(asdict(result), f, ensure_ascii=False, indent=2)
        except Exception as e:
            logger.debug("缓存保存失败: %s", e)

    @staticmethod
    def _report(callback, msg: str):
        if callback:
            callback(msg)
        else:
            logger.info(f"[ReferenceAnalyzer] {msg}")
