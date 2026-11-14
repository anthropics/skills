# -*- coding: utf-8 -*-
"""
去AI感检测器 — 7大死亡气味扫描

来自信息流广告投放实践经验: AI 生成的文案即使结构正确，
也会因为「AI味」导致完播率暴跌。这7项检测专门识别并消除AI味。

检测项:
  1. 开场AI词 ("在当今/随着/众所周知")
  2. 段落过于工整 (排比/对仗结构)
  3. 书面化用词 ("此外/然而/综上所述")
  4. 缺少口语过渡 ("你看/说真的/跟你说")
  5. 缺少停顿/重复/强调
  6. 情绪平淡
  7. 结尾僵硬

命中 ≥ 3项 → 自动打回重写
"""
import re
from dataclasses import dataclass, field


@dataclass
class AISmellResult:
    """AI感检测结果"""
    total_hits: int = 0                    # 命中项数
    hits: list[dict] = field(default_factory=list)  # [{"item": 1, "detail": "..."}]
    score: float = 10.0                    # 10=无AI感, 0=AI感极重
    needs_rewrite: bool = False            # 是否需要重写
    suggestions: list[str] = field(default_factory=list)
    summary: str = ""


class AISmellDetector:
    """AI感检测器 — 7大死亡气味"""

    # 阈值: 命中 ≥3项 → 打回重写
    REWRITE_THRESHOLD = 3

    def detect(self, text: str) -> AISmellResult:
        """执行7项AI感检测

        Args:
            text: 文案全文 (narration_text 拼接)

        Returns:
            AISmellResult
        """
        result = AISmellResult()
        hits = []

        # ── 1. 开场AI词 ──
        first_30 = text[:30] if len(text) > 30 else text
        opening_patterns = [
            r'在当今', r'随着.*的发展', r'众所周知', r'在.*时代背景下',
            r'近年来', r'当下', r'现代社会',
        ]
        for pat in opening_patterns:
            if re.search(pat, first_30):
                hits.append({
                    "item": 1,
                    "name": "开场AI词",
                    "detail": f"开头包含AI高频词: {pat}",
                    "fix": "换成口语化开头: '你有没有...' / '这个东西...' / 直接进入场景",
                })
                break

        # ── 2. 段落过于工整 (排比/对仗) ──
        # 检测连续3句长度相近的句子
        sentences = re.split(r'[。！？，]', text)
        sentences = [s.strip() for s in sentences if s.strip() and len(s.strip()) > 5]
        if len(sentences) >= 3:
            # 检查是否有3句长度差异<20%的连续句
            for i in range(len(sentences) - 2):
                lens = [len(sentences[i]), len(sentences[i + 1]), len(sentences[i + 2])]
                avg_len = sum(lens) / 3
                if all(abs(l - avg_len) / max(avg_len, 1) < 0.2 for l in lens):
                    hits.append({
                        "item": 2,
                        "name": "段落过于工整",
                        "detail": f"连续3句长度均匀 (排比/对仗感): "
                                  f"{lens[0]},{lens[1]},{lens[2]}字",
                        "fix": "打乱一句的节奏: 加个口语词、变短一句、拉长一句",
                    })
                    break

        # ── 3. 书面化用词 ──
        written_words = {
            "此外": "换成'还有'/'而且'",
            "然而": "换成'但是'/'可是'",
            "因此": "换成'所以'",
            "综上所述": "删掉，直接说结论",
            "总而言之": "删掉",
            "值得注意": "删掉",
            "不可忽视": "删掉",
            "毋庸置疑": "删掉",
            "显而易见": "删掉",
        }
        found_written = []
        for word, fix in written_words.items():
            if word in text:
                found_written.append(f"{word}→{fix}")
        if found_written:
            hits.append({
                "item": 3,
                "name": "书面化用词",
                "detail": f"检测到: {', '.join(found_written[:3])}",
                "fix": "全部换成口语表达",
            })

        # ── 4. 缺少口语过渡 ──
        oral_transitions = [
            "你看", "说真的", "跟你说", "说实话", "你知道吗",
            "就是", "那种", "哎", "哇", "天哪", "真的假的",
        ]
        oral_count = sum(1 for t in oral_transitions if t in text)
        if oral_count == 0:
            hits.append({
                "item": 4,
                "name": "缺少口语过渡",
                "detail": "全文无口语化过渡词",
                "fix": "在1-2处加入: '你看' / '说真的' / '你知道吗'",
            })

        # ── 5. 缺少停顿/重复/强调 ──
        emphasis_patterns = [
            r'([!！]{2,})',           # 连续感叹号
            r'真的.*真的',             # 重复强调
            r'太.{1,3}了',             # "太好了""太值了"
            r'(超级|非常|特别).{2,6}', # 程度副词
        ]
        emphasis_count = sum(
            1 for pat in emphasis_patterns if re.search(pat, text))
        if emphasis_count < 2:
            hits.append({
                "item": 5,
                "name": "缺少停顿/重复/强调",
                "detail": f"全文仅{emphasis_count}处口语强调",
                "fix": "加1-2个: '真的真的' / '太太太太太' / '超级.....'",
            })

        # ── 6. 情绪平淡 ──
        emotion_words = [
            "绝了", "太牛", "疯抢", "爆款", "惊呆了", "冲", "抢",
            "竟然", "居然", "没想到", "天哪", "厉害了", "顶不住",
        ]
        emotion_count = sum(1 for w in emotion_words if w in text)
        if emotion_count < 3:
            hits.append({
                "item": 6,
                "name": "情绪平淡",
                "detail": f"全文仅{emotion_count}处情绪词",
                "fix": "加2-3个情绪词: '绝了' / '冲' / '真的顶不住'",
            })

        # ── 7. 结尾僵硬 ──
        last_50 = text[-50:] if len(text) > 50 else text
        stiff_endings = [
            "赶快行动吧", "快来试试吧", "不要错过哦", "期待您的光临",
            "以上就是", "希望你喜欢", "谢谢观看", "欢迎关注",
        ]
        for ending in stiff_endings:
            if ending in last_50:
                hits.append({
                    "item": 7,
                    "name": "结尾僵硬",
                    "detail": f"结尾用了模板化表达: '{ending}'",
                    "fix": "换成: 紧迫感+具体指令: '现在下单立减XX' / '手慢真的没了'",
                })
                break

        # ── 汇总 ──
        result.total_hits = len(hits)
        result.hits = hits
        result.score = max(0, 10 - len(hits) * 1.5)
        result.needs_rewrite = len(hits) >= self.REWRITE_THRESHOLD
        result.suggestions = [h["fix"] for h in hits]

        # 生成摘要
        if len(hits) == 0:
            result.summary = "✅ 无AI感，口语自然"
        elif len(hits) < self.REWRITE_THRESHOLD:
            names = [h["name"] for h in hits]
            result.summary = f"⚠️ 轻微AI感 ({len(hits)}项: {', '.join(names)})"
        else:
            names = [h["name"] for h in hits]
            result.summary = f"❌ AI感较重 ({len(hits)}项: {', '.join(names)})，需要重写"

        return result


# ── 便捷函数 ──

def detect_ai_smell(text: str) -> AISmellResult:
    """快速检测AI感"""
    return AISmellDetector().detect(text)
