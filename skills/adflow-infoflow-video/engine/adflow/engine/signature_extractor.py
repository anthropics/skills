# -*- coding: utf-8 -*-
"""
6维特征签名提取器 — 结构化元组，不绑定任何产品词

维度: 角色序列 | 时长分布 | 情绪走势 | 句式骨架 | 叙事视角 | 段落转折
"""
import re
from collections import namedtuple

# 6维结构化签名
Signature = namedtuple("Signature", [
    "role_sequence",      # tuple[str]
    "duration_bucket",    # tuple[int]
    "emotion_curve",      # tuple[str] — ↖↗→↘↓
    "sentence_pattern",   # tuple[str] — 疑问/陈述/感叹/祈使/数据
    "narrative_pov",      # tuple[str] — 第一/第二/第三人称/无主语
    "transition_type",    # tuple[str] — 因果/转折/递进/并列/时间/总结
])

EMOTION_ORDER = {
    "anxious": 0, "serious": 1, "urgent": 1,
    "neutral": 2, "calm": 2,
    "curious": 3, "happy": 4, "excited": 5, "trust": 4, "surprise": 5,
}

DIMENSION_NAMES = {
    "role_sequence": "角色序列",
    "duration_bucket": "时长分布",
    "emotion_curve": "情绪走势",
    "sentence_pattern": "句式骨架",
    "narrative_pov": "叙事视角",
    "transition_type": "段落转折",
}

DIMENSION_SUGGESTIONS = {
    "role_sequence": "换镜头角色顺序，如省略problem直接hook→demo→cta，或加入comparison",
    "duration_bucket": "调整各段时长比例，如hook缩短到2秒，demo拉长到15秒",
    "emotion_curve": "换情绪走势，如从'好奇→信任'改成'焦虑→惊喜→兴奋'",
    "sentence_pattern": "换开头句式，如疑问句改成数据句、感叹句改成陈述句",
    "narrative_pov": "换叙事视角，如从'你'改成'我'或第三人称",
    "transition_type": "换段落转折方式，如因果改成转折、递进改成并列",
}


def extract_signature(script) -> Signature:
    """从 StoryboardScript 提取6维结构签名"""
    roles = []
    durations = []
    emotions = []
    patterns = []
    povs = []
    transitions = []

    shots = script.shots
    for i, shot in enumerate(shots):
        roles.append(shot.role or "b_roll")
        durations.append(shot.duration_ms)

        e = getattr(shot, 'required_emotion', '') or ''
        emotions.append(e)

        text = getattr(shot, 'narration_text', '') or ''
        patterns.append(extract_sentence_pattern(text))
        povs.append(infer_pov(text))

        if i > 0:
            transitions.append(extract_transition(shots[i-1], shot))

    return Signature(
        role_sequence=tuple(roles),
        duration_bucket=_bucket_durations(durations),
        emotion_curve=tuple(_emotion_to_arrows(emotions)),
        sentence_pattern=tuple(patterns),
        narrative_pov=tuple(povs),
        transition_type=tuple(transitions),
    )


def extract_sentence_pattern(text: str) -> str:
    """从句式推断句首类型，不提取具体词"""
    text = text.strip()
    if not text:
        return "陈述"
    if text.endswith(("？", "?")) or any(text.startswith(w) for w in ["为什么", "怎么", "难道"]):
        return "疑问"
    if text.endswith(("！", "!")) or any(w in text[:10] for w in ["太", "超", "绝了", "疯了"]):
        return "感叹"
    if any(text.startswith(w) for w in ["点击", "下单", "抢", "赶紧", "马上", "立刻", "现在"]):
        return "祈使"
    if re.search(r"\d+[%％]", text[:15]) or re.search(r"\d{2,}", text[:15]):
        return "数据"
    return "陈述"


def infer_pov(text: str) -> str:
    """推断叙事视角"""
    text = text.strip()
    if any(text.startswith(w) for w in ["你", "您的", "你们", "你是不是", "你有没有"]):
        return "第二人称"
    if any(text.startswith(w) for w in ["我", "我们", "咱", "小编"]):
        return "第一人称"
    if any(text.startswith(w) for w in ["他", "她", "它", "这个", "这款", "这"]):
        return "第三人称"
    return "无主语"


def extract_transition(prev_shot, curr_shot) -> str:
    """推断段间逻辑关系"""
    prev_role = getattr(prev_shot, 'role', '')
    curr_role = getattr(curr_shot, 'role', '')
    prev_text = (getattr(prev_shot, 'narration_text', '') or '')[:10]
    curr_text = (getattr(curr_shot, 'narration_text', '') or '')[:10]

    # 因果: problem→solution
    if prev_role == "problem" and curr_role in ("solution", "product_demo"):
        return "因果"
    # 转折: 任何→but
    if any(w in curr_text for w in ["但是", "可是", "不过", "然而"]):
        return "转折"
    # 递进: demo持续
    if prev_role == curr_role:
        return "递进"
    # 时间: hook→后续
    if prev_role == "hook":
        return "时间"
    # 总结→结束
    if curr_role == "cta":
        return "总结"
    return "并列"


def _bucket_durations(durations: list[int]) -> tuple[int, ...]:
    """时长分桶: 0-20%:1, 20-40%:2, 40-60%:3, 60-100%:4"""
    total = sum(durations) or 1
    buckets = []
    for d in durations:
        pct = d / total
        if pct < 0.20:
            buckets.append(1)
        elif pct < 0.40:
            buckets.append(2)
        elif pct < 0.60:
            buckets.append(3)
        else:
            buckets.append(4)
    return tuple(buckets)


def _emotion_to_arrows(emotions: list[str]) -> list[str]:
    """情绪序列→走势箭头"""
    arrows = []
    prev_val = None
    for e in emotions:
        val = EMOTION_ORDER.get(e, 2) if e else 2
        if prev_val is None:
            arrows.append("→")
        else:
            diff = val - prev_val
            if diff > 1:
                arrows.append("↑")
            elif diff == 1:
                arrows.append("↗")
            elif diff == 0:
                arrows.append("→")
            elif diff == -1:
                arrows.append("↘")
            else:
                arrows.append("↓")
        prev_val = val
    return arrows


def signature_distance(s1: Signature, s2: Signature) -> float:
    """两个签名间加权结构距离 (0-1)"""
    dims = [
        ("role_sequence",   0.15, _tuple_dist),
        ("duration_bucket", 0.10, _tuple_dist),
        ("emotion_curve",   0.20, _tuple_dist),
        ("sentence_pattern",0.25, _tuple_dist),
        ("narrative_pov",   0.15, _tuple_dist),
        ("transition_type", 0.15, _tuple_dist),
    ]
    total = 0.0
    for dim, w, fn in dims:
        v1 = getattr(s1, dim)
        v2 = getattr(s2, dim)
        total += w * fn(v1, v2)
    return total


def _tuple_dist(t1: tuple, t2: tuple) -> float:
    if not t1 and not t2:
        return 0.0
    ml = max(len(t1), len(t2))
    if ml == 0:
        return 0.0
    matches = sum(1 for a, b in zip(t1, t2) if a == b)
    return 1.0 - matches / ml
