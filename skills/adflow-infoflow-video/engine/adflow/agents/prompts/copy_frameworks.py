# -*- coding: utf-8 -*-
"""
Top 文案框架库 v2 — 五段式爆款框架

对齐《信息流广告文案爆款框架》文档:
  五段: 钩子+福利 → 产品+卖点 → 功能展开 → 信任层 → 引导转化

每框架包含: 钩子句式库 + 卖点翻译法则 + 合规清单
"""
from dataclasses import dataclass


@dataclass
class CopyFramework:
    name: str
    hook_type: str          # 钩子类型: 痛点/悬念/反差/利益/情绪/证据
    hook_paradigm: str      # 前3秒范式: 反常识/利益前置/具体数字冲击/共鸣·悬念
    category: str           # 适用品类
    hook_template: str      # 钩子+福利模板 (≤25字)
    scene_template: str     # 产品出场+核心卖点
    feature_template: str   # 功能展开
    trust_template: str     # 信任层
    cta_template: str       # 引导转化
    total_chars: int        # 总字数建议


# ═══════════════════════════════════════
# 五段式框架库（按钩子类型组织）
# ═══════════════════════════════════════

FRAMEWORKS = [
    # ── 痛点+福利 ──
    CopyFramework(
        name="痛点直击·福利前置",
        hook_type="痛点+福利",
        hook_paradigm="共鸣/悬念",
        category="通用",
        hook_template="{痛点一句话}？今天{福利一句话}",
        scene_template="{场景}的时候，拿出{产品}，{核心卖点一句话效果}",
        feature_template="不仅{卖点1效果}，{卖点2场景+使用+效果}。{卖点3场景+使用}",
        trust_template="{人群范围}都能{放心用/放心吃}，{保障承诺}",
        cta_template="现在下单，{福利重申}只有{紧迫词}，{恢复原价/卖完即止}",
        total_chars=135,
    ),
    CopyFramework(
        name="痛点反问·数据冲击",
        hook_type="痛点+福利",
        hook_paradigm="具体数字冲击",
        category="护肤/健康",
        hook_template="{数据}%的人{痛点行为}？今天{福利}",
        scene_template="其实{常识纠正}。{产品}的{核心卖点}，{数据效果}",
        feature_template="{卖点A}的同时{卖点B}。{场景}一{使用}，{效果}",
        trust_template="{人群}+{检测报告}验证，{保障}无后顾之忧",
        cta_template="点击下方，{福利}限{数量}份，{时间窗口}恢复原价",
        total_chars=140,
    ),

    # ── 悬念+福利 ──
    CopyFramework(
        name="价格悬念·福利爆破",
        hook_type="悬念+福利",
        hook_paradigm="反常识",
        category="快消/日用",
        hook_template="{价格}能买到什么？今天{福利}",
        scene_template="就这个{产品}，{核心卖点}，{使用场景}一用就知道",
        feature_template="{卖点1场景+效果}。{卖点2使用方式}，{效果}。关键是{卖点3}",
        trust_template="{销量}人都在回购，{保障}不满意直接退",
        cta_template="点下方链接，{福利}只剩{数量}份，手慢真的没了",
        total_chars=130,
    ),

    # ── 反差+福利 ──
    CopyFramework(
        name="反差冲击·福利炸场",
        hook_type="反差+福利",
        hook_paradigm="反常识",
        category="数码/家电",
        hook_template="{高端对比物}同款{卖点}？却只要{价格}？今天{福利}",
        scene_template="就是这个{产品}，{核心卖点}，{使用效果一句话}",
        feature_template="{卖点1}不比{对比物}差。{卖点2场景+使用}，{效果}",
        trust_template="{保障}，{人群}都能用，{检测/认证}品质保证",
        cta_template="现在点击，{福利}只有{时间窗口}，卖完立刻恢复{原价}",
        total_chars=145,
    ),

    # ── 利益+福利 ──
    CopyFramework(
        name="利益承诺·效果前置",
        hook_type="利益+福利",
        hook_paradigm="利益前置",
        category="美妆/护肤",
        hook_template="{天数}{效果承诺}，今天{福利}",
        scene_template="自从用了{产品}，{使用场景}的时候{效果描述}",
        feature_template="{卖点1效果}不算什么，{卖点2}才是惊喜。{卖点3使用方式}",
        trust_template="{人群}+{敏感肌/孕妇}放心用，{保障}",
        cta_template="下方链接，{福利}前{数量}名还送{赠品}，卖完恢复原价",
        total_chars=140,
    ),

    # ── 情绪+福利 ──
    CopyFramework(
        name="情绪共鸣·找到救星",
        hook_type="情绪+福利",
        hook_paradigm="共鸣/悬念",
        category="食品/家居/母婴",
        hook_template="终于找到了！今天{福利}",
        scene_template="{疲惫/困扰场景}的时候，{产品}就是救星。{核心卖点}",
        feature_template="{卖点1场景+感受}。{卖点2}，{使用方式+效果}",
        trust_template="{人群}都能放心{吃/用}，{保障承诺}",
        cta_template="现在下单{福利}，{赠品/优惠}限今天，错过等一年",
        total_chars=130,
    ),

    # ── 证据+福利 ──
    CopyFramework(
        name="销量背书·社交证明",
        hook_type="证据+福利",
        hook_paradigm="具体数字冲击",
        category="通用/爆款",
        hook_template="{销量}人都在{行为}，今天{福利}",
        scene_template="就是这个{产品}，{核心卖点}，{效果一句话}",
        feature_template="回购率{数据}%，因为{卖点1}、{卖点2}。{场景+使用}",
        trust_template="{权威背书}+{保障}，{人群}都在回购",
        cta_template="点下方链接，{福利}限时{时间}，抢完立刻恢复原价",
        total_chars=140,
    ),
]

# 按钩子类型索引
FRAMEWORKS_BY_HOOK = {}
for fw in FRAMEWORKS:
    FRAMEWORKS_BY_HOOK.setdefault(fw.hook_type, []).append(fw)


def get_frameworks(hook_type: str = "", category: str = "",
                   max_count: int = 3) -> list[CopyFramework]:
    """获取匹配的文案框架"""
    candidates = []
    if hook_type:
        for key in FRAMEWORKS_BY_HOOK:
            if hook_type in key:
                candidates.extend(FRAMEWORKS_BY_HOOK[key])
    if not candidates:
        candidates = list(FRAMEWORKS)
    if category:
        category_match = [f for f in candidates if f.category in (category, "通用")]
        if category_match:
            candidates = category_match
    return candidates[:max_count]


def build_framework_prompt_context(hook_type: str = "",
                                   category: str = "",
                                   max_count: int = 2) -> str:
    """构建注入ScriptAgent的框架参考上下文"""
    frameworks = get_frameworks(hook_type, category, max_count)
    if not frameworks:
        return ""

    lines = ["## 爆款文案结构参考（学习怎么表达的，不是填空模板）", ""]
    for i, fw in enumerate(frameworks, 1):
        lines.append(f"### 参考{i}: {fw.name}")
        lines.append(f"- 前3秒范式: {fw.hook_paradigm}")
        lines.append(f"- 钩子方式: `{fw.hook_template}`")
        lines.append(f"- 产品引出: `{fw.scene_template}`")
        lines.append(f"- 卖点展开: `{fw.feature_template}`")
        lines.append(f"- 信任建立: `{fw.trust_template}`")
        lines.append(f"- 转化引导: `{fw.cta_template}`")
        lines.append(f"- 参考节奏: ~{fw.total_chars}字")
        lines.append("")
    lines.append("以上是爆款文案常见的表达方式，学它的节奏和语气，不要逐字填空。5个条件覆盖到了就行，顺序和比重你自己判断。")
    return "\n".join(lines)
