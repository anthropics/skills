# -*- coding: utf-8 -*-
"""
卖点翻译预处理器 — 在喂给LLM之前，把专业卖点翻译成用户语言

例如: "高膳食纤维+天然果胶" → "吃完特别通畅，第二天就能感觉到"
      "低GI高钾含钙"     → "控糖不发胖，比榴莲友好多了"

两层翻译:
  1. 死表命中 → 直接使用（零延迟）
  2. 死表 miss → 收集后一次 LLM 调用批量翻译，结果缓存到本地 JSON

这样LLM收到的不是成分表，而是已经翻译好的感受表达，
大大降低LLM写出"产品说明书式文案"的概率。
"""
import json
import logging
from pathlib import Path

logger = logging.getLogger("adflow.translator")

# 常见专业词→人话对照表（死表，快速命中）
TERM_MAP = {
    # 食品类
    "膳食纤维": "吃完通畅、肠道舒服",
    "高纤维": "吃完特别通畅",
    "天然果胶": "自然润滑肠道",
    "低GI": "控糖不发胖",
    "高钾": "对心脏好",
    "含钙": "补钙强骨",
    "蛋白酶": "帮助消化",
    "多酚": "抗氧化抗衰老",
    "类黄酮": "天然抗炎",
    "非添加糖": "天然甜不腻",
    "无糖添加": "配料干净，吃着放心",
    "独立包装": "随身带、随时吃",
    "开袋即食": "不用洗不用切",
    # 护肤类
    "烟酰胺": "用完脸亮了一个度",
    "玻尿酸": "涂上去水水润润",
    "透明质酸钠": "涂上去水水润润",
    "5μm": "上脸细腻到看不见粉感",
    "微囊包裹": "一天下来还是刚涂的样子",
    # 日用类
    "杀菌": "深度清洁",
    "除螨": "安心睡眠",
    # 通用
    "天然成分": "天然不刺激",
    "SGS检测": "敏感肌测过不过敏",
    "0添加": "孕妈妈都能放心用",
    "冷萃": "营养没被破坏效果更好",
}

# 翻译缓存路径
_CACHE_DIR = Path(__file__).parent.parent.parent / "data"
_CACHE_PATH = _CACHE_DIR / "_translation_cache.json"


def _load_cache() -> dict[str, str]:
    """加载翻译缓存"""
    if _CACHE_PATH.exists():
        try:
            with open(_CACHE_PATH, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            pass
    return {}


def _save_cache(cache: dict[str, str]) -> None:
    """保存翻译缓存"""
    _CACHE_DIR.mkdir(parents=True, exist_ok=True)
    try:
        with open(_CACHE_PATH, "w", encoding="utf-8") as f:
            json.dump(cache, f, ensure_ascii=False, indent=2)
    except Exception as e:
        logger.warning("翻译缓存保存失败: %s", e)


def _llm_translate(terms: list[str], category: str) -> dict[str, str]:
    """用 LLM 批量翻译专业卖点为人话

    Args:
        terms: 需要翻译的专业术语列表
        category: 产品品类

    Returns:
        {term: human_phrase} 映射
    """
    if not terms:
        return {}

    try:
        from adflow.agents.base_agent import BaseAgent
        agent = BaseAgent(temperature=0.3, task="rewrite")

        prompt = (
            "你是消费品文案专家，负责把专业术语翻译成用户能感受到的人话。\n\n"
            "规则:\n"
            "- 每一条翻译成一句用户能感受到的效果/体验\n"
            "- 不要保留专业名词（如'膳食纤维''烟酰胺'）\n"
            "- 用具体感受替代抽象概念（如'吃完通畅''脸亮了一个度'）\n"
            "- 尽量简短，控制在15字以内\n\n"
            "返回纯JSON对象，key是原词，value是翻译后的人话。\n"
            "不要包裹在代码块中。\n\n"
            "翻译示例:\n"
            "- 高膳食纤维 → 吃完特别通畅\n"
            "- 烟酰胺 → 用完脸亮了一个度\n"
            "- 冷萃工艺 → 营养没被高温破坏\n"
            "- 微囊包裹 → 一天下来还是刚涂的样子"
        )

        term_list = "\n".join(f"- {t}" for t in terms)
        result = agent.call_structured(
            system_prompt=prompt,
            user_message=f"品类: {category}\n请翻译以下专业术语:\n{term_list}",
            output_schema={
                "type": "object",
                "additionalProperties": {"type": "string"},
            },
            temperature=0.3,
        )

        # result 是 {term: human_phrase} 的 dict
        if isinstance(result, dict):
            filtered = {}
            for k, v in result.items():
                if isinstance(k, str) and isinstance(v, str) and k.strip() and v.strip():
                    filtered[k.strip()] = v.strip()
            if filtered:
                logger.info("LLM翻译了%d个卖点: %s", len(filtered), list(filtered.keys())[:5])
            return filtered

    except Exception as e:
        logger.warning("LLM卖点翻译失败，回退到原文: %s", e)

    return {}


class SellingPointTranslator:
    """卖点翻译器 — 专业词→用户语言（死表 + LLM fallback + 缓存）"""

    @staticmethod
    def translate(selling_points: list[str], category: str = "") -> list[dict]:
        """翻译卖点列表

        Returns: [{"original": "...", "translated": "...", "scene": "...", "effect": "..."}]
        """
        results = []
        missed: list[str] = []
        cache = _load_cache()

        for sp in selling_points:
            sp = sp.strip()
            if not sp:
                continue

            # 1. 先查缓存
            if sp in cache:
                translated = cache[sp]
            else:
                # 2. 查死表
                translated = sp
                for term, human in TERM_MAP.items():
                    if term in sp:
                        translated = human
                        break
                # 3. 死表也 miss → 标记等 LLM
                if translated == sp:
                    missed.append(sp)

            # 4. 生成场景+效果
            scene, effect = _infer_scene_effect(sp, category)

            results.append({
                "original": sp,
                "translated": translated,
                "scene": scene,
                "effect": effect,
            })

        # ── LLM批量翻译 miss 的卖点 ──
        if missed:
            llm_result = _llm_translate(missed, category)
            if llm_result:
                # 更新缓存
                cache.update(llm_result)
                _save_cache(cache)
                # 更新结果中的翻译
                for r in results:
                    if r["translated"] in missed:
                        r["translated"] = llm_result.get(r["original"], r["translated"])

        return results

    @staticmethod
    def build_context(translated: list[dict]) -> str:
        """构建注入LLM的翻译后上下文"""
        lines = ["## 产品卖点（已翻译成人话，直接用这些表达）"]
        for i, t in enumerate(translated, 1):
            lines.append(f"{i}. 卖点: {t['translated']}")
            if t['scene']:
                lines.append(f"   场景: {t['scene']}")
            if t['effect']:
                lines.append(f"   效果: {t['effect']}")
        lines.append("\n以上卖点已翻译，请在你的文案中直接使用这些表达，不要恢复专业名词。")
        return "\n".join(lines)


def _infer_scene_effect(point: str, category: str) -> tuple[str, str]:
    """从卖点推断使用场景和效果"""
    scene_hints = {
        "食": ("便秘的时候", "第二天就顺了"),
        "护肤": ("早上化妆前", "一天不脱妆"),
        "日用": ("打扫卫生时", "轻松搞定"),
        "数码": ("出门带在身上", "随时用"),
    }
    for key, (s, e) in scene_hints.items():
        if key in category or key in point:
            return s, e

    # 通用
    if "便秘" in point or "通畅" in point or "纤维" in point:
        return ("便秘的时候吃两颗", "第二天就顺了")
    if "糖" in point or "GI" in point:
        return ("下午茶时间", "不用担心发胖")
    if "包装" in point or "便携" in point:
        return ("出门放包里", "随时拿出来吃")
    if "钙" in point or "钾" in point:
        return ("日常补充", "营养够够的")

    return ("日常使用", "用了就知道")
