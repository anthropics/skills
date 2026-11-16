# -*- coding: utf-8 -*-
"""
智能时长计算器 — 信息流广告时长策略

原则:
  1. 30秒是黄金线 — 65%跑量素材在此区间
  2. 短就是好 — 能20秒讲清就别拖到30秒
  3. 配音为主 — 最终时长由配音长度决定，30秒是及格参考线
  4. 内容不硬裁 — 如果产品需要更长文案才能表达完整，允许超时

策略:
  default  → 30秒 (建议值，但不是硬限制)
  guideline → 15-45秒 (合理区间)
  max      → 60秒 (超过此值提示用户确认)
"""
import logging

logger = logging.getLogger("adflow.duration")


def suggest_duration(
    product_category: str = "",
    text_length: int = 0,
    custom_target_ms: int = 0,
) -> dict:
    """智能建议时长

    Args:
        product_category: 品类
        text_length: 文案字数（已知时估算）
        custom_target_ms: 用户自定义时长（0=自动）

    Returns:
        {
            "target_ms": 30000,       # 建议目标
            "guideline": "30秒黄金线",
            "min_ms": 15000,
            "max_ms": 60000,
            "is_suggestion": True,    # True=建议值可浮动，False=用户硬性指定
            "note": "..."
        }
    """
    DEFAULT = 30000   # 30秒黄金线
    MIN_MS = 15000    # 15秒下限
    MAX_MS = 60000    # 60秒上限

    if custom_target_ms > 0:
        return {
            "target_ms": custom_target_ms,
            "guideline": "用户指定",
            "min_ms": max(MIN_MS, custom_target_ms - 10000),
            "max_ms": min(MAX_MS, custom_target_ms + 15000),
            "is_suggestion": False,
            "note": f"使用用户指定的 {custom_target_ms/1000:.0f} 秒",
        }

    # 自动推荐：以30秒为基线
    target = DEFAULT

    # 品类微调
    category_hints = {
        "数码": 35000,   # 数码产品功能多，需要多展示
        "家电": 35000,
        "护肤": 30000,
        "美妆": 25000,   # 快消品可以短一些
        "零食": 25000,
        "服装": 25000,
        "母婴": 30000,
        "教育": 40000,   # 教育类需要讲清楚
        "金融": 35000,
    }
    target = category_hints.get(product_category, DEFAULT)

    # 文字量估算
    if text_length > 0:
        # 中文 TTS ~4 字/秒
        estimated_ms = int(text_length / 4 * 1000)
        # 给文案留30%余量（镜头切换、停顿、BGM）
        estimated_ms = int(estimated_ms * 1.3)
        # 限制在15-60秒区间
        estimated_ms = max(MIN_MS, min(MAX_MS, estimated_ms))
        # 取品类建议和字数估算的中间值
        target = int((target + estimated_ms) / 2)

    # 规范化到整秒
    target = (target // 1000) * 1000

    note = "30秒黄金线"
    if target < 25000:
        note = "短平快（快消品适合15-25秒）"
    elif target < 35000:
        note = "30秒黄金线（65%跑量素材区间）"
    else:
        note = "长文案模式（确保信息完整表达）"

    return {
        "target_ms": target,
        "guideline": note,
        "min_ms": MIN_MS,
        "max_ms": MAX_MS,
        "is_suggestion": True,
        "note": note,
    }


def fit_to_narration(narration_duration_ms: int,
                     target_ms: int = 30000,
                     is_suggestion: bool = True) -> int:
    """根据配音实际长度调整最终时长

    核心逻辑: 配音说了算，不注水也不截断
      - 配音比目标短 → 用配音长度（不啰嗦凑时长，重点不是长度是跳出率）
      - 配音比目标长 → 用配音长度（内容需要就说清楚，截断话不完整更致命）
      - 超过60秒 → 提醒但允许（如果内容能留住人，长也没问题）

    Args:
        narration_duration_ms: 配音实际时长
        target_ms: 建议目标时长（仅供参考）
        is_suggestion: 保留参数兼容，实际始终以配音为准

    Returns:
        最终视频时长(ms)
    """
    MAX_MS = 60000

    if narration_duration_ms <= 0:
        return target_ms

    if narration_duration_ms > MAX_MS:
        logger.warning(
            "配音 %.1f 秒超过60秒，长视频跳出率高，建议精简",
            narration_duration_ms / 1000)

    deviation = abs(narration_duration_ms - target_ms)
    if deviation < 5000:
        logger.info("配音 %.1f秒≈目标 %.1f秒，以配音为准",
                     narration_duration_ms / 1000, target_ms / 1000)
    elif narration_duration_ms < target_ms:
        logger.info("配音 %.1f秒 < 目标 %.1f秒，不注水",
                     narration_duration_ms / 1000, target_ms / 1000)
    else:
        logger.info("配音 %.1f秒 > 目标 %.1f秒，不截断",
                     narration_duration_ms / 1000, target_ms / 1000)

    return narration_duration_ms
