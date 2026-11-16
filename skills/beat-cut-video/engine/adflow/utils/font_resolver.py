"""
中文字体解析 — 配置字体缺失时按平台探测系统 CJK 字体
"""

import os

# 常见中文字体候选（按平台排序，命中即返回）
_CJK_FONT_CANDIDATES = [
    # Windows
    "C:/Windows/Fonts/msyhbd.ttc",   # 微软雅黑 Bold
    "C:/Windows/Fonts/msyh.ttc",     # 微软雅黑
    "C:/Windows/Fonts/simhei.ttf",   # 黑体
    "C:/Windows/Fonts/simsun.ttc",   # 宋体
    # macOS
    "/System/Library/Fonts/PingFang.ttc",
    "/System/Library/Fonts/STHeiti Light.ttc",
    # Linux
    "/usr/share/fonts/opentype/noto/NotoSansCJK-Regular.ttc",
    "/usr/share/fonts/truetype/noto/NotoSansCJK-Regular.ttc",
]


def resolve_subtitle_font(config_value: str = "") -> str:
    """返回可用的中文字体路径。

    - config_value 非空且文件存在 → 原样返回
    - 否则按平台探测候选字体，命中即返回
    - 全都没命中 → 返回 config_value（或第一个候选），由调用方兜底
    """
    if config_value and os.path.exists(config_value):
        return config_value
    for cand in _CJK_FONT_CANDIDATES:
        if os.path.exists(cand):
            return cand
    return config_value or _CJK_FONT_CANDIDATES[0]
