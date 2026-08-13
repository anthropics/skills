"""
scenes.py 的共用小工具。
- cn(text): 中文 Text 快捷(PingFang SC)
- add_avatar_guard(scene): 迭代时在右下角画出"主播占位红框", 提醒动画避开该区域。
  设环境变量 SHOW_AVATAR_ZONE=1 时显示; 出片时不设(自动隐藏)。
  红框位置/大小**按 pipeline_config.AVATAR 精确算**, 与最终合成时主播落点一致。
"""
import os
from manim import Text, Rectangle, RED

CJK = "PingFang SC"


def cn(text, **kwargs):
    kwargs.setdefault("font", CJK)
    return Text(text, **kwargs)


def _avatar_rect_units():
    """根据 AVATAR 配置, 算出主播在 manim 坐标系里的矩形(中心 + 宽高, 单位)。"""
    from pipeline_config import AVATAR as A
    VW, VH = 1920, 1080
    dw = A["disp_w"]
    dh = dw * (A["H"] * A["crop"]) / A["W"]          # crop 后再 scale 到 disp_w 的高度
    x = VW - dw - A["margin_x"]                       # 左上角
    y = VH - dh - A["margin_y"]
    cx, cy = x + dw / 2, y + dh / 2
    ppu = VH / 8.0                                    # manim: 8 单位高 = 1080px → 135 px/单位
    return (cx - VW / 2) / ppu, (VH / 2 - cy) / ppu, dw / ppu, dh / ppu


def add_avatar_guard(scene):
    """SHOW_AVATAR_ZONE=1 时, 给场景加一个右下角主播占位红框(仅调试用)。"""
    if not os.environ.get("SHOW_AVATAR_ZONE"):
        return
    try:
        ux, uy, w, h = _avatar_rect_units()
    except Exception:
        ux, uy, w, h = 4.5, -3.2, 2.3, 1.5           # 兜底(当前默认 AVATAR 的近似值)
    box = Rectangle(width=w, height=h, color=RED, stroke_width=2).move_to([ux, uy, 0])
    scene.add(box)
