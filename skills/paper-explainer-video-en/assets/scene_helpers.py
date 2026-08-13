"""
Shared helpers for scenes.py (English skill).
- txt(text): Latin Text shortcut (default font Helvetica Neue) — use for English on-screen text.
- cn(text):  CJK Text shortcut (PingFang SC) — use only for any Chinese/Japanese (e.g. an author name).
- add_avatar_guard(scene): draws a red "host placeholder box" in the bottom-right while iterating,
  reminding you to keep animation clear of that zone. Shown when env SHOW_AVATAR_ZONE=1; hidden in
  the final render. The box position/size is computed precisely from pipeline_config.AVATAR, matching
  where the host actually lands in the final mux.
"""
import os
from manim import Text, Rectangle, RED

LATIN = "Helvetica Neue"   # always present on macOS; clean for English
CJK = "PingFang SC"        # for any Chinese/Japanese glyphs


def txt(text, **kwargs):
    """English / Latin Text shortcut."""
    kwargs.setdefault("font", LATIN)
    return Text(text, **kwargs)


def cn(text, **kwargs):
    """CJK Text shortcut (kept for author names etc.)."""
    kwargs.setdefault("font", CJK)
    return Text(text, **kwargs)


def _avatar_rect_units():
    """From the AVATAR config, compute the host's rectangle in manim coords (center + w/h, in units)."""
    from pipeline_config import AVATAR as A
    VW, VH = 1920, 1080
    dw = A["disp_w"]
    dh = dw * (A["H"] * A["crop"]) / A["W"]          # height after crop, scaled to disp_w
    x = VW - dw - A["margin_x"]                       # top-left
    y = VH - dh - A["margin_y"]
    cx, cy = x + dw / 2, y + dh / 2
    ppu = VH / 8.0                                    # manim: 8 units tall = 1080px -> 135 px/unit
    return (cx - VW / 2) / ppu, (VH / 2 - cy) / ppu, dw / ppu, dh / ppu


def add_avatar_guard(scene):
    """When SHOW_AVATAR_ZONE=1, add a bottom-right host placeholder box (debug only)."""
    if not os.environ.get("SHOW_AVATAR_ZONE"):
        return
    try:
        ux, uy, w, h = _avatar_rect_units()
    except Exception:
        ux, uy, w, h = 4.5, -3.2, 2.3, 1.5           # fallback (approx for the current default AVATAR)
    box = Rectangle(width=w, height=h, color=RED, stroke_width=2).move_to([ux, uy, 0])
    scene.add(box)
