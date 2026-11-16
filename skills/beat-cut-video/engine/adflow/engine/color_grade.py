# -*- coding: utf-8 -*-
"""
调色引擎 — 两层调色系统

层1: 全局基线 — FFmpeg eq+curves 滤镜（亮度/对比度/饱和度/色温）
层2: LUT工作流 — .cube 3D LUT应用（品牌风格/电影感/自定义）

使用:
  engine = ColorGradeEngine()
  params = engine.params_from_config()  # 从config读取层1+层2
  chain = engine.build_filter_chain(params)  # 拼接滤镜链
"""
import os
from dataclasses import dataclass


@dataclass
class ColorGradeParams:
    """调色参数"""
    # 层1：全局基线
    brightness: float = 0.0       # -1.0~1.0
    contrast: float = 1.0         # 1.0=不变
    saturation: float = 1.0       # 1.0=不变
    gamma_r: float = 1.0
    gamma_g: float = 1.0
    gamma_b: float = 1.0

    # 层2：LUT
    lut_file: str = ""

    # 品类推荐
    category_preset: str = ""       # "美食"/"美妆"/"数码"等

    @property
    def has_global_grade(self) -> bool:
        return (self.brightness != 0 or self.contrast != 1.0 or
                self.saturation != 1.0 or self.gamma_r != 1.0 or
                self.gamma_g != 1.0 or self.gamma_b != 1.0)

    @property
    def has_lut(self) -> bool:
        return bool(self.lut_file)

    @property
    def is_empty(self) -> bool:
        return not (self.has_global_grade or self.has_lut)


# 品类推荐基线
CATEGORY_PRESETS = {
    "美妆": ColorGradeParams(brightness=0.03, contrast=1.08, saturation=1.12,
                             gamma_r=1.03, gamma_b=0.98),
    "美食": ColorGradeParams(brightness=0.05, contrast=1.10, saturation=1.20,
                             gamma_r=1.04, gamma_b=0.96),
    "数码": ColorGradeParams(contrast=1.12, saturation=1.05,
                             gamma_b=1.02, gamma_r=0.98),
    "服装": ColorGradeParams(brightness=0.02, contrast=1.06, saturation=1.10),
    "家居": ColorGradeParams(brightness=0.05, contrast=1.05, saturation=1.08,
                             gamma_r=1.02, gamma_b=0.99),
    "母婴": ColorGradeParams(brightness=0.03, contrast=1.05, saturation=1.10,
                             gamma_r=1.01, gamma_b=0.99),
}


class ColorGradeEngine:
    """调色引擎"""

    def __init__(self):
        from adflow.config_loader import config
        self.cfg = config.get("color_grade", {}) or {}

    # ── 层1: 滤镜链 ──

    def build_eq_filter(self, params: ColorGradeParams) -> str:
        """eq 滤镜: 亮度/对比度/饱和度"""
        parts = []
        if params.brightness != 0:
            parts.append(f"brightness={params.brightness:.3f}")
        if params.contrast != 1.0:
            parts.append(f"contrast={params.contrast:.3f}")
        if params.saturation != 1.0:
            parts.append(f"saturation={params.saturation:.3f}")
        return f"eq={':'.join(parts)}" if parts else ""

    def build_curves_filter(self, params: ColorGradeParams) -> str:
        """curves 滤镜: RGB三通道gamma"""
        curves = []
        for ch, g in [('r', params.gamma_r), ('g', params.gamma_g),
                       ('b', params.gamma_b)]:
            if g != 1.0:
                mid = 0.5 ** (1 / max(g, 0.1))
                curves.append(f"{ch}=0/0 0.5/{mid:.4f} 1/1")
        return f"curves={':'.join(curves)}" if curves else ""

    def build_lut_filter(self, params: ColorGradeParams) -> str:
        """lut3d 滤镜"""
        if params.lut_file and os.path.exists(params.lut_file):
            return f"lut3d='{params.lut_file}'"
        return ""

    def build_filter_chain(self, params: ColorGradeParams) -> str:
        """拼接完整滤镜链: eq,curves,lut3d"""
        parts = []
        eq = self.build_eq_filter(params)
        if eq:
            parts.append(eq)
        curves = self.build_curves_filter(params)
        if curves:
            parts.append(curves)
        lut = self.build_lut_filter(params)
        if lut:
            parts.append(lut)
        return ",".join(parts)

    # ── 工厂方法 ──

    @classmethod
    def params_from_config(cls) -> ColorGradeParams:
        """从config.yaml构建"""
        from adflow.config_loader import config
        cfg = config.get("color_grade", {}) or {}
        if not cfg.get("enabled", True):
            return ColorGradeParams()

        params = ColorGradeParams(
            brightness=cfg.get("brightness", 0.0),
            contrast=1.0 + cfg.get("contrast", 0.0),
            saturation=1.0 + cfg.get("saturation", 0.0),
        )

        temp = cfg.get("temperature", 0.0)
        if temp > 0:
            params.gamma_r = 1.0 + temp * 0.3
            params.gamma_b = 1.0 - temp * 0.2
        elif temp < 0:
            params.gamma_b = 1.0 + abs(temp) * 0.3
            params.gamma_r = 1.0 - abs(temp) * 0.2

        # LUT
        lut_cfg = cfg.get("lut", {})
        if isinstance(lut_cfg, dict) and lut_cfg.get("enabled"):
            lut_file = lut_cfg.get("default_lut", "")
            if lut_file:
                lut_dir = lut_cfg.get("lut_dir", "data/luts/")
                full = os.path.join(lut_dir, lut_file)
                if os.path.exists(full):
                    params.lut_file = full

        return params

    @classmethod
    def params_from_category(cls, category: str) -> ColorGradeParams:
        """品类推荐基线"""
        preset = CATEGORY_PRESETS.get(category)
        if preset:
            return preset
        return cls.params_from_config()
