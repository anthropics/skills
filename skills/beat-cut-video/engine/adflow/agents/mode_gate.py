# -*- coding: utf-8 -*-
"""
文案生成模式门控 — 根据输入类型选择生成策略

Mode:
  product_only:     只有产品信息 → 走创意矩阵发散（现有逻辑）
  reference_copy:   有 1 条爆款参考 → 爆款结构拆解+复用
  reference_mix:    有 2+ 条爆款参考 → 爆款混剪模式
  custom_text:      用户提供文案 → TextRewriter 改写+拆镜
  remix:            强制测新角度 → 选未使用角度
"""

from enum import Enum


class CopyMode(str, Enum):
    PRODUCT_ONLY = "product_only"
    REFERENCE_COPY = "reference_copy"
    REFERENCE_MIX = "reference_mix"
    CUSTOM_TEXT = "custom_text"
    CUSTOM_AUDIO = "custom_audio"
    REMIX = "remix"


class ModeGate:
    """文案生成模式门控"""

    @staticmethod
    def detect(
        custom_text: str = "",
        custom_audio: str = "",
        ref_hit_ids: list[str] | None = None,
        force_remix: bool = False,
    ) -> CopyMode:
        """根据输入参数自动判断应走哪种生成模式

        判断优先级：自定义输入 > 爆款参考 > 强制remix > 默认

        Args:
            custom_text: 用户自写文案
            custom_audio: 用户上传配音
            ref_hit_ids: 参考爆款ID列表
            force_remix: 强制使用测新角度模式

        Returns:
            对应的 CopyMode
        """
        if custom_text:
            return CopyMode.CUSTOM_TEXT
        if custom_audio:
            return CopyMode.CUSTOM_AUDIO
        if ref_hit_ids:
            if len(ref_hit_ids) >= 2:
                return CopyMode.REFERENCE_MIX
            return CopyMode.REFERENCE_COPY
        if force_remix:
            return CopyMode.REMIX
        return CopyMode.PRODUCT_ONLY

    @staticmethod
    def build_mode_context(mode: CopyMode, ref_hit_ids: list[str] | None = None) -> str:
        """构建注入 prompt 的模式上下文

        Args:
            mode: 当前模式
            ref_hit_ids: 爆款参考ID列表（REFERENCE_COPY/REFERENCE_MIX 时使用）

        Returns:
            注入 StrategyAgent/ScriptAgent 的上下文文本
        """
        if mode == CopyMode.CUSTOM_TEXT:
            return ""
        if mode == CopyMode.CUSTOM_AUDIO:
            return ""
        if mode == CopyMode.REMIX:
            return (
                "## 模式: 测新角度\n"
                "本次必须选择之前未使用过的全新角度，回避所有历史使用过的卖点×人群组合。\n"
                "大胆测试——有人工审核兜底。\n"
            )
        if mode == CopyMode.REFERENCE_COPY:
            count = len(ref_hit_ids) if ref_hit_ids else 1
            return (
                f"## 模式: 爆款参考\n"
                f"有 {count} 条爆款参考可用。\n"
                f"请重点拆解参考的结构和节奏，套用到当前产品上——学结构不抄内容。\n"
            )
        if mode == CopyMode.REFERENCE_MIX:
            count = len(ref_hit_ids) if ref_hit_ids else 2
            return (
                f"## 模式: 爆款混剪\n"
                f"有 {count} 条爆款参考可用。\n"
                f"请混剪多条爆款的结构——例如取A的开场方式+B的卖点展开+C的CTA设计，组合成全新文案。\n"
            )
        # PRODUCT_ONLY: 默认模式，不注入额外上下文
        return ""
