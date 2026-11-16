# -*- coding: utf-8 -*-
"""
平台差异化文案风格 — 根据投放平台注入不同的语调/钩子/CTA/字幕风格

复用 config.yaml 中 platform_styles 段，支持:
  - douyin（抖音）: 口语化、强钩子、快节奏
  - xiaohongshu（小红书）: 种草、闺蜜安利、emoji
  - kuaishou（快手）: 接地气、老铁、价格敏感
  - shipinhao（视频号）: 情感故事、中老年友好
  - ocean_engine（巨量引擎）: 通用信息流

在 ScriptAgent prompt 末尾注入当前平台的风格约束。
"""

from adflow.config_loader import config


class PlatformStyle:
    """平台差异化风格"""

    @staticmethod
    def get_style(platform: str) -> dict:
        """获取平台风格配置，带默认回退"""
        style = config.get(f"platform_styles.{platform}")
        if style and isinstance(style, dict):
            return style
        # 未知平台回退到 douyin 默认
        return config.get("platform_styles.douyin", {})

    @staticmethod
    def build_prompt_context(platform: str) -> str:
        """构建注入 ScriptAgent prompt 的平台风格上下文"""
        style = PlatformStyle.get_style(platform)
        if not style:
            # 没有配置的平台风格，不注入
            return ""

        lines = [f"## 平台风格约束（{platform}）", ""]

        if tone := style.get("tone", ""):
            lines.append(f"- **语调要求**: {tone}")
        if hooks := style.get("hook_types", []):
            lines.append(f"- **推荐钩子类型**: {', '.join(hooks)}")
        if ctas := style.get("cta_phrases", []):
            lines.append(f"- **CTA用语偏好**: {', '.join(ctas)}")
        if speed := style.get("subtitle_speed", ""):
            lines.append(f"- **字幕节奏**: {speed}")
        if emoji := style.get("emoji_usage", False):
            lines.append("- **Emoji**: 适度使用 emoji 增强亲和力")
        if max_dur := style.get("max_duration_sec", 0):
            lines.append(f"- **时长上限**: {max_dur}秒")

        lines.append("")
        lines.append("请在文案中体现以上平台风格，尤其是语调和CTA用语。")
        return "\n".join(lines)
