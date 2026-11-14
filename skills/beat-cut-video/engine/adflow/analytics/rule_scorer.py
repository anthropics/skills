# -*- coding: utf-8 -*-
"""
前3秒预检门禁 — 出片前验证钩子质量

HookGate: 前3秒预检门禁，拦截低质量钩子
"""


class HookGate:
    """前3秒预检门禁 — 出片前验证钩子质量"""

    @staticmethod
    def validate(script, edit_timeline=None) -> dict:
        """验证前3秒质量

        Returns: {"passed": bool, "issues": [str], "score": float}
        """
        issues = []
        hook_shots = [s for s in script.shots
                      if getattr(s, 'role', '') in ("hook",)]
        if not hook_shots:
            hook_shots = script.shots[:1]  # 第一个镜头当钩子

        # 1. 钩子总时长 ≤3.5s
        hook_dur = sum(getattr(s, 'duration_ms', 3000) for s in hook_shots) / 1000
        if hook_dur > 3.5:
            issues.append(f"钩子时长 {hook_dur:.1f}s，超过3.5s红线")

        # 2. 钩子文案 ≤15字
        hook_text = "".join(getattr(s, 'narration_text', '') or ""
                           for s in hook_shots)
        if len(hook_text) > 15:
            issues.append(f"钩子文案 {len(hook_text)}字，建议≤12字")

        # 3. 钩子镜头数 ≤2
        if len(hook_shots) > 2:
            issues.append(f"钩子 {len(hook_shots)}个镜头，建议1-2个")

        # 4. 钩子有口播（字幕=口播，静音可懂性）
        has_subtitle = any(getattr(s, 'narration_segments', '')
                           or getattr(s, 'narration_text', '') for s in hook_shots)
        if not has_subtitle:
            issues.append("钩子无口播，静音可懂性不达标")

        # 5. 钩子情绪不能是"中性"
        hook_emotions = {getattr(s, 'required_emotion', '') for s in hook_shots}
        if hook_emotions == {"neutral"} or hook_emotions == {"中性"}:
            issues.append("钩子情绪为中性，缺乏吸引力")

        score = max(0, 10 - len(issues) * 2.5)
        return {
            "passed": len(issues) <= 1,
            "issues": issues,
            "score": score,
        }
