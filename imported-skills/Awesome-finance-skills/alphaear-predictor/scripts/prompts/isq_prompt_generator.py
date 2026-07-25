"""
ISQ prompt helpers to render dimension guidance directly from the template.
Any change in the template propagates to prompts automatically.
"""

from typing import List, Optional
from ..schema.isq_template import get_isq_template, ISQTemplate


def _ordered_dimension_keys(template: ISQTemplate, order: Optional[List[str]] = None) -> List[str]:
    if order:
        return [k for k in order if k in template.dimensions]
    # fallback to template insertion order
    return list(template.dimensions.keys())


def generate_isq_prompt_section(template_id: str = "default_isq_v1", order: Optional[List[str]] = None, include_header: bool = True) -> str:
    """Render ISQ dimension text block based on the template.
    This allows prompt text to stay in sync with template edits.
    """
    template = get_isq_template(template_id)
    keys = _ordered_dimension_keys(template, order)

    lines: List[str] = []
    if include_header:
        lines.append("### 1. ISQ 评估框架 (Investment Signal Quality)")
        lines.append(f"参考模板: {template.template_name} (id: {template.template_id})")
        lines.append("")
        lines.append("你需要对信号进行以下维度的评分：")
        lines.append("")

    for idx, key in enumerate(keys, start=1):
        spec = template.dimensions[key]
        examples = "；".join([f"{k}: {v}" for k, v in spec.examples.items()]) if spec.examples else ""
        lines.append(f"{idx}. **{spec.key} ({spec.name})**: {spec.range_type}")
        lines.append(f"   - 描述: {spec.description}")
        if spec.scale_factor and spec.scale_factor != 1.0:
            lines.append(f"   - 缩放因子: {spec.scale_factor}")
        if examples:
            lines.append(f"   - 示例: {examples}")
        lines.append("")

    return "\n".join(lines).rstrip()
