#!/usr/bin/env python3
"""
Render the Detailed Learning Plan (markdown) from a learning-plan.json file.

Usage:
    python3 render_plan.py <plan.json> [--template <path>] [--output <path>]

By default:
  --template defaults to assets/learning-plan.template.md (relative to this script)
  --output   defaults to learning-plan.md in the same directory as <plan.json>

This script assumes <plan.json> has already passed scripts/validate_plan.py.
Modules are rendered in hierarchical order: top-level modules (parent_id=null)
in the order they appear in the JSON 'modules' array, each immediately
followed by its submodules (recursively, also in JSON order). This preserves
whatever learning order the plan's author intended.
"""
import argparse
import os
import re

from _common import STATUS_LABELS, extract_section, fill, load_json, ordered_modules, read_file


def slugify(text):
    text = text.lower().strip()
    text = re.sub(r"[^a-z0-9\s-]", "", text)
    text = re.sub(r"[\s_]+", "-", text)
    text = re.sub(r"-+", "-", text).strip("-")
    return text


def render_bullets(items):
    if not items:
        return "_None specified._"
    return "\n".join(f"- {item}" for item in items)


def render_evaluation(items):
    if not items:
        return "_None specified._"
    return "\n".join(f"- **{e.get('method', '')}**: {e.get('description', '')}" for e in items)


def render_resources(items):
    if not items:
        return "_None specified._"
    lines = []
    for r in items:
        line = f"- **{r.get('title', '')}** ({r.get('type', '')}) -- {r.get('source', '')}"
        if r.get("notes"):
            line += f" _{r['notes']}_"
        lines.append(line)
    return "\n".join(lines)


def render_prerequisites(ids, by_id):
    if not ids:
        return "_None -- this module has no prerequisites._"
    parts = []
    for pid in ids:
        title = by_id[pid]["title"] if pid in by_id else "?"
        parts.append(f"`{pid}` ({title})")
    return ", ".join(parts)


def render_module(m, depth, by_id):
    heading_marker = "##" if depth == 0 else "###"
    values = {
        "heading_marker": heading_marker,
        "title": m.get("title", ""),
        "milestone_marker": " (Milestone)" if m.get("is_milestone") else "",
        "id": m.get("id", ""),
        "status": STATUS_LABELS.get(m.get("status"), m.get("status", "")),
        "category": m.get("category", ""),
        "sequencing": m.get("sequencing", ""),
        "priority": m.get("priority", ""),
        "skippable": "Yes" if m.get("skippable") else "No",
        "estimated_effort": m.get("estimated_effort") or "_Not specified._",
        "prerequisites_list": render_prerequisites(m.get("prerequisites") or [], by_id),
        "learning_objectives_list": render_bullets(m.get("learning_objectives") or []),
        "deep_understanding_concepts_list": render_bullets(m.get("deep_understanding_concepts") or []),
        "common_mistakes_list": render_bullets(m.get("common_mistakes") or []),
        "expected_competence": m.get("expected_competence") or "_Not specified._",
        "industry_expectations": m.get("industry_expectations") or "_Not applicable._",
        "mastery_goals_list": render_bullets(m.get("mastery_goals") or []),
        "evaluation_list": render_evaluation(m.get("evaluation") or []),
        "real_world_competence_list": render_bullets(m.get("real_world_competence") or []),
        "resources_list": render_resources(m.get("resources") or []),
        "module_notes_section": (f"\n#### Notes\n\n{m['notes']}\n" if m.get("notes") else ""),
    }
    return values


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("plan", help="Path to learning-plan.json")
    default_template = os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "..", "assets", "learning-plan.template.md"
    )
    parser.add_argument("--template", default=default_template, help="Path to learning-plan.template.md")
    parser.add_argument("--output", default=None, help="Output path (default: learning-plan.md next to <plan.json>)")
    args = parser.parse_args()

    data = load_json(args.plan)
    template_text = read_file(args.template)
    header_tpl = extract_section(template_text, "TEMPLATE:HEADER")
    module_tpl = extract_section(template_text, "TEMPLATE:MODULE")

    modules = data.get("modules", [])
    by_id = {m["id"]: m for m in modules if "id" in m}
    ordered = ordered_modules(modules)

    index_lines = []
    for m, depth in ordered:
        slug = slugify(m.get("title", ""))
        status_label = STATUS_LABELS.get(m.get("status"), m.get("status", ""))
        index_lines.append("  " * depth + f"- [{m.get('title', '')}](#{slug}) -- {status_label}")
    module_index = "\n".join(index_lines) if index_lines else "_No modules defined._"

    meta = data.get("meta", {})
    header_values = {
        "plan_title": meta.get("title", ""),
        "discipline": meta.get("discipline", ""),
        "goal_type": meta.get("goal_type", ""),
        "target_outcome": meta.get("target_outcome") or "_Not specified._",
        "current_level": meta.get("current_level") or "_Not specified._",
        "timeline": meta.get("timeline") or "_Not specified._",
        "created_date": meta.get("created_date", ""),
        "last_updated": meta.get("last_updated", ""),
        "roadmap_notes": meta.get("notes", ""),
        "module_index": module_index,
    }

    output_parts = [fill(header_tpl, header_values)]
    for m, depth in ordered:
        output_parts.append(fill(module_tpl, render_module(m, depth, by_id)))

    output = "\n\n".join(output_parts) + "\n"

    output_path = args.output or os.path.join(os.path.dirname(args.plan) or ".", "learning-plan.md")
    with open(output_path, "w", encoding="utf-8") as f:
        f.write(output)

    print(f"Wrote {output_path} ({len(ordered)} modules)")


if __name__ == "__main__":
    main()
