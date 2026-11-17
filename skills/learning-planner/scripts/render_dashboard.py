#!/usr/bin/env python3
"""
Render the Dashboard (markdown, and optionally a Notion-importable CSV) from
a learning-plan.json file.

Usage:
    python3 render_dashboard.py <plan.json> [--template <path>] [--output <path>]
                                 [--notion-csv <path>]

By default:
  --template defaults to assets/dashboard.template.md (relative to this script)
  --output   defaults to dashboard.md in the same directory as <plan.json>

The dashboard contains nine views, all derived from the same learning-plan.json
so they cannot drift out of sync with each other or with the Detailed Learning
Plan (see scripts/render_plan.py):

  1. Roadmap List   -- hierarchical view with status/category/priority
  2. Kanban         -- Not Started / In Progress / Blocked / Completed
  3. Timeline       -- suggested order with effort estimates
  4. Priority       -- grouped by high/medium/low
  5. Milestones     -- modules with is_milestone = true
  6. Dependency     -- Mermaid graph of prerequisites
  7. Available      -- modules whose prerequisites are satisfied
  8. Advanced       -- modules with category = advanced
  9. Optional       -- modules with category = optional

This script assumes <plan.json> has already passed scripts/validate_plan.py
and that scripts/update_progress.py has been run if statuses recently changed.
"""
import argparse
import csv
import os
import re

from _common import STATUS_LABELS, extract_section, fill, load_json, ordered_modules, read_file


KANBAN_COLUMNS = [
    ("available", "Not Started"),
    ("in-progress", "In Progress"),
    ("locked", "Blocked"),
    ("completed", "Completed"),
]


def module_line(m, fields=("status", "category", "priority")):
    parts = [f"**{m.get('title', '')}** (`{m.get('id', '')}`)"]
    extras = []
    for field in fields:
        if field == "status":
            extras.append(f"status: {STATUS_LABELS.get(m.get('status'), m.get('status', ''))}")
        elif field == "effort":
            extras.append(f"effort: {m.get('estimated_effort') or 'not specified'}")
        else:
            extras.append(f"{field}: {m.get(field, '')}")
    if extras:
        parts.append("(" + ", ".join(extras) + ")")
    return "- " + " ".join(parts)


def render_progress_summary(modules):
    total = len(modules)
    completed = sum(1 for m in modules if m.get("status") == "completed")
    overall_pct = round(100 * completed / total, 1) if total else 0.0

    lines = [f"- **Overall:** {completed} / {total} modules completed ({overall_pct}%)"]

    for cat in ("core", "optional", "advanced"):
        cat_modules = [m for m in modules if m.get("category") == cat]
        if cat_modules:
            cat_completed = sum(1 for m in cat_modules if m.get("status") == "completed")
            pct = round(100 * cat_completed / len(cat_modules), 1)
            lines.append(f"- **{cat.capitalize()}:** {cat_completed} / {len(cat_modules)} ({pct}%)")

    counts = {}
    for m in modules:
        s = m.get("status", "unknown")
        counts[s] = counts.get(s, 0) + 1
    breakdown = ", ".join(f"{STATUS_LABELS.get(k, k)}: {v}" for k, v in counts.items())
    lines.append(f"- **Status breakdown:** {breakdown}")

    return "\n".join(lines)


def render_roadmap_list_view(ordered):
    if not ordered:
        return "_No modules defined._"
    lines = []
    for m, depth in ordered:
        prefix = "  " * depth + "- "
        flags = []
        if m.get("is_milestone"):
            flags.append("milestone")
        if m.get("category") in ("optional", "advanced"):
            flags.append(m["category"])
        flag_str = f" [{', '.join(flags)}]" if flags else ""
        lines.append(
            f"{prefix}**{m.get('title', '')}** (`{m.get('id', '')}`){flag_str} -- "
            f"{STATUS_LABELS.get(m.get('status'), m.get('status', ''))}, "
            f"priority: {m.get('priority', '')}, sequencing: {m.get('sequencing', '')}"
        )
    return "\n".join(lines)


def render_kanban_view(modules):
    sections = []
    for status_key, column_name in KANBAN_COLUMNS:
        items = [m for m in modules if m.get("status") == status_key]
        sections.append(f"### {column_name} ({len(items)})")
        if items:
            sections.append("\n".join(module_line(m, fields=("category", "priority")) for m in items))
        else:
            sections.append("_None._")
    return "\n\n".join(sections)


def render_timeline_view(ordered):
    if not ordered:
        return "_No modules defined._"
    lines = []
    for i, (m, depth) in enumerate(ordered, start=1):
        seq_note = "parallel with surrounding modules" if m.get("sequencing") == "parallel" else "sequential"
        lines.append(
            f"{i}. **{m.get('title', '')}** (`{m.get('id', '')}`) -- "
            f"effort: {m.get('estimated_effort') or 'not specified'}, {seq_note}, "
            f"status: {STATUS_LABELS.get(m.get('status'), m.get('status', ''))}"
        )
    return "\n".join(lines)


def render_priority_view(modules):
    sections = []
    for level in ("high", "medium", "low"):
        items = [m for m in modules if m.get("priority") == level]
        sections.append(f"### {level.capitalize()} priority ({len(items)})")
        if items:
            sections.append("\n".join(module_line(m, fields=("status", "category")) for m in items))
        else:
            sections.append("_None._")
    return "\n\n".join(sections)


def render_milestones_view(modules, by_id):
    items = [m for m in modules if m.get("is_milestone")]
    if not items:
        return "_No milestones defined._"
    lines = []
    for m in items:
        unmet = [p for p in (m.get("prerequisites") or []) if by_id.get(p, {}).get("status") != "completed"]
        readiness = "ready" if not unmet else f"waiting on: {', '.join(unmet)}"
        lines.append(
            f"- **{m.get('title', '')}** (`{m.get('id', '')}`) -- "
            f"status: {STATUS_LABELS.get(m.get('status'), m.get('status', ''))}, {readiness}"
        )
    return "\n".join(lines)


def render_dependency_view(modules):
    if not modules:
        return "_No modules defined._"

    def node_id(mid):
        return re.sub(r"[^a-zA-Z0-9_]", "_", mid)

    lines = ["```mermaid", "graph TD"]
    for m in modules:
        nid = node_id(m["id"])
        label = m.get("title", m["id"]).replace('"', "'")
        lines.append(f'    {nid}["{label}"]')

    has_edges = False
    for m in modules:
        nid = node_id(m["id"])
        for prereq in m.get("prerequisites") or []:
            lines.append(f"    {node_id(prereq)} --> {nid}")
            has_edges = True

    lines.append("")
    lines.append("    classDef completed fill:#d4f7dc,stroke:#2e7d32;")
    lines.append("    classDef inprogress fill:#fff3cd,stroke:#f9a825;")
    lines.append("    classDef available fill:#cce5ff,stroke:#1565c0;")
    lines.append("    classDef locked fill:#f0f0f0,stroke:#9e9e9e;")
    status_to_class = {"completed": "completed", "in-progress": "inprogress", "available": "available", "locked": "locked"}
    for m in modules:
        cls = status_to_class.get(m.get("status"), "locked")
        lines.append(f"    class {node_id(m['id'])} {cls};")

    lines.append("```")
    if not has_edges:
        lines.insert(2, "    %% No prerequisite edges defined.")
    return "\n".join(lines)


def render_available_view(modules):
    items = [m for m in modules if m.get("status") == "available"]
    if not items:
        return "_Nothing is currently available -- either everything is blocked, in progress, or completed._"
    return "\n".join(module_line(m, fields=("priority", "category", "effort")) for m in items)


def render_category_view(modules, category, empty_message):
    items = [m for m in modules if m.get("category") == category]
    if not items:
        return empty_message
    return "\n".join(module_line(m, fields=("status", "priority")) for m in items)


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("plan", help="Path to learning-plan.json")
    default_template = os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "..", "assets", "dashboard.template.md"
    )
    parser.add_argument("--template", default=default_template, help="Path to dashboard.template.md")
    parser.add_argument("--output", default=None, help="Output path (default: dashboard.md next to <plan.json>)")
    parser.add_argument("--notion-csv", default=None, help="Also write a Notion-importable CSV to this path")
    args = parser.parse_args()

    data = load_json(args.plan)
    template_text = read_file(args.template)
    body_tpl = extract_section(template_text, "TEMPLATE:DASHBOARD")

    modules = data.get("modules", [])
    by_id = {m["id"]: m for m in modules if "id" in m}
    ordered = ordered_modules(modules)
    meta = data.get("meta", {})

    values = {
        "plan_title": meta.get("title", ""),
        "last_updated": meta.get("last_updated", ""),
        "progress_summary": render_progress_summary(modules),
        "roadmap_list_view": render_roadmap_list_view(ordered),
        "kanban_view": render_kanban_view(modules),
        "timeline_view": render_timeline_view(ordered),
        "priority_view": render_priority_view(modules),
        "milestones_view": render_milestones_view(modules, by_id),
        "dependency_view": render_dependency_view(modules),
        "available_view": render_available_view(modules),
        "advanced_view": render_category_view(modules, "advanced", "_No advanced topics defined._"),
        "optional_view": render_category_view(modules, "optional", "_No optional topics defined._"),
    }

    output = fill(body_tpl, values).strip("\n") + "\n"

    output_path = args.output or os.path.join(os.path.dirname(args.plan) or ".", "dashboard.md")
    with open(output_path, "w", encoding="utf-8") as f:
        f.write(output)
    print(f"Wrote {output_path}")

    if args.notion_csv:
        write_notion_csv(args.notion_csv, ordered, by_id)
        print(f"Wrote {args.notion_csv}")


def write_notion_csv(path, ordered, by_id):
    fieldnames = [
        "Title", "ID", "Status", "Category", "Sequencing", "Priority",
        "Skippable", "Is Milestone", "Estimated Effort", "Prerequisites", "Parent",
    ]
    with open(path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        for m, _depth in ordered:
            prereq_titles = [by_id[p]["title"] for p in (m.get("prerequisites") or []) if p in by_id]
            parent_title = by_id[m["parent_id"]]["title"] if m.get("parent_id") in by_id else ""
            writer.writerow({
                "Title": m.get("title", ""),
                "ID": m.get("id", ""),
                "Status": STATUS_LABELS.get(m.get("status"), m.get("status", "")),
                "Category": m.get("category", ""),
                "Sequencing": m.get("sequencing", ""),
                "Priority": m.get("priority", ""),
                "Skippable": "Yes" if m.get("skippable") else "No",
                "Is Milestone": "Yes" if m.get("is_milestone") else "No",
                "Estimated Effort": m.get("estimated_effort", ""),
                "Prerequisites": ", ".join(prereq_titles),
                "Parent": parent_title,
            })


if __name__ == "__main__":
    main()
