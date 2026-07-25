"""Generate a journal-specific submission checklist.

Reads the journal-formats fact sheet and the journal-templates yaml and
assembles a markdown checklist. Deterministic; no LLM call.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from template_support import (
    SUPPORTED_JOURNALS,
    append_declaration_checklist_items,
    append_required_field_items,
    append_required_artifacts,
    article_type_label,
    find_article_type,
    field_is_required,
    load_template,
)


def render_checklist(template: dict, article_type: str) -> str:
    at = find_article_type(template, article_type)
    lines = []
    lines.append(f"# Submission Checklist - {template.get('full_name', template.get('journal_id'))}")
    lines.append("")
    lines.append(f"Article type: {article_type_label(template, article_type)}")
    lines.append(f"Word limit: {at.get('word_limit', 'verify')}")
    if at.get("abstract_required") is False:
        lines.append("Abstract: not required")
    else:
        lines.append(f"Abstract words: {at.get('abstract_words', 'verify')}")
        lines.append(f"Abstract structure: {at.get('abstract_structure', 'verify')}")
    lines.append("")
    lines.append("## Mandatory items")
    append_required_field_items(lines, template, article_type)
    if template.get("highlights_required"):
        rules = template.get("highlights_rules", {})
        lines.append(f"- [ ] Highlights {rules.get('min_count',3)}-{rules.get('max_count',5)} items, ≤{rules.get('max_characters_per_item',85)} characters each")
    if field_is_required(template, article_type, "declarations"):
        lines.append("")
        lines.append("## Declarations")
        append_declaration_checklist_items(lines, template)
    append_required_artifacts(lines, template)
    lines.append("")
    lines.append("## Cover letter")
    for point in template.get("cover_letter_required_points", []):
        lines.append(f"- [ ] Cover letter states: {point}")
    lines.append("")
    lines.append("## Live-verification items")
    for field in template.get("live_verification_fields", []):
        lines.append(f"- [LIVE-VERIFICATION: {field} — re-check against current Guide for Authors]")
    lines.append("")
    lines.append(f"Official class: {template.get('official_class', 'verify')}")
    lines.append(f"Submission portal: {template.get('submission_portal', 'verify')}")
    lines.append(f"Official template: {template.get('official_template_url', 'verify')}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--journal", required=True, choices=SUPPORTED_JOURNALS)
    parser.add_argument("--article-type", default="research-article")
    parser.add_argument("--output", default="-", help="output path or '-' for stdout")
    args = parser.parse_args(argv)

    template = load_template(args.journal)
    try:
        checklist = render_checklist(template, args.article_type)
    except KeyError as exc:
        parser.error(str(exc))

    if args.output == "-":
        print(checklist)
    else:
        Path(args.output).write_text(checklist, encoding="utf-8")
        print(f"wrote {args.output}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
