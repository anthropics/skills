"""Generate a cover letter skeleton from the submission manifest.

Reads the manifest, loads the journal template, and produces a 7-paragraph
skeleton with [LLM: ...] placeholders for the LLM to fill. Declaration
fields are filled from the manifest; empty fields become
[LIVE-VERIFICATION: ...] placeholders.
"""

from __future__ import annotations

import argparse
import datetime as _dt
import sys
from pathlib import Path

import yaml

from build_submission_package import _data_availability_line, prepare_submission_inputs
from template_support import SUPPORTED_JOURNALS, article_type_label, load_template


def _decl(value: str, label: str) -> str:
    if value and value.strip():
        return value.strip()
    return f"[LIVE-VERIFICATION: {label} — user must verify]"


def _get_suggested_reviewers(manifest: dict) -> list[str]:
    reviewers = manifest.get("suggested_reviewers") or []
    if isinstance(reviewers, str):
        return [reviewers] if reviewers.strip() else []
    if not isinstance(reviewers, list):
        return []
    return [reviewer for reviewer in reviewers if isinstance(reviewer, str) and reviewer.strip()]


def render_cover_letter(
    manifest: dict,
    template: dict,
    abstract: str,
    inputs: dict | None = None,
) -> str:
    journal_name = template.get("full_name", template.get("journal_id", ""))
    title = manifest.get("title", "[TITLE MISSING]")
    article_type = manifest.get("article_type", "research-article")
    article_label = article_type_label(template, article_type)
    decl_req = template.get("declaration_requirements", {})
    corresponding = manifest.get("corresponding_author", "[CORRESPONDING AUTHOR MISSING]")
    funding = _decl(manifest.get("funding", ""), "funding statement")
    conflicts = _decl(manifest.get("conflicts", ""), "conflict of interest declaration")
    data_line = _data_availability_line(manifest, inputs)
    code_line = ""
    if decl_req.get("code_availability"):
        code_status = manifest.get("code_availability_status", "")
        if code_status == "ready":
            code_line = "Code availability: ready"
        elif code_status == "not-applicable":
            code_line = "Code availability: not applicable"
        else:
            code_line = "[LIVE-VERIFICATION: code availability - verify if custom code was used]"
    reviewers = _get_suggested_reviewers(manifest)
    today = _dt.date.today().isoformat()

    lines = []
    lines.append(f"# Cover Letter — {journal_name}")
    lines.append("")
    lines.append(today)
    lines.append("")
    lines.append("Editorial Office")
    lines.append(journal_name)
    lines.append("")
    lines.append("Dear Editor,")
    lines.append("")
    lines.append(f'We wish to submit our manuscript entitled "{title}" for consideration as a {article_label} in {journal_name}.')
    lines.append("")
    lines.append("[LLM: One paragraph summarizing the problem, approach, and key finding. "
                 "Use the manuscript title, the abstract below, and the journal's "
                 "cover_letter_required_points. Do not repeat detailed methods or results.]")
    lines.append("")
    if abstract:
        lines.append("Abstract (for LLM reference):")
        lines.append(abstract)
        lines.append("")
    points = template.get("cover_letter_required_points", [])
    if points:
        lines.append("Journal triage points (for LLM reference):")
        for p in points:
            lines.append(f"- {p}")
        lines.append("")
    lines.append(f"We believe this work aligns with the scope of {journal_name} because "
                 "[LLM: one sentence explaining the specific fit, using the triage points above].")
    lines.append("")
    if any(decl_req.get(name) for name in ("funding", "conflict_of_interest", "data_availability", "code_availability")):
        lines.append("Declarations:")
    if decl_req.get("funding"):
        lines.append(f"- Funding: {funding}")
    if decl_req.get("conflict_of_interest"):
        lines.append(f"- Conflicts of interest: {conflicts}")
    if decl_req.get("data_availability"):
        lines.append(f"- {data_line}")
    if code_line:
        lines.append(f"- {code_line}")
    if reviewers:
        lines.append("- Suggested reviewers:")
        for r in reviewers:
            lines.append(f"  - {r}")
    else:
        lines.append("- Suggested reviewers: [omitted — supply real names only if available]")
    lines.append("")
    lines.append("Thank you for your consideration.")
    lines.append("")
    lines.append("Sincerely,")
    lines.append(corresponding)
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", required=True, help="path to submission-manifest.yaml")
    parser.add_argument("--abstract", default="", help="manuscript abstract (if writing state not available)")
    parser.add_argument("--output", default="-", help="output path or '-' for stdout")
    args = parser.parse_args(argv)

    manifest_path = Path(args.manifest).resolve()
    if not manifest_path.exists():
        print(f"manifest not found: {manifest_path}", file=sys.stderr)
        return 1
    with manifest_path.open(encoding="utf-8") as fh:
        manifest = yaml.safe_load(fh) or {}
    manifest, _, inputs = prepare_submission_inputs(manifest, manifest_path.parent)

    journal = manifest.get("target_journal")
    if journal not in SUPPORTED_JOURNALS:
        print(f"target_journal {journal!r} not in supported journals {SUPPORTED_JOURNALS}", file=sys.stderr)
        return 1

    template = load_template(journal)
    try:
        letter = render_cover_letter(manifest, template, args.abstract, inputs)
    except KeyError as exc:
        parser.error(str(exc))

    if args.output == "-":
        print(letter)
    else:
        Path(args.output).write_text(letter, encoding="utf-8")
        print(f"wrote {args.output}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
