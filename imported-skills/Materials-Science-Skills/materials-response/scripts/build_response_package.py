#!/usr/bin/env python3
"""Scaffold a materials point-by-point reviewer response package."""

from __future__ import annotations

import argparse
import csv
from pathlib import Path


def load_comments(path: str | None) -> list[dict[str, str]]:
    if not path:
        return []
    with Path(path).open("r", encoding="utf-8-sig", newline="") as handle:
        return list(csv.DictReader(handle))


def default_comments(reviewers: int, comments_per_reviewer: int) -> list[dict[str, str]]:
    rows = []
    for reviewer in range(1, reviewers + 1):
        for comment in range(1, comments_per_reviewer + 1):
            rows.append(
                {
                    "reviewer": f"Reviewer {reviewer}",
                    "comment_id": f"{reviewer}.{comment}",
                    "concern_type": "[classify concern]",
                    "reviewer_comment": "[paste reviewer comment]",
                    "response_strategy": "accept and revise / clarify and revise / rebut with evidence / add limitation",
                    "manuscript_action": "[specific manuscript change]",
                    "evidence_needed": "[data/citation/line number needed]",
                    "risk_note": "[risk if unresolved]",
                }
            )
    return rows


def render(rows: list[dict[str, str]], title: str) -> str:
    chunks = [
        "# Response to Reviewers",
        "",
        f"Manuscript: {title}",
        "",
        "Dear Editor and Reviewers,",
        "",
        "We sincerely appreciate the constructive comments and suggestions. We have carefully revised the manuscript and provide point-by-point responses below.",
        "",
        "## Revision Summary",
        "",
        "| Area | Revision made | Manuscript location |",
        "|---|---|---|",
        "| [area] | [revision] | [page/line] |",
        "",
    ]
    current = None
    for row in rows:
        reviewer = row.get("reviewer", "Reviewer")
        if reviewer != current:
            chunks.extend([f"## {reviewer}", ""])
            current = reviewer
        chunks.extend(
            [
                f"### Comment {row.get('comment_id', '')}",
                "",
                f"**Concern type:** {row.get('concern_type', '[classify concern]')}",
                "",
                f"**Reviewer comment:** {row.get('reviewer_comment', '[paste reviewer comment]')}",
                "",
                f"**Response strategy:** {row.get('response_strategy', '[choose strategy]')}",
                "",
                "**Response:**",
                "",
                "We sincerely appreciate this comment. [Draft the technical response here and keep the claim tied to evidence.]",
                "",
                f"**Manuscript action:** {row.get('manuscript_action', '[specific change]')}",
                "",
                f"**Evidence needed:** {row.get('evidence_needed', '[data/citation/line number needed]')}",
                "",
                f"**Risk note:** {row.get('risk_note', '[risk if unresolved]')}",
                "",
            ]
        )
    chunks.extend(
        [
            "## Final Audit",
            "",
            "- [ ] Every comment has a response.",
            "- [ ] Every response has a manuscript action.",
            "- [ ] All line numbers are verified.",
            "- [ ] No new experiment is claimed unless data are available.",
            "- [ ] Tone is respectful and non-defensive.",
            "",
        ]
    )
    return "\n".join(chunks)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--title", default="[manuscript title]")
    parser.add_argument("--comments-csv", help="Optional CSV with reviewer comments.")
    parser.add_argument("--reviewers", type=int, default=2)
    parser.add_argument("--comments-per-reviewer", type=int, default=3)
    parser.add_argument("--output", default="materials-response-package.md")
    args = parser.parse_args()

    rows = load_comments(args.comments_csv) or default_comments(args.reviewers, args.comments_per_reviewer)
    Path(args.output).write_text(render(rows, args.title), encoding="utf-8")
    print(args.output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
