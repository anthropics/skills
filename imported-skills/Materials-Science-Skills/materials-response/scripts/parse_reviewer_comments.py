#!/usr/bin/env python3
"""Parse reviewer comments from text/Markdown and generate a structured CSV.

Reads raw reviewer decision letters (Markdown or plain text) and extracts
individual comments, classifies concern types, and outputs a CSV compatible
with ``build_response_package.py``.

Usage::

    python parse_reviewer_comments.py review_letter.md --output comments.csv
    python parse_reviewer_comments.py review_letter.txt --reviewer-labels "Reviewer 1,Reviewer 2"
"""

from __future__ import annotations

import argparse
import csv
import re
from pathlib import Path


# ---------------------------------------------------------------------------
# Concern-type classifier
# ---------------------------------------------------------------------------

_CONCERN_PATTERNS: list[tuple[str, tuple[str, ...]]] = [
    ("novelty", (
        "novel", "novelty", "original", "incremental", "first time",
        "not new", "already been reported", "lack of novelty",
    )),
    ("methodology", (
        "method", "protocol", "procedure", "experimental design",
        "test method", "measurement", "calibration", "reproducib",
        "replicate", "sample size", "statistical",
    )),
    ("evidence", (
        "evidence", "data", "proof", "support", "demonstrate",
        "validate", "verify", "confirm", "insufficient data",
        "more data", "additional experiment",
    )),
    ("mechanism", (
        "mechanism", "mechanis", "why", "root cause", "explanation",
        "hypothesis", "underlying", "fundamental",
    )),
    ("writing", (
        "writing", "grammar", "typo", "clarity", "ambiguous",
        "unclear", "confusing", "restructure", "reorganize",
        "language", "readability", "figure quality",
    )),
    ("scope", (
        "scope", "out of scope", "within the scope", "journal fit",
        "better suited", "audience",
    )),
    ("references", (
        "reference", "citation", "cite", "bibliography", "literature",
        "missing reference", "outdated", "recent work",
    )),
]


def classify_concern(text: str) -> str:
    """Return the most likely concern type for a comment."""
    norm = text.lower()
    scores: dict[str, int] = {}
    for ctype, keywords in _CONCERN_PATTERNS:
        score = sum(1 for kw in keywords if kw in norm)
        if score:
            scores[ctype] = score
    if not scores:
        return "general"
    return max(scores, key=scores.get)  # type: ignore[arg-type]


# ---------------------------------------------------------------------------
# Reviewer comment parser
# ---------------------------------------------------------------------------

_REVIEWER_HEADING = re.compile(
    r"^#{1,3}\s*(reviewer\s+[ab\d]|reviewer\s+\d+)\b",
    re.IGNORECASE | re.MULTILINE,
)

_COMMENT_HEADING = re.compile(
    r"^#{1,4}\s*(?:comment|major\s+comment|minor\s+comment|point)\s*(\d+)",
    re.IGNORECASE | re.MULTILINE,
)

_NUMBERED_COMMENT = re.compile(
    r"^(\d+)\.\s*\[?severity[:\s]",
    re.IGNORECASE | re.MULTILINE,
)

_SIMPLE_NUMBERED = re.compile(
    r"^(?:\*\*)?(\d+)\.\*\*\s",
    re.MULTILINE,
)


def _split_by_reviewer(text: str, labels: list[str] | None) -> list[tuple[str, str]]:
    """Split text into (reviewer_label, body) pairs."""
    if labels:
        pattern = re.compile(
            r"^#{1,3}\s*(" + "|".join(re.escape(lb) for lb in labels) + r")\b",
            re.IGNORECASE | re.MULTILINE,
        )
    else:
        pattern = _REVIEWER_HEADING

    matches = list(pattern.finditer(text))
    if not matches:
        return [("Reviewer", text)]

    pairs: list[tuple[str, str]] = []
    for i, m in enumerate(matches):
        label = m.group(1).strip().title()
        start = m.end()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        pairs.append((label, text[start:end]))
    return pairs


def _extract_comments(body: str) -> list[str]:
    """Extract individual comment texts from a reviewer's section."""
    # Try numbered headings first (## Comment 1, ### Comment 2, ...)
    heading_matches = list(_COMMENT_HEADING.finditer(body))
    if len(heading_matches) >= 2:
        comments: list[str] = []
        for i, m in enumerate(heading_matches):
            start = m.end()
            end = heading_matches[i + 1].start() if i + 1 < len(heading_matches) else len(body)
            comments.append(body[start:end].strip())
        return comments

    # Try severity-tagged numbered comments: 1. [severity: ...]
    sev_matches = list(_NUMBERED_COMMENT.finditer(body))
    if len(sev_matches) >= 2:
        comments = []
        for i, m in enumerate(sev_matches):
            start = m.start()
            end = sev_matches[i + 1].start() if i + 1 < len(sev_matches) else len(body)
            comments.append(body[start:end].strip())
        return comments

    # Try simple numbered comments: 1. **text**
    num_matches = list(_SIMPLE_NUMBERED.finditer(body))
    if len(num_matches) >= 2:
        comments = []
        for i, m in enumerate(num_matches):
            start = m.start()
            end = num_matches[i + 1].start() if i + 1 < len(num_matches) else len(body)
            comments.append(body[start:end].strip())
        return comments

    # Fallback: treat entire body as one comment
    stripped = body.strip()
    return [stripped] if stripped else []


def parse_review_letter(
    text: str,
    reviewer_labels: list[str] | None = None,
) -> list[dict[str, str]]:
    """Parse a review letter into structured comment rows."""
    rows: list[dict[str, str]] = []
    reviewer_sections = _split_by_reviewer(text, reviewer_labels)

    for reviewer_label, body in reviewer_sections:
        comments = _extract_comments(body)
        for idx, comment_text in enumerate(comments, start=1):
            concern = classify_concern(comment_text)
            # Determine severity from text
            severity = "minor"
            if re.search(r"severity:\s*(major|high|critical)", comment_text, re.IGNORECASE):
                severity = "major"
            elif re.search(r"(major|critical|essential|fundamental|must|require)", comment_text[:200], re.IGNORECASE):
                severity = "major"

            rows.append({
                "reviewer": reviewer_label,
                "comment_id": f"{reviewer_label.split()[-1]}.{idx}",
                "concern_type": concern,
                "severity": severity,
                "reviewer_comment": comment_text[:500],
                "response_strategy": "[choose strategy]",
                "manuscript_action": "[specific change]",
                "evidence_needed": "[data/citation/line needed]",
                "risk_note": "[risk if unresolved]",
            })

    return rows


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

CSV_FIELDS = [
    "reviewer", "comment_id", "concern_type", "severity",
    "reviewer_comment", "response_strategy", "manuscript_action",
    "evidence_needed", "risk_note",
]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", help="Path to review letter (Markdown or plain text)")
    parser.add_argument("--output", "-o", default="reviewer-comments.csv",
                        help="Output CSV path (default: reviewer-comments.csv)")
    parser.add_argument("--reviewer-labels", default=None,
                        help='Comma-separated reviewer labels (e.g. "Reviewer 1,Reviewer 2")')
    args = parser.parse_args()

    text = Path(args.input).read_text(encoding="utf-8")
    labels = None
    if args.reviewer_labels:
        labels = [lb.strip() for lb in args.reviewer_labels.split(",")]

    rows = parse_review_letter(text, labels)
    if not rows:
        print("No reviewer comments found.", file=__import__("sys").stderr)
        return 1

    with Path(args.output).open("w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=CSV_FIELDS, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)

    print(f"Parsed {len(rows)} comments from {len(set(r['reviewer'] for r in rows))} reviewer(s).")
    print(args.output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
