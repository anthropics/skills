#!/usr/bin/env python3
"""annotation_extractor.py - Extract severity-tagged review annotations from markdown.

Stdlib-only. Scans the same markdown source the diff_parser walks, finds
severity callouts and inline review markers, and attaches each annotation to
the nearest preceding diff block. The result is what the renderer puts in
the right margin of the 2-column layout.

Severity conventions accepted:

  GFM callouts (preferred):
      > [!BLOCKER]    must-fix before merge
      > [!MAJOR]      strongly recommend addressing
      > [!MINOR]      worth fixing
      > [!NIT]        cosmetic / style preference

  Inline markers (legacy, less structured):
      blocker: <prose>
      major:   <prose>
      minor:   <prose>
      nit:     <prose>
      LGTM     (treated as APPROVAL marker; not severity-coded)

The --severity-convention flag accepts a custom 4-tier ordering, e.g.
"critical,important,suggestion,nit" — but defaults to the BLOCKER/MAJOR/
MINOR/NIT convention. The order matters: position 0 = most severe.

Attachment heuristic: each annotation attaches to the most recent diff block
that appeared above it in the markdown source (by source line number). If
no diff appears above, the annotation is "unanchored" and the renderer
shows it in a "general comments" section.

NO LLM CALLS. Pure regex + line-index attachment.

Usage:
    python annotation_extractor.py --input review.md --diff-blocks hunks.json
    python annotation_extractor.py --sample
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

DEFAULT_SEVERITY_CONVENTION = ["BLOCKER", "MAJOR", "MINOR", "NIT"]

CALLOUT_OPEN_RE = re.compile(r"^>\s*\[!([A-Z]+)\]\s*$")
BLOCKQUOTE_RE = re.compile(r"^>\s?(.*)$")
INLINE_MARKER_RE = re.compile(r"^(?P<sev>[A-Za-z]+):\s+(?P<body>.+)$")
APPROVAL_RE = re.compile(r"^(LGTM|👍|approved|approve)\s*$", re.IGNORECASE)


def extract_annotations(
    text: str,
    diff_blocks: dict[str, Any] | None,
    severity_convention: list[str],
) -> dict[str, Any]:
    """Returns {annotations: [...], approvals: [...], summary: {...}}."""
    lines = text.splitlines()
    upper_severities = {s.upper() for s in severity_convention}

    # Index of diff-block source lines, for attachment lookup
    diff_source_lines: list[tuple[int, int]] = []  # (source_line, block_index)
    if diff_blocks:
        for b in diff_blocks.get("blocks", []):
            diff_source_lines.append((b["source_line"], b["block_index"]))

    def nearest_preceding_block(line_index: int) -> int | None:
        best: int | None = None
        for src_line, block_idx in diff_source_lines:
            if src_line <= line_index:
                best = block_idx
            else:
                break
        return best

    annotations: list[dict[str, Any]] = []
    approvals: list[dict[str, Any]] = []

    i = 0
    while i < len(lines):
        ln = lines[i]

        # GFM callout (multi-line)
        m_open = CALLOUT_OPEN_RE.match(ln)
        if m_open:
            severity_raw = m_open.group(1).upper()
            body_lines: list[str] = []
            j = i + 1
            while j < len(lines):
                bq = BLOCKQUOTE_RE.match(lines[j])
                if not bq:
                    break
                body_lines.append(bq.group(1))
                j += 1
            if severity_raw in upper_severities:
                annotations.append({
                    "kind": "callout",
                    "severity": severity_raw,
                    "severity_rank": severity_convention.index(
                        next(s for s in severity_convention if s.upper() == severity_raw)
                    ),
                    "body": " ".join(b.strip() for b in body_lines).strip(),
                    "source_line": i,
                    "attached_block": nearest_preceding_block(i),
                })
            i = j
            continue

        # Approval marker (LGTM, etc.)
        if APPROVAL_RE.match(ln.strip()):
            approvals.append({
                "kind": "approval",
                "marker": ln.strip(),
                "source_line": i,
                "attached_block": nearest_preceding_block(i),
            })
            i += 1
            continue

        # Inline marker (single-line, prose-leading)
        m_inline = INLINE_MARKER_RE.match(ln.strip())
        if m_inline:
            sev_raw = m_inline.group("sev").upper()
            if sev_raw in upper_severities:
                annotations.append({
                    "kind": "inline",
                    "severity": sev_raw,
                    "severity_rank": severity_convention.index(
                        next(s for s in severity_convention if s.upper() == sev_raw)
                    ),
                    "body": m_inline.group("body").strip(),
                    "source_line": i,
                    "attached_block": nearest_preceding_block(i),
                })
        i += 1

    # Sort annotations primarily by source_line (preserves narrative order
    # in the renderer's jump-nav), then group by severity in summary.
    annotations.sort(key=lambda a: a["source_line"])

    counts_by_severity: dict[str, int] = {}
    for a in annotations:
        counts_by_severity[a["severity"]] = counts_by_severity.get(a["severity"], 0) + 1

    return {
        "annotations": annotations,
        "approvals": approvals,
        "summary": {
            "total_annotations": len(annotations),
            "total_approvals": len(approvals),
            "counts_by_severity": counts_by_severity,
            "severity_convention": severity_convention,
        },
    }


def main(argv: list[str]) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--input", help="Path to markdown file, or '-' for stdin")
    p.add_argument("--diff-blocks", help="Path to diff_parser JSON output (for attachment)")
    p.add_argument("--severity-convention",
                   default=",".join(DEFAULT_SEVERITY_CONVENTION),
                   help="Comma-separated severity tier list, most-to-least severe. "
                        "Default: BLOCKER,MAJOR,MINOR,NIT")
    p.add_argument("--output", help="Path to write JSON output (else stdout)")
    p.add_argument("--sample", action="store_true",
                   help="Run on a built-in sample PR review")
    args = p.parse_args(argv)

    severity_convention = [s.strip().upper() for s in args.severity_convention.split(",")]
    if len(severity_convention) < 2:
        print("error: --severity-convention needs at least 2 tiers", file=sys.stderr)
        return 2

    if args.sample:
        sys.path.insert(0, str(Path(__file__).resolve().parent))
        import diff_parser
        text = diff_parser.SAMPLE_MARKDOWN
        diff_blocks = diff_parser.parse_markdown_for_diffs(text)
    elif args.input:
        text = sys.stdin.read() if args.input == "-" else Path(args.input).read_text(encoding="utf-8")
        diff_blocks = (
            json.loads(Path(args.diff_blocks).read_text(encoding="utf-8"))
            if args.diff_blocks else None
        )
    else:
        p.print_help()
        return 0

    result = extract_annotations(text, diff_blocks, severity_convention)
    payload = json.dumps(result, indent=2)
    if args.output:
        Path(args.output).write_text(payload, encoding="utf-8")
        print(f"wrote {args.output}: {result['summary']['total_annotations']} annotations, "
              f"{result['summary']['total_approvals']} approvals, "
              f"counts={result['summary']['counts_by_severity']}")
    else:
        print(payload)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
