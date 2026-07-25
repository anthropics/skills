#!/usr/bin/env python3
"""presenter_notes_parser.py - Extract <!-- notes: ... --> blocks from slide bodies.

Stdlib-only. Operates on the slide JSON produced by slide_splitter.py. For each
slide, finds any HTML-comment notes block (the convention used by reveal.js,
Marp, Big, Pandoc-Beamer) and:

  - Records the notes text separately under `notes`
  - Removes the notes block from `body_markdown` so the slide renders cleanly

Accepted notes syntax (case-insensitive on the keyword):

    <!-- notes: This is a single-line presenter note. -->

    <!-- notes:
      Multi-line notes block. Can contain markdown.
      - Bullet points
      - Multiple paragraphs
    -->

    <!-- speaker-notes: alias -->
    <!-- presenter: alias -->

If a slide has multiple notes blocks, they're concatenated with blank lines
between them.

NO LLM CALLS. Pure regex + slide-by-slide transformation.

Usage:
    python presenter_notes_parser.py --slides slides.json --output slides-notes.json
    python presenter_notes_parser.py --sample
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

# Matches the entire <!-- notes: ... --> block, including multi-line
NOTES_BLOCK_RE = re.compile(
    r"<!--\s*(?:notes|speaker-notes|presenter)\s*:\s*(.*?)\s*-->",
    re.IGNORECASE | re.DOTALL,
)


def extract_notes_from_slide(slide: dict[str, Any]) -> dict[str, Any]:
    """Return a new slide dict with `notes` populated and `body_markdown`
    stripped of any notes blocks."""
    body = slide.get("body_markdown", "")
    found: list[str] = []
    def _capture(m: re.Match) -> str:
        found.append(m.group(1).strip())
        return ""  # remove the block from body
    cleaned = NOTES_BLOCK_RE.sub(_capture, body)
    # Tidy up: collapse runs of >2 blank lines, trim trailing whitespace
    cleaned = re.sub(r"\n{3,}", "\n\n", cleaned).strip("\n")

    out = dict(slide)
    out["body_markdown"] = cleaned
    out["notes"] = "\n\n".join(found) if found else ""
    out["has_notes"] = bool(found)
    return out


def attach_notes(slides_payload: dict[str, Any]) -> dict[str, Any]:
    slides = slides_payload.get("slides", [])
    new_slides = [extract_notes_from_slide(s) for s in slides]
    notes_count = sum(1 for s in new_slides if s["has_notes"])
    out = dict(slides_payload)
    out["slides"] = new_slides
    out["summary"] = dict(out.get("summary", {}))
    out["summary"]["slides_with_notes"] = notes_count
    out["summary"]["notes_coverage_pct"] = (
        round(100 * notes_count / len(new_slides), 1) if new_slides else 0.0
    )
    return out


def main(argv: list[str]) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--slides", help="Path to slide_splitter JSON output, or '-' for stdin")
    p.add_argument("--output", help="Path to write JSON output (else stdout)")
    p.add_argument("--sample", action="store_true",
                   help="Run on the slide_splitter built-in sample")
    args = p.parse_args(argv)

    if args.sample:
        sys.path.insert(0, str(Path(__file__).resolve().parent))
        import slide_splitter
        slides_payload = slide_splitter.split_slides(slide_splitter.SAMPLE_MARKDOWN)
    elif args.slides:
        raw = sys.stdin.read() if args.slides == "-" else Path(args.slides).read_text(encoding="utf-8")
        slides_payload = json.loads(raw)
    else:
        p.print_help()
        return 0

    result = attach_notes(slides_payload)
    payload = json.dumps(result, indent=2)

    if args.output:
        Path(args.output).write_text(payload, encoding="utf-8")
        print(f"wrote {args.output}: {result['summary']['slides_with_notes']}/"
              f"{result['summary']['total_slides']} slides have presenter notes "
              f"({result['summary']['notes_coverage_pct']}% coverage)")
    else:
        print(payload)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
