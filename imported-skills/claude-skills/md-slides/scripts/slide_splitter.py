#!/usr/bin/env python3
"""slide_splitter.py - Split a markdown deck into ordered slides.

Stdlib-only. Accepts three boundary modes:

  --boundary hr     Split on `---` HR lines (the most common convention; what
                    reveal.js / pandoc / Marp / Big all read by default).
  --boundary h1     Split on top-level `# ` headings; each H1 starts a new slide.
  --boundary auto   (default) Pick the better signal automatically:
                      - HR count ≥ 3 → use HR
                      - else H1 count ≥ 5 → use H1
                      - else FAIL — input has no clear slide boundaries

The first slide gets everything from the start of file up to the first boundary.
H1-mode treats the H1 line as part of the slide (it becomes the slide title);
HR-mode does NOT include the `---` line in either slide.

NO LLM CALLS. Pure regex + state machine.

Hard rules (refusals):
  1. 1-slide deck → exit 5 (it's a poster — route to md-document)
  2. Any slide body > 40 source lines → warning printed to stderr (signal-to-
     noise; presenters fail with too much per slide). Soft-fail; renders anyway.
  3. No boundaries detectable in auto mode → exit 6 (route to md-document)

Usage:
    python slide_splitter.py --input deck.md --output slides.json
    python slide_splitter.py --input - --boundary h1
    python slide_splitter.py --sample
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

HR_RE = re.compile(r"^---\s*$")
H1_RE = re.compile(r"^#\s+(.+?)\s*$")

MAX_SLIDE_LINES = 40  # soft warn above this (signal-to-noise)


def _extract_title(slide_body: list[str]) -> tuple[str, list[str]]:
    """If the first non-blank line is a heading, treat it as the title and
    return (title, body_without_title_line). Otherwise return ('', body)."""
    for i, line in enumerate(slide_body):
        if not line.strip():
            continue
        m = H1_RE.match(line)
        if m:
            return (m.group(1).strip(), slide_body[:i] + slide_body[i + 1:])
        # Also accept H2 as a slide title if the slide has no H1 (common in
        # decks where H1 = whole-deck title and each slide leads with H2)
        m2 = re.match(r"^##\s+(.+?)\s*$", line)
        if m2:
            return (m2.group(1).strip(), slide_body[:i] + slide_body[i + 1:])
        break
    return ("", slide_body)


def _pick_boundary_auto(lines: list[str]) -> str:
    """Pick HR vs H1 based on signal counts. HR wins if ≥3; else H1 if ≥5."""
    hr_count = sum(1 for ln in lines if HR_RE.match(ln))
    h1_count = sum(1 for ln in lines if H1_RE.match(ln))
    if hr_count >= 3:
        return "hr"
    if h1_count >= 5:
        return "h1"
    return ""  # caller treats empty as "no boundary detected"


def split_slides(text: str, boundary: str = "auto") -> dict[str, Any]:
    lines = text.splitlines()

    if boundary == "auto":
        chosen = _pick_boundary_auto(lines)
        if not chosen:
            return {
                "slides": [],
                "boundary": "auto",
                "boundary_used": None,
                "summary": {
                    "total_slides": 0,
                    "max_slide_lines": 0,
                    "over_threshold": [],
                    "error": "no clear slide boundaries (need ≥3 HR or ≥5 H1)",
                },
            }
        boundary = chosen

    raw_groups: list[list[str]] = []
    current: list[str] = []
    boundary_lines: list[int] = []  # source line indices where each slide starts

    if boundary == "hr":
        current_start = 0
        for i, ln in enumerate(lines):
            if HR_RE.match(ln):
                raw_groups.append(current)
                boundary_lines.append(current_start)
                current = []
                current_start = i + 1
                continue
            current.append(ln)
        # Last slide
        raw_groups.append(current)
        boundary_lines.append(current_start)
    elif boundary == "h1":
        current_start = 0
        first_h1_seen = False
        for i, ln in enumerate(lines):
            if H1_RE.match(ln):
                if first_h1_seen:
                    raw_groups.append(current)
                    boundary_lines.append(current_start)
                    current = []
                    current_start = i
                else:
                    # Everything before the first H1 (if non-empty) is the
                    # opening slide; the first H1 starts slide 2.
                    if any(s.strip() for s in current):
                        raw_groups.append(current)
                        boundary_lines.append(0)
                    current = []
                    current_start = i
                    first_h1_seen = True
            current.append(ln)
        if current:
            raw_groups.append(current)
            boundary_lines.append(current_start)
    else:
        return {
            "slides": [],
            "boundary": boundary,
            "boundary_used": boundary,
            "summary": {
                "total_slides": 0,
                "max_slide_lines": 0,
                "over_threshold": [],
                "error": f"unknown --boundary mode: {boundary}",
            },
        }

    # Trim leading/trailing blank lines per slide; drop empty slides
    cleaned: list[dict[str, Any]] = []
    over_threshold: list[int] = []
    max_lines = 0
    for idx, body_lines in enumerate(raw_groups):
        while body_lines and not body_lines[0].strip():
            body_lines = body_lines[1:]
        while body_lines and not body_lines[-1].strip():
            body_lines = body_lines[:-1]
        if not body_lines:
            continue

        title, body_no_title = _extract_title(body_lines)
        line_count = len(body_lines)
        max_lines = max(max_lines, line_count)
        if line_count > MAX_SLIDE_LINES:
            over_threshold.append(idx + 1)

        cleaned.append({
            "slide_number": len(cleaned) + 1,
            "title": title,
            "body_markdown": "\n".join(body_no_title),
            "raw_body_markdown": "\n".join(body_lines),
            "source_line": boundary_lines[idx] if idx < len(boundary_lines) else 0,
            "line_count": line_count,
        })

    return {
        "slides": cleaned,
        "boundary": boundary,
        "boundary_used": boundary,
        "summary": {
            "total_slides": len(cleaned),
            "max_slide_lines": max_lines,
            "over_threshold": over_threshold,
            "max_threshold": MAX_SLIDE_LINES,
        },
    }


SAMPLE_MARKDOWN = """# The Case for Single-File HTML

Why agent-generated artifacts should ship as one .html file.

---

# Three forces converged

- Outputs got longer
- The editing relationship changed (LLM edits, not human)
- The information became spatial

Markdown can't carry any of those three at length.

<!-- notes: This is the framing slide. Start by asking the audience how
  many of them have stopped reading a markdown spec past line 100. -->

---

# What HTML restores

| Dimension | Markdown | HTML |
|-----------|----------|------|
| Hierarchy | Indented `#` | Typography scale |
| Navigation | Linear | Sticky TOC + scrollspy |
| Comparison | Lists | Tables, grids |
| Interaction | None | Search, copy, hover |

<!-- notes: Spend 30 seconds on each row. The hierarchy row is the one
  that lands hardest for engineers. -->

---

# Single-file discipline

- All CSS inline
- All JS inline
- Only externals: Google Fonts + Prism CDN
- Falls back gracefully

> One `.html` file uploads to S3, opens in any browser, attaches to email.

<!-- notes: The shareability point is the easiest sell. Skip the technical
  details unless someone asks. -->

---

# Try it now

Append "as an HTML file" to your next Claude Code prompt.

That's the whole switch.
"""


def main(argv: list[str]) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--input", help="Path to markdown file, or '-' for stdin")
    p.add_argument("--output", help="Path to write JSON output (else stdout)")
    p.add_argument("--boundary", choices=["auto", "hr", "h1"], default="auto",
                   help="Slide boundary mode (default: auto-detect)")
    p.add_argument("--sample", action="store_true",
                   help="Run on a built-in 5-slide deck")
    args = p.parse_args(argv)

    if args.sample:
        text = SAMPLE_MARKDOWN
    elif args.input:
        text = sys.stdin.read() if args.input == "-" else Path(args.input).read_text(encoding="utf-8")
    else:
        p.print_help()
        return 0

    result = split_slides(text, args.boundary)

    # Hard rule: auto mode with no clear boundaries
    if "error" in result["summary"]:
        print(f"refusing: {result['summary']['error']}. "
              f"Add `---` between slides, or use H1 boundaries, or route to md-document.",
              file=sys.stderr)
        return 6

    # Hard rule: single-slide deck is a poster, not a deck
    if result["summary"]["total_slides"] == 1:
        print("refusing: input produces a 1-slide deck — that's a poster. "
              "Route to md-document or add more --- boundaries.",
              file=sys.stderr)
        return 5

    # Soft warn: slides over 40 source lines
    if result["summary"]["over_threshold"]:
        offenders = ", ".join(f"#{n}" for n in result["summary"]["over_threshold"])
        print(f"warning: slides {offenders} exceed {MAX_SLIDE_LINES} source lines "
              f"(signal-to-noise — consider splitting). Rendering anyway.",
              file=sys.stderr)

    payload = json.dumps(result, indent=2)
    if args.output:
        Path(args.output).write_text(payload, encoding="utf-8")
        print(f"wrote {args.output}: {result['summary']['total_slides']} slides "
              f"(boundary={result['boundary_used']}, max_lines={result['summary']['max_slide_lines']})")
    else:
        print(payload)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
