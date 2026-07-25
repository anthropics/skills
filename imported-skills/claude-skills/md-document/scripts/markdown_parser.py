#!/usr/bin/env python3
"""markdown_parser.py - CommonMark-subset parser for the md-document converter.

Stdlib-only. Reads a markdown file (or stdin), produces a structured section
tree as JSON that the html_renderer can consume. NO LLM CALLS — pure regex
+ state-machine line tokenization.

Scope (CommonMark subset sufficient for agent-generated specs/reports/RFCs):
  - Headings: # / ## / ### / #### / ##### / ######  (1-6 levels)
  - Paragraphs (lines separated by blank lines)
  - Fenced code blocks (``` with optional language tag)
  - Tables (GFM: header row + delimiter row + body rows)
  - GFM-style callouts: > [!NOTE], > [!TIP], > [!IMPORTANT], > [!WARNING], > [!CAUTION]
  - Plain blockquotes: > text
  - Ordered lists: 1. / 2. / 3. (single-level only)
  - Unordered lists: - / * / + (single-level only)
  - Horizontal rules: --- / *** / ___
  - Inline: **bold** / *italic* / `code` / [text](url) / ![alt](url)

Out of scope: nested lists, HTML inlines, footnotes, definition lists, task
list checkboxes (rendered as plain text), reference-style links, hard line
breaks (two-space). These can be added later if a real document needs them.

The output is a JSON object with two keys:
  - meta:   {title, line_count, heading_count, section_count}
  - blocks: ordered list of block nodes; each section H2+ is also stored as
            a structural anchor for the TOC + scrollspy.

Usage:
    python markdown_parser.py --input report.md
    python markdown_parser.py --input - --output sections.json
    python markdown_parser.py --sample
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

CALLOUT_RE = re.compile(r"^>\s*\[!(NOTE|TIP|IMPORTANT|WARNING|CAUTION)\]\s*$", re.IGNORECASE)
HEADING_RE = re.compile(r"^(#{1,6})\s+(.+?)\s*#*\s*$")
FENCE_RE = re.compile(r"^```(\S*)\s*$")
HR_RE = re.compile(r"^(-{3,}|\*{3,}|_{3,})\s*$")
ORDERED_LI_RE = re.compile(r"^(\d+)\.\s+(.+)$")
UNORDERED_LI_RE = re.compile(r"^[-*+]\s+(.+)$")
TABLE_DELIM_RE = re.compile(r"^\|?\s*:?-{3,}:?\s*(\|\s*:?-{3,}:?\s*)+\|?\s*$")
TABLE_ROW_RE = re.compile(r"^\|.*\|\s*$")
BLOCKQUOTE_RE = re.compile(r"^>\s?(.*)$")

INLINE_CODE_RE = re.compile(r"`([^`]+)`")
BOLD_RE = re.compile(r"\*\*([^*]+)\*\*")
ITALIC_RE = re.compile(r"(?<!\*)\*([^*]+)\*(?!\*)")
LINK_RE = re.compile(r"\[([^\]]+)\]\(([^)]+)\)")
IMAGE_RE = re.compile(r"!\[([^\]]*)\]\(([^)]+)\)")


def slugify(text: str) -> str:
    """Convert a heading text to a URL-safe anchor slug."""
    text = re.sub(r"<[^>]+>", "", text)  # strip any HTML tags
    text = re.sub(r"[^a-zA-Z0-9\s-]", "", text)
    text = re.sub(r"\s+", "-", text.strip())
    return text.lower() or "section"


def render_inline_html(text: str) -> str:
    """Convert inline markdown markup to HTML, with HTML-escaping for safety."""
    # HTML-escape first, then re-introduce markup via tokens that won't collide
    # with user content. We use placeholder tokens to avoid double-substitution.
    out = text
    out = out.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")

    # Images first (so the ! prefix isn't eaten by link)
    out = IMAGE_RE.sub(lambda m: f'<img src="{m.group(2)}" alt="{m.group(1)}">', out)
    # Links
    out = LINK_RE.sub(lambda m: f'<a href="{m.group(2)}">{m.group(1)}</a>', out)
    # Inline code (before bold/italic so backticks short-circuit emphasis)
    out = INLINE_CODE_RE.sub(lambda m: f"<code>{m.group(1)}</code>", out)
    # Bold
    out = BOLD_RE.sub(lambda m: f"<strong>{m.group(1)}</strong>", out)
    # Italic (single * not adjacent to another *)
    out = ITALIC_RE.sub(lambda m: f"<em>{m.group(1)}</em>", out)
    return out


def parse_table(lines: list[str], start: int) -> tuple[dict[str, Any], int]:
    """Parse a GFM table starting at lines[start]. Returns (node, next_index)."""
    header_line = lines[start]
    delim_line = lines[start + 1]
    body_lines: list[str] = []
    i = start + 2
    while i < len(lines) and TABLE_ROW_RE.match(lines[i]):
        body_lines.append(lines[i])
        i += 1

    def split_row(row: str) -> list[str]:
        cells = row.strip().strip("|").split("|")
        return [c.strip() for c in cells]

    headers = split_row(header_line)
    aligns = []
    for cell in split_row(delim_line):
        s = cell.strip()
        if s.startswith(":") and s.endswith(":"):
            aligns.append("center")
        elif s.endswith(":"):
            aligns.append("right")
        else:
            aligns.append("left")
    rows = [split_row(r) for r in body_lines]

    return ({"type": "table", "headers": headers, "aligns": aligns, "rows": rows}, i)


def parse_list(lines: list[str], start: int) -> tuple[dict[str, Any], int]:
    """Parse a single-level ordered or unordered list starting at start."""
    first = lines[start]
    ordered = bool(ORDERED_LI_RE.match(first))
    items: list[str] = []
    i = start
    while i < len(lines):
        if ordered:
            m = ORDERED_LI_RE.match(lines[i])
            if not m:
                break
            items.append(m.group(2))
        else:
            m = UNORDERED_LI_RE.match(lines[i])
            if not m:
                break
            items.append(m.group(1))
        i += 1
    return ({"type": "list", "ordered": ordered, "items": items}, i)


def parse_callout(lines: list[str], start: int) -> tuple[dict[str, Any], int]:
    """Parse a GFM-style callout starting at start.

    Pattern:
        > [!NOTE]
        > Body line 1
        > Body line 2
    """
    m = CALLOUT_RE.match(lines[start])
    kind = m.group(1).upper() if m else "NOTE"
    body: list[str] = []
    i = start + 1
    while i < len(lines):
        bq = BLOCKQUOTE_RE.match(lines[i])
        if not bq:
            break
        body.append(bq.group(1))
        i += 1
    return ({"type": "callout", "kind": kind, "body_lines": body}, i)


def parse_blockquote(lines: list[str], start: int) -> tuple[dict[str, Any], int]:
    """Parse a plain blockquote (no callout marker)."""
    body: list[str] = []
    i = start
    while i < len(lines):
        bq = BLOCKQUOTE_RE.match(lines[i])
        if not bq:
            break
        body.append(bq.group(1))
        i += 1
    return ({"type": "blockquote", "body_lines": body}, i)


def parse_code_block(lines: list[str], start: int) -> tuple[dict[str, Any], int]:
    """Parse a fenced code block starting at start (which is the opening fence)."""
    m = FENCE_RE.match(lines[start])
    language = m.group(1).strip() if m else ""
    body: list[str] = []
    i = start + 1
    while i < len(lines):
        if FENCE_RE.match(lines[i]):
            i += 1
            break
        body.append(lines[i])
        i += 1
    return ({"type": "code", "language": language, "body": "\n".join(body)}, i)


def parse_paragraph(lines: list[str], start: int) -> tuple[dict[str, Any], int]:
    """Collect consecutive non-empty, non-block lines into a paragraph."""
    body: list[str] = []
    i = start
    while i < len(lines):
        ln = lines[i]
        if not ln.strip():
            break
        # Stop if we hit a block-level construct
        if (HEADING_RE.match(ln) or FENCE_RE.match(ln) or HR_RE.match(ln) or
                CALLOUT_RE.match(ln) or BLOCKQUOTE_RE.match(ln) or
                ORDERED_LI_RE.match(ln) or UNORDERED_LI_RE.match(ln) or
                TABLE_ROW_RE.match(ln)):
            break
        body.append(ln)
        i += 1
    text = " ".join(s.strip() for s in body)
    return ({"type": "paragraph", "text": text}, i)


def parse_markdown(text: str) -> dict[str, Any]:
    """Top-level parse — returns {meta, blocks}."""
    lines = text.splitlines()
    blocks: list[dict[str, Any]] = []
    i = 0
    title = ""
    heading_count = 0
    section_count = 0

    while i < len(lines):
        line = lines[i]

        if not line.strip():
            i += 1
            continue

        # Heading
        h = HEADING_RE.match(line)
        if h:
            level = len(h.group(1))
            text_inline = h.group(2).strip()
            anchor = slugify(text_inline)
            heading_count += 1
            if level == 1 and not title:
                title = text_inline
            if level >= 2:
                section_count += 1
            blocks.append({
                "type": "heading",
                "level": level,
                "text": text_inline,
                "anchor": anchor,
            })
            i += 1
            continue

        # HR
        if HR_RE.match(line):
            blocks.append({"type": "hr"})
            i += 1
            continue

        # Fenced code
        if FENCE_RE.match(line):
            node, next_i = parse_code_block(lines, i)
            blocks.append(node)
            i = next_i
            continue

        # Callout (more specific than blockquote — must match first)
        if CALLOUT_RE.match(line):
            node, next_i = parse_callout(lines, i)
            blocks.append(node)
            i = next_i
            continue

        # Plain blockquote
        if BLOCKQUOTE_RE.match(line):
            node, next_i = parse_blockquote(lines, i)
            blocks.append(node)
            i = next_i
            continue

        # Table (header row + delim row check ahead)
        if TABLE_ROW_RE.match(line) and i + 1 < len(lines) and TABLE_DELIM_RE.match(lines[i + 1]):
            node, next_i = parse_table(lines, i)
            blocks.append(node)
            i = next_i
            continue

        # Lists
        if ORDERED_LI_RE.match(line) or UNORDERED_LI_RE.match(line):
            node, next_i = parse_list(lines, i)
            blocks.append(node)
            i = next_i
            continue

        # Paragraph (fallback)
        node, next_i = parse_paragraph(lines, i)
        blocks.append(node)
        i = next_i

    return {
        "meta": {
            "title": title,
            "line_count": len(lines),
            "heading_count": heading_count,
            "section_count": section_count,
        },
        "blocks": blocks,
    }


SAMPLE_MARKDOWN = """# Sample Specification

## Table of Contents

- Goals
- Architecture
- Risks

## Goals

We will integrate **Stripe Connect** with the existing checkout flow.

| Phase | Timeline | Owner |
|-------|----------|-------|
| Design | Week 1 | jane |
| Build | Week 2-3 | dev team |
| Ship | Week 4 | jane |

## Architecture

The integration uses webhooks for async events.

```python
def handle_webhook(event):
    if event.type == "payment.succeeded":
        mark_paid(event.data.object.id)
```

> [!NOTE]
> All webhook handlers must be idempotent.

> [!WARNING]
> Tax calculation has edge cases for digital goods in the EU.

## Risks

1. Webhook delivery delays
2. Tax calculation edge cases for VAT
3. Refund cascading across multi-party transfers

See [Stripe Connect docs](https://stripe.com/docs/connect) for details.
"""


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--input", help="Path to markdown file, or '-' for stdin")
    parser.add_argument("--output", help="Path to write JSON output (else stdout)")
    parser.add_argument("--sample", action="store_true",
                        help="Parse a built-in sample markdown document")
    args = parser.parse_args(argv)

    if args.sample:
        text = SAMPLE_MARKDOWN
    elif args.input:
        if args.input == "-":
            text = sys.stdin.read()
        else:
            path = Path(args.input)
            if not path.exists():
                print(f"error: input not found: {path}", file=sys.stderr)
                return 2
            text = path.read_text(encoding="utf-8")
    else:
        parser.print_help()
        return 0

    result = parse_markdown(text)
    payload = json.dumps(result, indent=2)

    if args.output:
        Path(args.output).write_text(payload, encoding="utf-8")
        print(f"wrote {args.output}: {result['meta']['heading_count']} headings, "
              f"{len(result['blocks'])} blocks")
    else:
        print(payload)

    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
