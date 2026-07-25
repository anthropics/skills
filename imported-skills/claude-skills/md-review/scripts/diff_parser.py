#!/usr/bin/env python3
"""diff_parser.py - Extract unified-diff hunks from markdown code review notes.

Stdlib-only. Scans markdown for ```diff fenced code blocks (the convention used
in PR writeups), parses each one as a unified diff, and returns structured
hunk data the renderer can lay out as a 2-column annotated diff.

Pattern (the standard unified-diff shape):

    ```diff
    --- a/path/to/file.py
    +++ b/path/to/file.py
    @@ -10,7 +10,8 @@ def existing_context
     context line (unchanged)
    -removed line
    +added line
    +another added line
     context line
    @@ -50,3 +51,4 @@
     ...
    ```

Also accepts:
  - Multiple ```diff blocks (each treated as a separate "section")
  - Inline-fenced diffs (no language tag) IF --infer-diff is passed
  - Per-hunk @@ header context strings (preserved in output)

NO LLM CALLS. Pure regex + state machine.

Usage:
    python diff_parser.py --input review.md --output hunks.json
    python diff_parser.py --sample
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

FENCE_OPEN_RE = re.compile(r"^```(diff)?\s*$")
FENCE_CLOSE_RE = re.compile(r"^```\s*$")
FILE_OLD_RE = re.compile(r"^---\s+(?:a/)?(.+?)\s*$")
FILE_NEW_RE = re.compile(r"^\+\+\+\s+(?:b/)?(.+?)\s*$")
HUNK_RE = re.compile(
    r"^@@\s+-(\d+)(?:,(\d+))?\s+\+(\d+)(?:,(\d+))?\s+@@\s*(.*)$"
)


def _parse_hunk_body(lines: list[str], old_start: int, new_start: int) -> list[dict[str, Any]]:
    """Walk hunk body lines and assign source-side and target-side line numbers."""
    body: list[dict[str, Any]] = []
    old_num = old_start
    new_num = new_start
    for ln in lines:
        if not ln:
            # treat as context (truly empty line in diff)
            body.append({"kind": "context", "text": "", "old": old_num, "new": new_num})
            old_num += 1
            new_num += 1
            continue
        prefix = ln[0]
        text = ln[1:] if len(ln) > 1 else ""
        if prefix == "+":
            body.append({"kind": "addition", "text": text, "old": None, "new": new_num})
            new_num += 1
        elif prefix == "-":
            body.append({"kind": "deletion", "text": text, "old": old_num, "new": None})
            old_num += 1
        elif prefix == " ":
            body.append({"kind": "context", "text": text, "old": old_num, "new": new_num})
            old_num += 1
            new_num += 1
        elif prefix == "\\":
            body.append({"kind": "meta", "text": text.strip(), "old": None, "new": None})
        else:
            # Unknown line — preserve as context with the raw prefix
            body.append({"kind": "context", "text": ln, "old": old_num, "new": new_num})
            old_num += 1
            new_num += 1
    return body


def _parse_single_diff(block_lines: list[str]) -> list[dict[str, Any]]:
    """Parse one fenced diff block. Returns a list of file entries.

    File entry shape:
        {
            "path_old": str | None,
            "path_new": str | None,
            "hunks": [
                {"old_start": int, "new_start": int, "header_context": str,
                 "lines": [...], "hunk_index_in_block": int}
            ]
        }
    """
    files: list[dict[str, Any]] = []
    current_file: dict[str, Any] | None = None
    current_hunk: dict[str, Any] | None = None
    hunk_body: list[str] = []
    hunk_index_in_block = 0

    def flush_hunk() -> None:
        nonlocal current_hunk, hunk_body, hunk_index_in_block
        if current_hunk is None or current_file is None:
            current_hunk = None
            hunk_body = []
            return
        current_hunk["lines"] = _parse_hunk_body(
            hunk_body, current_hunk["old_start"], current_hunk["new_start"]
        )
        current_hunk["hunk_index_in_block"] = hunk_index_in_block
        hunk_index_in_block += 1
        current_file["hunks"].append(current_hunk)
        current_hunk = None
        hunk_body = []

    def flush_file() -> None:
        nonlocal current_file
        flush_hunk()
        if current_file:
            files.append(current_file)
            current_file = None

    for raw in block_lines:
        m_old = FILE_OLD_RE.match(raw)
        m_new = FILE_NEW_RE.match(raw)
        m_hunk = HUNK_RE.match(raw)

        if m_old:
            # New file boundary; flush previous
            flush_file()
            current_file = {"path_old": m_old.group(1), "path_new": None, "hunks": []}
            continue
        if m_new:
            if current_file is None:
                current_file = {"path_old": None, "path_new": m_new.group(1), "hunks": []}
            else:
                current_file["path_new"] = m_new.group(1)
            continue
        if m_hunk:
            flush_hunk()
            current_hunk = {
                "old_start": int(m_hunk.group(1)),
                "old_count": int(m_hunk.group(2) or 1),
                "new_start": int(m_hunk.group(3)),
                "new_count": int(m_hunk.group(4) or 1),
                "header_context": m_hunk.group(5).strip(),
                "lines": [],
            }
            continue
        if current_hunk is not None:
            hunk_body.append(raw)

    flush_file()
    return files


def parse_markdown_for_diffs(text: str, infer_unfenced: bool = False) -> dict[str, Any]:
    """Top-level: find every ```diff block and parse it.

    Returns:
        {
            "blocks": [
                {"block_index": int, "files": [...]},
                ...
            ],
            "summary": {"total_files": int, "total_hunks": int, "total_blocks": int}
        }
    """
    lines = text.splitlines()
    in_block = False
    is_diff_block = False
    block_buf: list[str] = []
    blocks: list[dict[str, Any]] = []
    block_index = 0
    block_line_starts: list[int] = []

    i = 0
    while i < len(lines):
        ln = lines[i]
        if not in_block:
            m = FENCE_OPEN_RE.match(ln)
            if m:
                in_block = True
                lang = m.group(1)
                is_diff_block = (lang == "diff")
                block_buf = []
                block_line_starts.append(i)
        else:
            if FENCE_CLOSE_RE.match(ln):
                if is_diff_block:
                    files = _parse_single_diff(block_buf)
                    blocks.append({
                        "block_index": block_index,
                        "source_line": block_line_starts[block_index],
                        "files": files,
                    })
                    block_index += 1
                elif infer_unfenced:
                    # Try to detect if this looks like a diff (starts with --- / +++ / @@)
                    head = "\n".join(block_buf[:3])
                    if "@@" in head or head.startswith("---") or head.startswith("+++"):
                        files = _parse_single_diff(block_buf)
                        blocks.append({
                            "block_index": block_index,
                            "source_line": block_line_starts[block_index],
                            "files": files,
                            "inferred": True,
                        })
                        block_index += 1
                in_block = False
                is_diff_block = False
                block_buf = []
            else:
                block_buf.append(ln)
        i += 1

    total_files = sum(len(b["files"]) for b in blocks)
    total_hunks = sum(
        sum(len(f["hunks"]) for f in b["files"]) for b in blocks
    )

    return {
        "blocks": blocks,
        "summary": {
            "total_files": total_files,
            "total_hunks": total_hunks,
            "total_blocks": len(blocks),
        },
    }


SAMPLE_MARKDOWN = """# PR Review: Add payment retry logic

Two changes worth flagging.

```diff
--- a/payments/retry.py
+++ b/payments/retry.py
@@ -10,7 +10,8 @@ def schedule_retry(payment_id, attempt):
     if attempt > MAX_ATTEMPTS:
         return None
     delay = 2 ** attempt
-    return _enqueue(payment_id, delay)
+    jitter = random.uniform(0, delay * 0.1)
+    return _enqueue(payment_id, delay + jitter)
```

> [!MAJOR]
> This `random.uniform()` call is not seeded. In test runs it'll produce
> non-deterministic retry delays — make tests flaky.

```diff
--- a/payments/queue.py
+++ b/payments/queue.py
@@ -40,3 +40,7 @@ def _enqueue(payment_id, delay):
     redis.zadd("retries", {payment_id: time.time() + delay})
     log.info("scheduled", payment_id=payment_id, delay=delay)
+
+def cancel_retries(payment_id):
+    redis.zrem("retries", payment_id)
+    log.info("cancelled retries", payment_id=payment_id)
```

> [!NIT]
> Minor — would prefer `log.info("retries.cancelled", ...)` (dotted event name).
"""


def main(argv: list[str]) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--input", help="Path to markdown file, or '-' for stdin")
    p.add_argument("--output", help="Path to write JSON output (else stdout)")
    p.add_argument("--infer-diff", action="store_true",
                   help="Also parse unfenced or language-less blocks that look like diffs")
    p.add_argument("--sample", action="store_true",
                   help="Parse a built-in sample PR-review markdown")
    args = p.parse_args(argv)

    if args.sample:
        text = SAMPLE_MARKDOWN
    elif args.input:
        text = sys.stdin.read() if args.input == "-" else Path(args.input).read_text(encoding="utf-8")
    else:
        p.print_help()
        return 0

    result = parse_markdown_for_diffs(text, infer_unfenced=args.infer_diff)
    payload = json.dumps(result, indent=2)
    if args.output:
        Path(args.output).write_text(payload, encoding="utf-8")
        print(f"wrote {args.output}: {result['summary']['total_files']} files, "
              f"{result['summary']['total_hunks']} hunks across "
              f"{result['summary']['total_blocks']} diff blocks")
    else:
        print(payload)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
