#!/usr/bin/env python3
"""sync_adapter_docs: keep academic-pipeline/references/adapters/overview.md
field tables in lockstep with literature_corpus_entry.schema.json.

Markers in overview.md:
  <!-- GENERATED:LITERATURE_CORPUS_REQUIRED:START -->  ... auto ...  <!-- GENERATED:LITERATURE_CORPUS_REQUIRED:END -->
  <!-- GENERATED:LITERATURE_CORPUS_OPTIONAL:START -->  ... auto ...  <!-- GENERATED:LITERATURE_CORPUS_OPTIONAL:END -->

Modes:
  sync_adapter_docs.py           # rewrite the marked regions in place
  sync_adapter_docs.py --check   # fail if rewrite would change anything

Exit codes:
  0 — no drift (or rewrote successfully without --check)
  1 — drift detected under --check
  2 — invocation error (schema or target missing)
"""
from __future__ import annotations
import argparse
import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
SCHEMA_PATH = REPO_ROOT / "shared/contracts/passport/literature_corpus_entry.schema.json"
DEFAULT_TARGET = REPO_ROOT / "academic-pipeline/references/adapters/overview.md"

MARKERS = {
    "LITERATURE_CORPUS_REQUIRED": "required",
    "LITERATURE_CORPUS_OPTIONAL": "optional",
}


def _short_type(prop_def: dict) -> str:
    t = prop_def.get("type")
    if isinstance(t, list):
        # Markdown-table cells are pipe-delimited, so a JSON Schema
        # union type rendered as `null | string` would split into extra
        # columns. Escape the separator with `\|` so GitHub renders it
        # as a literal pipe inside the cell.
        return r" \| ".join(sorted(x for x in t if x))
    if t:
        return t
    if "oneOf" in prop_def:
        return "oneOf"
    if "$ref" in prop_def:
        return prop_def["$ref"].split("/")[-1]
    return "any"


def _short_desc(prop_def: dict) -> str:
    d = (prop_def.get("description") or "").strip()
    m = re.match(r"(.+?[.!?])(?:\s|$)", d)
    return (m.group(1) if m else d) or "—"


def build_table(schema: dict, which: str) -> str:
    required = set(schema.get("required", []))
    props = schema.get("properties", {})
    rows = []
    for name, prop_def in sorted(props.items()):
        is_req = name in required
        if which == "required" and not is_req:
            continue
        if which == "optional" and is_req:
            continue
        rows.append(f"| `{name}` | {_short_type(prop_def)} | {_short_desc(prop_def)} |")
    header = "| Field | Type | Description (first sentence) |\n|---|---|---|"
    return header + "\n" + "\n".join(rows) + "\n"


def regenerate_file(content: str, schema: dict) -> str:
    for marker_name, which in MARKERS.items():
        start = f"<!-- GENERATED:{marker_name}:START -->"
        end = f"<!-- GENERATED:{marker_name}:END -->"
        if start not in content or end not in content:
            continue
        table = build_table(schema, which)
        pattern = re.compile(re.escape(start) + r".*?" + re.escape(end), re.DOTALL)
        content = pattern.sub(f"{start}\n{table}{end}", content)
    return content


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check", action="store_true", help="Exit 1 on drift, do not modify files.")
    ap.add_argument("--target", type=Path, default=DEFAULT_TARGET, help="Overview file to update.")
    args = ap.parse_args()

    if not SCHEMA_PATH.exists():
        print(f"ERROR: schema missing at {SCHEMA_PATH}", file=sys.stderr)
        return 2
    if not args.target.exists():
        print(f"ERROR: target missing at {args.target}", file=sys.stderr)
        return 2

    schema = json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))
    old = args.target.read_text(encoding="utf-8")
    new = regenerate_file(old, schema)

    if old == new:
        return 0

    if args.check:
        print(
            f"DRIFT: {args.target} is out-of-date relative to the schema.",
            file=sys.stderr,
        )
        print("Run `python scripts/sync_adapter_docs.py` to regenerate.", file=sys.stderr)
        return 1

    args.target.write_text(new, encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main())
