#!/usr/bin/env python3
"""Lint a PR body against the Review Gate body rules before you push or edit it.

usage: python3 scripts/lint-review-body.py [BODY_FILE]   (reads stdin when no file or "-")

Runs the gate's own `review_region` from check-review-gate.py beside this file, so the two cannot
drift. Exit 0 when the body passes, 1 with one line per problem (line number and offending construct)
when it does not. It checks only the body rules; the attestation's head SHA is the gate's job.
"""
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

_spec = importlib.util.spec_from_file_location("check_review_gate", Path(__file__).with_name("check-review-gate.py"))
_gate = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_gate)


def lint(body: str) -> list[str]:
    return _gate.review_region(body)[1]


def main(argv: list[str]) -> int:
    if len(argv) > 1:
        print(__doc__.strip().splitlines()[2], file=sys.stderr)
        return 2
    try:
        body = sys.stdin.read() if not argv or argv[0] == "-" else Path(argv[0]).read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as e:  # a bad path is a usage error (2), never a lint verdict (1)
        print(f"review-gate body: cannot read {argv[0] if argv else 'stdin'}: {e}", file=sys.stderr)
        return 2
    problems = lint(body)
    for p in problems:
        print(f"review-gate body: {p}", file=sys.stderr)
    if not problems:
        print("review-gate body: OK")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
