#!/usr/bin/env python3
"""Make a PPTX compatible with Apple Keynote without changing its content."""

from __future__ import annotations

import argparse
import sys

from office.helpers.keynote import SanitizeError, sanitize_file


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Repair OOXML metadata that prevents a PPTX from opening in Keynote."
    )
    parser.add_argument("path", help="PPTX file to sanitize in place")
    args = parser.parse_args()

    try:
        changes = sanitize_file(args.path)
    except (OSError, SanitizeError) as exc:
        print(f"Error: {exc}", file=sys.stderr)
        return 1

    if changes:
        print(f"Sanitized {args.path}:")
        for change in changes:
            print(f"- {change}")
    else:
        print(f"No Keynote compatibility changes needed: {args.path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
