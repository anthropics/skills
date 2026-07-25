#!/usr/bin/env python3
"""Create a materials paper reading Markdown scaffold."""

from __future__ import annotations

import argparse
from pathlib import Path


TEMPLATE = """# {title}

## 1. Paper Identity

- Title: {title}
- Journal/year: {journal_year}
- DOI:
- Material family: {material_family}
- Paper type:

## 2. One-Sentence Takeaway

## 3. Research Problem and Gap

## 4. Material System

| Component | Role | Notes |
|---|---|---|

## 5. Experiment Matrix

| Variable | Levels | Control | Test | Purpose |
|---|---|---|---|---|

## 6. Figure/Table Evidence Map

| Figure/Table | What it shows | Claim supported | Caution |
|---|---|---|---|

## 7. Key Results

## 8. Mechanism Chain

Measured evidence -> interpretation -> boundary.

## 9. Limitations

## 10. What I Can Borrow

## 11. Questions for Group Meeting
"""


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--title", default="Untitled materials paper")
    parser.add_argument("--journal-year", default="")
    parser.add_argument("--material-family", default="materials")
    parser.add_argument("--output", default="paper-reader.md")
    args = parser.parse_args()

    out = Path(args.output)
    out.write_text(
        TEMPLATE.format(
            title=args.title,
            journal_year=args.journal_year,
            material_family=args.material_family,
        ),
        encoding="utf-8",
    )
    print(out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
