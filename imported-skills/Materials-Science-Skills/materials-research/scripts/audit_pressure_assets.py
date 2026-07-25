#!/usr/bin/env python3
"""Audit materials pressure tests coverage."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


REQUIRED_MODULES = [
    "materials-research",
    "materials-reader",
    "materials-citation",
    "materials-polishing",
    "materials-response",
    "materials-html-deck",
    "materials-figure",
    "materials-data",
]

REQUIRED_THEMES = [
    "overclaim",
    "fake citation",
    "journal mismatch",
    "missing experimental conditions",
    "literal translation",
    "weak novelty",
    "figure caption",
    "HTML deck missing data",
    "FAIR data",
    "reviewer response",
    "statistics",
    "scope creep",
]


def audit(skill_root: Path) -> dict[str, object]:
    pressure_files = sorted((skill_root / "tests" / "pressure-tests").glob("*.md"))
    pressure_text = "\n".join(path.read_text(encoding="utf-8") for path in pressure_files)

    covered_modules = [module for module in REQUIRED_MODULES if module in pressure_text]
    missing_modules = [module for module in REQUIRED_MODULES if module not in covered_modules]
    missing_themes = [theme for theme in REQUIRED_THEMES if theme not in pressure_text]

    status = "pass"
    if len(pressure_files) < 12:
        status = "incomplete"
    if missing_modules or missing_themes:
        status = "incomplete"

    return {
        "status": status,
        "pressure_test_count": len(pressure_files),
        "covered_modules": covered_modules,
        "missing_modules": missing_modules,
        "missing_themes": missing_themes,
    }


def render_markdown(report: dict[str, object]) -> str:
    lines = [
        "# Materials Science Pressure Asset Audit",
        "",
        f"- status: {report['status']}",
        f"- pressure_test_count: {report['pressure_test_count']}",
        "",
        "## Missing",
    ]
    for key in ("missing_modules", "missing_themes"):
        values = report[key]
        assert isinstance(values, list)
        lines.append(f"- {key}: {', '.join(values) if values else 'none'}")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skill-root", default=str(Path(__file__).resolve().parents[1]))
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    report = audit(Path(args.skill_root))
    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        print(render_markdown(report), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
