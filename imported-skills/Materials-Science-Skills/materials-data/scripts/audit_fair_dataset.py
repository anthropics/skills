#!/usr/bin/env python3
"""Audit a materials dataset package against a lightweight FAIR checklist."""

from __future__ import annotations

import argparse
import csv
import json
import sys
from pathlib import Path


REQUIRED_PATHS = [
    "raw_data",
    "processed_data",
    "figures",
    "metadata.md",
    "README.md",
    "data_availability_statement.md",
]

REUSABLE_FIELDS = [
    "test_standard",
    "replicate_count",
    "temperature",
    "humidity",
    "curing_condition",
    "aging_condition",
]


def audit(dataset_dir: Path) -> dict[str, object]:
    missing = [relative for relative in REQUIRED_PATHS if not (dataset_dir / relative).exists()]
    metadata_text = _read(dataset_dir / "metadata.md")
    readme_text = _read(dataset_dir / "README.md")
    statement_text = _read(dataset_dir / "data_availability_statement.md")
    csv_files = list((dataset_dir / "raw_data").glob("*.csv")) + list((dataset_dir / "processed_data").glob("*.csv"))
    csv_text = "\n".join(_read(path) for path in csv_files)
    csv_headers = _csv_headers(csv_files)

    fair = {
        "findable": bool(metadata_text and readme_text),
        "accessible": bool(statement_text),
        "interoperable": bool(csv_files and {"sample_id", "unit"}.issubset(csv_headers)),
        "reusable": all(field in metadata_text or field in csv_text for field in REUSABLE_FIELDS),
    }
    status = "pass" if not missing and all(fair.values()) else "incomplete"
    return {
        "status": status,
        "dataset_dir": str(dataset_dir),
        "missing": missing,
        "fair": fair,
        "actions": actions(missing, fair),
    }


def actions(missing: list[str], fair: dict[str, bool]) -> list[str]:
    result = []
    for item in missing:
        result.append(f"Create or restore {item}.")
    for key, passed in fair.items():
        if not passed:
            result.append(f"Strengthen FAIR item: {key}.")
    return result


def _read(path: Path) -> str:
    if not path.exists() or path.is_dir():
        return ""
    return path.read_text(encoding="utf-8")


def _csv_headers(paths: list[Path]) -> set[str]:
    headers: set[str] = set()
    for path in paths:
        try:
            with path.open("r", encoding="utf-8-sig", newline="") as handle:
                reader = csv.reader(handle)
                first_row = next(reader, [])
        except OSError:
            continue
        headers.update(cell.strip() for cell in first_row if cell.strip())
    return headers


def render_markdown(report: dict[str, object]) -> str:
    lines = [
        "# FAIR Dataset Audit",
        "",
        f"- status: {report['status']}",
        f"- dataset_dir: {report['dataset_dir']}",
        "",
        "## FAIR",
    ]
    fair = report["fair"]
    if not isinstance(fair, dict):
        raise TypeError("report['fair'] must be a dict")
    for key, value in fair.items():
        lines.append(f"- {key}: {'pass' if value else 'incomplete'}")
    lines.extend(["", "## Missing"])
    missing = report["missing"]
    if not isinstance(missing, list):
        raise TypeError("report['missing'] must be a list")
    lines.extend([f"- {item}" for item in missing] or ["- none"])
    lines.extend(["", "## Actions"])
    actions_list = report["actions"]
    if not isinstance(actions_list, list):
        raise TypeError("report['actions'] must be a list")
    lines.extend([f"- {item}" for item in actions_list] or ["- none"])
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dataset-dir", required=True)
    parser.add_argument("--json", action="store_true", help="Emit JSON instead of Markdown.")
    args = parser.parse_args()

    dataset_dir = Path(args.dataset_dir)
    if not dataset_dir.is_dir():
        print(f"Error: directory not found: {dataset_dir}", file=sys.stderr)
        return 1

    report = audit(dataset_dir)
    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        print(render_markdown(report), end="")
    return 0 if report["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
