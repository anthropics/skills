"""Audit materials paper-production routing and gate templates."""

from __future__ import annotations

import argparse
import csv
import json
import re
from pathlib import Path
from typing import Any


WEAKNESS_REQUIRED_FIELDS = [
    "weakness_id",
    "source",
    "severity",
    "weakness_type",
    "evidence_gap",
    "route_to",
    "required_fix",
    "expected_artifact",
    "status",
    "regression_check",
]

GATE_REQUIRED_FIELDS = [
    "gate_id",
    "gate_name",
    "status",
    "evidence_checked",
    "missing_inputs",
    "routed_weakness_ids",
    "next_skill",
    "reviewer_risk",
]

REQUIRED_GATE_NAMES = [
    "Literature Coverage",
    "Source Anchoring",
    "Mechanism Boundary",
    "Figure And Table Integrity",
    "Manuscript Logic",
    "Reviewer Simulation",
    "Submission Fit",
]

ALLOWED_WEAKNESS_STATUS = {"open", "fixed", "regression-checked"}
ALLOWED_REGRESSION_STATUS = {"pending", "pass", "fail", "not_applicable"}
ALLOWED_GATE_STATUS = {"pass", "fail", "blocked", "not_applicable"}


def _missing_fields(found: list[str], required: list[str]) -> list[str]:
    return [field for field in required if field not in found]


def _split_markdown_row(line: str) -> list[str]:
    return [cell.strip() for cell in line.strip().strip("|").split("|")]


def _parse_gate_table(path: Path) -> tuple[list[str], list[dict[str, str]], list[str]]:
    issues: list[str] = []
    text = path.read_text(encoding="utf-8")
    table_lines = [line.strip() for line in text.splitlines() if line.strip().startswith("|")]
    if len(table_lines) < 2:
        return [], [], [f"{path.as_posix()} missing markdown table"]

    header = _split_markdown_row(table_lines[0])
    missing = _missing_fields(header, GATE_REQUIRED_FIELDS)
    if missing:
        issues.append(f"{path.as_posix()} missing fields: {', '.join(missing)}")
        return header, [], issues

    start_index = 1
    separator_cells = _split_markdown_row(table_lines[1])
    if separator_cells and all(set(cell) <= {"-", ":"} for cell in separator_cells):
        start_index = 2

    rows: list[dict[str, str]] = []
    for row_line in table_lines[start_index:]:
        cells = _split_markdown_row(row_line)
        if len(cells) != len(header):
            issues.append(f"{path.as_posix()} has malformed row: {row_line}")
            continue
        rows.append(dict(zip(header, cells)))
    return header, rows, issues


def _parse_routed_weakness_ids(raw_value: str) -> list[str]:
    if not raw_value or raw_value.strip().lower() == "none":
        return []
    return [token.strip() for token in re.split(r"[;,]", raw_value) if token.strip()]


def audit_weakness_routing(path: Path) -> tuple[list[str], set[str]]:
    issues: list[str] = []
    if not path.is_file():
        return [f"missing {path.as_posix()}"], set()

    with path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        if reader.fieldnames is None:
            return [f"{path.as_posix()} is empty"], set()
        header = [field.strip() for field in reader.fieldnames]

        missing = _missing_fields(header, WEAKNESS_REQUIRED_FIELDS)
        if missing:
            issues.append(f"{path.as_posix()} missing fields: {', '.join(missing)}")
            return issues, set()

        weakness_ids: set[str] = set()
        saw_row = False
        for row in reader:
            saw_row = True
            normalized = {field: (row.get(field, "") or "").strip() for field in WEAKNESS_REQUIRED_FIELDS}
            weakness_id = normalized["weakness_id"]
            if not weakness_id:
                issues.append(f"{path.as_posix()} has row with empty weakness_id")
                continue

            if weakness_id in weakness_ids:
                issues.append(f"{path.as_posix()} duplicates weakness id {weakness_id}")
            weakness_ids.add(weakness_id)

            for field, value in normalized.items():
                if not value:
                    issues.append(f"{path.as_posix()} row {weakness_id} missing value for {field}")

            status = normalized["status"]
            if status and status not in ALLOWED_WEAKNESS_STATUS:
                issues.append(f"{path.as_posix()} row {weakness_id} has invalid status {status!r}")

            regression_check = normalized["regression_check"]
            if regression_check and regression_check not in ALLOWED_REGRESSION_STATUS:
                issues.append(
                    f"{path.as_posix()} row {weakness_id} has invalid regression_check {regression_check!r}"
                )

        if not saw_row:
            issues.append(f"{path.as_posix()} has header but no weakness rows")

    return issues, weakness_ids


def audit_gate_report(path: Path, weakness_ids: set[str]) -> list[str]:
    issues: list[str] = []
    if not path.is_file():
        return [f"missing {path.as_posix()}"]

    _, rows, parse_issues = _parse_gate_table(path)
    issues.extend(parse_issues)
    if parse_issues:
        return issues

    seen_gate_ids: set[str] = set()
    seen_gate_names: set[str] = set()
    if not rows:
        issues.append(f"{path.as_posix()} has header but no gate rows")
        return issues

    for row in rows:
        gate_id = row["gate_id"].strip()
        gate_name = row["gate_name"].strip()
        status = row["status"].strip()

        if not gate_id:
            issues.append(f"{path.as_posix()} has row with empty gate_id")
            continue
        if gate_id in seen_gate_ids:
            issues.append(f"{path.as_posix()} duplicates gate id {gate_id}")
        seen_gate_ids.add(gate_id)

        if gate_name in seen_gate_names:
            issues.append(f"{path.as_posix()} duplicates gate name {gate_name}")
        seen_gate_names.add(gate_name)

        for field in GATE_REQUIRED_FIELDS:
            if not row[field].strip():
                issues.append(f"{path.as_posix()} row {gate_id} missing value for {field}")

        if status and status not in ALLOWED_GATE_STATUS:
            issues.append(f"{path.as_posix()} row {gate_id} has invalid status {status!r}")

        for weakness_id in _parse_routed_weakness_ids(row["routed_weakness_ids"]):
            if weakness_id not in weakness_ids:
                issues.append(f"{path.as_posix()} references unknown weakness id {weakness_id}")

    for gate_name in REQUIRED_GATE_NAMES:
        if gate_name not in seen_gate_names:
            issues.append(f"{path.as_posix()} missing gate {gate_name}")

    return issues


def audit_files(weakness_path: Path, gate_path: Path) -> dict[str, Any]:
    weakness_issues, weakness_ids = audit_weakness_routing(Path(weakness_path))
    gate_issues = audit_gate_report(Path(gate_path), weakness_ids)
    issues = {
        "weakness_routing": weakness_issues,
        "gate_report": gate_issues,
    }
    status = "pass" if not any(issues.values()) else "fail"
    return {
        "status": status,
        "weakness_path": str(weakness_path),
        "gate_path": str(gate_path),
        "issues": issues,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--weakness-routing",
        type=Path,
        default=Path(__file__).resolve().with_name("weakness-routing-template.csv"),
    )
    parser.add_argument(
        "--gate-report",
        type=Path,
        default=Path(__file__).resolve().with_name("paper-gate-report-template.md"),
    )
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    report = audit_files(args.weakness_routing, args.gate_report)
    print(json.dumps(report, ensure_ascii=False, indent=2))
    return 0 if report["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
