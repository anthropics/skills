#!/usr/bin/env python3
"""
SOC 2 Evidence Tracker

Tracks evidence collection status per control in a SOC 2 control matrix.
Reads a JSON control matrix (from control_matrix_builder.py) and reports
collection completeness, overdue items, and readiness scoring.

Usage:
    python evidence_tracker.py --matrix controls.json --status
    python evidence_tracker.py --matrix controls.json --status --json
"""

import argparse
import json
import sys
from datetime import datetime
from typing import Dict, List, Any


# Evidence status classifications
EVIDENCE_STATUSES = {
    "collected": "Evidence gathered and verified",
    "pending": "Evidence identified but not yet collected",
    "overdue": "Evidence past its collection deadline",
    "not_started": "No evidence collection initiated",
    "not_applicable": "Control not applicable to the environment",
}

# Expected evidence fields for a well-formed control entry
REQUIRED_FIELDS = ["control_id", "tsc_criteria", "description", "evidence_required"]


def load_matrix(filepath: str) -> List[Dict[str, Any]]:
    """Load a control matrix from a JSON file."""
    try:
        with open(filepath, "r") as f:
            data = json.load(f)
    except FileNotFoundError:
        print(f"Error: File not found: {filepath}", file=sys.stderr)
        sys.exit(1)
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON in {filepath}: {e}", file=sys.stderr)
        sys.exit(1)

    # Accept both {"controls": [...]} and plain [...]
    if isinstance(data, dict) and "controls" in data:
        controls = data["controls"]
    elif isinstance(data, list):
        controls = data
    else:
        print(
            "Error: Expected JSON with 'controls' array or a plain array.",
            file=sys.stderr,
        )
        sys.exit(1)

    return controls


def classify_evidence_status(control: Dict[str, Any]) -> str:
    """Classify the evidence collection status for a control."""
    status = control.get("status", "Not Started").lower().strip()
    evidence_date = control.get("evidence_date", "")

    if status in ("not_applicable", "n/a", "not applicable"):
        return "not_applicable"
    if status in ("collected", "complete", "done"):
        return "collected"
    if status in ("pending", "in progress", "in_progress"):
        # Check if overdue
        if evidence_date:
            try:
                due = datetime.strptime(evidence_date, "%Y-%m-%d")
                if due < datetime.now():
                    return "overdue"
            except ValueError:
                pass
        return "pending"
    if status in ("overdue", "late"):
        return "overdue"

    return "not_started"


def generate_status_report(controls: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Generate an evidence collection status report."""
    total = len(controls)
    status_counts = {s: 0 for s in EVIDENCE_STATUSES}
    by_category: Dict[str, Dict[str, int]] = {}
    issues: List[Dict[str, str]] = []

    for ctrl in controls:
        status = classify_evidence_status(ctrl)
        status_counts[status] = status_counts.get(status, 0) + 1

        category = ctrl.get("category", "Unknown")
        if category not in by_category:
            by_category[category] = {s: 0 for s in EVIDENCE_STATUSES}
        by_category[category][status] += 1

        # Flag issues
        if status == "overdue":
            issues.append(
                {
                    "control_id": ctrl.get("control_id", "N/A"),
                    "tsc_criteria": ctrl.get("tsc_criteria", "N/A"),
                    "description": ctrl.get("description", "N/A"),
                    "issue": "Evidence collection overdue",
                    "evidence_date": ctrl.get("evidence_date", "N/A"),
                }
            )
        elif status == "not_started":
            issues.append(
                {
                    "control_id": ctrl.get("control_id", "N/A"),
                    "tsc_criteria": ctrl.get("tsc_criteria", "N/A"),
                    "description": ctrl.get("description", "N/A"),
                    "issue": "Evidence collection not started",
                }
            )

        # Check for missing required fields
        missing = [f for f in REQUIRED_FIELDS if f not in ctrl or not ctrl[f]]
        if missing:
            issues.append(
                {
                    "control_id": ctrl.get("control_id", "N/A"),
                    "issue": f"Missing fields: {', '.join(missing)}",
                }
            )

    # Calculate readiness score
    applicable = total - status_counts.get("not_applicable", 0)
    collected = status_counts.get("collected", 0)
    readiness_pct = round((collected / applicable * 100), 1) if applicable > 0 else 0.0

    if readiness_pct >= 90:
        readiness_rating = "Audit Ready"
    elif readiness_pct >= 75:
        readiness_rating = "Minor Gaps"
    elif readiness_pct >= 50:
        readiness_rating = "Significant Gaps"
    else:
        readiness_rating = "Not Ready"

    return {
        "summary": {
            "total_controls": total,
            "status_breakdown": status_counts,
            "readiness_score": readiness_pct,
            "readiness_rating": readiness_rating,
            "report_date": datetime.now().strftime("%Y-%m-%d"),
        },
        "by_category": by_category,
        "issues": issues,
    }


def format_status_text(report: Dict[str, Any]) -> str:
    """Format the status report as human-readable text."""
    lines = ["=" * 60, "SOC 2 Evidence Collection Status Report", "=" * 60, ""]

    summary = report["summary"]
    lines.append(f"Report Date: {summary['report_date']}")
    lines.append(f"Total Controls: {summary['total_controls']}")
    lines.append(
        f"Readiness Score: {summary['readiness_score']}% ({summary['readiness_rating']})"
    )
    lines.append("")

    # Status breakdown
    lines.append("--- Status Breakdown ---")
    for status, count in summary["status_breakdown"].items():
        label = EVIDENCE_STATUSES.get(status, status)
        lines.append(f"  {status:15s}: {count:3d}  ({label})")
    lines.append("")

    # By category
    lines.append("--- By Category ---")
    for cat, statuses in report["by_category"].items():
        cat_total = sum(statuses.values())
        cat_collected = statuses.get("collected", 0)
        cat_pct = round(cat_collected / cat_total * 100, 1) if cat_total > 0 else 0
        lines.append(f"  {cat}: {cat_collected}/{cat_total} collected ({cat_pct}%)")
    lines.append("")

    # Issues
    if report["issues"]:
        lines.append(f"--- Issues ({len(report['issues'])}) ---")
        for issue in report["issues"]:
            ctrl_id = issue.get("control_id", "N/A")
            desc = issue.get("issue", "Unknown issue")
            lines.append(f"  [{ctrl_id}] {desc}")
    else:
        lines.append("--- No Issues Found ---")

    lines.append("")
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="SOC 2 Evidence Tracker — tracks evidence collection status per control."
    )
    parser.add_argument(
        "--matrix",
        type=str,
        required=True,
        help="Path to JSON control matrix file (from control_matrix_builder.py)",
    )
    parser.add_argument(
        "--status",
        action="store_true",
        help="Generate evidence collection status report",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output in JSON format",
    )

    args = parser.parse_args()

    if not args.status:
        parser.print_help()
        print("\nError: --status flag is required.", file=sys.stderr)
        sys.exit(1)

    controls = load_matrix(args.matrix)
    report = generate_status_report(controls)

    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print(format_status_text(report))


if __name__ == "__main__":
    main()
