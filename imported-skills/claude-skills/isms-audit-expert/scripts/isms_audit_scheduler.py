#!/usr/bin/env python3
"""
ISMS Audit Scheduler

Risk-based audit planning and scheduling for ISO 27001 compliance.
Generates annual audit plans based on control risk ratings.

Usage:
    python isms_audit_scheduler.py --year 2025 --output audit_plan.json
    python isms_audit_scheduler.py --controls controls.csv --format markdown
"""

import argparse
import csv
import json
import sys
from datetime import datetime, timedelta
from typing import Dict, List, Any, Optional


# ISO 27001:2022 Annex A control domains
CONTROL_DOMAINS = {
    "A.5": {"name": "Organizational Controls", "count": 37},
    "A.6": {"name": "People Controls", "count": 8},
    "A.7": {"name": "Physical Controls", "count": 14},
    "A.8": {"name": "Technological Controls", "count": 34},
}

# Default risk ratings for control areas
DEFAULT_RISK_RATINGS = {
    "A.5.1": {"name": "Policies for information security", "risk": "medium"},
    "A.5.2": {"name": "Information security roles", "risk": "medium"},
    "A.5.15": {"name": "Access control", "risk": "high"},
    "A.5.24": {"name": "Incident management planning", "risk": "high"},
    "A.5.25": {"name": "Assessment of security events", "risk": "high"},
    "A.6.1": {"name": "Screening", "risk": "medium"},
    "A.6.3": {"name": "Information security awareness", "risk": "medium"},
    "A.6.7": {"name": "Remote working", "risk": "high"},
    "A.7.1": {"name": "Physical security perimeters", "risk": "medium"},
    "A.7.4": {"name": "Physical security monitoring", "risk": "medium"},
    "A.8.2": {"name": "Privileged access rights", "risk": "critical"},
    "A.8.5": {"name": "Secure authentication", "risk": "critical"},
    "A.8.7": {"name": "Protection against malware", "risk": "high"},
    "A.8.8": {"name": "Management of vulnerabilities", "risk": "critical"},
    "A.8.13": {"name": "Information backup", "risk": "high"},
    "A.8.15": {"name": "Logging", "risk": "critical"},
    "A.8.20": {"name": "Networks security", "risk": "high"},
    "A.8.24": {"name": "Use of cryptography", "risk": "high"},
}

# Audit frequency based on risk level
AUDIT_FREQUENCY = {
    "critical": 4,  # Quarterly
    "high": 2,      # Semi-annual
    "medium": 1,    # Annual
    "low": 1,       # Annual
}


def load_controls_from_csv(filepath: str) -> Dict[str, Dict]:
    """Load control risk ratings from CSV file."""
    controls = {}
    try:
        with open(filepath, "r", encoding="utf-8") as f:
            reader = csv.DictReader(f)
            for row in reader:
                control_id = row.get("control_id", row.get("id", ""))
                if control_id:
                    controls[control_id] = {
                        "name": row.get("name", "Unknown"),
                        "risk": row.get("risk", "medium").lower(),
                    }
    except FileNotFoundError:
        print(f"Error: File not found: {filepath}", file=sys.stderr)
        sys.exit(1)
    return controls


def calculate_audit_dates(
    year: int,
    frequency: int
) -> List[str]:
    """Calculate audit dates based on frequency."""
    dates = []
    interval = 12 // frequency
    for i in range(frequency):
        month = (i * interval) + 2  # Start in February
        if month > 12:
            month = month - 12
        date = datetime(year, month, 15)
        dates.append(date.strftime("%Y-%m-%d"))
    return dates


def generate_audit_plan(
    year: int,
    controls: Optional[Dict[str, Dict]] = None
) -> Dict[str, Any]:
    """Generate risk-based annual audit plan."""
    if controls is None:
        controls = DEFAULT_RISK_RATINGS

    plan = {
        "metadata": {
            "year": year,
            "generated": datetime.now().isoformat(),
            "methodology": "ISO 27001 Risk-Based Internal Auditing",
            "total_controls": len(controls),
        },
        "schedule": {
            "Q1": {"month": "February-March", "audits": []},
            "Q2": {"month": "May-June", "audits": []},
            "Q3": {"month": "August-September", "audits": []},
            "Q4": {"month": "November", "audits": []},
        },
        "controls": {},
    }

    # Assign controls to quarters based on risk
    for control_id, control_data in controls.items():
        risk = control_data.get("risk", "medium")
        frequency = AUDIT_FREQUENCY.get(risk, 1)
        audit_dates = calculate_audit_dates(year, frequency)

        plan["controls"][control_id] = {
            "name": control_data.get("name", "Unknown"),
            "risk": risk,
            "frequency": frequency,
            "scheduled_audits": audit_dates,
        }

        # Add to quarterly schedule
        for i, date in enumerate(audit_dates):
            month = int(date.split("-")[1])
            if month <= 3:
                quarter = "Q1"
            elif month <= 6:
                quarter = "Q2"
            elif month <= 9:
                quarter = "Q3"
            else:
                quarter = "Q4"

            plan["schedule"][quarter]["audits"].append({
                "control_id": control_id,
                "control_name": control_data.get("name", "Unknown"),
                "risk_level": risk,
                "target_date": date,
            })

    # Sort audits within each quarter
    for quarter in plan["schedule"]:
        plan["schedule"][quarter]["audits"].sort(
            key=lambda x: (
                {"critical": 0, "high": 1, "medium": 2, "low": 3}.get(x["risk_level"], 4),
                x["target_date"]
            )
        )

    # Calculate summary statistics
    risk_counts = {"critical": 0, "high": 0, "medium": 0, "low": 0}
    total_audits = 0
    for control_data in plan["controls"].values():
        risk_counts[control_data["risk"]] += 1
        total_audits += control_data["frequency"]

    plan["summary"] = {
        "total_controls_in_scope": len(controls),
        "total_audits_planned": total_audits,
        "risk_distribution": risk_counts,
        "audits_per_quarter": {
            q: len(plan["schedule"][q]["audits"])
            for q in plan["schedule"]
        },
    }

    return plan


def format_markdown(plan: Dict[str, Any]) -> str:
    """Format audit plan as markdown."""
    lines = [
        f"# ISMS Audit Plan {plan['metadata']['year']}",
        f"",
        f"**Generated:** {plan['metadata']['generated'][:10]}",
        f"**Methodology:** {plan['metadata']['methodology']}",
        f"",
        f"## Summary",
        f"",
        f"| Metric | Value |",
        f"|--------|-------|",
        f"| Controls in Scope | {plan['summary']['total_controls_in_scope']} |",
        f"| Total Audits Planned | {plan['summary']['total_audits_planned']} |",
        f"| Critical Risk Controls | {plan['summary']['risk_distribution']['critical']} |",
        f"| High Risk Controls | {plan['summary']['risk_distribution']['high']} |",
        f"| Medium Risk Controls | {plan['summary']['risk_distribution']['medium']} |",
        f"",
    ]

    for quarter, data in plan["schedule"].items():
        lines.extend([
            f"## {quarter}: {data['month']}",
            f"",
            f"| Control | Name | Risk | Target Date |",
            f"|---------|------|------|-------------|",
        ])
        for audit in data["audits"]:
            lines.append(
                f"| {audit['control_id']} | {audit['control_name']} | "
                f"{audit['risk_level'].capitalize()} | {audit['target_date']} |"
            )
        lines.append("")

    lines.extend([
        f"## Risk-Based Audit Frequency",
        f"",
        f"| Risk Level | Audit Frequency |",
        f"|------------|-----------------|",
        f"| Critical | Quarterly (4x/year) |",
        f"| High | Semi-Annual (2x/year) |",
        f"| Medium | Annual (1x/year) |",
        f"| Low | Annual (1x/year) |",
    ])

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="ISMS Audit Scheduler - Risk-based audit planning"
    )
    parser.add_argument(
        "--year", "-y",
        type=int,
        default=datetime.now().year,
        help="Audit plan year (default: current year)"
    )
    parser.add_argument(
        "--controls", "-c",
        help="CSV file with control risk ratings"
    )
    parser.add_argument(
        "--output", "-o",
        help="Output file path"
    )
    parser.add_argument(
        "--format", "-f",
        choices=["json", "markdown"],
        default="json",
        help="Output format (default: json)"
    )

    args = parser.parse_args()

    # Load controls
    controls = None
    if args.controls:
        controls = load_controls_from_csv(args.controls)

    # Generate plan
    plan = generate_audit_plan(args.year, controls)

    # Format output
    if args.format == "markdown":
        output = format_markdown(plan)
    else:
        output = json.dumps(plan, indent=2)

    # Write output
    if args.output:
        with open(args.output, "w", encoding="utf-8") as f:
            f.write(output)
        print(f"Audit plan saved to: {args.output}", file=sys.stderr)
    else:
        print(output)


if __name__ == "__main__":
    main()
