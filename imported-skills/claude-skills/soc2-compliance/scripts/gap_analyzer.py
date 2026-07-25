#!/usr/bin/env python3
"""
SOC 2 Gap Analyzer

Analyzes current controls against SOC 2 Trust Service Criteria requirements
and identifies gaps. Supports both Type I (design) and Type II (design +
operating effectiveness) analysis.

Usage:
    python gap_analyzer.py --controls current_controls.json --type type1
    python gap_analyzer.py --controls current_controls.json --type type2 --json
"""

import argparse
import json
import sys
from datetime import datetime
from typing import Dict, List, Any, Tuple


# Minimum required TSC criteria coverage per category
REQUIRED_TSC = {
    "security": {
        "CC1.1": "Integrity and ethical values",
        "CC1.2": "Board oversight",
        "CC1.3": "Organizational structure",
        "CC1.4": "Competence commitment",
        "CC1.5": "Accountability",
        "CC2.1": "Information quality",
        "CC2.2": "Internal communication",
        "CC2.3": "External communication",
        "CC3.1": "Risk objectives",
        "CC3.2": "Risk identification",
        "CC3.3": "Fraud risk consideration",
        "CC3.4": "Change risk assessment",
        "CC4.1": "Monitoring evaluations",
        "CC4.2": "Deficiency communication",
        "CC5.1": "Control activities selection",
        "CC5.2": "Technology controls",
        "CC5.3": "Policy deployment",
        "CC6.1": "Logical access security",
        "CC6.2": "Access provisioning",
        "CC6.3": "Access removal",
        "CC6.4": "Access review",
        "CC6.5": "Physical access",
        "CC6.6": "Encryption",
        "CC6.7": "Data transmission restrictions",
        "CC6.8": "Unauthorized software prevention",
        "CC7.1": "Vulnerability management",
        "CC7.2": "Anomaly monitoring",
        "CC7.3": "Event evaluation",
        "CC7.4": "Incident response",
        "CC7.5": "Incident recovery",
        "CC8.1": "Change management",
        "CC9.1": "Vendor risk management",
        "CC9.2": "Risk mitigation/transfer",
    },
    "availability": {
        "A1.1": "Capacity and performance management",
        "A1.2": "Backup and recovery",
        "A1.3": "Recovery testing",
    },
    "confidentiality": {
        "C1.1": "Confidential data identification",
        "C1.2": "Confidential data protection",
        "C1.3": "Confidential data disposal",
    },
    "processing-integrity": {
        "PI1.1": "Processing accuracy",
        "PI1.2": "Processing completeness",
        "PI1.3": "Processing timeliness",
        "PI1.4": "Processing authorization",
    },
    "privacy": {
        "P1.1": "Privacy notice",
        "P2.1": "Choice and consent",
        "P3.1": "Data collection",
        "P4.1": "Use and retention",
        "P4.2": "Disposal",
        "P5.1": "Access rights",
        "P5.2": "Correction rights",
        "P6.1": "Disclosure controls",
        "P6.2": "Breach notification",
        "P7.1": "Data quality",
        "P8.1": "Privacy monitoring",
    },
}

# Type II additional checks
TYPE2_CHECKS = [
    {
        "check": "evidence_period",
        "description": "Evidence covers the full observation period",
        "severity": "critical",
    },
    {
        "check": "operating_consistency",
        "description": "Control operated consistently throughout the period",
        "severity": "critical",
    },
    {
        "check": "exception_handling",
        "description": "Exceptions are documented and addressed",
        "severity": "high",
    },
    {
        "check": "owner_accountability",
        "description": "Control owners documented and accountable",
        "severity": "medium",
    },
    {
        "check": "evidence_timestamps",
        "description": "Evidence has timestamps within the observation period",
        "severity": "high",
    },
    {
        "check": "frequency_adherence",
        "description": "Control executed at the specified frequency",
        "severity": "critical",
    },
]


def load_controls(filepath: str) -> List[Dict[str, Any]]:
    """Load current controls from a JSON file."""
    try:
        with open(filepath, "r") as f:
            data = json.load(f)
    except FileNotFoundError:
        print(f"Error: File not found: {filepath}", file=sys.stderr)
        sys.exit(1)
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON in {filepath}: {e}", file=sys.stderr)
        sys.exit(1)

    if isinstance(data, dict) and "controls" in data:
        return data["controls"]
    elif isinstance(data, list):
        return data
    else:
        print(
            "Error: Expected JSON with 'controls' array or a plain array.",
            file=sys.stderr,
        )
        sys.exit(1)


def detect_categories(controls: List[Dict[str, Any]]) -> List[str]:
    """Detect which TSC categories are represented in the controls."""
    tsc_values = set()
    for ctrl in controls:
        tsc = ctrl.get("tsc_criteria", "")
        if tsc:
            tsc_values.add(tsc)

    categories = set()
    for cat, criteria in REQUIRED_TSC.items():
        for tsc_id in criteria:
            if tsc_id in tsc_values:
                categories.add(cat)
                break

    # Always include security as it's required
    categories.add("security")
    return sorted(categories)


def analyze_coverage(
    controls: List[Dict[str, Any]], categories: List[str]
) -> Tuple[List[Dict], List[Dict], List[Dict]]:
    """Analyze TSC coverage and identify gaps."""
    # Map existing controls by TSC criteria
    covered_tsc = {}
    for ctrl in controls:
        tsc = ctrl.get("tsc_criteria", "")
        if tsc:
            if tsc not in covered_tsc:
                covered_tsc[tsc] = []
            covered_tsc[tsc].append(ctrl)

    gaps = []
    partial = []
    covered = []

    for cat in categories:
        if cat not in REQUIRED_TSC:
            continue
        for tsc_id, tsc_desc in REQUIRED_TSC[cat].items():
            if tsc_id not in covered_tsc:
                gaps.append(
                    {
                        "tsc_criteria": tsc_id,
                        "description": tsc_desc,
                        "category": cat,
                        "gap_type": "missing",
                        "severity": "critical" if cat == "security" else "high",
                        "remediation": f"Implement control(s) addressing {tsc_id}: {tsc_desc}",
                    }
                )
            else:
                ctrls = covered_tsc[tsc_id]
                # Check for partial implementation
                has_issues = False
                for ctrl in ctrls:
                    status = ctrl.get("status", "").lower()
                    if status in ("not started", "not_started", ""):
                        has_issues = True
                    owner = ctrl.get("owner", "TBD")
                    if owner in ("TBD", "", "N/A"):
                        has_issues = True

                if has_issues:
                    partial.append(
                        {
                            "tsc_criteria": tsc_id,
                            "description": tsc_desc,
                            "category": cat,
                            "gap_type": "partial",
                            "severity": "medium",
                            "controls": [c.get("control_id", "N/A") for c in ctrls],
                            "remediation": f"Complete implementation and assign owners for {tsc_id} controls",
                        }
                    )
                else:
                    covered.append(
                        {
                            "tsc_criteria": tsc_id,
                            "description": tsc_desc,
                            "category": cat,
                            "controls": [c.get("control_id", "N/A") for c in ctrls],
                        }
                    )

    return gaps, partial, covered


def analyze_type2_gaps(controls: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """Additional gap analysis for Type II operating effectiveness."""
    type2_gaps = []

    for ctrl in controls:
        ctrl_id = ctrl.get("control_id", "N/A")
        issues = []

        # Check for evidence date coverage
        evidence_date = ctrl.get("evidence_date", "")
        if not evidence_date:
            issues.append(
                {
                    "check": "evidence_period",
                    "severity": "critical",
                    "detail": "No evidence date recorded",
                }
            )

        # Check owner assignment
        owner = ctrl.get("owner", "TBD")
        if owner in ("TBD", "", "N/A"):
            issues.append(
                {
                    "check": "owner_accountability",
                    "severity": "medium",
                    "detail": "No control owner assigned",
                }
            )

        # Check status for operating evidence
        status = ctrl.get("status", "").lower()
        if status not in ("collected", "complete", "done"):
            issues.append(
                {
                    "check": "operating_consistency",
                    "severity": "critical",
                    "detail": f"Control status is '{ctrl.get('status', 'Not Started')}' — operating evidence needed",
                }
            )

        # Check frequency is defined
        frequency = ctrl.get("frequency", "")
        if not frequency:
            issues.append(
                {
                    "check": "frequency_adherence",
                    "severity": "critical",
                    "detail": "No control frequency defined",
                }
            )

        if issues:
            type2_gaps.append(
                {
                    "control_id": ctrl_id,
                    "tsc_criteria": ctrl.get("tsc_criteria", "N/A"),
                    "description": ctrl.get("description", "N/A"),
                    "issues": issues,
                }
            )

    return type2_gaps


def build_report(
    controls: List[Dict[str, Any]],
    audit_type: str,
    categories: List[str],
    gaps: List[Dict],
    partial: List[Dict],
    covered: List[Dict],
    type2_gaps: List[Dict],
) -> Dict[str, Any]:
    """Build the complete gap analysis report."""
    total_criteria = sum(
        len(REQUIRED_TSC[c]) for c in categories if c in REQUIRED_TSC
    )
    covered_count = len(covered)
    gap_count = len(gaps)
    partial_count = len(partial)

    coverage_pct = (
        round(covered_count / total_criteria * 100, 1) if total_criteria > 0 else 0
    )
    critical_gaps = len([g for g in gaps if g.get("severity") == "critical"])

    if coverage_pct >= 90 and critical_gaps == 0:
        readiness = "Ready"
    elif coverage_pct >= 75:
        readiness = "Near Ready — address gaps before audit"
    elif coverage_pct >= 50:
        readiness = "Significant work needed"
    else:
        readiness = "Not ready — major build-out required"

    report = {
        "report_metadata": {
            "audit_type": audit_type,
            "categories_assessed": categories,
            "report_date": datetime.now().strftime("%Y-%m-%d"),
            "total_controls_assessed": len(controls),
        },
        "coverage_summary": {
            "total_criteria": total_criteria,
            "covered": covered_count,
            "partially_covered": partial_count,
            "missing": gap_count,
            "coverage_percentage": coverage_pct,
            "critical_gaps": critical_gaps,
            "readiness_assessment": readiness,
        },
        "gaps": gaps,
        "partial_implementations": partial,
        "covered_criteria": covered,
    }

    if audit_type == "type2":
        type2_issue_count = sum(len(g["issues"]) for g in type2_gaps)
        report["type2_operating_gaps"] = {
            "controls_with_issues": len(type2_gaps),
            "total_issues": type2_issue_count,
            "details": type2_gaps,
        }

    return report


def format_text_report(report: Dict[str, Any]) -> str:
    """Format the gap analysis report as human-readable text."""
    lines = [
        "=" * 65,
        "SOC 2 Gap Analysis Report",
        "=" * 65,
        "",
    ]

    meta = report["report_metadata"]
    lines.append(f"Audit Type:    {meta['audit_type'].upper()}")
    lines.append(f"Report Date:   {meta['report_date']}")
    lines.append(f"Categories:    {', '.join(meta['categories_assessed'])}")
    lines.append(f"Controls:      {meta['total_controls_assessed']}")
    lines.append("")

    # Coverage summary
    cov = report["coverage_summary"]
    lines.append("--- Coverage Summary ---")
    lines.append(f"  Total TSC Criteria:    {cov['total_criteria']}")
    lines.append(f"  Fully Covered:         {cov['covered']}")
    lines.append(f"  Partially Covered:     {cov['partially_covered']}")
    lines.append(f"  Missing:               {cov['missing']}")
    lines.append(f"  Coverage:              {cov['coverage_percentage']}%")
    lines.append(f"  Critical Gaps:         {cov['critical_gaps']}")
    lines.append(f"  Readiness:             {cov['readiness_assessment']}")
    lines.append("")

    # Gaps
    gaps = report.get("gaps", [])
    if gaps:
        lines.append(f"--- Missing Controls ({len(gaps)}) ---")
        for g in gaps:
            sev = g["severity"].upper()
            lines.append(
                f"  [{sev}] {g['tsc_criteria']}: {g['description']}"
            )
            lines.append(f"         Remediation: {g['remediation']}")
        lines.append("")

    # Partial
    partial = report.get("partial_implementations", [])
    if partial:
        lines.append(f"--- Partial Implementations ({len(partial)}) ---")
        for p in partial:
            ctrls = ", ".join(p.get("controls", []))
            lines.append(
                f"  [{p['severity'].upper()}] {p['tsc_criteria']}: {p['description']}"
            )
            lines.append(f"         Controls: {ctrls}")
            lines.append(f"         Remediation: {p['remediation']}")
        lines.append("")

    # Type II operating gaps
    if "type2_operating_gaps" in report:
        t2 = report["type2_operating_gaps"]
        lines.append(
            f"--- Type II Operating Gaps ({t2['controls_with_issues']} controls, {t2['total_issues']} issues) ---"
        )
        for detail in t2["details"]:
            lines.append(f"  [{detail['control_id']}] {detail['description']}")
            for issue in detail["issues"]:
                lines.append(
                    f"    - [{issue['severity'].upper()}] {issue['check']}: {issue['detail']}"
                )
        lines.append("")

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="SOC 2 Gap Analyzer — identifies gaps between current controls and SOC 2 requirements."
    )
    parser.add_argument(
        "--controls",
        type=str,
        required=True,
        help="Path to JSON file with current controls (from control_matrix_builder.py or custom)",
    )
    parser.add_argument(
        "--type",
        type=str,
        choices=["type1", "type2"],
        default="type1",
        help="Audit type: type1 (design only) or type2 (design + operating effectiveness)",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output in JSON format",
    )

    args = parser.parse_args()

    controls = load_controls(args.controls)
    categories = detect_categories(controls)
    gaps, partial, covered = analyze_coverage(controls, categories)

    type2_gaps = []
    if args.type == "type2":
        type2_gaps = analyze_type2_gaps(controls)

    report = build_report(
        controls, args.type, categories, gaps, partial, covered, type2_gaps
    )

    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print(format_text_report(report))


if __name__ == "__main__":
    main()
