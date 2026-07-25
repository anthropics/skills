#!/usr/bin/env python3
"""
ISO 27001/27002 Compliance Checker

Verify control implementation status and generate compliance reports.
Supports gap analysis and remediation recommendations.

Usage:
    python compliance_checker.py --standard iso27001
    python compliance_checker.py --standard iso27001 --gap-analysis --output gaps.md
"""

import argparse
import csv
import json
import sys
from datetime import datetime
from typing import Dict, List, Any, Optional


# ISO 27001:2022 Annex A Controls (simplified)
ISO27001_CONTROLS = {
    "organizational": {
        "name": "Organizational Controls",
        "controls": [
            {"id": "A.5.1", "name": "Policies for information security", "priority": "high"},
            {"id": "A.5.2", "name": "Information security roles and responsibilities", "priority": "high"},
            {"id": "A.5.3", "name": "Segregation of duties", "priority": "medium"},
            {"id": "A.5.4", "name": "Management responsibilities", "priority": "high"},
            {"id": "A.5.5", "name": "Contact with authorities", "priority": "medium"},
            {"id": "A.5.6", "name": "Contact with special interest groups", "priority": "low"},
            {"id": "A.5.7", "name": "Threat intelligence", "priority": "medium"},
            {"id": "A.5.8", "name": "Information security in project management", "priority": "medium"},
            {"id": "A.5.9", "name": "Inventory of information and assets", "priority": "high"},
            {"id": "A.5.10", "name": "Acceptable use of information", "priority": "high"},
        ]
    },
    "people": {
        "name": "People Controls",
        "controls": [
            {"id": "A.6.1", "name": "Screening", "priority": "high"},
            {"id": "A.6.2", "name": "Terms and conditions of employment", "priority": "high"},
            {"id": "A.6.3", "name": "Information security awareness and training", "priority": "high"},
            {"id": "A.6.4", "name": "Disciplinary process", "priority": "medium"},
            {"id": "A.6.5", "name": "Responsibilities after termination", "priority": "high"},
            {"id": "A.6.6", "name": "Confidentiality agreements", "priority": "high"},
            {"id": "A.6.7", "name": "Remote working", "priority": "high"},
            {"id": "A.6.8", "name": "Information security event reporting", "priority": "high"},
        ]
    },
    "physical": {
        "name": "Physical Controls",
        "controls": [
            {"id": "A.7.1", "name": "Physical security perimeters", "priority": "high"},
            {"id": "A.7.2", "name": "Physical entry", "priority": "high"},
            {"id": "A.7.3", "name": "Securing offices and facilities", "priority": "medium"},
            {"id": "A.7.4", "name": "Physical security monitoring", "priority": "medium"},
            {"id": "A.7.5", "name": "Protecting against environmental threats", "priority": "medium"},
            {"id": "A.7.6", "name": "Working in secure areas", "priority": "medium"},
            {"id": "A.7.7", "name": "Clear desk and screen", "priority": "medium"},
            {"id": "A.7.8", "name": "Equipment siting and protection", "priority": "medium"},
        ]
    },
    "technological": {
        "name": "Technological Controls",
        "controls": [
            {"id": "A.8.1", "name": "User endpoint devices", "priority": "high"},
            {"id": "A.8.2", "name": "Privileged access rights", "priority": "critical"},
            {"id": "A.8.3", "name": "Information access restriction", "priority": "high"},
            {"id": "A.8.4", "name": "Access to source code", "priority": "high"},
            {"id": "A.8.5", "name": "Secure authentication", "priority": "critical"},
            {"id": "A.8.6", "name": "Capacity management", "priority": "medium"},
            {"id": "A.8.7", "name": "Protection against malware", "priority": "critical"},
            {"id": "A.8.8", "name": "Management of technical vulnerabilities", "priority": "critical"},
            {"id": "A.8.9", "name": "Configuration management", "priority": "high"},
            {"id": "A.8.10", "name": "Information deletion", "priority": "high"},
            {"id": "A.8.11", "name": "Data masking", "priority": "medium"},
            {"id": "A.8.12", "name": "Data leakage prevention", "priority": "high"},
            {"id": "A.8.13", "name": "Information backup", "priority": "critical"},
            {"id": "A.8.14", "name": "Redundancy of information processing", "priority": "high"},
            {"id": "A.8.15", "name": "Logging", "priority": "critical"},
            {"id": "A.8.16", "name": "Monitoring activities", "priority": "high"},
            {"id": "A.8.17", "name": "Clock synchronization", "priority": "medium"},
            {"id": "A.8.18", "name": "Use of privileged utility programs", "priority": "high"},
            {"id": "A.8.19", "name": "Installation of software", "priority": "high"},
            {"id": "A.8.20", "name": "Networks security", "priority": "critical"},
            {"id": "A.8.21", "name": "Security of network services", "priority": "high"},
            {"id": "A.8.22", "name": "Segregation of networks", "priority": "high"},
            {"id": "A.8.23", "name": "Web filtering", "priority": "medium"},
            {"id": "A.8.24", "name": "Use of cryptography", "priority": "critical"},
            {"id": "A.8.25", "name": "Secure development lifecycle", "priority": "high"},
            {"id": "A.8.26", "name": "Application security requirements", "priority": "high"},
            {"id": "A.8.27", "name": "Secure system architecture", "priority": "high"},
            {"id": "A.8.28", "name": "Secure coding", "priority": "high"},
        ]
    },
}

# Remediation recommendations by control
REMEDIATION_GUIDANCE = {
    "A.5.1": "Develop and publish information security policy signed by management",
    "A.5.2": "Define RACI matrix for security roles; appoint Information Security Manager",
    "A.5.9": "Create asset inventory with owners and classification",
    "A.6.3": "Implement annual security awareness training program",
    "A.6.7": "Establish remote working policy with technical controls",
    "A.8.2": "Implement privileged access management (PAM) solution",
    "A.8.5": "Deploy MFA for all user and admin accounts",
    "A.8.7": "Deploy endpoint protection on all devices with central management",
    "A.8.8": "Implement vulnerability scanning with 30-day remediation SLA",
    "A.8.13": "Configure automated backups with encryption and offsite storage",
    "A.8.15": "Deploy SIEM with log retention per compliance requirements",
    "A.8.20": "Implement firewall, IDS/IPS, and network monitoring",
    "A.8.24": "Enforce TLS 1.3 for transit, AES-256 for data at rest",
}


def get_control_status(control_id: str, controls_data: Optional[Dict] = None) -> str:
    """Get implementation status for a control."""
    if controls_data and control_id in controls_data:
        return controls_data[control_id]
    # Default: simulate partial implementation
    import random
    random.seed(hash(control_id))
    statuses = ["implemented", "implemented", "partial", "partial", "not_implemented"]
    return random.choice(statuses)


def load_controls_from_csv(filepath: str) -> Dict[str, str]:
    """Load control status from CSV file."""
    controls = {}
    try:
        with open(filepath, "r", encoding="utf-8") as f:
            reader = csv.DictReader(f)
            for row in reader:
                control_id = row.get("control_id", row.get("id", ""))
                status = row.get("status", "not_implemented").lower()
                if control_id:
                    controls[control_id] = status
    except FileNotFoundError:
        print(f"Error: Controls file not found: {filepath}", file=sys.stderr)
        sys.exit(1)
    return controls


def check_compliance(
    standard: str,
    controls_data: Optional[Dict] = None,
    domains: Optional[List[str]] = None
) -> Dict[str, Any]:
    """Check compliance against standard controls."""
    if standard not in ["iso27001", "iso27002"]:
        print(f"Error: Unsupported standard: {standard}", file=sys.stderr)
        sys.exit(1)

    results = {
        "standard": standard,
        "timestamp": datetime.now().isoformat(),
        "domains": {},
        "summary": {
            "total_controls": 0,
            "implemented": 0,
            "partial": 0,
            "not_implemented": 0,
        },
        "findings": [],
    }

    for domain_key, domain_data in ISO27001_CONTROLS.items():
        if domains and domain_key not in domains:
            continue

        domain_results = {
            "name": domain_data["name"],
            "controls": [],
            "implemented": 0,
            "partial": 0,
            "not_implemented": 0,
        }

        for control in domain_data["controls"]:
            status = get_control_status(control["id"], controls_data)

            control_result = {
                "id": control["id"],
                "name": control["name"],
                "priority": control["priority"],
                "status": status,
            }

            domain_results["controls"].append(control_result)
            results["summary"]["total_controls"] += 1

            if status == "implemented":
                domain_results["implemented"] += 1
                results["summary"]["implemented"] += 1
            elif status == "partial":
                domain_results["partial"] += 1
                results["summary"]["partial"] += 1
            else:
                domain_results["not_implemented"] += 1
                results["summary"]["not_implemented"] += 1

                # Add to findings if high priority
                if control["priority"] in ["critical", "high"]:
                    results["findings"].append({
                        "control_id": control["id"],
                        "control_name": control["name"],
                        "priority": control["priority"],
                        "status": status,
                        "remediation": REMEDIATION_GUIDANCE.get(
                            control["id"],
                            "Implement control per ISO 27001 requirements"
                        ),
                    })

        results["domains"][domain_key] = domain_results

    # Calculate compliance percentage
    total = results["summary"]["total_controls"]
    implemented = results["summary"]["implemented"]
    partial = results["summary"]["partial"]
    results["summary"]["compliance_percentage"] = round(
        ((implemented + partial * 0.5) / total) * 100, 1
    ) if total > 0 else 0

    return results


def generate_gap_analysis(results: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Generate gap analysis with prioritized recommendations."""
    gaps = []

    for finding in results["findings"]:
        gap = {
            "control_id": finding["control_id"],
            "control_name": finding["control_name"],
            "current_status": finding["status"],
            "priority": finding["priority"],
            "remediation": finding["remediation"],
            "effort": "medium" if finding["priority"] == "high" else "high",
            "timeline": "30 days" if finding["priority"] == "critical" else "90 days",
        }
        gaps.append(gap)

    # Sort by priority
    priority_order = {"critical": 0, "high": 1, "medium": 2, "low": 3}
    gaps.sort(key=lambda x: priority_order.get(x["priority"], 99))

    return gaps


def format_output(
    results: Dict[str, Any],
    gap_analysis: bool,
    output_format: str
) -> str:
    """Format compliance results for output."""
    if output_format == "json":
        if gap_analysis:
            results["gap_analysis"] = generate_gap_analysis(results)
        return json.dumps(results, indent=2)

    # Markdown format
    lines = [
        f"# {results['standard'].upper()} Compliance Report",
        f"",
        f"**Generated:** {results['timestamp']}",
        f"",
        f"## Summary",
        f"",
        f"| Metric | Value |",
        f"|--------|-------|",
        f"| Total Controls | {results['summary']['total_controls']} |",
        f"| Implemented | {results['summary']['implemented']} |",
        f"| Partial | {results['summary']['partial']} |",
        f"| Not Implemented | {results['summary']['not_implemented']} |",
        f"| **Compliance** | **{results['summary']['compliance_percentage']}%** |",
        f"",
    ]

    # Domain breakdown
    lines.extend([
        f"## Compliance by Domain",
        f"",
        f"| Domain | Implemented | Partial | Not Impl | Score |",
        f"|--------|-------------|---------|----------|-------|",
    ])

    for domain_key, domain_data in results["domains"].items():
        total = len(domain_data["controls"])
        score = round(
            ((domain_data["implemented"] + domain_data["partial"] * 0.5) / total) * 100
        ) if total > 0 else 0
        lines.append(
            f"| {domain_data['name']} | {domain_data['implemented']} | "
            f"{domain_data['partial']} | {domain_data['not_implemented']} | {score}% |"
        )

    # Findings
    if results["findings"]:
        lines.extend([
            f"",
            f"## Priority Findings",
            f"",
            f"| Control | Name | Priority | Status |",
            f"|---------|------|----------|--------|",
        ])
        for finding in results["findings"][:15]:  # Top 15
            lines.append(
                f"| {finding['control_id']} | {finding['control_name']} | "
                f"{finding['priority'].capitalize()} | {finding['status'].replace('_', ' ').capitalize()} |"
            )

    # Gap analysis
    if gap_analysis:
        gaps = generate_gap_analysis(results)
        lines.extend([
            f"",
            f"## Gap Analysis & Remediation",
            f"",
        ])
        for gap in gaps[:10]:  # Top 10 gaps
            lines.extend([
                f"### {gap['control_id']}: {gap['control_name']}",
                f"",
                f"- **Priority:** {gap['priority'].capitalize()}",
                f"- **Current Status:** {gap['current_status'].replace('_', ' ').capitalize()}",
                f"- **Remediation:** {gap['remediation']}",
                f"- **Timeline:** {gap['timeline']}",
                f"",
            ])

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="ISO 27001/27002 Compliance Checker"
    )
    parser.add_argument(
        "--standard", "-s",
        required=True,
        choices=["iso27001", "iso27002", "hipaa"],
        help="Compliance standard to check"
    )
    parser.add_argument(
        "--controls-file", "-c",
        help="CSV file with current control implementation status"
    )
    parser.add_argument(
        "--gap-analysis", "-g",
        action="store_true",
        help="Include gap analysis with remediation recommendations"
    )
    parser.add_argument(
        "--domains", "-d",
        help="Comma-separated list of domains to check (e.g., organizational,technological)"
    )
    parser.add_argument(
        "--output", "-o",
        help="Output file path (default: stdout)"
    )
    parser.add_argument(
        "--format", "-f",
        choices=["json", "markdown"],
        default="markdown",
        help="Output format (default: markdown)"
    )

    args = parser.parse_args()

    # Load control status if provided
    controls_data = None
    if args.controls_file:
        controls_data = load_controls_from_csv(args.controls_file)

    # Parse domains
    domains = None
    if args.domains:
        domains = [d.strip().lower().replace("-", "_") for d in args.domains.split(",")]

    # Check compliance
    results = check_compliance(args.standard, controls_data, domains)

    # Format output
    output = format_output(results, args.gap_analysis, args.format)

    # Write output
    if args.output:
        with open(args.output, "w", encoding="utf-8") as f:
            f.write(output)
        print(f"Report saved to: {args.output}", file=sys.stderr)
    else:
        print(output)


if __name__ == "__main__":
    main()
