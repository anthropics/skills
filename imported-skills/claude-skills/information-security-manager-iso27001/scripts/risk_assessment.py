#!/usr/bin/env python3
"""
Security Risk Assessment Tool

Automated risk assessment following ISO 27001 Clause 6.1.2 methodology.
Identifies assets, threats, vulnerabilities, and calculates risk scores.

Usage:
    python risk_assessment.py --scope "system-name" --output risks.json
    python risk_assessment.py --assets assets.csv --template healthcare
"""

import argparse
import csv
import json
import sys
from datetime import datetime
from typing import Dict, List, Any, Optional


# Threat catalogs by template
THREAT_CATALOGS = {
    "general": [
        {"id": "T01", "name": "Unauthorized access", "category": "Access", "likelihood": 4},
        {"id": "T02", "name": "Data breach", "category": "Confidentiality", "likelihood": 3},
        {"id": "T03", "name": "Malware infection", "category": "Integrity", "likelihood": 4},
        {"id": "T04", "name": "Phishing attack", "category": "Social Engineering", "likelihood": 5},
        {"id": "T05", "name": "Denial of service", "category": "Availability", "likelihood": 3},
        {"id": "T06", "name": "Insider threat", "category": "Personnel", "likelihood": 2},
        {"id": "T07", "name": "Physical theft", "category": "Physical", "likelihood": 2},
        {"id": "T08", "name": "System misconfiguration", "category": "Technical", "likelihood": 4},
        {"id": "T09", "name": "Third-party compromise", "category": "Supply Chain", "likelihood": 3},
        {"id": "T10", "name": "Natural disaster", "category": "Environmental", "likelihood": 1},
    ],
    "healthcare": [
        {"id": "T01", "name": "Patient data breach", "category": "Confidentiality", "likelihood": 4},
        {"id": "T02", "name": "Ransomware attack", "category": "Availability", "likelihood": 4},
        {"id": "T03", "name": "Medical device tampering", "category": "Integrity", "likelihood": 3},
        {"id": "T04", "name": "EHR unauthorized access", "category": "Access", "likelihood": 4},
        {"id": "T05", "name": "HIPAA violation", "category": "Compliance", "likelihood": 3},
        {"id": "T06", "name": "Clinical data corruption", "category": "Integrity", "likelihood": 2},
        {"id": "T07", "name": "Telemedicine interception", "category": "Confidentiality", "likelihood": 3},
        {"id": "T08", "name": "Credential theft", "category": "Access", "likelihood": 5},
        {"id": "T09", "name": "Third-party vendor breach", "category": "Supply Chain", "likelihood": 3},
        {"id": "T10", "name": "Insider data theft", "category": "Personnel", "likelihood": 2},
    ],
    "cloud": [
        {"id": "T01", "name": "Cloud misconfiguration", "category": "Technical", "likelihood": 5},
        {"id": "T02", "name": "API vulnerability exploit", "category": "Application", "likelihood": 4},
        {"id": "T03", "name": "Account hijacking", "category": "Access", "likelihood": 4},
        {"id": "T04", "name": "Data exfiltration", "category": "Confidentiality", "likelihood": 3},
        {"id": "T05", "name": "Shared tenancy attack", "category": "Infrastructure", "likelihood": 2},
        {"id": "T06", "name": "Service outage", "category": "Availability", "likelihood": 3},
        {"id": "T07", "name": "Compliance violation", "category": "Compliance", "likelihood": 3},
        {"id": "T08", "name": "Shadow IT exposure", "category": "Governance", "likelihood": 4},
        {"id": "T09", "name": "Encryption key exposure", "category": "Cryptography", "likelihood": 2},
        {"id": "T10", "name": "CSP vendor lock-in", "category": "Strategic", "likelihood": 3},
    ],
}

# Vulnerability patterns
VULNERABILITY_PATTERNS = {
    "access": ["No MFA", "Weak passwords", "Excessive privileges", "Shared accounts"],
    "technical": ["Unpatched systems", "Weak encryption", "Missing logging", "Open ports"],
    "process": ["No incident response", "Missing backups", "No change control", "Lack of monitoring"],
    "people": ["Untrained staff", "No security awareness", "Social engineering susceptibility"],
}

# Asset classification criteria
CLASSIFICATION_CRITERIA = {
    "critical": {"description": "Business-critical, severe impact if compromised", "impact": 5},
    "high": {"description": "Important assets, significant impact", "impact": 4},
    "medium": {"description": "Standard business assets, moderate impact", "impact": 3},
    "low": {"description": "Limited business value, minor impact", "impact": 2},
    "minimal": {"description": "Public or non-sensitive, negligible impact", "impact": 1},
}

# Risk treatment options
TREATMENT_OPTIONS = {
    "critical": "Immediate mitigation required - implement controls within 7 days",
    "high": "Priority mitigation - implement controls within 30 days",
    "medium": "Planned mitigation - implement controls within 90 days",
    "low": "Accept risk with monitoring or implement low-cost controls",
    "minimal": "Accept risk - document acceptance decision",
}


def calculate_risk_score(likelihood: int, impact: int) -> int:
    """Calculate risk score as likelihood × impact."""
    return likelihood * impact


def get_risk_level(score: int) -> str:
    """Determine risk level from score."""
    if score >= 20:
        return "critical"
    elif score >= 15:
        return "high"
    elif score >= 10:
        return "medium"
    elif score >= 5:
        return "low"
    return "minimal"


def load_assets_from_csv(filepath: str) -> List[Dict[str, Any]]:
    """Load asset inventory from CSV file."""
    assets = []
    try:
        with open(filepath, "r", encoding="utf-8") as f:
            reader = csv.DictReader(f)
            for row in reader:
                asset = {
                    "id": row.get("id", f"A{len(assets)+1:03d}"),
                    "name": row.get("name", "Unknown"),
                    "type": row.get("type", "Information"),
                    "owner": row.get("owner", "Unassigned"),
                    "classification": row.get("classification", "medium").lower(),
                }
                assets.append(asset)
    except FileNotFoundError:
        print(f"Error: Asset file not found: {filepath}", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error reading asset file: {e}", file=sys.stderr)
        sys.exit(1)
    return assets


def generate_sample_assets(scope: str, template: str) -> List[Dict[str, Any]]:
    """Generate sample asset inventory based on scope and template."""
    base_assets = []

    if template == "healthcare":
        base_assets = [
            {"id": "A001", "name": "Patient Database", "type": "Information", "owner": "DBA Team", "classification": "critical"},
            {"id": "A002", "name": "EHR Application", "type": "Software", "owner": "App Team", "classification": "critical"},
            {"id": "A003", "name": "Medical Imaging System", "type": "Software", "owner": "Radiology", "classification": "high"},
            {"id": "A004", "name": "Database Servers", "type": "Hardware", "owner": "Infrastructure", "classification": "high"},
            {"id": "A005", "name": "Admin Credentials", "type": "Access", "owner": "Security", "classification": "critical"},
            {"id": "A006", "name": "Backup Systems", "type": "Service", "owner": "IT Ops", "classification": "high"},
            {"id": "A007", "name": "Network Infrastructure", "type": "Hardware", "owner": "Network Team", "classification": "high"},
            {"id": "A008", "name": "API Gateway", "type": "Software", "owner": "Platform Team", "classification": "high"},
        ]
    elif template == "cloud":
        base_assets = [
            {"id": "A001", "name": "Cloud Storage Buckets", "type": "Service", "owner": "Platform", "classification": "high"},
            {"id": "A002", "name": "Container Registry", "type": "Service", "owner": "DevOps", "classification": "high"},
            {"id": "A003", "name": "API Services", "type": "Software", "owner": "Engineering", "classification": "critical"},
            {"id": "A004", "name": "Database Instances", "type": "Service", "owner": "DBA Team", "classification": "critical"},
            {"id": "A005", "name": "IAM Configuration", "type": "Access", "owner": "Security", "classification": "critical"},
            {"id": "A006", "name": "Secrets Manager", "type": "Service", "owner": "Security", "classification": "critical"},
            {"id": "A007", "name": "Load Balancers", "type": "Infrastructure", "owner": "Platform", "classification": "high"},
            {"id": "A008", "name": "Monitoring Systems", "type": "Service", "owner": "SRE", "classification": "medium"},
        ]
    else:  # general
        base_assets = [
            {"id": "A001", "name": "Corporate Data", "type": "Information", "owner": "Data Team", "classification": "high"},
            {"id": "A002", "name": "Business Applications", "type": "Software", "owner": "IT", "classification": "high"},
            {"id": "A003", "name": "Server Infrastructure", "type": "Hardware", "owner": "Infrastructure", "classification": "high"},
            {"id": "A004", "name": "User Credentials", "type": "Access", "owner": "Security", "classification": "critical"},
            {"id": "A005", "name": "Email System", "type": "Service", "owner": "IT", "classification": "medium"},
            {"id": "A006", "name": "File Servers", "type": "Hardware", "owner": "Infrastructure", "classification": "medium"},
            {"id": "A007", "name": "Network Equipment", "type": "Hardware", "owner": "Network", "classification": "high"},
            {"id": "A008", "name": "Backup Infrastructure", "type": "Service", "owner": "IT Ops", "classification": "high"},
        ]

    # Tag assets with scope
    for asset in base_assets:
        asset["scope"] = scope

    return base_assets


def assess_risks(
    assets: List[Dict[str, Any]],
    template: str
) -> List[Dict[str, Any]]:
    """Perform risk assessment on assets."""
    threats = THREAT_CATALOGS.get(template, THREAT_CATALOGS["general"])
    risks = []
    risk_id = 1

    for asset in assets:
        classification = asset.get("classification", "medium")
        impact = CLASSIFICATION_CRITERIA.get(classification, {}).get("impact", 3)

        # Map relevant threats to asset
        relevant_threats = threats[:5]  # Top 5 threats for each asset

        for threat in relevant_threats:
            likelihood = threat["likelihood"]
            score = calculate_risk_score(likelihood, impact)
            level = get_risk_level(score)

            # Identify potential vulnerabilities
            vuln_category = threat["category"].lower()
            vulns = VULNERABILITY_PATTERNS.get("technical", ["Unknown vulnerability"])
            if "access" in vuln_category:
                vulns = VULNERABILITY_PATTERNS["access"]
            elif "personnel" in vuln_category or "social" in vuln_category:
                vulns = VULNERABILITY_PATTERNS["people"]

            risk = {
                "id": f"R{risk_id:03d}",
                "asset_id": asset["id"],
                "asset_name": asset["name"],
                "threat_id": threat["id"],
                "threat_name": threat["name"],
                "threat_category": threat["category"],
                "vulnerability": vulns[0] if vulns else "Unidentified",
                "likelihood": likelihood,
                "impact": impact,
                "score": score,
                "level": level,
                "treatment": TREATMENT_OPTIONS.get(level, "Review required"),
            }
            risks.append(risk)
            risk_id += 1

    # Sort by risk score descending
    risks.sort(key=lambda x: x["score"], reverse=True)
    return risks


def calculate_residual_risk(risk: Dict[str, Any], control_effectiveness: float = 0.7) -> Dict[str, Any]:
    """Calculate residual risk after applying controls."""
    residual_likelihood = max(1, int(risk["likelihood"] * (1 - control_effectiveness)))
    residual_score = calculate_risk_score(residual_likelihood, risk["impact"])

    return {
        "risk_id": risk["id"],
        "inherent_score": risk["score"],
        "control_effectiveness": control_effectiveness,
        "residual_likelihood": residual_likelihood,
        "residual_score": residual_score,
        "residual_level": get_risk_level(residual_score),
    }


def generate_report(
    scope: str,
    template: str,
    assets: List[Dict[str, Any]],
    risks: List[Dict[str, Any]],
    output_format: str
) -> str:
    """Generate risk assessment report."""
    timestamp = datetime.now().isoformat()

    # Calculate summary statistics
    risk_counts = {"critical": 0, "high": 0, "medium": 0, "low": 0, "minimal": 0}
    for risk in risks:
        risk_counts[risk["level"]] += 1

    report_data = {
        "metadata": {
            "scope": scope,
            "template": template,
            "timestamp": timestamp,
            "methodology": "ISO 27001 Clause 6.1.2",
        },
        "summary": {
            "total_assets": len(assets),
            "total_risks": len(risks),
            "risk_distribution": risk_counts,
            "critical_risks": risk_counts["critical"],
            "high_risks": risk_counts["high"],
        },
        "assets": assets,
        "risks": risks,
        "residual_risks": [calculate_residual_risk(r) for r in risks[:10]],  # Top 10
    }

    if output_format == "json":
        return json.dumps(report_data, indent=2)
    elif output_format == "csv":
        lines = ["risk_id,asset,threat,likelihood,impact,score,level,treatment"]
        for risk in risks:
            lines.append(
                f"{risk['id']},{risk['asset_name']},{risk['threat_name']},"
                f"{risk['likelihood']},{risk['impact']},{risk['score']},"
                f"{risk['level']},{risk['treatment']}"
            )
        return "\n".join(lines)
    else:  # markdown
        lines = [
            f"# Security Risk Assessment Report",
            f"",
            f"**Scope:** {scope}",
            f"**Template:** {template}",
            f"**Date:** {timestamp}",
            f"**Methodology:** ISO 27001 Clause 6.1.2",
            f"",
            f"## Summary",
            f"",
            f"| Metric | Value |",
            f"|--------|-------|",
            f"| Total Assets | {len(assets)} |",
            f"| Total Risks | {len(risks)} |",
            f"| Critical Risks | {risk_counts['critical']} |",
            f"| High Risks | {risk_counts['high']} |",
            f"| Medium Risks | {risk_counts['medium']} |",
            f"",
            f"## Asset Inventory",
            f"",
            f"| ID | Asset | Type | Owner | Classification |",
            f"|----|-------|------|-------|----------------|",
        ]
        for asset in assets:
            lines.append(
                f"| {asset['id']} | {asset['name']} | {asset['type']} | "
                f"{asset['owner']} | {asset['classification'].capitalize()} |"
            )

        lines.extend([
            f"",
            f"## Risk Register",
            f"",
            f"| Risk ID | Asset | Threat | L | I | Score | Level |",
            f"|---------|-------|--------|---|---|-------|-------|",
        ])
        for risk in risks[:20]:  # Top 20 risks
            lines.append(
                f"| {risk['id']} | {risk['asset_name']} | {risk['threat_name']} | "
                f"{risk['likelihood']} | {risk['impact']} | {risk['score']} | "
                f"{risk['level'].capitalize()} |"
            )

        lines.extend([
            f"",
            f"## Treatment Recommendations",
            f"",
        ])
        for level, treatment in TREATMENT_OPTIONS.items():
            count = risk_counts[level]
            if count > 0:
                lines.append(f"**{level.capitalize()} ({count} risks):** {treatment}")

        return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Security Risk Assessment Tool - ISO 27001 Clause 6.1.2"
    )
    parser.add_argument(
        "--scope", "-s",
        required=True,
        help="System or area to assess"
    )
    parser.add_argument(
        "--template", "-t",
        choices=["general", "healthcare", "cloud"],
        default="general",
        help="Assessment template (default: general)"
    )
    parser.add_argument(
        "--assets", "-a",
        help="CSV file with asset inventory"
    )
    parser.add_argument(
        "--output", "-o",
        help="Output file path (default: stdout)"
    )
    parser.add_argument(
        "--format", "-f",
        choices=["json", "csv", "markdown"],
        default="markdown",
        help="Output format (default: markdown)"
    )

    args = parser.parse_args()

    # Load or generate assets
    if args.assets:
        assets = load_assets_from_csv(args.assets)
    else:
        assets = generate_sample_assets(args.scope, args.template)

    # Perform risk assessment
    risks = assess_risks(assets, args.template)

    # Generate report
    report = generate_report(
        args.scope,
        args.template,
        assets,
        risks,
        args.format
    )

    # Output
    if args.output:
        with open(args.output, "w", encoding="utf-8") as f:
            f.write(report)
        print(f"Report saved to: {args.output}", file=sys.stderr)
    else:
        print(report)


if __name__ == "__main__":
    main()
