#!/usr/bin/env python3
"""
SOC 2 Control Matrix Builder

Generates a SOC 2 control matrix from selected Trust Service Criteria categories.
Outputs in markdown, JSON, or CSV format.

Usage:
    python control_matrix_builder.py --categories security --format md
    python control_matrix_builder.py --categories security,availability --format json
    python control_matrix_builder.py --categories security,availability,confidentiality,processing-integrity,privacy --format csv
"""

import argparse
import csv
import io
import json
import sys
from typing import Dict, List, Any


# Trust Service Criteria control definitions
TSC_CONTROLS: Dict[str, Dict[str, Any]] = {
    "security": {
        "name": "Security (Common Criteria)",
        "controls": [
            {
                "id": "SEC-001",
                "tsc": "CC1.1",
                "description": "Management demonstrates commitment to integrity and ethical values",
                "type": "Preventive",
                "frequency": "Annual",
                "evidence": "Code of conduct, ethics policy, signed acknowledgments",
            },
            {
                "id": "SEC-002",
                "tsc": "CC1.2",
                "description": "Board of directors demonstrates independence and exercises oversight",
                "type": "Preventive",
                "frequency": "Quarterly",
                "evidence": "Board meeting minutes, oversight committee charters",
            },
            {
                "id": "SEC-003",
                "tsc": "CC1.3",
                "description": "Management establishes organizational structure, reporting lines, and authorities",
                "type": "Preventive",
                "frequency": "Annual",
                "evidence": "Org charts, RACI matrices, role descriptions",
            },
            {
                "id": "SEC-004",
                "tsc": "CC1.4",
                "description": "Organization demonstrates commitment to attract, develop, and retain competent individuals",
                "type": "Preventive",
                "frequency": "Annual",
                "evidence": "Training records, competency assessments, HR policies",
            },
            {
                "id": "SEC-005",
                "tsc": "CC1.5",
                "description": "Organization holds individuals accountable for internal control responsibilities",
                "type": "Preventive",
                "frequency": "Annual",
                "evidence": "Performance reviews, disciplinary policy, accountability matrix",
            },
            {
                "id": "SEC-006",
                "tsc": "CC2.1",
                "description": "Organization obtains and generates relevant quality information to support internal control",
                "type": "Detective",
                "frequency": "Continuous",
                "evidence": "Information classification policy, data flow diagrams",
            },
            {
                "id": "SEC-007",
                "tsc": "CC2.2",
                "description": "Organization internally communicates objectives and responsibilities for internal control",
                "type": "Preventive",
                "frequency": "Quarterly",
                "evidence": "Internal communications, policy distribution records, training materials",
            },
            {
                "id": "SEC-008",
                "tsc": "CC2.3",
                "description": "Organization communicates with external parties regarding matters affecting internal control",
                "type": "Preventive",
                "frequency": "Continuous",
                "evidence": "Customer notifications, external communication policy, incident notices",
            },
            {
                "id": "SEC-009",
                "tsc": "CC3.1",
                "description": "Organization specifies objectives to identify and assess risks",
                "type": "Preventive",
                "frequency": "Annual",
                "evidence": "Risk assessment methodology, risk register, risk appetite statement",
            },
            {
                "id": "SEC-010",
                "tsc": "CC3.2",
                "description": "Organization identifies and analyzes risks to achievement of objectives",
                "type": "Detective",
                "frequency": "Annual",
                "evidence": "Risk assessment report, threat modeling documentation",
            },
            {
                "id": "SEC-011",
                "tsc": "CC3.3",
                "description": "Organization considers potential for fraud in assessing risks",
                "type": "Detective",
                "frequency": "Annual",
                "evidence": "Fraud risk assessment, anti-fraud controls documentation",
            },
            {
                "id": "SEC-012",
                "tsc": "CC3.4",
                "description": "Organization identifies and assesses changes that could impact internal control",
                "type": "Detective",
                "frequency": "Quarterly",
                "evidence": "Change impact assessments, environmental scan reports",
            },
            {
                "id": "SEC-013",
                "tsc": "CC4.1",
                "description": "Organization selects and performs ongoing and separate monitoring evaluations",
                "type": "Detective",
                "frequency": "Continuous",
                "evidence": "Monitoring dashboards, automated alert configurations, review logs",
            },
            {
                "id": "SEC-014",
                "tsc": "CC4.2",
                "description": "Organization evaluates and communicates internal control deficiencies",
                "type": "Corrective",
                "frequency": "Quarterly",
                "evidence": "Deficiency tracking log, management reports, remediation plans",
            },
            {
                "id": "SEC-015",
                "tsc": "CC5.1",
                "description": "Organization selects and develops control activities that mitigate risks",
                "type": "Preventive",
                "frequency": "Annual",
                "evidence": "Control matrix, risk treatment plans, control design documentation",
            },
            {
                "id": "SEC-016",
                "tsc": "CC5.2",
                "description": "Organization selects and develops general control activities over technology",
                "type": "Preventive",
                "frequency": "Continuous",
                "evidence": "IT general controls documentation, technology policies",
            },
            {
                "id": "SEC-017",
                "tsc": "CC5.3",
                "description": "Organization deploys control activities through policies and procedures",
                "type": "Preventive",
                "frequency": "Annual",
                "evidence": "Policy library, procedure documents, acknowledgment records",
            },
            {
                "id": "SEC-018",
                "tsc": "CC6.1",
                "description": "Logical access security controls over protected information assets",
                "type": "Preventive",
                "frequency": "Continuous",
                "evidence": "Access control policy, IAM configuration, SSO/MFA settings",
            },
            {
                "id": "SEC-019",
                "tsc": "CC6.2",
                "description": "User access provisioning based on role and business need",
                "type": "Preventive",
                "frequency": "Continuous",
                "evidence": "Provisioning tickets, role matrix, access request approvals",
            },
            {
                "id": "SEC-020",
                "tsc": "CC6.3",
                "description": "User access removal upon termination or role change",
                "type": "Preventive",
                "frequency": "Continuous",
                "evidence": "Deprovisioning tickets, termination checklists, access removal logs",
            },
            {
                "id": "SEC-021",
                "tsc": "CC6.4",
                "description": "Periodic access reviews to validate appropriateness",
                "type": "Detective",
                "frequency": "Quarterly",
                "evidence": "Access review reports, user entitlement listings, review sign-offs",
            },
            {
                "id": "SEC-022",
                "tsc": "CC6.5",
                "description": "Physical access restrictions to facilities and protected assets",
                "type": "Preventive",
                "frequency": "Continuous",
                "evidence": "Badge access logs, visitor logs, physical security configuration",
            },
            {
                "id": "SEC-023",
                "tsc": "CC6.6",
                "description": "Encryption of data in transit and at rest",
                "type": "Preventive",
                "frequency": "Continuous",
                "evidence": "TLS configuration, encryption settings, certificate inventory",
            },
            {
                "id": "SEC-024",
                "tsc": "CC6.7",
                "description": "Restrictions on data transmission and movement",
                "type": "Preventive",
                "frequency": "Continuous",
                "evidence": "DLP configuration, network segmentation, firewall rules",
            },
            {
                "id": "SEC-025",
                "tsc": "CC6.8",
                "description": "Controls to prevent or detect unauthorized software",
                "type": "Detective",
                "frequency": "Continuous",
                "evidence": "Endpoint protection config, software whitelist, malware scan reports",
            },
            {
                "id": "SEC-026",
                "tsc": "CC7.1",
                "description": "Vulnerability identification and management",
                "type": "Detective",
                "frequency": "Weekly",
                "evidence": "Vulnerability scan reports, remediation SLAs, patch records",
            },
            {
                "id": "SEC-027",
                "tsc": "CC7.2",
                "description": "Monitoring for anomalies and security events",
                "type": "Detective",
                "frequency": "Continuous",
                "evidence": "SIEM configuration, alert rules, monitoring dashboards",
            },
            {
                "id": "SEC-028",
                "tsc": "CC7.3",
                "description": "Security event evaluation and incident classification",
                "type": "Detective",
                "frequency": "Continuous",
                "evidence": "Incident classification criteria, triage procedures, event logs",
            },
            {
                "id": "SEC-029",
                "tsc": "CC7.4",
                "description": "Incident response execution and recovery",
                "type": "Corrective",
                "frequency": "Continuous",
                "evidence": "Incident response plan, incident tickets, postmortem reports",
            },
            {
                "id": "SEC-030",
                "tsc": "CC7.5",
                "description": "Incident recovery and lessons learned",
                "type": "Corrective",
                "frequency": "Continuous",
                "evidence": "Recovery records, lessons learned documentation, plan updates",
            },
            {
                "id": "SEC-031",
                "tsc": "CC8.1",
                "description": "Change management authorization and testing",
                "type": "Preventive",
                "frequency": "Continuous",
                "evidence": "Change tickets, approval records, test results, deployment logs",
            },
            {
                "id": "SEC-032",
                "tsc": "CC9.1",
                "description": "Vendor and business partner risk management",
                "type": "Preventive",
                "frequency": "Annual",
                "evidence": "Vendor risk assessments, vendor register, SOC 2 reports from vendors",
            },
            {
                "id": "SEC-033",
                "tsc": "CC9.2",
                "description": "Risk mitigation through insurance and other transfer mechanisms",
                "type": "Preventive",
                "frequency": "Annual",
                "evidence": "Insurance policies, risk transfer documentation",
            },
        ],
    },
    "availability": {
        "name": "Availability",
        "controls": [
            {
                "id": "AVL-001",
                "tsc": "A1.1",
                "description": "Capacity management and infrastructure scaling",
                "type": "Preventive",
                "frequency": "Continuous",
                "evidence": "Capacity monitoring dashboards, scaling policies, resource utilization reports",
            },
            {
                "id": "AVL-002",
                "tsc": "A1.1",
                "description": "System performance monitoring and SLA tracking",
                "type": "Detective",
                "frequency": "Continuous",
                "evidence": "Uptime reports, SLA dashboards, performance metrics",
            },
            {
                "id": "AVL-003",
                "tsc": "A1.2",
                "description": "Data backup procedures and verification",
                "type": "Preventive",
                "frequency": "Daily",
                "evidence": "Backup logs, backup success/failure reports, retention configuration",
            },
            {
                "id": "AVL-004",
                "tsc": "A1.2",
                "description": "Disaster recovery planning and documentation",
                "type": "Preventive",
                "frequency": "Annual",
                "evidence": "DR plan, BCP documentation, recovery procedures",
            },
            {
                "id": "AVL-005",
                "tsc": "A1.2",
                "description": "Business continuity management and communication",
                "type": "Preventive",
                "frequency": "Annual",
                "evidence": "BCP plan, communication tree, emergency contacts",
            },
            {
                "id": "AVL-006",
                "tsc": "A1.3",
                "description": "Disaster recovery testing and validation",
                "type": "Detective",
                "frequency": "Annual",
                "evidence": "DR test results, RTO/RPO measurements, test reports",
            },
            {
                "id": "AVL-007",
                "tsc": "A1.3",
                "description": "Failover testing and redundancy validation",
                "type": "Detective",
                "frequency": "Quarterly",
                "evidence": "Failover test records, redundancy configuration, test results",
            },
        ],
    },
    "confidentiality": {
        "name": "Confidentiality",
        "controls": [
            {
                "id": "CON-001",
                "tsc": "C1.1",
                "description": "Data classification and labeling policy",
                "type": "Preventive",
                "frequency": "Annual",
                "evidence": "Data classification policy, labeling standards, data inventory",
            },
            {
                "id": "CON-002",
                "tsc": "C1.1",
                "description": "Confidential data inventory and mapping",
                "type": "Detective",
                "frequency": "Quarterly",
                "evidence": "Data inventory, data flow diagrams, system classification",
            },
            {
                "id": "CON-003",
                "tsc": "C1.2",
                "description": "Encryption of confidential data at rest and in transit",
                "type": "Preventive",
                "frequency": "Continuous",
                "evidence": "Encryption configuration, TLS settings, key management procedures",
            },
            {
                "id": "CON-004",
                "tsc": "C1.2",
                "description": "Access restrictions to confidential information",
                "type": "Preventive",
                "frequency": "Continuous",
                "evidence": "Access control lists, need-to-know policy, access review records",
            },
            {
                "id": "CON-005",
                "tsc": "C1.2",
                "description": "Data loss prevention controls",
                "type": "Detective",
                "frequency": "Continuous",
                "evidence": "DLP configuration, DLP alerts/incidents, exception approvals",
            },
            {
                "id": "CON-006",
                "tsc": "C1.3",
                "description": "Secure data disposal and media sanitization",
                "type": "Preventive",
                "frequency": "Continuous",
                "evidence": "Disposal procedures, sanitization certificates, destruction logs",
            },
            {
                "id": "CON-007",
                "tsc": "C1.3",
                "description": "Data retention enforcement and schedule compliance",
                "type": "Preventive",
                "frequency": "Quarterly",
                "evidence": "Retention schedule, deletion logs, retention compliance reports",
            },
        ],
    },
    "processing-integrity": {
        "name": "Processing Integrity",
        "controls": [
            {
                "id": "PRI-001",
                "tsc": "PI1.1",
                "description": "Input validation and data accuracy controls",
                "type": "Preventive",
                "frequency": "Continuous",
                "evidence": "Validation rules, input sanitization config, error handling logs",
            },
            {
                "id": "PRI-002",
                "tsc": "PI1.1",
                "description": "Output verification and data integrity checks",
                "type": "Detective",
                "frequency": "Continuous",
                "evidence": "Reconciliation reports, checksum verification, output validation logs",
            },
            {
                "id": "PRI-003",
                "tsc": "PI1.2",
                "description": "Transaction completeness monitoring",
                "type": "Detective",
                "frequency": "Continuous",
                "evidence": "Transaction logs, reconciliation reports, completeness dashboards",
            },
            {
                "id": "PRI-004",
                "tsc": "PI1.2",
                "description": "Error handling and exception management",
                "type": "Corrective",
                "frequency": "Continuous",
                "evidence": "Error logs, exception handling procedures, retry mechanisms",
            },
            {
                "id": "PRI-005",
                "tsc": "PI1.3",
                "description": "Processing timeliness and SLA monitoring",
                "type": "Detective",
                "frequency": "Continuous",
                "evidence": "SLA reports, processing time metrics, batch job monitoring",
            },
            {
                "id": "PRI-006",
                "tsc": "PI1.4",
                "description": "Processing authorization and segregation of duties",
                "type": "Preventive",
                "frequency": "Continuous",
                "evidence": "Authorization matrix, SoD controls, approval workflows",
            },
        ],
    },
    "privacy": {
        "name": "Privacy",
        "controls": [
            {
                "id": "PRV-001",
                "tsc": "P1.1",
                "description": "Privacy notice publication and data collection transparency",
                "type": "Preventive",
                "frequency": "Annual",
                "evidence": "Privacy policy, data collection notices, purpose statements",
            },
            {
                "id": "PRV-002",
                "tsc": "P2.1",
                "description": "Consent management and preference tracking",
                "type": "Preventive",
                "frequency": "Continuous",
                "evidence": "Consent records, opt-in/opt-out mechanisms, preference center",
            },
            {
                "id": "PRV-003",
                "tsc": "P3.1",
                "description": "Data minimization and lawful collection",
                "type": "Preventive",
                "frequency": "Continuous",
                "evidence": "Data collection audit, purpose limitation documentation, lawful basis records",
            },
            {
                "id": "PRV-004",
                "tsc": "P4.1",
                "description": "Purpose limitation and use restrictions",
                "type": "Preventive",
                "frequency": "Continuous",
                "evidence": "Data use policy, purpose limitation controls, access restrictions",
            },
            {
                "id": "PRV-005",
                "tsc": "P4.2",
                "description": "Data retention schedules and disposal procedures",
                "type": "Preventive",
                "frequency": "Quarterly",
                "evidence": "Retention schedule, deletion logs, disposal certificates",
            },
            {
                "id": "PRV-006",
                "tsc": "P5.1",
                "description": "Data subject access request (DSAR) processing",
                "type": "Corrective",
                "frequency": "Continuous",
                "evidence": "DSAR log, response records, processing timelines",
            },
            {
                "id": "PRV-007",
                "tsc": "P5.2",
                "description": "Data correction and rectification rights",
                "type": "Corrective",
                "frequency": "Continuous",
                "evidence": "Correction request records, data update logs",
            },
            {
                "id": "PRV-008",
                "tsc": "P6.1",
                "description": "Third-party data sharing controls and notifications",
                "type": "Preventive",
                "frequency": "Continuous",
                "evidence": "Data sharing agreements, third-party inventory, DPAs",
            },
            {
                "id": "PRV-009",
                "tsc": "P6.2",
                "description": "Breach notification procedures",
                "type": "Corrective",
                "frequency": "Continuous",
                "evidence": "Breach response plan, notification templates, incident records",
            },
            {
                "id": "PRV-010",
                "tsc": "P7.1",
                "description": "Data quality and accuracy verification",
                "type": "Detective",
                "frequency": "Quarterly",
                "evidence": "Data quality reports, accuracy checks, correction logs",
            },
            {
                "id": "PRV-011",
                "tsc": "P8.1",
                "description": "Privacy program monitoring and compliance reviews",
                "type": "Detective",
                "frequency": "Quarterly",
                "evidence": "Privacy audits, compliance dashboards, complaint tracking",
            },
        ],
    },
}

VALID_CATEGORIES = list(TSC_CONTROLS.keys())


def build_matrix(categories: List[str]) -> List[Dict[str, str]]:
    """Build a control matrix for the selected TSC categories."""
    matrix = []
    for cat in categories:
        if cat not in TSC_CONTROLS:
            continue
        cat_data = TSC_CONTROLS[cat]
        for ctrl in cat_data["controls"]:
            matrix.append(
                {
                    "control_id": ctrl["id"],
                    "tsc_criteria": ctrl["tsc"],
                    "category": cat_data["name"],
                    "description": ctrl["description"],
                    "control_type": ctrl["type"],
                    "frequency": ctrl["frequency"],
                    "evidence_required": ctrl["evidence"],
                    "owner": "TBD",
                    "status": "Not Started",
                }
            )
    return matrix


def format_markdown(matrix: List[Dict[str, str]]) -> str:
    """Format control matrix as markdown table."""
    lines = ["# SOC 2 Control Matrix", ""]
    lines.append(
        "| Control ID | TSC | Category | Description | Type | Frequency | Evidence | Owner | Status |"
    )
    lines.append(
        "|------------|-----|----------|-------------|------|-----------|----------|-------|--------|"
    )
    for row in matrix:
        lines.append(
            "| {control_id} | {tsc_criteria} | {category} | {description} | {control_type} | {frequency} | {evidence_required} | {owner} | {status} |".format(
                **row
            )
        )
    lines.append("")
    lines.append(f"**Total Controls:** {len(matrix)}")
    return "\n".join(lines)


def format_csv(matrix: List[Dict[str, str]]) -> str:
    """Format control matrix as CSV."""
    output = io.StringIO()
    if not matrix:
        return ""
    writer = csv.DictWriter(output, fieldnames=matrix[0].keys())
    writer.writeheader()
    writer.writerows(matrix)
    return output.getvalue()


def format_json(matrix: List[Dict[str, str]]) -> str:
    """Format control matrix as JSON."""
    return json.dumps({"controls": matrix, "total": len(matrix)}, indent=2)


def main():
    parser = argparse.ArgumentParser(
        description="SOC 2 Control Matrix Builder — generates control matrices from selected Trust Service Criteria categories."
    )
    parser.add_argument(
        "--categories",
        type=str,
        required=True,
        help=f"Comma-separated TSC categories: {','.join(VALID_CATEGORIES)}",
    )
    parser.add_argument(
        "--format",
        type=str,
        choices=["md", "json", "csv"],
        default="md",
        help="Output format (default: md)",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Shorthand for --format json",
    )

    args = parser.parse_args()

    # Parse categories
    categories = [c.strip().lower() for c in args.categories.split(",")]
    invalid = [c for c in categories if c not in VALID_CATEGORIES]
    if invalid:
        print(
            f"Error: Invalid categories: {', '.join(invalid)}. Valid options: {', '.join(VALID_CATEGORIES)}",
            file=sys.stderr,
        )
        sys.exit(1)

    # Build matrix
    matrix = build_matrix(categories)

    if not matrix:
        print("No controls found for the selected categories.", file=sys.stderr)
        sys.exit(1)

    # Output
    fmt = "json" if args.json else args.format
    if fmt == "md":
        print(format_markdown(matrix))
    elif fmt == "json":
        print(format_json(matrix))
    elif fmt == "csv":
        print(format_csv(matrix))


if __name__ == "__main__":
    main()
