#!/usr/bin/env python3
"""
CISO Compliance Tracker
========================
Tracks compliance requirements across SOC 2, ISO 27001, HIPAA, and GDPR.
Shows control overlaps, estimates effort and cost, and prioritizes by business value.

Usage:
  python compliance_tracker.py                    # Run with sample data
  python compliance_tracker.py --json             # JSON output
  python compliance_tracker.py --csv output.csv   # Export CSV
  python compliance_tracker.py --framework soc2   # Show single framework
  python compliance_tracker.py --gap-analysis     # Show unaddressed requirements
  python compliance_tracker.py --roadmap          # Show sequenced roadmap
"""

import json
import csv
import sys
import argparse
from datetime import datetime, date
from typing import Optional


# ─── Framework Definitions ───────────────────────────────────────────────────

FRAMEWORKS = {
    "soc2": {
        "name": "SOC 2 Type II",
        "full_name": "AICPA Trust Service Criteria — Security",
        "typical_timeline_months": 12,
        "typical_cost_usd": 65_000,    # Audit + platform
        "annual_maintenance_usd": 40_000,
        "business_value": "Enterprise sales unblock, US market table stakes",
        "mandatory_for": ["B2B SaaS selling to enterprise US companies"],
    },
    "iso27001": {
        "name": "ISO 27001:2022",
        "full_name": "Information Security Management System",
        "typical_timeline_months": 15,
        "typical_cost_usd": 95_000,
        "annual_maintenance_usd": 30_000,
        "business_value": "EU enterprise sales, global credibility",
        "mandatory_for": ["EU enterprise customers", "Government contracts"],
    },
    "hipaa": {
        "name": "HIPAA",
        "full_name": "Health Insurance Portability and Accountability Act",
        "typical_timeline_months": 7,
        "typical_cost_usd": 75_000,
        "annual_maintenance_usd": 20_000,
        "business_value": "Healthcare customer access, BAA execution",
        "mandatory_for": ["Business Associates", "Companies handling PHI"],
    },
    "gdpr": {
        "name": "GDPR",
        "full_name": "General Data Protection Regulation (EU) 2016/679",
        "typical_timeline_months": 5,
        "typical_cost_usd": 45_000,
        "annual_maintenance_usd": 15_000,
        "business_value": "EU market access, legal compliance",
        "mandatory_for": ["EU-based companies", "Any company with EU user data"],
    },
}


# ─── Control Domain Library ──────────────────────────────────────────────────

def build_control_domain(
    domain_id: str,
    name: str,
    description: str,
    soc2_ref: Optional[str],
    iso27001_ref: Optional[str],
    hipaa_ref: Optional[str],
    gdpr_ref: Optional[str],
    effort_days: int,              # Estimated implementation effort in person-days
    cost_usd: int,                 # Estimated implementation cost (tooling + time)
    implementation_notes: str,
    status: str = "Not Started",   # Not Started | In Progress | Implemented | Verified
    owner: Optional[str] = None,
    target_date: Optional[str] = None,
) -> dict:
    """Build a control domain record."""
    frameworks_applicable = []
    if soc2_ref:
        frameworks_applicable.append("soc2")
    if iso27001_ref:
        frameworks_applicable.append("iso27001")
    if hipaa_ref:
        frameworks_applicable.append("hipaa")
    if gdpr_ref:
        frameworks_applicable.append("gdpr")

    return {
        "domain_id": domain_id,
        "name": name,
        "description": description,
        "references": {
            "soc2": soc2_ref,
            "iso27001": iso27001_ref,
            "hipaa": hipaa_ref,
            "gdpr": gdpr_ref,
        },
        "frameworks_applicable": frameworks_applicable,
        "framework_count": len(frameworks_applicable),
        "effort_days": effort_days,
        "cost_usd": cost_usd,
        "implementation_notes": implementation_notes,
        "status": status,
        "owner": owner,
        "target_date": target_date,
    }


def load_control_library() -> list[dict]:
    """
    Core control domains mapped across SOC 2, ISO 27001, HIPAA, and GDPR.
    Each domain represents a logical grouping of controls.
    """
    controls = []

    controls.append(build_control_domain(
        domain_id="IAM-001",
        name="Identity and Access Management",
        description=(
            "Unique user identities, MFA enforcement, SSO, least privilege access, "
            "role-based access control, access provisioning and de-provisioning workflows."
        ),
        soc2_ref="CC6.1, CC6.2, CC6.3",
        iso27001_ref="A.5.15, A.5.16, A.5.17, A.5.18",
        hipaa_ref="§164.312(a)(2)(i), §164.308(a)(3)",
        gdpr_ref="Art. 32(1)(b)",
        effort_days=15,
        cost_usd=25_000,  # SSO + MFA tooling
        implementation_notes=(
            "Deploy IdP (Okta/Azure AD/Google Workspace). Enforce MFA on all applications. "
            "Document access provisioning process. Implement quarterly access reviews."
        ),
        status="In Progress",
        owner="IT/Security",
    ))

    controls.append(build_control_domain(
        domain_id="ENC-001",
        name="Encryption at Rest and in Transit",
        description=(
            "Encryption of sensitive data stored in databases, file systems, and backups. "
            "TLS 1.2+ for all data in transit. Key management and rotation."
        ),
        soc2_ref="CC6.7",
        iso27001_ref="A.8.24",
        hipaa_ref="§164.312(a)(2)(iv), §164.312(e)(2)(ii)",
        gdpr_ref="Art. 32(1)(a)",
        effort_days=10,
        cost_usd=8_000,
        implementation_notes=(
            "Enable encryption at rest on all databases (RDS, S3, etc.). "
            "Configure TLS on all services. Use KMS for key management. "
            "Document encryption standards in a security policy."
        ),
        status="Implemented",
        owner="Engineering",
    ))

    controls.append(build_control_domain(
        domain_id="LOG-001",
        name="Audit Logging and Monitoring",
        description=(
            "Comprehensive logging of user activity, system events, and security events. "
            "Log integrity protection. SIEM or log aggregation. Alerting on anomalies."
        ),
        soc2_ref="CC7.2, CC7.3",
        iso27001_ref="A.8.15, A.8.16, A.8.17",
        hipaa_ref="§164.312(b)",
        gdpr_ref="Art. 32(1)(b)",
        effort_days=20,
        cost_usd=30_000,  # SIEM tooling
        implementation_notes=(
            "Centralize logs from application, infrastructure, and cloud provider. "
            "Define log retention (minimum 1 year). Set up alerting for authentication "
            "failures, privilege escalation, data export events."
        ),
        status="Not Started",
        owner="DevOps/Security",
    ))

    controls.append(build_control_domain(
        domain_id="IR-001",
        name="Incident Response",
        description=(
            "Documented incident response plan. Defined severity levels. Escalation procedures. "
            "Communication templates. Annual tabletop exercise. Post-incident review process."
        ),
        soc2_ref="CC7.3, CC7.4, CC7.5",
        iso27001_ref="A.5.24, A.5.25, A.5.26, A.5.27, A.5.28",
        hipaa_ref="§164.308(a)(6)",
        gdpr_ref="Art. 33, Art. 34",
        effort_days=12,
        cost_usd=10_000,
        implementation_notes=(
            "Write IR plan covering detection, containment, eradication, recovery, communication. "
            "Define breach notification timelines (GDPR: 72 hours, HIPAA: 60 days). "
            "Run annual tabletop exercise. Retain IR firm on retainer."
        ),
        status="In Progress",
        owner="CISO",
    ))

    controls.append(build_control_domain(
        domain_id="VM-001",
        name="Vulnerability Management and Patching",
        description=(
            "Regular vulnerability scanning of infrastructure and applications. "
            "Defined patch SLAs by severity. Penetration testing program. "
            "Dependency vulnerability scanning in CI/CD."
        ),
        soc2_ref="CC7.1",
        iso27001_ref="A.8.8",
        hipaa_ref="§164.308(a)(1)(ii)(A)",
        gdpr_ref="Art. 32(1)(d)",
        effort_days=15,
        cost_usd=20_000,
        implementation_notes=(
            "Deploy infrastructure scanner (Tenable, Qualys, AWS Inspector). "
            "Add SAST/DAST to CI/CD pipeline. Define patch SLAs: Critical <24h, High <7d, "
            "Medium <30d. Conduct annual pentest."
        ),
        status="In Progress",
        owner="DevOps/Security",
    ))

    controls.append(build_control_domain(
        domain_id="VRISK-001",
        name="Vendor and Third-Party Risk Management",
        description=(
            "Inventory of all third-party vendors with data access. Tiered risk assessment "
            "process. Contractual security requirements. Annual reviews for critical vendors."
        ),
        soc2_ref="CC9.2",
        iso27001_ref="A.5.19, A.5.20, A.5.21, A.5.22",
        hipaa_ref="§164.308(b) Business Associate Agreements",
        gdpr_ref="Art. 28 Data Processing Agreements",
        effort_days=10,
        cost_usd=8_000,
        implementation_notes=(
            "Build vendor inventory spreadsheet. Tier vendors (Tier 1: PII access, "
            "Tier 2: business data, Tier 3: no data). Execute DPAs for all processors (GDPR). "
            "Execute BAAs for PHI processors (HIPAA). Annual security questionnaire for Tier 1."
        ),
        status="Not Started",
        owner="Legal/Security",
    ))

    controls.append(build_control_domain(
        domain_id="RISK-001",
        name="Risk Assessment and Treatment",
        description=(
            "Formal risk assessment methodology. Risk register maintained. "
            "Risk treatment decisions documented. Annual risk review cycle."
        ),
        soc2_ref="CC3.1, CC3.2, CC3.3, CC3.4",
        iso27001_ref="Clause 6.1.2, 6.1.3",
        hipaa_ref="§164.308(a)(1) Security Risk Analysis",
        gdpr_ref="Art. 32, Art. 35 DPIA",
        effort_days=15,
        cost_usd=12_000,
        implementation_notes=(
            "Document risk methodology (FAIR, NIST, ISO 27005). Maintain risk register. "
            "HIPAA: formal security risk analysis required — not optional. "
            "GDPR: DPIA required for high-risk processing activities. Annual refresh."
        ),
        status="Not Started",
        owner="CISO",
    ))

    controls.append(build_control_domain(
        domain_id="TRAIN-001",
        name="Security Awareness Training",
        description=(
            "Annual security awareness training for all employees. "
            "Role-specific training for high-risk roles. Phishing simulations. "
            "Training completion tracking."
        ),
        soc2_ref="CC1.4",
        iso27001_ref="A.6.3, A.6.8",
        hipaa_ref="§164.308(a)(5)",
        gdpr_ref="Art. 39(1)(b)",
        effort_days=5,
        cost_usd=8_000,
        implementation_notes=(
            "Deploy security training platform (KnowBe4, Proofpoint, etc.). "
            "Annual training required — track completion (100% target). "
            "Quarterly phishing simulations. Role-specific training for devs (secure coding), "
            "finance (BEC), support (social engineering)."
        ),
        status="Not Started",
        owner="HR/Security",
    ))

    controls.append(build_control_domain(
        domain_id="CHGMGMT-001",
        name="Change Management",
        description=(
            "Formal change management process for production changes. "
            "Code review requirements. Deployment approvals. Rollback procedures. "
            "Change log maintained."
        ),
        soc2_ref="CC8.1",
        iso27001_ref="A.8.32",
        hipaa_ref="§164.312(c)(1) Integrity controls",
        gdpr_ref="Art. 25 Privacy by design",
        effort_days=10,
        cost_usd=5_000,
        implementation_notes=(
            "Document change management policy. Require peer review for all production changes. "
            "Maintain audit trail in version control. No direct production access — "
            "all changes via CI/CD pipeline."
        ),
        status="In Progress",
        owner="Engineering",
    ))

    controls.append(build_control_domain(
        domain_id="BCP-001",
        name="Business Continuity and Disaster Recovery",
        description=(
            "Business continuity plan. Disaster recovery plan with defined RTO/RPO. "
            "Backup procedures with tested restores. Failover capabilities."
        ),
        soc2_ref="A1.1, A1.2, A1.3",
        iso27001_ref="A.5.29, A.5.30",
        hipaa_ref="§164.308(a)(7) Contingency Plan",
        gdpr_ref="Art. 32(1)(c)",
        effort_days=12,
        cost_usd=15_000,
        implementation_notes=(
            "Define RTO (<4 hours) and RPO (<1 hour) targets. Configure automated backups. "
            "Test restore quarterly — paper backups that aren't tested aren't backups. "
            "Document DR runbook. Annual DR exercise."
        ),
        status="In Progress",
        owner="DevOps",
    ))

    controls.append(build_control_domain(
        domain_id="ASSET-001",
        name="Asset Inventory and Classification",
        description=(
            "Complete inventory of hardware, software, and data assets. "
            "Data classification scheme. Ownership assigned to all assets. "
            "Regular reconciliation."
        ),
        soc2_ref="CC6.1",
        iso27001_ref="A.5.9, A.5.10, A.5.11, A.5.12, A.5.13",
        hipaa_ref="§164.310(d) Device and Media Controls",
        gdpr_ref="Art. 30 Records of Processing Activities",
        effort_days=8,
        cost_usd=5_000,
        implementation_notes=(
            "Build asset register (CMDB or spreadsheet at minimum). "
            "Classify data: Public, Internal, Confidential, Restricted. "
            "GDPR requires RoPA (Record of Processing Activities) — data map of all PII. "
            "ISO 27001 requires SoA referencing asset inventory."
        ),
        status="Not Started",
        owner="IT/Security",
    ))

    controls.append(build_control_domain(
        domain_id="ENDPOINT-001",
        name="Endpoint Security",
        description=(
            "EDR/antivirus on all managed endpoints. Device management (MDM). "
            "Full disk encryption. Patch management. BYOD policy."
        ),
        soc2_ref="CC6.8",
        iso27001_ref="A.8.1, A.8.7",
        hipaa_ref="§164.310(a)(2)(iv) Workstation security",
        gdpr_ref="Art. 32(1)(a)",
        effort_days=8,
        cost_usd=20_000,
        implementation_notes=(
            "Deploy EDR (CrowdStrike, SentinelOne, or Microsoft Defender for Business). "
            "Enable full disk encryption (FileVault/BitLocker). "
            "MDM for device management. BYOD policy documented."
        ),
        status="In Progress",
        owner="IT",
    ))

    controls.append(build_control_domain(
        domain_id="POLICY-001",
        name="Security Policies and Procedures",
        description=(
            "Documented security policies covering acceptable use, access control, "
            "incident response, data classification, vendor management, etc. "
            "Annual review cycle. Employee attestation."
        ),
        soc2_ref="CC1.2, CC1.3",
        iso27001_ref="A.5.1, A.5.2",
        hipaa_ref="§164.308(a)(1) Security Management Process",
        gdpr_ref="Art. 24 Responsibility of the controller",
        effort_days=15,
        cost_usd=10_000,
        implementation_notes=(
            "Minimum policy set: Information Security Policy, Acceptable Use, "
            "Access Control, Incident Response, Data Classification, Password, "
            "Change Management, Vendor Management, Business Continuity. "
            "Use policy templates from GRC platform (Vanta/Drata)."
        ),
        status="In Progress",
        owner="CISO",
    ))

    controls.append(build_control_domain(
        domain_id="PRIV-001",
        name="Privacy and Data Subject Rights",
        description=(
            "Privacy policy and notices. Data subject rights fulfilment process "
            "(access, erasure, portability). Consent management. Cookie compliance. "
            "Privacy by design in product development."
        ),
        soc2_ref=None,  # Not a SOC 2 requirement (unless Privacy TSC selected)
        iso27001_ref="A.5.34",
        hipaa_ref="§164.524 Access, §164.528 Accounting of Disclosures",
        gdpr_ref="Art. 13, 14, 15–22 (Rights), Art. 25",
        effort_days=20,
        cost_usd=15_000,
        implementation_notes=(
            "GDPR: Update privacy policy, implement DSAR process (30-day SLA), "
            "build deletion capability into product. Cookie consent (PECR/ePrivacy). "
            "HIPAA: Patient rights for PHI access. "
            "Consider OneTrust, Termly, or CookieYes for consent management."
        ),
        status="Not Started",
        owner="Legal/Product",
    ))

    controls.append(build_control_domain(
        domain_id="NET-001",
        name="Network Security and Segmentation",
        description=(
            "Network segmentation (production vs. development vs. corporate). "
            "Firewall rules. Intrusion detection. VPN or ZTNA for remote access."
        ),
        soc2_ref="CC6.6, CC6.7",
        iso27001_ref="A.8.20, A.8.21, A.8.22",
        hipaa_ref="§164.312(e)(1) Transmission security",
        gdpr_ref="Art. 32(1)(a)",
        effort_days=12,
        cost_usd=18_000,
        implementation_notes=(
            "Segment production from development. WAF in front of public applications. "
            "Replace VPN with ZTNA for remote access (Series B+ consideration). "
            "DDoS protection (Cloudflare or AWS Shield)."
        ),
        status="In Progress",
        owner="DevOps",
    ))

    controls.append(build_control_domain(
        domain_id="PENTEST-001",
        name="Penetration Testing",
        description=(
            "Annual external penetration test by qualified third-party firm. "
            "Finding remediation tracking. Results reviewed by leadership."
        ),
        soc2_ref="CC7.1",
        iso27001_ref="A.8.8",
        hipaa_ref="§164.308(a)(8) Evaluation",
        gdpr_ref="Art. 32(1)(d)",
        effort_days=5,
        cost_usd=25_000,
        implementation_notes=(
            "Scope: external attack surface, application, API, and optionally social engineering. "
            "Budget $15–35K for a reputable firm. Track findings in risk register. "
            "Re-test critical findings within 90 days. Share pentest summary with enterprise "
            "customers on request (under NDA)."
        ),
        status="Not Started",
        owner="CISO",
    ))

    return controls


# ─── Analysis ────────────────────────────────────────────────────────────────

def calculate_framework_coverage(controls: list[dict]) -> dict:
    """Calculate per-framework coverage statistics."""
    coverage = {}
    for fw in FRAMEWORKS:
        applicable = [c for c in controls if fw in c["frameworks_applicable"]]
        implemented = [c for c in applicable if c["status"] in ("Implemented", "Verified")]
        in_progress = [c for c in applicable if c["status"] == "In Progress"]
        not_started = [c for c in applicable if c["status"] == "Not Started"]

        total_effort = sum(c["effort_days"] for c in applicable)
        remaining_effort = sum(
            c["effort_days"] for c in applicable
            if c["status"] not in ("Implemented", "Verified")
        )
        total_cost = sum(c["cost_usd"] for c in applicable)
        remaining_cost = sum(
            c["cost_usd"] for c in applicable
            if c["status"] not in ("Implemented", "Verified")
        )

        pct_complete = (len(implemented) / len(applicable) * 100) if applicable else 0

        coverage[fw] = {
            "framework": FRAMEWORKS[fw]["name"],
            "total_controls": len(applicable),
            "implemented": len(implemented),
            "in_progress": len(in_progress),
            "not_started": len(not_started),
            "pct_complete": pct_complete,
            "total_effort_days": total_effort,
            "remaining_effort_days": remaining_effort,
            "total_cost_usd": total_cost,
            "remaining_cost_usd": remaining_cost,
            "gap_controls": [c["name"] for c in not_started],
        }

    return coverage


def find_high_leverage_controls(controls: list[dict]) -> list[dict]:
    """Controls that satisfy the most frameworks — highest ROI to implement."""
    multi_fw = [c for c in controls if c["framework_count"] >= 3
                and c["status"] not in ("Implemented", "Verified")]
    return sorted(multi_fw, key=lambda c: (-c["framework_count"], c["effort_days"]))


def estimate_roadmap(controls: list[dict], target_frameworks: list[str]) -> list[dict]:
    """
    Generate an ordered implementation roadmap for target frameworks.
    Prioritize: (1) controls blocking most frameworks, (2) quick wins (low effort).
    """
    applicable = [c for c in controls
                  if any(fw in c["frameworks_applicable"] for fw in target_frameworks)
                  and c["status"] not in ("Implemented", "Verified")]

    # Score: (frameworks_covered × 10) - (effort_days) → higher is better
    for c in applicable:
        fw_overlap = len([fw for fw in target_frameworks if fw in c["frameworks_applicable"]])
        c["_priority_score"] = (fw_overlap * 10) - c["effort_days"]

    return sorted(applicable, key=lambda c: -c["_priority_score"])


def fmt_dollars(amount: float) -> str:
    if amount >= 1_000_000:
        return f"${amount/1_000_000:.1f}M"
    if amount >= 1_000:
        return f"${amount/1_000:.0f}K"
    return f"${amount:.0f}"


def status_icon(status: str) -> str:
    icons = {
        "Implemented": "✅",
        "Verified": "✅",
        "In Progress": "🔄",
        "Not Started": "⬜",
        "Planned": "📋",
    }
    return icons.get(status, "❓")


# ─── Display ─────────────────────────────────────────────────────────────────

def print_header():
    print("\n" + "=" * 80)
    print("  CISO COMPLIANCE TRACKER — Multi-Framework Coverage")
    print(f"  Generated: {datetime.now().strftime('%Y-%m-%d %H:%M')}")
    print("=" * 80)


def print_framework_summary(coverage: dict):
    print("\n📋 FRAMEWORK COVERAGE SUMMARY")
    print("-" * 80)
    header = f"{'Framework':<20} {'Done':<6} {'WIP':<5} {'Gap':<5} {'Complete':<10} {'Remain Cost':<14} {'Remain Days'}"
    print(header)
    print("-" * 80)
    for fw_id, data in coverage.items():
        pct = f"{data['pct_complete']:.0f}%"
        print(
            f"{data['framework']:<20} {data['implemented']:<6} {data['in_progress']:<5} "
            f"{data['not_started']:<5} {pct:<10} {fmt_dollars(data['remaining_cost_usd']):<14} "
            f"{data['remaining_effort_days']} days"
        )


def print_control_table(controls: list[dict], framework_filter: Optional[str] = None):
    filtered = controls
    if framework_filter:
        filtered = [c for c in controls if framework_filter in c["frameworks_applicable"]]

    title = f"CONTROL DOMAINS"
    if framework_filter:
        title += f" — {FRAMEWORKS[framework_filter]['name']}"

    print(f"\n🔧 {title}")
    print("-" * 90)
    header = f"{'ID':<14} {'Control Name':<30} {'Frameworks':<8} {'Effort':<8} {'Cost':<10} {'Status'}"
    print(header)
    print("-" * 90)

    for c in filtered:
        fw_badges = "/".join(
            fw.upper()[:3] for fw in ["soc2", "iso27001", "hipaa", "gdpr"]
            if fw in c["frameworks_applicable"]
        )
        icon = status_icon(c["status"])
        print(
            f"{c['domain_id']:<14} {c['name'][:29]:<30} {fw_badges:<8} "
            f"{c['effort_days']:>3}d    {fmt_dollars(c['cost_usd']):<10} {icon} {c['status']}"
        )


def print_gap_analysis(coverage: dict):
    print("\n⚠️  GAP ANALYSIS — Controls Not Yet Started")
    print("-" * 70)
    for fw_id, data in coverage.items():
        if data["gap_controls"]:
            print(f"\n  {data['framework']} — {len(data['gap_controls'])} gaps:")
            for gap in data["gap_controls"]:
                print(f"    • {gap}")


def print_high_leverage(controls: list[dict]):
    hl = find_high_leverage_controls(controls)
    print(f"\n🎯 HIGH-LEVERAGE CONTROLS — Implement Once, Satisfy Multiple Frameworks")
    print("-" * 70)
    print(f"{'Control':<30} {'Frameworks':<35} {'Effort':<8} {'Cost'}")
    print("-" * 70)
    for c in hl:
        fw_list = " + ".join(FRAMEWORKS[fw]["name"] for fw in c["frameworks_applicable"])
        print(
            f"{c['name'][:29]:<30} {fw_list[:34]:<35} "
            f"{c['effort_days']:>3}d    {fmt_dollars(c['cost_usd'])}"
        )


def print_roadmap(controls: list[dict], target_frameworks: list[str]):
    ordered = estimate_roadmap(controls, target_frameworks)
    fw_names = " + ".join(FRAMEWORKS[fw]["name"] for fw in target_frameworks)
    print(f"\n🗺️  IMPLEMENTATION ROADMAP — {fw_names}")
    print("-" * 80)
    print("Priority order: most framework coverage first, then quick wins")
    print()

    cumulative_days = 0
    cumulative_cost = 0
    for i, c in enumerate(ordered, 1):
        cumulative_days += c["effort_days"]
        cumulative_cost += c["cost_usd"]
        fw_badges = ", ".join(
            FRAMEWORKS[fw]["name"] for fw in target_frameworks
            if fw in c["frameworks_applicable"]
        )
        print(f"  {i:>2}. {c['name']}")
        print(f"      Frameworks: {fw_badges}")
        print(f"      Effort: {c['effort_days']} days | Cost: {fmt_dollars(c['cost_usd'])} "
              f"| Cumulative: {cumulative_days}d / {fmt_dollars(cumulative_cost)}")
        if c.get("owner"):
            print(f"      Owner: {c['owner']}")
        print()


def print_framework_profiles():
    print("\n💼 FRAMEWORK PROFILES")
    print("-" * 70)
    for fw_id, fw in FRAMEWORKS.items():
        print(f"\n  {fw['name']} ({fw_id.upper()})")
        print(f"  Timeline:     ~{fw['typical_timeline_months']} months")
        print(f"  First-year cost: {fmt_dollars(fw['typical_cost_usd'])}")
        print(f"  Annual maintenance: {fmt_dollars(fw['annual_maintenance_usd'])}/yr")
        print(f"  Business value: {fw['business_value']}")
        print(f"  Required for:  {', '.join(fw['mandatory_for'])}")


def export_csv(controls: list[dict], filepath: str):
    fields = [
        "domain_id", "name", "frameworks_applicable", "framework_count",
        "effort_days", "cost_usd", "status", "owner", "target_date",
        "soc2_ref", "iso27001_ref", "hipaa_ref", "gdpr_ref", "implementation_notes"
    ]
    with open(filepath, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fields)
        writer.writeheader()
        for c in controls:
            row = {k: c.get(k, "") for k in fields}
            row["frameworks_applicable"] = ", ".join(c["frameworks_applicable"])
            row["soc2_ref"] = c["references"].get("soc2", "")
            row["iso27001_ref"] = c["references"].get("iso27001", "")
            row["hipaa_ref"] = c["references"].get("hipaa", "")
            row["gdpr_ref"] = c["references"].get("gdpr", "")
            writer.writerow(row)
    print(f"✅ Exported {len(controls)} controls to {filepath}")


# ─── Main ────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="CISO Compliance Tracker — Multi-framework coverage and roadmap"
    )
    parser.add_argument("--json", action="store_true", help="Output JSON")
    parser.add_argument("--csv", metavar="FILE", help="Export CSV to file")
    parser.add_argument(
        "--framework", metavar="FRAMEWORK",
        choices=list(FRAMEWORKS.keys()),
        help="Filter to single framework (soc2, iso27001, hipaa, gdpr)"
    )
    parser.add_argument("--gap-analysis", action="store_true", help="Show gap analysis")
    parser.add_argument("--roadmap", metavar="FRAMEWORKS",
                        help="Sequenced roadmap for frameworks e.g. 'soc2,iso27001'")
    parser.add_argument("--profiles", action="store_true", help="Show framework profiles")
    parser.add_argument("--leverage", action="store_true", help="Show high-leverage controls")
    args = parser.parse_args()

    controls = load_control_library()
    coverage = calculate_framework_coverage(controls)

    if args.json:
        output = {
            "generated": datetime.now().isoformat(),
            "frameworks": FRAMEWORKS,
            "coverage": coverage,
            "controls": controls,
        }
        print(json.dumps(output, indent=2, default=str))
        return

    if args.csv:
        export_csv(controls, args.csv)
        return

    print_header()

    if args.profiles:
        print_framework_profiles()
        return

    if args.roadmap:
        target_fws = [fw.strip() for fw in args.roadmap.split(",") if fw.strip() in FRAMEWORKS]
        if not target_fws:
            print(f"Unknown frameworks. Valid: {', '.join(FRAMEWORKS.keys())}")
            sys.exit(1)
        print_framework_summary(coverage)
        print_roadmap(controls, target_fws)
        return

    print_framework_summary(coverage)
    print_control_table(controls, args.framework)

    if args.gap_analysis:
        print_gap_analysis(coverage)

    if args.leverage:
        print_high_leverage(controls)

    if not any([args.framework, args.gap_analysis, args.leverage]):
        print_high_leverage(controls)
        print_gap_analysis(coverage)

    print("\n💡 NEXT STEPS")
    print("  --roadmap soc2,iso27001     Priority order for dual-framework")
    print("  --framework hipaa           HIPAA-only control view")
    print("  --gap-analysis              What's not started")
    print("  --leverage                  Controls covering most frameworks")
    print("  --profiles                  Framework timelines and costs")
    print("  --csv controls.csv          Export for stakeholder review")
    print()


if __name__ == "__main__":
    main()
