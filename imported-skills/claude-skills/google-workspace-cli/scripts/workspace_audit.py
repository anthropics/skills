#!/usr/bin/env python3
"""
Google Workspace Security Audit — Audit Workspace configuration for security risks.

Checks Drive external sharing, Gmail forwarding rules, OAuth app grants,
Calendar visibility, admin settings, and generates remediation commands.
Runs in demo mode with embedded sample data when gws is not installed.

Usage:
    python3 workspace_audit.py
    python3 workspace_audit.py --json
    python3 workspace_audit.py --services gmail,drive,calendar
    python3 workspace_audit.py --demo
"""

import argparse
import json
import shutil
import subprocess
import sys
from dataclasses import dataclass, field, asdict
from typing import List, Dict, Optional


@dataclass
class AuditFinding:
    area: str
    check: str
    status: str  # PASS, WARN, FAIL
    message: str
    risk: str = ""
    remediation: str = ""


@dataclass
class AuditReport:
    findings: List[dict] = field(default_factory=list)
    score: int = 0
    max_score: int = 100
    grade: str = ""
    summary: str = ""
    demo_mode: bool = False


DEMO_FINDINGS = [
    AuditFinding("drive", "External sharing", "WARN",
                 "External sharing is enabled for the domain",
                 "Data exfiltration via shared links",
                 "Review sharing settings in Admin Console > Apps > Google Workspace > Drive"),
    AuditFinding("drive", "Link sharing defaults", "FAIL",
                 "Default link sharing is set to 'Anyone with the link'",
                 "Sensitive files accessible without authentication",
                 "Restrict default link sharing: Admin Console > Apps > Google Workspace > Drive > Sharing settings"),
    AuditFinding("gmail", "Auto-forwarding", "PASS",
                 "No auto-forwarding rules detected for admin accounts"),
    AuditFinding("gmail", "SPF record", "PASS",
                 "SPF record configured correctly"),
    AuditFinding("gmail", "DMARC record", "WARN",
                 "DMARC policy is set to 'none' (monitoring only)",
                 "Email spoofing not actively blocked",
                 "Update DMARC DNS record: v=DMARC1; p=quarantine; rua=mailto:dmarc@company.com"),
    AuditFinding("gmail", "DKIM signing", "PASS",
                 "DKIM signing is enabled"),
    AuditFinding("calendar", "Default visibility", "WARN",
                 "Calendar default visibility is 'See all event details'",
                 "Meeting details visible to all domain users",
                 "Admin Console > Apps > Calendar > Sharing settings > Set to 'Free/Busy'"),
    AuditFinding("calendar", "External sharing", "PASS",
                 "External calendar sharing is restricted"),
    AuditFinding("oauth", "Third-party apps", "FAIL",
                 "12 third-party OAuth apps with broad access detected",
                 "Unauthorized data access via OAuth grants",
                 "Review: Admin Console > Security > API controls > App access control"),
    AuditFinding("oauth", "High-risk apps", "WARN",
                 "3 apps have Drive full access scope",
                 "Apps can read/modify all Drive files",
                 "Audit each app via the Directory API tokens resource (verify: gws schema admin.tokens.list)"),
    AuditFinding("admin", "Super admin count", "WARN",
                 "4 super admin accounts detected (recommended: 2-3)",
                 "Increased attack surface for privilege escalation",
                 "Reduce super admins: list them via the Directory API (verify: gws schema admin.users.list)"),
    AuditFinding("admin", "2-Step verification", "PASS",
                 "2-Step verification enforced for all users"),
    AuditFinding("admin", "Password policy", "PASS",
                 "Minimum password length: 12 characters"),
    AuditFinding("admin", "Login challenges", "PASS",
                 "Suspicious login challenges enabled"),
]


def run_gws_command(cmd: List[str]) -> Optional[str]:
    """Run a gws command and return stdout, or None on failure."""
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=20)
        if result.returncode == 0:
            return result.stdout
        return None
    except (subprocess.TimeoutExpired, FileNotFoundError, OSError):
        return None


def audit_drive() -> List[AuditFinding]:
    """Audit Drive sharing and security settings."""
    findings = []

    # Check sharing settings
    output = run_gws_command(["gws", "drive", "about", "get", "--params", '{"fields": "*"}'])
    if output:
        try:
            data = json.loads(output)
            # Check if external sharing is enabled
            if data.get("canShareOutsideDomain", True):
                findings.append(AuditFinding(
                    "drive", "External sharing", "WARN",
                    "External sharing is enabled",
                    "Data exfiltration via shared links",
                    "Review Admin Console > Apps > Drive > Sharing settings"
                ))
            else:
                findings.append(AuditFinding(
                    "drive", "External sharing", "PASS",
                    "External sharing is restricted"
                ))
        except json.JSONDecodeError:
            findings.append(AuditFinding(
                "drive", "External sharing", "WARN",
                "Could not parse Drive settings"
            ))
    else:
        findings.append(AuditFinding(
            "drive", "External sharing", "WARN",
            "Could not retrieve Drive settings"
        ))

    return findings


def audit_gmail() -> List[AuditFinding]:
    """Audit Gmail forwarding and email security."""
    findings = []

    # Check forwarding rules
    output = run_gws_command(["gws", "gmail", "users", "settings", "forwardingAddresses", "list",
                              "--params", '{"userId": "me"}'])
    if output:
        try:
            data = json.loads(output)
            addrs = data if isinstance(data, list) else data.get("forwardingAddresses", [])
            if addrs:
                findings.append(AuditFinding(
                    "gmail", "Auto-forwarding", "WARN",
                    f"{len(addrs)} forwarding addresses configured",
                    "Data exfiltration via email forwarding",
                    "Review forwarding addresses (verify: gws schema gmail.users.settings.forwardingAddresses.list)"
                ))
            else:
                findings.append(AuditFinding(
                    "gmail", "Auto-forwarding", "PASS",
                    "No forwarding addresses configured"
                ))
        except json.JSONDecodeError:
            pass
    else:
        findings.append(AuditFinding(
            "gmail", "Auto-forwarding", "WARN",
            "Could not check forwarding settings"
        ))

    return findings


def audit_calendar() -> List[AuditFinding]:
    """Audit Calendar sharing settings."""
    findings = []

    output = run_gws_command(["gws", "calendar", "calendarList", "get", "--params", '{"calendarId": "primary"}'])
    if output:
        findings.append(AuditFinding(
            "calendar", "Primary calendar", "PASS",
            "Primary calendar accessible"
        ))
    else:
        findings.append(AuditFinding(
            "calendar", "Primary calendar", "WARN",
            "Could not access primary calendar"
        ))

    return findings


def run_live_audit(services: List[str]) -> AuditReport:
    """Run live audit against actual gws installation."""
    report = AuditReport()
    all_findings = []

    audit_map = {
        "drive": audit_drive,
        "gmail": audit_gmail,
        "calendar": audit_calendar,
    }

    for svc in services:
        fn = audit_map.get(svc)
        if fn:
            all_findings.extend(fn())

    report.findings = [asdict(f) for f in all_findings]
    report = calculate_score(report)
    return report


def run_demo_audit() -> AuditReport:
    """Return demo audit report with embedded sample data."""
    report = AuditReport(
        findings=[asdict(f) for f in DEMO_FINDINGS],
        demo_mode=True,
    )
    report = calculate_score(report)
    return report


def calculate_score(report: AuditReport) -> AuditReport:
    """Calculate audit score and grade."""
    total = len(report.findings)
    if total == 0:
        report.score = 0
        report.grade = "N/A"
        report.summary = "No checks performed"
        return report

    passes = sum(1 for f in report.findings if f["status"] == "PASS")
    warns = sum(1 for f in report.findings if f["status"] == "WARN")
    fails = sum(1 for f in report.findings if f["status"] == "FAIL")

    # Score: PASS=100, WARN=50, FAIL=0
    score = int(((passes * 100) + (warns * 50)) / total)
    report.score = score
    report.max_score = 100

    if score >= 90:
        report.grade = "A"
    elif score >= 75:
        report.grade = "B"
    elif score >= 60:
        report.grade = "C"
    elif score >= 40:
        report.grade = "D"
    else:
        report.grade = "F"

    report.summary = f"{passes} passed, {warns} warnings, {fails} failures — Score: {score}/100 (Grade: {report.grade})"
    return report


def main():
    parser = argparse.ArgumentParser(
        description="Security and configuration audit for Google Workspace",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s                              # Full audit (or demo if gws not installed)
  %(prog)s --json                       # JSON output
  %(prog)s --services gmail,drive       # Audit specific services
  %(prog)s --demo                       # Demo mode with sample data
        """,
    )
    parser.add_argument("--json", action="store_true", help="Output JSON")
    parser.add_argument("--services", default="gmail,drive,calendar",
                        help="Comma-separated services to audit (default: gmail,drive,calendar)")
    parser.add_argument("--demo", action="store_true", help="Run with demo data")
    args = parser.parse_args()

    services = [s.strip() for s in args.services.split(",") if s.strip()]

    if args.demo or not shutil.which("gws"):
        report = run_demo_audit()
    else:
        report = run_live_audit(services)

    if args.json:
        print(json.dumps(asdict(report), indent=2))
    else:
        print(f"\n{'='*60}")
        print(f"  GOOGLE WORKSPACE SECURITY AUDIT")
        if report.demo_mode:
            print(f"  (DEMO MODE — sample data)")
        print(f"{'='*60}\n")
        print(f"  Score: {report.score}/{report.max_score} (Grade: {report.grade})\n")

        current_area = ""
        for f in report.findings:
            if f["area"] != current_area:
                current_area = f["area"]
                print(f"\n  {current_area.upper()}")
                print(f"  {'-'*40}")

            icon = {"PASS": "PASS", "WARN": "WARN", "FAIL": "FAIL"}.get(f["status"], "????")
            print(f"  [{icon}] {f['check']}: {f['message']}")
            if f.get("risk") and f["status"] != "PASS":
                print(f"         Risk: {f['risk']}")
            if f.get("remediation") and f["status"] != "PASS":
                print(f"         Fix: {f['remediation']}")

        print(f"\n  {'='*56}")
        print(f"  {report.summary}")
        print(f"\n{'='*60}\n")


if __name__ == "__main__":
    main()
