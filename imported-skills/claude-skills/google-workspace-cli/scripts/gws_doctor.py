#!/usr/bin/env python3
"""
Google Workspace CLI Doctor — Pre-flight diagnostics for gws CLI.

Checks installation, version, authentication status, and service
connectivity. Runs in demo mode with embedded sample data when gws
is not installed.

Usage:
    python3 gws_doctor.py
    python3 gws_doctor.py --json
    python3 gws_doctor.py --services gmail,drive,calendar
"""

import argparse
import json
import shutil
import subprocess
import sys
from dataclasses import dataclass, field, asdict
from typing import List, Optional


@dataclass
class Check:
    name: str
    status: str  # PASS, WARN, FAIL
    message: str
    fix: str = ""


@dataclass
class DiagnosticReport:
    gws_installed: bool = False
    gws_version: str = ""
    auth_status: str = ""
    checks: List[dict] = field(default_factory=list)
    summary: str = ""
    demo_mode: bool = False


DEMO_CHECKS = [
    Check("gws-installed", "PASS", "gws v0.9.2 found at /usr/local/bin/gws"),
    Check("gws-version", "PASS", "Version 0.9.2 (latest)"),
    Check("auth-status", "PASS", "Authenticated as admin@company.com"),
    Check("token-expiry", "WARN", "Token expires in 23 minutes",
          "Run 'gws auth refresh' to extend token lifetime"),
    Check("gmail-access", "PASS", "Gmail API accessible — user profile retrieved"),
    Check("drive-access", "PASS", "Drive API accessible — root folder listed"),
    Check("calendar-access", "PASS", "Calendar API accessible — primary calendar found"),
    Check("sheets-access", "PASS", "Sheets API accessible"),
    Check("tasks-access", "FAIL", "Tasks API not authorized",
          "Run 'gws auth setup' and add 'tasks' scope"),
]

SERVICE_TEST_COMMANDS = {
    "gmail": ["gws", "gmail", "users", "getProfile", "--params", '{"userId": "me"}'],
    "drive": ["gws", "drive", "files", "list", "--params", '{"pageSize": 1}'],
    "calendar": ["gws", "calendar", "calendarList", "list", "--params", '{"maxResults": 1}'],
    "sheets": ["gws", "schema", "sheets.spreadsheets.get"],
    "tasks": ["gws", "tasks", "tasklists", "list", "--params", '{"maxResults": 1}'],
    "chat": ["gws", "chat", "spaces", "list", "--params", '{"pageSize": 1}'],
    "docs": ["gws", "schema", "docs.documents.get"],
}


def check_installation() -> Check:
    """Check if gws is installed and on PATH."""
    path = shutil.which("gws")
    if path:
        return Check("gws-installed", "PASS", f"gws found at {path}")
    return Check("gws-installed", "FAIL", "gws not found on PATH",
                 "Install via: npm install -g @googleworkspace/cli  OR  download from https://github.com/googleworkspace/cli/releases")


def check_version() -> Check:
    """Get gws version."""
    try:
        result = subprocess.run(
            ["gws", "--version"], capture_output=True, text=True, timeout=10
        )
        version = result.stdout.strip()
        if version:
            return Check("gws-version", "PASS", f"Version: {version}")
        return Check("gws-version", "WARN", "Could not parse version output")
    except (subprocess.TimeoutExpired, FileNotFoundError, OSError) as e:
        return Check("gws-version", "FAIL", f"Version check failed: {e}")


def check_auth() -> Check:
    """Check authentication status."""
    try:
        result = subprocess.run(
            ["gws", "auth", "status", "--json"],
            capture_output=True, text=True, timeout=15
        )
        if result.returncode == 0:
            try:
                data = json.loads(result.stdout)
                user = data.get("user", data.get("email", "unknown"))
                return Check("auth-status", "PASS", f"Authenticated as {user}")
            except json.JSONDecodeError:
                return Check("auth-status", "PASS", "Authenticated (could not parse details)")
        return Check("auth-status", "WARN",
                     "Could not confirm authentication ('gws auth status' may not exist "
                     "in your version; check 'gws auth --help')",
                     "Run 'gws auth setup' then 'gws auth login' to configure authentication")
    except (subprocess.TimeoutExpired, FileNotFoundError, OSError) as e:
        return Check("auth-status", "FAIL", f"Auth check failed: {e}",
                     "Run 'gws auth setup' then 'gws auth login' to configure authentication")


def check_service(service: str) -> Check:
    """Test connectivity to a specific service."""
    cmd = SERVICE_TEST_COMMANDS.get(service)
    if not cmd:
        return Check(f"{service}-access", "WARN", f"No test command for {service}")
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=15)
        if result.returncode == 0:
            return Check(f"{service}-access", "PASS", f"{service.title()} API accessible")
        stderr = result.stderr.strip()[:100]
        if "403" in stderr or "permission" in stderr.lower():
            return Check(f"{service}-access", "FAIL",
                         f"{service.title()} API permission denied",
                         f"Add '{service}' scope: gws auth setup --scopes {service}")
        return Check(f"{service}-access", "FAIL",
                     f"{service.title()} API error: {stderr}",
                     f"Check scope and permissions for {service}")
    except (subprocess.TimeoutExpired, FileNotFoundError, OSError) as e:
        return Check(f"{service}-access", "FAIL", f"{service.title()} test failed: {e}")


def run_diagnostics(services: List[str]) -> DiagnosticReport:
    """Run all diagnostic checks."""
    report = DiagnosticReport()
    checks = []

    # Installation check
    install_check = check_installation()
    checks.append(install_check)
    report.gws_installed = install_check.status == "PASS"

    if not report.gws_installed:
        report.checks = [asdict(c) for c in checks]
        report.summary = "FAIL: gws is not installed"
        return report

    # Version check
    version_check = check_version()
    checks.append(version_check)
    if version_check.status == "PASS":
        report.gws_version = version_check.message.replace("Version: ", "")

    # Auth check
    auth_check = check_auth()
    checks.append(auth_check)
    report.auth_status = auth_check.status

    if auth_check.status != "PASS":
        report.checks = [asdict(c) for c in checks]
        report.summary = "FAIL: Authentication not configured"
        return report

    # Service checks
    for svc in services:
        checks.append(check_service(svc))

    report.checks = [asdict(c) for c in checks]

    # Summary
    fails = sum(1 for c in checks if c.status == "FAIL")
    warns = sum(1 for c in checks if c.status == "WARN")
    passes = sum(1 for c in checks if c.status == "PASS")
    if fails > 0:
        report.summary = f"ISSUES FOUND: {passes} passed, {warns} warnings, {fails} failures"
    elif warns > 0:
        report.summary = f"MOSTLY OK: {passes} passed, {warns} warnings"
    else:
        report.summary = f"ALL CLEAR: {passes}/{passes} checks passed"

    return report


def run_demo() -> DiagnosticReport:
    """Return demo report with embedded sample data."""
    report = DiagnosticReport(
        gws_installed=True,
        gws_version="0.9.2",
        auth_status="PASS",
        checks=[asdict(c) for c in DEMO_CHECKS],
        summary="MOSTLY OK: 7 passed, 1 warning, 1 failure (demo mode)",
        demo_mode=True,
    )
    return report


def main():
    parser = argparse.ArgumentParser(
        description="Pre-flight diagnostics for Google Workspace CLI (gws)",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s                          # Run all checks
  %(prog)s --json                   # JSON output
  %(prog)s --services gmail,drive   # Check specific services only
  %(prog)s --demo                   # Demo mode (no gws required)
        """,
    )
    parser.add_argument("--json", action="store_true", help="Output JSON")
    parser.add_argument(
        "--services", default="gmail,drive,calendar,sheets,tasks",
        help="Comma-separated services to check (default: gmail,drive,calendar,sheets,tasks)"
    )
    parser.add_argument("--demo", action="store_true", help="Run with demo data")
    args = parser.parse_args()

    services = [s.strip() for s in args.services.split(",") if s.strip()]

    # Use demo mode if requested or gws not installed
    if args.demo or not shutil.which("gws"):
        report = run_demo()
    else:
        report = run_diagnostics(services)

    if args.json:
        print(json.dumps(asdict(report), indent=2))
    else:
        print(f"\n{'='*60}")
        print(f"  GWS CLI DIAGNOSTIC REPORT")
        if report.demo_mode:
            print(f"  (DEMO MODE — sample data)")
        print(f"{'='*60}\n")

        for c in report.checks:
            icon = {"PASS": "PASS", "WARN": "WARN", "FAIL": "FAIL"}.get(c["status"], "????")
            print(f"  [{icon}] {c['name']}: {c['message']}")
            if c.get("fix") and c["status"] != "PASS":
                print(f"         -> {c['fix']}")

        print(f"\n  {'-'*56}")
        print(f"  {report.summary}")
        print(f"\n{'='*60}\n")


if __name__ == "__main__":
    main()
