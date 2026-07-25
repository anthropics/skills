#!/usr/bin/env python3
"""
Secret Scanner

Detects hardcoded secrets, API keys, and credentials in source code.
Identifies exposed secrets before they reach version control.

Usage:
    python secret_scanner.py /path/to/project
    python secret_scanner.py /path/to/file.py
    python secret_scanner.py /path/to/project --format json
    python secret_scanner.py --list-patterns
"""

import argparse
import json
import os
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional
from enum import Enum


class Severity(Enum):
    CRITICAL = "critical"
    HIGH = "high"
    MEDIUM = "medium"
    LOW = "low"


@dataclass
class SecretPattern:
    pattern_id: str
    name: str
    description: str
    regex: str
    severity: Severity
    file_extensions: List[str]
    recommendation: str


@dataclass
class SecretFinding:
    pattern_id: str
    name: str
    severity: Severity
    file_path: str
    line_number: int
    matched_text: str
    recommendation: str


# Secret patterns database
SECRET_PATTERNS = [
    # Cloud Provider Keys
    SecretPattern(
        pattern_id="AWS001",
        name="AWS Access Key ID",
        description="AWS access key identifier",
        regex=r'AKIA[0-9A-Z]{16}',
        severity=Severity.CRITICAL,
        file_extensions=[".py", ".js", ".ts", ".java", ".go", ".rb", ".php", ".env", ".yml", ".yaml", ".json", ".xml", ".conf"],
        recommendation="Use IAM roles or AWS Secrets Manager instead of hardcoded keys"
    ),
    SecretPattern(
        pattern_id="AWS002",
        name="AWS Secret Access Key",
        description="AWS secret access key",
        regex=r'(?:aws_secret_access_key|AWS_SECRET_ACCESS_KEY)\s*[:=]\s*["\']?[A-Za-z0-9/+=]{40}["\']?',
        severity=Severity.CRITICAL,
        file_extensions=[".py", ".js", ".ts", ".java", ".go", ".rb", ".php", ".env", ".yml", ".yaml", ".json", ".conf"],
        recommendation="Use IAM roles or AWS Secrets Manager instead of hardcoded secrets"
    ),
    SecretPattern(
        pattern_id="GCP001",
        name="Google Cloud API Key",
        description="Google Cloud Platform API key",
        regex=r'AIza[0-9A-Za-z\-_]{35}',
        severity=Severity.CRITICAL,
        file_extensions=[".py", ".js", ".ts", ".java", ".go", ".rb", ".php", ".env", ".yml", ".yaml", ".json"],
        recommendation="Use service accounts or Google Secret Manager"
    ),
    SecretPattern(
        pattern_id="AZURE001",
        name="Azure Storage Key",
        description="Azure storage account key",
        regex=r'(?:AccountKey|account_key)\s*[:=]\s*["\']?[A-Za-z0-9+/=]{88}["\']?',
        severity=Severity.CRITICAL,
        file_extensions=[".py", ".js", ".ts", ".java", ".go", ".cs", ".env", ".yml", ".yaml", ".json"],
        recommendation="Use Azure Key Vault or managed identities"
    ),

    # Authentication Tokens
    SecretPattern(
        pattern_id="JWT001",
        name="JSON Web Token",
        description="Hardcoded JWT token",
        regex=r'eyJ[A-Za-z0-9-_=]+\.eyJ[A-Za-z0-9-_=]+\.[A-Za-z0-9-_.+/=]*',
        severity=Severity.HIGH,
        file_extensions=[".py", ".js", ".ts", ".java", ".go", ".rb", ".php", ".env", ".json"],
        recommendation="Generate tokens dynamically, never hardcode"
    ),
    SecretPattern(
        pattern_id="GITHUB001",
        name="GitHub Token",
        description="GitHub personal access token or OAuth token",
        regex=r'(?:ghp|gho|ghu|ghs|ghr)_[A-Za-z0-9_]{36,255}',
        severity=Severity.CRITICAL,
        file_extensions=[".py", ".js", ".ts", ".java", ".go", ".rb", ".php", ".env", ".yml", ".yaml", ".json"],
        recommendation="Use GitHub App authentication or environment variables"
    ),
    SecretPattern(
        pattern_id="GITLAB001",
        name="GitLab Token",
        description="GitLab personal access or pipeline token",
        regex=r'glpat-[A-Za-z0-9\-_]{20,}',
        severity=Severity.CRITICAL,
        file_extensions=[".py", ".js", ".ts", ".java", ".go", ".rb", ".php", ".env", ".yml", ".yaml"],
        recommendation="Use CI/CD variables or environment variables"
    ),
    SecretPattern(
        pattern_id="SLACK001",
        name="Slack Token",
        description="Slack API token",
        regex=r'xox[baprs]-[0-9]{10,13}-[0-9]{10,13}[a-zA-Z0-9-]*',
        severity=Severity.HIGH,
        file_extensions=[".py", ".js", ".ts", ".java", ".go", ".rb", ".php", ".env", ".yml", ".yaml", ".json"],
        recommendation="Use environment variables or secrets manager"
    ),
    SecretPattern(
        pattern_id="STRIPE001",
        name="Stripe API Key",
        description="Stripe secret or publishable key",
        regex=r'(?:sk|pk)_(?:test|live)_[0-9a-zA-Z]{24,}',
        severity=Severity.CRITICAL,
        file_extensions=[".py", ".js", ".ts", ".java", ".go", ".rb", ".php", ".env", ".yml", ".yaml", ".json"],
        recommendation="Use environment variables, never commit API keys"
    ),
    SecretPattern(
        pattern_id="TWILIO001",
        name="Twilio API Key",
        description="Twilio account SID or auth token",
        regex=r'(?:AC[a-z0-9]{32}|SK[a-z0-9]{32})',
        severity=Severity.HIGH,
        file_extensions=[".py", ".js", ".ts", ".java", ".go", ".rb", ".php", ".env", ".yml", ".yaml", ".json"],
        recommendation="Use environment variables for Twilio credentials"
    ),
    SecretPattern(
        pattern_id="SENDGRID001",
        name="SendGrid API Key",
        description="SendGrid API key",
        regex=r'SG\.[A-Za-z0-9_-]{22}\.[A-Za-z0-9_-]{43}',
        severity=Severity.HIGH,
        file_extensions=[".py", ".js", ".ts", ".java", ".go", ".rb", ".php", ".env", ".yml", ".yaml", ".json"],
        recommendation="Use environment variables for email service credentials"
    ),

    # Cryptographic Keys
    SecretPattern(
        pattern_id="CRYPTO001",
        name="RSA Private Key",
        description="RSA private key in PEM format",
        regex=r'-----BEGIN RSA PRIVATE KEY-----',
        severity=Severity.CRITICAL,
        file_extensions=[".py", ".js", ".ts", ".java", ".go", ".rb", ".php", ".pem", ".key", ".txt"],
        recommendation="Store private keys in secure key management systems"
    ),
    SecretPattern(
        pattern_id="CRYPTO002",
        name="EC Private Key",
        description="Elliptic curve private key",
        regex=r'-----BEGIN EC PRIVATE KEY-----',
        severity=Severity.CRITICAL,
        file_extensions=[".py", ".js", ".ts", ".java", ".go", ".rb", ".php", ".pem", ".key"],
        recommendation="Use hardware security modules or key management services"
    ),
    SecretPattern(
        pattern_id="CRYPTO003",
        name="OpenSSH Private Key",
        description="OpenSSH private key",
        regex=r'-----BEGIN OPENSSH PRIVATE KEY-----',
        severity=Severity.CRITICAL,
        file_extensions=[".py", ".js", ".ts", ".java", ".go", ".rb", ".php", ".pem", ".key", ".txt"],
        recommendation="Never commit SSH keys to repositories"
    ),
    SecretPattern(
        pattern_id="CRYPTO004",
        name="PGP Private Key",
        description="PGP/GPG private key block",
        regex=r'-----BEGIN PGP PRIVATE KEY BLOCK-----',
        severity=Severity.CRITICAL,
        file_extensions=[".py", ".js", ".ts", ".java", ".go", ".rb", ".php", ".asc", ".gpg", ".txt"],
        recommendation="Store PGP keys in secure key rings, not source code"
    ),

    # Generic Patterns
    SecretPattern(
        pattern_id="GEN001",
        name="Generic API Key",
        description="Generic API key or secret pattern",
        regex=r'(?:api[_-]?key|apikey|api[_-]?secret)\s*[:=]\s*["\'][a-zA-Z0-9_\-]{20,}["\']',
        severity=Severity.HIGH,
        file_extensions=[".py", ".js", ".ts", ".java", ".go", ".rb", ".php", ".env", ".yml", ".yaml", ".json", ".xml"],
        recommendation="Use environment variables or secrets manager"
    ),
    SecretPattern(
        pattern_id="GEN002",
        name="Generic Secret",
        description="Generic secret or token pattern",
        regex=r'(?:secret|token|auth[_-]?token)\s*[:=]\s*["\'][a-zA-Z0-9_\-]{20,}["\']',
        severity=Severity.HIGH,
        file_extensions=[".py", ".js", ".ts", ".java", ".go", ".rb", ".php", ".env", ".yml", ".yaml", ".json"],
        recommendation="Store secrets in environment variables or secret managers"
    ),
    SecretPattern(
        pattern_id="GEN003",
        name="Password in Config",
        description="Password in configuration file",
        regex=r'(?:password|passwd|pwd)\s*[:=]\s*["\'][^"\']{8,}["\']',
        severity=Severity.CRITICAL,
        file_extensions=[".py", ".js", ".ts", ".java", ".go", ".rb", ".php", ".env", ".yml", ".yaml", ".json", ".xml", ".conf", ".ini"],
        recommendation="Never hardcode passwords. Use secret managers"
    ),
    SecretPattern(
        pattern_id="GEN004",
        name="Database Connection String",
        description="Database connection string with credentials",
        regex=r'(?:mongodb|postgres|mysql|redis|amqp)://[^:]+:[^@]+@[^/]+',
        severity=Severity.CRITICAL,
        file_extensions=[".py", ".js", ".ts", ".java", ".go", ".rb", ".php", ".env", ".yml", ".yaml", ".json"],
        recommendation="Use environment variables for database credentials"
    ),

    # Low Severity Patterns
    SecretPattern(
        pattern_id="LOW001",
        name="TODO with Secret",
        description="TODO comment mentioning secrets or credentials",
        regex=r'(?:#|//|/\*)\s*(?:TODO|FIXME|XXX).*(?:secret|password|credential|key)',
        severity=Severity.LOW,
        file_extensions=[".py", ".js", ".ts", ".java", ".go", ".rb", ".php"],
        recommendation="Address security TODOs before deployment"
    ),
]


def scan_file(file_path: Path, patterns: List[SecretPattern]) -> List[SecretFinding]:
    """Scan a single file for secrets."""
    findings = []
    extension = file_path.suffix.lower()

    try:
        content = file_path.read_text(encoding='utf-8', errors='ignore')
        lines = content.split('\n')
    except Exception:
        return findings

    for pattern in patterns:
        if extension not in pattern.file_extensions:
            continue

        try:
            regex = re.compile(pattern.regex, re.IGNORECASE)

            for i, line in enumerate(lines, 1):
                # Skip comments that explain patterns (like in this file)
                if 'regex' in line.lower() or 'pattern' in line.lower():
                    continue

                match = regex.search(line)
                if match:
                    # Mask the actual secret for safety
                    matched = match.group(0)
                    if len(matched) > 20:
                        masked = matched[:10] + "..." + matched[-5:]
                    else:
                        masked = matched[:5] + "..."

                    findings.append(SecretFinding(
                        pattern_id=pattern.pattern_id,
                        name=pattern.name,
                        severity=pattern.severity,
                        file_path=str(file_path),
                        line_number=i,
                        matched_text=masked,
                        recommendation=pattern.recommendation
                    ))
        except re.error:
            continue

    return findings


def scan_directory(dir_path: Path, patterns: List[SecretPattern],
                   exclude_dirs: List[str] = None) -> List[SecretFinding]:
    """Scan all files in a directory for secrets."""
    if exclude_dirs is None:
        exclude_dirs = [
            "node_modules", ".git", "__pycache__", "venv", ".venv",
            "dist", "build", ".next", "vendor", ".idea", ".vscode"
        ]

    findings = []
    extensions = set()
    for pattern in patterns:
        extensions.update(pattern.file_extensions)

    for file_path in dir_path.rglob("*"):
        if file_path.is_file():
            # Check exclusions
            if any(excluded in file_path.parts for excluded in exclude_dirs):
                continue

            # Skip binary files and large files
            if file_path.stat().st_size > 1_000_000:  # 1MB limit
                continue

            if file_path.suffix.lower() in extensions or file_path.name in ['.env', '.env.local', '.env.production']:
                findings.extend(scan_file(file_path, patterns))

    return sorted(findings, key=lambda f: (
        0 if f.severity == Severity.CRITICAL else
        1 if f.severity == Severity.HIGH else
        2 if f.severity == Severity.MEDIUM else 3
    ))


def format_text_report(findings: List[SecretFinding], path: str) -> str:
    """Format findings as text report."""
    lines = []
    lines.append("=" * 70)
    lines.append("SECRET SCAN REPORT")
    lines.append("=" * 70)
    lines.append(f"Target: {path}")
    lines.append("")

    # Summary
    by_severity = {}
    for finding in findings:
        sev = finding.severity.value
        by_severity[sev] = by_severity.get(sev, 0) + 1

    lines.append("SUMMARY:")
    lines.append(f"  Total Secrets Found: {len(findings)}")
    for sev in ["critical", "high", "medium", "low"]:
        count = by_severity.get(sev, 0)
        if count > 0:
            lines.append(f"  {sev.upper()}: {count}")
    lines.append("")

    if not findings:
        lines.append("No secrets found!")
        lines.append("=" * 70)
        return "\n".join(lines)

    # Group by severity
    current_severity = None
    for finding in findings:
        if finding.severity != current_severity:
            current_severity = finding.severity
            lines.append("-" * 70)
            lines.append(f"[{current_severity.value.upper()}]")
            lines.append("-" * 70)

        lines.append("")
        lines.append(f"  [{finding.pattern_id}] {finding.name}")
        lines.append(f"  File: {finding.file_path}:{finding.line_number}")
        lines.append(f"  Match: {finding.matched_text}")
        lines.append(f"  Fix: {finding.recommendation}")

    lines.append("")
    lines.append("=" * 70)
    lines.append("IMPORTANT: Review all findings and rotate exposed credentials!")
    lines.append("=" * 70)
    return "\n".join(lines)


def format_json_report(findings: List[SecretFinding], path: str) -> Dict:
    """Format findings as JSON."""
    return {
        "target": path,
        "scan_date": __import__('datetime').datetime.now().isoformat(),
        "summary": {
            "total": len(findings),
            "by_severity": {
                sev.value: sum(1 for f in findings if f.severity == sev)
                for sev in Severity
            }
        },
        "findings": [
            {
                "pattern_id": f.pattern_id,
                "name": f.name,
                "severity": f.severity.value,
                "file_path": f.file_path,
                "line_number": f.line_number,
                "matched_text": f.matched_text,
                "recommendation": f.recommendation
            }
            for f in findings
        ]
    }


def list_patterns():
    """List all secret patterns."""
    print("\n" + "=" * 60)
    print("SECRET DETECTION PATTERNS")
    print("=" * 60)

    for pattern in sorted(SECRET_PATTERNS, key=lambda p: p.pattern_id):
        print(f"\n[{pattern.pattern_id}] {pattern.name}")
        print(f"  Severity: {pattern.severity.value.upper()}")
        print(f"  Description: {pattern.description}")


def main():
    parser = argparse.ArgumentParser(
        description="Secret Scanner - Detect hardcoded secrets in code",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Scan a project directory
  python secret_scanner.py /path/to/project

  # Scan a single file
  python secret_scanner.py /path/to/config.py

  # Output as JSON
  python secret_scanner.py /path/to/project --format json

  # List all detection patterns
  python secret_scanner.py --list-patterns

  # Save report to file
  python secret_scanner.py /path/to/project --output report.txt
        """
    )

    parser.add_argument(
        "path",
        nargs="?",
        help="Path to scan (file or directory)"
    )
    parser.add_argument(
        "--format", "-f",
        choices=["text", "json"],
        default="text",
        help="Output format (default: text)"
    )
    parser.add_argument(
        "--output", "-o",
        help="Output file path"
    )
    parser.add_argument(
        "--list-patterns", "-l",
        action="store_true",
        help="List all detection patterns"
    )
    parser.add_argument(
        "--severity", "-s",
        choices=["critical", "high", "medium", "low"],
        help="Minimum severity to report"
    )

    args = parser.parse_args()

    if args.list_patterns:
        list_patterns()
        return

    if not args.path:
        parser.error("path is required (or use --list-patterns)")

    path = Path(args.path)
    if not path.exists():
        print(f"Error: Path does not exist: {path}")
        sys.exit(1)

    # Filter patterns by severity
    patterns = SECRET_PATTERNS
    if args.severity:
        severity_order = ["critical", "high", "medium", "low"]
        min_index = severity_order.index(args.severity)
        allowed = set(Severity(s) for s in severity_order[:min_index + 1])
        patterns = [p for p in patterns if p.severity in allowed]

    # Scan
    if path.is_file():
        findings = scan_file(path, patterns)
    else:
        findings = scan_directory(path, patterns)

    # Format output
    if args.format == "json":
        output = json.dumps(format_json_report(findings, str(path)), indent=2)
    else:
        output = format_text_report(findings, str(path))

    # Write output
    if args.output:
        with open(args.output, 'w') as f:
            f.write(output)
        print(f"Report written to {args.output}")
    else:
        print(output)

    # Exit code based on findings
    if any(f.severity in (Severity.CRITICAL, Severity.HIGH) for f in findings):
        sys.exit(1)


if __name__ == "__main__":
    main()
