#!/usr/bin/env python3
"""
GDPR Compliance Checker

Scans codebases, configurations, and data handling patterns for potential
GDPR compliance issues. Identifies personal data processing, consent gaps,
and documentation requirements.

Usage:
    python gdpr_compliance_checker.py /path/to/project
    python gdpr_compliance_checker.py . --json
    python gdpr_compliance_checker.py /path/to/project --output report.json
"""

import argparse
import json
import os
import re
import sys
from pathlib import Path
from typing import Dict, List, Optional, Tuple


# Personal data patterns to detect
PERSONAL_DATA_PATTERNS = {
    "email": {
        "pattern": r"[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}",
        "category": "contact_data",
        "gdpr_article": "Art. 4(1)",
        "risk": "medium"
    },
    "ip_address": {
        "pattern": r"\b(?:\d{1,3}\.){3}\d{1,3}\b",
        "category": "online_identifier",
        "gdpr_article": "Art. 4(1), Recital 30",
        "risk": "medium"
    },
    "phone_number": {
        "pattern": r"(?:\+\d{1,3}[-.\s]?)?\(?\d{3}\)?[-.\s]?\d{3}[-.\s]?\d{4}",
        "category": "contact_data",
        "gdpr_article": "Art. 4(1)",
        "risk": "medium"
    },
    "credit_card": {
        "pattern": r"\b(?:\d{4}[-\s]?){3}\d{4}\b",
        "category": "financial_data",
        "gdpr_article": "Art. 4(1)",
        "risk": "high"
    },
    "iban": {
        "pattern": r"\b[A-Z]{2}\d{2}[A-Z0-9]{4}\d{7}(?:[A-Z0-9]?){0,16}\b",
        "category": "financial_data",
        "gdpr_article": "Art. 4(1)",
        "risk": "high"
    },
    "german_id": {
        "pattern": r"\b[A-Z0-9]{9}\b",
        "category": "government_id",
        "gdpr_article": "Art. 4(1)",
        "risk": "high"
    },
    "date_of_birth": {
        "pattern": r"\b(?:birth|dob|geboren|geburtsdatum)\b",
        "category": "demographic_data",
        "gdpr_article": "Art. 4(1)",
        "risk": "medium"
    },
    "health_data": {
        "pattern": r"\b(?:diagnosis|treatment|medication|patient|medical|health|symptom|disease)\b",
        "category": "special_category",
        "gdpr_article": "Art. 9(1)",
        "risk": "critical"
    },
    "biometric": {
        "pattern": r"\b(?:fingerprint|facial|retina|biometric|voice_print)\b",
        "category": "special_category",
        "gdpr_article": "Art. 9(1)",
        "risk": "critical"
    },
    "religion": {
        "pattern": r"\b(?:religion|religious|faith|church|mosque|synagogue)\b",
        "category": "special_category",
        "gdpr_article": "Art. 9(1)",
        "risk": "critical"
    }
}

# Code patterns indicating GDPR concerns
CODE_PATTERNS = {
    "logging_personal_data": {
        "pattern": r"(?:log|print|console)\s*\.\s*(?:info|debug|warn|error)\s*\([^)]*(?:email|user|name|address|phone)",
        "issue": "Potential logging of personal data",
        "gdpr_article": "Art. 5(1)(c) - Data minimization",
        "recommendation": "Review logging to ensure personal data is not logged or is properly pseudonymized",
        "severity": "high"
    },
    "missing_consent": {
        "pattern": r"(?:track|analytics|marketing|cookie)(?!.*consent)",
        "issue": "Tracking without apparent consent mechanism",
        "gdpr_article": "Art. 6(1)(a) - Consent",
        "recommendation": "Implement consent management before tracking",
        "severity": "high"
    },
    "hardcoded_retention": {
        "pattern": r"(?:retention|expire|ttl|lifetime)\s*[=:]\s*(?:null|undefined|0|never|forever)",
        "issue": "Indefinite data retention detected",
        "gdpr_article": "Art. 5(1)(e) - Storage limitation",
        "recommendation": "Define and implement data retention periods",
        "severity": "medium"
    },
    "third_party_transfer": {
        "pattern": r"(?:api|http|fetch|request)\s*\.\s*(?:post|put|send)\s*\([^)]*(?:user|personal|data)",
        "issue": "Potential third-party data transfer",
        "gdpr_article": "Art. 28 - Processor requirements",
        "recommendation": "Ensure Data Processing Agreement exists with third parties",
        "severity": "medium"
    },
    "encryption_missing": {
        "pattern": r"(?:password|secret|token|key)\s*[=:]\s*['\"][^'\"]+['\"]",
        "issue": "Potentially unencrypted sensitive data",
        "gdpr_article": "Art. 32(1)(a) - Encryption",
        "recommendation": "Encrypt sensitive data at rest and in transit",
        "severity": "critical"
    },
    "no_deletion": {
        "pattern": r"(?:delete|remove|erase).*(?:disabled|false|TODO|FIXME)",
        "issue": "Data deletion may be disabled or incomplete",
        "gdpr_article": "Art. 17 - Right to erasure",
        "recommendation": "Implement complete data deletion functionality",
        "severity": "high"
    }
}

# Configuration files to check for GDPR-relevant settings
CONFIG_PATTERNS = {
    "analytics_config": {
        "files": ["analytics.json", "gtag.js", "google-analytics.js"],
        "check": "anonymize_ip",
        "issue": "IP anonymization should be enabled for analytics",
        "gdpr_article": "Art. 5(1)(c)"
    },
    "cookie_config": {
        "files": ["cookie.config.js", "cookies.json"],
        "check": "consent_required",
        "issue": "Cookie consent should be required before non-essential cookies",
        "gdpr_article": "Art. 6(1)(a)"
    }
}

# File extensions to scan
SCANNABLE_EXTENSIONS = {
    ".py", ".js", ".ts", ".jsx", ".tsx", ".java", ".kt",
    ".go", ".rb", ".php", ".cs", ".swift", ".json", ".yaml",
    ".yml", ".xml", ".html", ".env", ".config"
}

# Files/directories to skip
SKIP_PATTERNS = {
    "node_modules", "vendor", ".git", "__pycache__", "dist",
    "build", ".venv", "venv", "env"
}


def should_skip(path: Path) -> bool:
    """Check if path should be skipped."""
    return any(skip in path.parts for skip in SKIP_PATTERNS)


def scan_file_for_patterns(
    filepath: Path,
    patterns: Dict
) -> List[Dict]:
    """Scan a file for pattern matches."""
    findings = []

    try:
        with open(filepath, "r", encoding="utf-8", errors="ignore") as f:
            content = f.read()
            lines = content.split("\n")

        for pattern_name, pattern_info in patterns.items():
            regex = re.compile(pattern_info["pattern"], re.IGNORECASE)

            for line_num, line in enumerate(lines, 1):
                matches = regex.findall(line)
                if matches:
                    findings.append({
                        "file": str(filepath),
                        "line": line_num,
                        "pattern": pattern_name,
                        "matches": len(matches) if isinstance(matches, list) else 1,
                        **{k: v for k, v in pattern_info.items() if k != "pattern"}
                    })

    except Exception as e:
        pass  # Skip files that can't be read

    return findings


def analyze_project(project_path: Path) -> Dict:
    """Analyze project for GDPR compliance issues."""
    personal_data_findings = []
    code_issue_findings = []
    config_findings = []
    files_scanned = 0

    # Scan all relevant files
    for filepath in project_path.rglob("*"):
        if filepath.is_file() and not should_skip(filepath):
            if filepath.suffix.lower() in SCANNABLE_EXTENSIONS:
                files_scanned += 1

                # Check for personal data patterns
                personal_data_findings.extend(
                    scan_file_for_patterns(filepath, PERSONAL_DATA_PATTERNS)
                )

                # Check for code issues
                code_issue_findings.extend(
                    scan_file_for_patterns(filepath, CODE_PATTERNS)
                )

    # Check for specific config files
    for config_name, config_info in CONFIG_PATTERNS.items():
        for config_file in config_info["files"]:
            config_path = project_path / config_file
            if config_path.exists():
                try:
                    with open(config_path, "r") as f:
                        content = f.read()
                    if config_info["check"] not in content.lower():
                        config_findings.append({
                            "file": str(config_path),
                            "config": config_name,
                            "issue": config_info["issue"],
                            "gdpr_article": config_info["gdpr_article"]
                        })
                except Exception:
                    pass

    # Calculate risk scores
    critical_count = sum(1 for f in personal_data_findings if f.get("risk") == "critical")
    critical_count += sum(1 for f in code_issue_findings if f.get("severity") == "critical")

    high_count = sum(1 for f in personal_data_findings if f.get("risk") == "high")
    high_count += sum(1 for f in code_issue_findings if f.get("severity") == "high")

    medium_count = sum(1 for f in personal_data_findings if f.get("risk") == "medium")
    medium_count += sum(1 for f in code_issue_findings if f.get("severity") == "medium")

    # Determine compliance score (100 = compliant, 0 = critical issues)
    score = 100
    score -= critical_count * 20
    score -= high_count * 10
    score -= medium_count * 5
    score -= len(config_findings) * 5
    score = max(0, score)

    # Determine compliance status
    if score >= 80:
        status = "compliant"
        status_description = "Low risk - minor improvements recommended"
    elif score >= 60:
        status = "needs_attention"
        status_description = "Medium risk - action required"
    elif score >= 40:
        status = "non_compliant"
        status_description = "High risk - immediate action required"
    else:
        status = "critical"
        status_description = "Critical risk - significant GDPR violations detected"

    return {
        "summary": {
            "files_scanned": files_scanned,
            "compliance_score": score,
            "status": status,
            "status_description": status_description,
            "issue_counts": {
                "critical": critical_count,
                "high": high_count,
                "medium": medium_count,
                "config_issues": len(config_findings)
            }
        },
        "personal_data_findings": personal_data_findings[:50],  # Limit output
        "code_issues": code_issue_findings[:50],
        "config_issues": config_findings,
        "recommendations": generate_recommendations(
            personal_data_findings, code_issue_findings, config_findings
        )
    }


def generate_recommendations(
    personal_data: List[Dict],
    code_issues: List[Dict],
    config_issues: List[Dict]
) -> List[Dict]:
    """Generate prioritized recommendations."""
    recommendations = []
    seen_issues = set()

    # Critical issues first
    for finding in code_issues:
        if finding.get("severity") == "critical":
            issue_key = finding.get("issue", "")
            if issue_key not in seen_issues:
                recommendations.append({
                    "priority": "P0",
                    "issue": finding.get("issue"),
                    "gdpr_article": finding.get("gdpr_article"),
                    "action": finding.get("recommendation"),
                    "affected_files": [finding.get("file")]
                })
                seen_issues.add(issue_key)

    # Special category data
    special_category_files = set()
    for finding in personal_data:
        if finding.get("category") == "special_category":
            special_category_files.add(finding.get("file"))

    if special_category_files:
        recommendations.append({
            "priority": "P0",
            "issue": "Special category personal data (Art. 9) detected",
            "gdpr_article": "Art. 9(1)",
            "action": "Ensure explicit consent or other Art. 9(2) legal basis exists",
            "affected_files": list(special_category_files)[:5]
        })

    # High priority issues
    for finding in code_issues:
        if finding.get("severity") == "high":
            issue_key = finding.get("issue", "")
            if issue_key not in seen_issues:
                recommendations.append({
                    "priority": "P1",
                    "issue": finding.get("issue"),
                    "gdpr_article": finding.get("gdpr_article"),
                    "action": finding.get("recommendation"),
                    "affected_files": [finding.get("file")]
                })
                seen_issues.add(issue_key)

    # Config issues
    for finding in config_issues:
        recommendations.append({
            "priority": "P1",
            "issue": finding.get("issue"),
            "gdpr_article": finding.get("gdpr_article"),
            "action": f"Update configuration in {finding.get('file')}",
            "affected_files": [finding.get("file")]
        })

    return recommendations[:15]


def print_report(analysis: Dict) -> None:
    """Print human-readable report."""
    summary = analysis["summary"]

    print("=" * 60)
    print("GDPR COMPLIANCE ASSESSMENT REPORT")
    print("=" * 60)
    print()
    print(f"Compliance Score: {summary['compliance_score']}/100")
    print(f"Status: {summary['status'].upper()}")
    print(f"Assessment: {summary['status_description']}")
    print(f"Files Scanned: {summary['files_scanned']}")
    print()

    counts = summary["issue_counts"]
    print("--- ISSUE SUMMARY ---")
    print(f"  Critical: {counts['critical']}")
    print(f"  High: {counts['high']}")
    print(f"  Medium: {counts['medium']}")
    print(f"  Config Issues: {counts['config_issues']}")
    print()

    if analysis["recommendations"]:
        print("--- PRIORITIZED RECOMMENDATIONS ---")
        for i, rec in enumerate(analysis["recommendations"][:10], 1):
            print(f"\n{i}. [{rec['priority']}] {rec['issue']}")
            print(f"   GDPR Article: {rec['gdpr_article']}")
            print(f"   Action: {rec['action']}")

    print()
    print("=" * 60)
    print("Note: This is an automated assessment. Manual review by a")
    print("qualified Data Protection Officer is recommended.")
    print("=" * 60)


def main():
    parser = argparse.ArgumentParser(
        description="Scan project for GDPR compliance issues"
    )
    parser.add_argument(
        "project_path",
        nargs="?",
        default=".",
        help="Path to project directory (default: current directory)"
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output in JSON format"
    )
    parser.add_argument(
        "--output", "-o",
        help="Write output to file"
    )

    args = parser.parse_args()

    project_path = Path(args.project_path).resolve()
    if not project_path.exists():
        print(f"Error: Path does not exist: {project_path}", file=sys.stderr)
        sys.exit(1)

    analysis = analyze_project(project_path)

    if args.json:
        output = json.dumps(analysis, indent=2)
        if args.output:
            with open(args.output, "w") as f:
                f.write(output)
            print(f"Report written to {args.output}")
        else:
            print(output)
    else:
        print_report(analysis)
        if args.output:
            with open(args.output, "w") as f:
                json.dump(analysis, f, indent=2)
            print(f"\nDetailed JSON report written to {args.output}")


if __name__ == "__main__":
    main()
