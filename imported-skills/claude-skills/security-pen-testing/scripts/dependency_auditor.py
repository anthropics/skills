#!/usr/bin/env python3
"""
Dependency Auditor - Analyze package manifests for known vulnerable patterns.

Table of Contents:
    DependencyAuditor - Main class for dependency vulnerability analysis
        __init__              - Initialize with manifest path and severity filter
        audit()               - Run full audit on the manifest
        _parse_manifest()     - Detect and parse the manifest file
        _parse_package_json() - Parse npm package.json
        _parse_requirements() - Parse pip requirements.txt
        _parse_go_mod()       - Parse Go go.mod
        _parse_gemfile()      - Parse Ruby Gemfile
        _check_vulnerabilities() - Check packages against known CVE patterns
        _check_risky_patterns()  - Detect risky dependency patterns
    main() - CLI entry point

Usage:
    python dependency_auditor.py --file package.json
    python dependency_auditor.py --file requirements.txt --severity high
    python dependency_auditor.py --file go.mod --json
"""

import argparse
import json
import os
import re
import sys
from dataclasses import dataclass, asdict, field
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Tuple


@dataclass
class Dependency:
    """Represents a parsed dependency."""
    name: str
    version: str
    ecosystem: str  # npm, pypi, go, rubygems
    is_dev: bool = False


@dataclass
class VulnerabilityFinding:
    """A known vulnerability match for a dependency."""
    package: str
    installed_version: str
    vulnerable_range: str
    cve_id: str
    severity: str  # critical, high, medium, low
    title: str
    description: str
    remediation: str
    cvss_score: float = 0.0
    references: List[str] = field(default_factory=list)


@dataclass
class RiskyPattern:
    """A risky dependency pattern (not a CVE, but a concern)."""
    package: str
    pattern_type: str  # pinning, wildcard, deprecated, typosquat
    severity: str
    description: str
    recommendation: str


class DependencyAuditor:
    """Analyze package manifests for known vulnerable patterns and risky dependencies."""

    # Known vulnerable package versions (curated subset of high-profile CVEs)
    KNOWN_VULNS = [
        {"ecosystem": "npm", "package": "lodash", "below": "4.17.21",
         "cve": "CVE-2021-23337", "severity": "high", "cvss": 7.2,
         "title": "Prototype Pollution in lodash",
         "description": "lodash before 4.17.21 is vulnerable to Command Injection via template function.",
         "remediation": "Upgrade lodash to >=4.17.21"},
        {"ecosystem": "npm", "package": "axios", "below": "1.6.0",
         "cve": "CVE-2023-45857", "severity": "medium", "cvss": 6.5,
         "title": "CSRF token exposure in axios",
         "description": "axios before 1.6.0 inadvertently exposes CSRF tokens in cross-site requests.",
         "remediation": "Upgrade axios to >=1.6.0"},
        {"ecosystem": "npm", "package": "express", "below": "4.19.2",
         "cve": "CVE-2024-29041", "severity": "medium", "cvss": 6.1,
         "title": "Open Redirect in express",
         "description": "express before 4.19.2 allows open redirects via malicious URLs.",
         "remediation": "Upgrade express to >=4.19.2"},
        {"ecosystem": "npm", "package": "jsonwebtoken", "below": "9.0.0",
         "cve": "CVE-2022-23529", "severity": "critical", "cvss": 9.8,
         "title": "Insecure key retrieval in jsonwebtoken",
         "description": "jsonwebtoken before 9.0.0 allows key confusion attacks via secretOrPublicKey.",
         "remediation": "Upgrade jsonwebtoken to >=9.0.0"},
        {"ecosystem": "npm", "package": "minimatch", "below": "3.0.5",
         "cve": "CVE-2022-3517", "severity": "high", "cvss": 7.5,
         "title": "ReDoS in minimatch",
         "description": "minimatch before 3.0.5 is vulnerable to Regular Expression Denial of Service.",
         "remediation": "Upgrade minimatch to >=3.0.5"},
        {"ecosystem": "npm", "package": "tar", "below": "6.1.9",
         "cve": "CVE-2021-37713", "severity": "high", "cvss": 8.6,
         "title": "Arbitrary File Creation in tar",
         "description": "tar before 6.1.9 allows arbitrary file creation/overwrite via symlinks.",
         "remediation": "Upgrade tar to >=6.1.9"},
        {"ecosystem": "pypi", "package": "pillow", "below": "9.3.0",
         "cve": "CVE-2022-45198", "severity": "high", "cvss": 7.5,
         "title": "DoS via crafted image in Pillow",
         "description": "Pillow before 9.3.0 allows denial of service via specially crafted image files.",
         "remediation": "Upgrade Pillow to >=9.3.0"},
        {"ecosystem": "pypi", "package": "django", "below": "4.2.8",
         "cve": "CVE-2023-46695", "severity": "high", "cvss": 7.5,
         "title": "DoS via file uploads in Django",
         "description": "Django before 4.2.8 allows denial of service via large file uploads.",
         "remediation": "Upgrade Django to >=4.2.8"},
        {"ecosystem": "pypi", "package": "flask", "below": "2.3.2",
         "cve": "CVE-2023-30861", "severity": "high", "cvss": 7.5,
         "title": "Session cookie exposure in Flask",
         "description": "Flask before 2.3.2 may expose session cookies on cross-origin redirects.",
         "remediation": "Upgrade Flask to >=2.3.2"},
        {"ecosystem": "pypi", "package": "requests", "below": "2.31.0",
         "cve": "CVE-2023-32681", "severity": "medium", "cvss": 6.1,
         "title": "Proxy-Authorization header leak in requests",
         "description": "requests before 2.31.0 leaks Proxy-Authorization headers on redirects.",
         "remediation": "Upgrade requests to >=2.31.0"},
        {"ecosystem": "pypi", "package": "cryptography", "below": "41.0.0",
         "cve": "CVE-2023-38325", "severity": "high", "cvss": 7.5,
         "title": "NULL dereference in cryptography",
         "description": "cryptography before 41.0.0 has a NULL pointer dereference in PKCS7 parsing.",
         "remediation": "Upgrade cryptography to >=41.0.0"},
        {"ecosystem": "pypi", "package": "pyyaml", "below": "6.0.1",
         "cve": "CVE-2020-14343", "severity": "critical", "cvss": 9.8,
         "title": "Arbitrary code execution in PyYAML",
         "description": "PyYAML before 6.0.1 allows arbitrary code execution via yaml.load().",
         "remediation": "Upgrade PyYAML to >=6.0.1 and use yaml.safe_load()"},
        {"ecosystem": "go", "package": "golang.org/x/crypto", "below": "0.17.0",
         "cve": "CVE-2023-48795", "severity": "medium", "cvss": 5.9,
         "title": "Terrapin SSH prefix truncation attack",
         "description": "golang.org/x/crypto before 0.17.0 vulnerable to SSH prefix truncation.",
         "remediation": "Upgrade golang.org/x/crypto to >=0.17.0"},
        {"ecosystem": "go", "package": "golang.org/x/net", "below": "0.17.0",
         "cve": "CVE-2023-44487", "severity": "high", "cvss": 7.5,
         "title": "HTTP/2 rapid reset DoS",
         "description": "golang.org/x/net before 0.17.0 vulnerable to HTTP/2 rapid reset attack.",
         "remediation": "Upgrade golang.org/x/net to >=0.17.0"},
        {"ecosystem": "rubygems", "package": "rails", "below": "7.0.8",
         "cve": "CVE-2023-44487", "severity": "high", "cvss": 7.5,
         "title": "ReDoS in Rails",
         "description": "Rails before 7.0.8 vulnerable to Regular Expression Denial of Service.",
         "remediation": "Upgrade rails to >=7.0.8"},
    ]

    # Known typosquat / malicious package names
    TYPOSQUAT_PACKAGES = {
        "npm": ["crossenv", "event-stream-malicious", "flatmap-stream", "ua-parser-jss",
                 "loadsh", "lodashs", "axois", "requets"],
        "pypi": ["python3-dateutil", "jeIlyfish", "python-binance-sdk", "requestss",
                 "djago", "flassk", "requets"],
    }

    def __init__(self, manifest_path: str, severity_filter: str = "low"):
        self.manifest_path = Path(manifest_path)
        self.severity_filter = severity_filter
        self.severity_order = {"critical": 4, "high": 3, "medium": 2, "low": 1}
        self.min_severity = self.severity_order.get(severity_filter, 1)

    def audit(self) -> Dict:
        """Run full audit on the manifest file."""
        deps = self._parse_manifest()
        vuln_findings = self._check_vulnerabilities(deps)
        risky_patterns = self._check_risky_patterns(deps)

        # Filter by severity
        vuln_findings = [f for f in vuln_findings
                         if self.severity_order.get(f.severity, 0) >= self.min_severity]
        risky_patterns = [r for r in risky_patterns
                          if self.severity_order.get(r.severity, 0) >= self.min_severity]

        return {
            "manifest": str(self.manifest_path),
            "ecosystem": deps[0].ecosystem if deps else "unknown",
            "total_dependencies": len(deps),
            "dev_dependencies": len([d for d in deps if d.is_dev]),
            "vulnerability_findings": vuln_findings,
            "risky_patterns": risky_patterns,
            "summary": {
                "critical": len([f for f in vuln_findings if f.severity == "critical"]),
                "high": len([f for f in vuln_findings if f.severity == "high"]),
                "medium": len([f for f in vuln_findings if f.severity == "medium"]),
                "low": len([f for f in vuln_findings if f.severity == "low"]),
                "risky_patterns_count": len(risky_patterns),
            }
        }

    def _parse_manifest(self) -> List[Dependency]:
        """Detect manifest type and parse dependencies."""
        name = self.manifest_path.name.lower()
        try:
            content = self.manifest_path.read_text(encoding="utf-8")
        except (OSError, PermissionError) as e:
            print(f"Error reading {self.manifest_path}: {e}", file=sys.stderr)
            sys.exit(1)

        if name == "package.json":
            return self._parse_package_json(content)
        elif name in ("requirements.txt", "requirements-dev.txt", "requirements_dev.txt"):
            return self._parse_requirements(content)
        elif name == "go.mod":
            return self._parse_go_mod(content)
        elif name in ("gemfile", "gemfile.lock"):
            return self._parse_gemfile(content)
        else:
            print(f"Unsupported manifest type: {name}", file=sys.stderr)
            print("Supported: package.json, requirements.txt, go.mod, Gemfile", file=sys.stderr)
            sys.exit(1)

    def _parse_package_json(self, content: str) -> List[Dependency]:
        """Parse npm package.json."""
        deps = []
        try:
            data = json.loads(content)
        except json.JSONDecodeError as e:
            print(f"Invalid JSON in package.json: {e}", file=sys.stderr)
            sys.exit(1)

        for name, version in data.get("dependencies", {}).items():
            clean_ver = re.sub(r"[^0-9.]", "", version).strip(".")
            deps.append(Dependency(name=name, version=clean_ver or version, ecosystem="npm", is_dev=False))
        for name, version in data.get("devDependencies", {}).items():
            clean_ver = re.sub(r"[^0-9.]", "", version).strip(".")
            deps.append(Dependency(name=name, version=clean_ver or version, ecosystem="npm", is_dev=True))
        return deps

    def _parse_requirements(self, content: str) -> List[Dependency]:
        """Parse pip requirements.txt."""
        deps = []
        for line in content.strip().split("\n"):
            line = line.strip()
            if not line or line.startswith("#") or line.startswith("-"):
                continue
            match = re.match(r"^([a-zA-Z0-9_.-]+)\s*(?:[=<>!~]+\s*)?([\d.]*)", line)
            if match:
                name, version = match.group(1), match.group(2) or "unknown"
                deps.append(Dependency(name=name.lower(), version=version, ecosystem="pypi"))
        return deps

    def _parse_go_mod(self, content: str) -> List[Dependency]:
        """Parse Go go.mod."""
        deps = []
        in_require = False
        for line in content.strip().split("\n"):
            line = line.strip()
            if line.startswith("require ("):
                in_require = True
                continue
            if line == ")":
                in_require = False
                continue
            if in_require or line.startswith("require "):
                cleaned = line.replace("require ", "").strip()
                parts = cleaned.split()
                if len(parts) >= 2:
                    name = parts[0]
                    version = parts[1].lstrip("v")
                    indirect = "// indirect" in line
                    deps.append(Dependency(name=name, version=version, ecosystem="go", is_dev=indirect))
        return deps

    def _parse_gemfile(self, content: str) -> List[Dependency]:
        """Parse Ruby Gemfile."""
        deps = []
        for line in content.strip().split("\n"):
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            match = re.match(r'''gem\s+['"]([\w-]+)['"](?:\s*,\s*['"]([^'"]*)['"'])?''', line)
            if match:
                name = match.group(1)
                version = match.group(2) or "unknown"
                version = re.sub(r"[~><=\s]", "", version)
                deps.append(Dependency(name=name, version=version, ecosystem="rubygems"))
        return deps

    @staticmethod
    def _version_below(installed: str, threshold: str) -> bool:
        """Check if installed version is below threshold (simple numeric comparison)."""
        try:
            inst_parts = [int(x) for x in installed.split(".") if x.isdigit()]
            thresh_parts = [int(x) for x in threshold.split(".") if x.isdigit()]
            # Pad shorter list
            max_len = max(len(inst_parts), len(thresh_parts))
            inst_parts.extend([0] * (max_len - len(inst_parts)))
            thresh_parts.extend([0] * (max_len - len(thresh_parts)))
            return inst_parts < thresh_parts
        except (ValueError, IndexError):
            return False

    def _check_vulnerabilities(self, deps: List[Dependency]) -> List[VulnerabilityFinding]:
        """Check dependencies against known CVE database."""
        findings = []
        for dep in deps:
            for vuln in self.KNOWN_VULNS:
                if (dep.ecosystem == vuln["ecosystem"] and
                        dep.name.lower() == vuln["package"].lower() and
                        self._version_below(dep.version, vuln["below"])):
                    findings.append(VulnerabilityFinding(
                        package=dep.name,
                        installed_version=dep.version,
                        vulnerable_range=f"< {vuln['below']}",
                        cve_id=vuln["cve"],
                        severity=vuln["severity"],
                        title=vuln["title"],
                        description=vuln["description"],
                        remediation=vuln["remediation"],
                        cvss_score=vuln.get("cvss", 0.0),
                        references=[f"https://nvd.nist.gov/vuln/detail/{vuln['cve']}"],
                    ))
        return findings

    def _check_risky_patterns(self, deps: List[Dependency]) -> List[RiskyPattern]:
        """Detect risky dependency patterns."""
        patterns = []
        ecosystem = deps[0].ecosystem if deps else "unknown"

        # Check for typosquat packages
        typosquats = self.TYPOSQUAT_PACKAGES.get(ecosystem, [])
        for dep in deps:
            if dep.name.lower() in [t.lower() for t in typosquats]:
                patterns.append(RiskyPattern(
                    package=dep.name,
                    pattern_type="typosquat",
                    severity="critical",
                    description=f"'{dep.name}' is a known typosquat or malicious package name.",
                    recommendation="Remove immediately and check for compromised data. Install the legitimate package.",
                ))

        # Check for wildcard/unpinned versions
        for dep in deps:
            if dep.version in ("*", "latest", "unknown", ""):
                patterns.append(RiskyPattern(
                    package=dep.name,
                    pattern_type="unpinned",
                    severity="medium",
                    description=f"'{dep.name}' has an unpinned version ({dep.version}).",
                    recommendation="Pin to a specific version to prevent supply chain attacks.",
                ))

        # Check for excessive dev dependencies in production
        dev_count = len([d for d in deps if d.is_dev])
        total = len(deps)
        if total > 0 and dev_count / total > 0.7:
            patterns.append(RiskyPattern(
                package="(project-level)",
                pattern_type="dev-heavy",
                severity="low",
                description=f"{dev_count}/{total} dependencies are dev-only. Large dev surface increases supply chain risk.",
                recommendation="Review dev dependencies. Remove unused ones. Consider using --production for installs.",
            ))

        return patterns


def format_report_text(result: Dict) -> str:
    """Format audit result as human-readable text."""
    lines = []
    lines.append("=" * 70)
    lines.append("DEPENDENCY VULNERABILITY AUDIT REPORT")
    lines.append(f"Manifest: {result['manifest']}")
    lines.append(f"Ecosystem: {result['ecosystem']}")
    lines.append(f"Total dependencies: {result['total_dependencies']} ({result['dev_dependencies']} dev)")
    lines.append(f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    lines.append("=" * 70)

    summary = result["summary"]
    lines.append(f"\nSummary: {summary['critical']} critical, {summary['high']} high, "
                 f"{summary['medium']} medium, {summary['low']} low, "
                 f"{summary['risky_patterns_count']} risky pattern(s)")

    vulns = result["vulnerability_findings"]
    if vulns:
        lines.append(f"\n--- VULNERABILITY FINDINGS ({len(vulns)}) ---\n")
        for v in vulns:
            lines.append(f"  [{v.severity.upper()}] {v.package} {v.installed_version}")
            lines.append(f"    CVE: {v.cve_id} (CVSS: {v.cvss_score})")
            lines.append(f"    {v.title}")
            lines.append(f"    Vulnerable: {v.vulnerable_range}")
            lines.append(f"    Fix: {v.remediation}")
            lines.append("")
    else:
        lines.append("\nNo known vulnerabilities found in dependencies.")

    risky = result["risky_patterns"]
    if risky:
        lines.append(f"\n--- RISKY PATTERNS ({len(risky)}) ---\n")
        for r in risky:
            lines.append(f"  [{r.severity.upper()}] {r.package} — {r.pattern_type}")
            lines.append(f"    {r.description}")
            lines.append(f"    Fix: {r.recommendation}")
            lines.append("")

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Dependency Auditor — Analyze package manifests for known vulnerabilities and risky patterns.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Supported manifests:
  package.json      (npm)
  requirements.txt  (pip/PyPI)
  go.mod            (Go)
  Gemfile           (Ruby)

Examples:
  %(prog)s --file package.json
  %(prog)s --file requirements.txt --severity high
  %(prog)s --file go.mod --json
        """,
    )
    parser.add_argument("--file", required=True, metavar="PATH",
                        help="Path to package manifest file")
    parser.add_argument("--severity", choices=["low", "medium", "high", "critical"], default="low",
                        help="Minimum severity to report (default: low)")
    parser.add_argument("--json", action="store_true", dest="json_output",
                        help="Output results as JSON")
    args = parser.parse_args()

    if not Path(args.file).exists():
        print(f"Error: File not found: {args.file}", file=sys.stderr)
        sys.exit(1)

    auditor = DependencyAuditor(manifest_path=args.file, severity_filter=args.severity)
    result = auditor.audit()

    if args.json_output:
        json_result = {
            "manifest": result["manifest"],
            "ecosystem": result["ecosystem"],
            "total_dependencies": result["total_dependencies"],
            "dev_dependencies": result["dev_dependencies"],
            "summary": result["summary"],
            "vulnerability_findings": [asdict(f) for f in result["vulnerability_findings"]],
            "risky_patterns": [asdict(r) for r in result["risky_patterns"]],
            "generated_at": datetime.now().isoformat(),
        }
        print(json.dumps(json_result, indent=2))
    else:
        print(format_report_text(result))

    # Exit non-zero if critical or high vulnerabilities found
    if result["summary"]["critical"] > 0 or result["summary"]["high"] > 0:
        sys.exit(1)


if __name__ == "__main__":
    main()
