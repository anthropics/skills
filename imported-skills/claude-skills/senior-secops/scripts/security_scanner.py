#!/usr/bin/env python3
"""
Security Scanner - Scan source code for security vulnerabilities.

Table of Contents:
    SecurityScanner - Main class for security scanning
        __init__         - Initialize with target path and options
        scan()           - Run all security scans
        scan_secrets()   - Detect hardcoded secrets
        scan_sql_injection() - Detect SQL injection patterns
        scan_xss()       - Detect XSS vulnerabilities
        scan_command_injection() - Detect command injection
        scan_path_traversal() - Detect path traversal
        _scan_file()     - Scan individual file for patterns
        _calculate_severity() - Calculate finding severity
    main() - CLI entry point

Usage:
    python security_scanner.py /path/to/project
    python security_scanner.py /path/to/project --severity high
    python security_scanner.py /path/to/project --output report.json --json
"""

import os
import sys
import json
import re
import argparse
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from dataclasses import dataclass, asdict
from datetime import datetime


@dataclass
class SecurityFinding:
    """Represents a security finding."""
    rule_id: str
    severity: str  # critical, high, medium, low, info
    category: str
    title: str
    description: str
    file_path: str
    line_number: int
    code_snippet: str
    recommendation: str


class SecurityScanner:
    """Scan source code for security vulnerabilities."""

    # File extensions to scan
    SCAN_EXTENSIONS = {
        '.py', '.js', '.ts', '.jsx', '.tsx', '.java', '.go',
        '.rb', '.php', '.cs', '.rs', '.swift', '.kt',
        '.yml', '.yaml', '.json', '.xml', '.env', '.conf', '.config'
    }

    # Directories to skip
    SKIP_DIRS = {
        'node_modules', '.git', '__pycache__', '.venv', 'venv',
        'vendor', 'dist', 'build', '.next', 'coverage'
    }

    # Secret patterns
    SECRET_PATTERNS = [
        (r'(?i)(api[_-]?key|apikey)\s*[:=]\s*["\']?([a-zA-Z0-9_\-]{20,})["\']?',
         'API Key', 'Hardcoded API key detected'),
        (r'(?i)(secret[_-]?key|secretkey)\s*[:=]\s*["\']?([a-zA-Z0-9_\-]{16,})["\']?',
         'Secret Key', 'Hardcoded secret key detected'),
        (r'(?i)(password|passwd|pwd)\s*[:=]\s*["\']([^"\']{4,})["\']',
         'Password', 'Hardcoded password detected'),
        (r'(?i)(aws[_-]?access[_-]?key[_-]?id)\s*[:=]\s*["\']?(AKIA[A-Z0-9]{16})["\']?',
         'AWS Access Key', 'Hardcoded AWS access key detected'),
        (r'(?i)(aws[_-]?secret[_-]?access[_-]?key)\s*[:=]\s*["\']?([a-zA-Z0-9/+=]{40})["\']?',
         'AWS Secret Key', 'Hardcoded AWS secret access key detected'),
        (r'ghp_[a-zA-Z0-9]{36}',
         'GitHub Token', 'GitHub personal access token detected'),
        (r'sk-[a-zA-Z0-9]{48}',
         'OpenAI API Key', 'OpenAI API key detected'),
        (r'-----BEGIN\s+(RSA|DSA|EC|OPENSSH)?\s*PRIVATE KEY-----',
         'Private Key', 'Private key detected in source code'),
    ]

    # SQL injection patterns
    SQL_INJECTION_PATTERNS = [
        (r'execute\s*\(\s*["\']?\s*SELECT.*\+.*\+',
         'Dynamic SQL query with string concatenation'),
        (r'execute\s*\(\s*f["\']SELECT',
         'F-string SQL query (Python)'),
        (r'cursor\.execute\s*\(\s*["\'].*%s.*%\s*\(',
         'Unsafe string formatting in SQL'),
        (r'query\s*\(\s*[`"\']SELECT.*\$\{',
         'Template literal SQL injection (JavaScript)'),
        (r'\.query\s*\(\s*["\'].*\+.*\+',
         'String concatenation in SQL query'),
    ]

    # XSS patterns
    XSS_PATTERNS = [
        (r'innerHTML\s*=\s*[^;]+(?:user|input|param|query)',
         'User input assigned to innerHTML'),
        (r'document\.write\s*\([^;]*(?:user|input|param|query)',
         'User input in document.write'),
        (r'\.html\s*\(\s*[^)]*(?:user|input|param|query)',
         'User input in jQuery .html()'),
        (r'dangerouslySetInnerHTML',
         'React dangerouslySetInnerHTML usage'),
        (r'\|safe\s*}}',
         'Django safe filter may disable escaping'),
    ]

    # Command injection patterns (detection rules for finding unsafe patterns)
    COMMAND_INJECTION_PATTERNS = [
        (r'subprocess\.(?:call|run|Popen)\s*\([^)]*shell\s*=\s*True',
         'Subprocess with shell=True'),
        (r'exec\s*\(\s*[^)]*(?:user|input|param|request)',
         'exec() with potential user input'),
        (r'eval\s*\(\s*[^)]*(?:user|input|param|request)',
         'eval() with potential user input'),
    ]

    # Path traversal patterns
    PATH_TRAVERSAL_PATTERNS = [
        (r'open\s*\(\s*[^)]*(?:user|input|param|request)',
         'File open with potential user input'),
        (r'readFile\s*\(\s*[^)]*(?:user|input|param|req\.|query)',
         'File read with potential user input'),
        (r'path\.join\s*\([^)]*(?:user|input|param|req\.|query)',
         'Path.join with user input without validation'),
    ]

    def __init__(
        self,
        target_path: str,
        severity_threshold: str = "low",
        verbose: bool = False
    ):
        """
        Initialize the security scanner.

        Args:
            target_path: Directory or file to scan
            severity_threshold: Minimum severity to report (critical, high, medium, low)
            verbose: Enable verbose output
        """
        self.target_path = Path(target_path)
        self.severity_threshold = severity_threshold
        self.verbose = verbose
        self.findings: List[SecurityFinding] = []
        self.files_scanned = 0
        self.severity_order = {'critical': 0, 'high': 1, 'medium': 2, 'low': 3, 'info': 4}

    def scan(self) -> Dict:
        """
        Run all security scans.

        Returns:
            Dict with scan results and findings
        """
        print(f"Security Scanner - Scanning: {self.target_path}")
        print(f"Severity threshold: {self.severity_threshold}")
        print()

        if not self.target_path.exists():
            return {"status": "error", "message": f"Path not found: {self.target_path}"}

        start_time = datetime.now()

        # Collect files to scan
        files_to_scan = self._collect_files()
        print(f"Files to scan: {len(files_to_scan)}")

        # Run scans
        for file_path in files_to_scan:
            self._scan_file(file_path)
            self.files_scanned += 1

        # Filter by severity threshold
        threshold_level = self.severity_order.get(self.severity_threshold, 3)
        filtered_findings = [
            f for f in self.findings
            if self.severity_order.get(f.severity, 3) <= threshold_level
        ]

        end_time = datetime.now()
        scan_duration = (end_time - start_time).total_seconds()

        # Group findings by severity
        severity_counts = {}
        for finding in filtered_findings:
            severity_counts[finding.severity] = severity_counts.get(finding.severity, 0) + 1

        result = {
            "status": "completed",
            "target": str(self.target_path),
            "files_scanned": self.files_scanned,
            "scan_duration_seconds": round(scan_duration, 2),
            "total_findings": len(filtered_findings),
            "severity_counts": severity_counts,
            "findings": [asdict(f) for f in filtered_findings]
        }

        self._print_summary(result)

        return result

    def _collect_files(self) -> List[Path]:
        """Collect files to scan."""
        files = []

        if self.target_path.is_file():
            return [self.target_path]

        for root, dirs, filenames in os.walk(self.target_path):
            # Skip directories
            dirs[:] = [d for d in dirs if d not in self.SKIP_DIRS]

            for filename in filenames:
                file_path = Path(root) / filename
                if file_path.suffix.lower() in self.SCAN_EXTENSIONS:
                    files.append(file_path)

        return files

    def _scan_file(self, file_path: Path):
        """Scan a single file for security issues."""
        try:
            content = file_path.read_text(encoding='utf-8', errors='ignore')
            lines = content.split('\n')

            relative_path = str(file_path.relative_to(self.target_path) if self.target_path.is_dir() else file_path.name)

            # Scan for secrets
            self._scan_patterns(
                lines, relative_path,
                self.SECRET_PATTERNS,
                'secrets',
                'Hardcoded Secret',
                'critical'
            )

            # Scan for SQL injection
            self._scan_patterns(
                lines, relative_path,
                [(p[0], p[1]) for p in self.SQL_INJECTION_PATTERNS],
                'injection',
                'SQL Injection',
                'high'
            )

            # Scan for XSS
            self._scan_patterns(
                lines, relative_path,
                [(p[0], p[1]) for p in self.XSS_PATTERNS],
                'xss',
                'Cross-Site Scripting (XSS)',
                'high'
            )

            # Scan for command injection
            self._scan_patterns(
                lines, relative_path,
                [(p[0], p[1]) for p in self.COMMAND_INJECTION_PATTERNS],
                'injection',
                'Command Injection',
                'critical'
            )

            # Scan for path traversal
            self._scan_patterns(
                lines, relative_path,
                [(p[0], p[1]) for p in self.PATH_TRAVERSAL_PATTERNS],
                'path-traversal',
                'Path Traversal',
                'medium'
            )

            if self.verbose:
                print(f"  Scanned: {relative_path}")

        except Exception as e:
            if self.verbose:
                print(f"  Error scanning {file_path}: {e}")

    def _scan_patterns(
        self,
        lines: List[str],
        file_path: str,
        patterns: List[Tuple],
        category: str,
        title: str,
        default_severity: str
    ):
        """Scan lines for patterns."""
        for line_num, line in enumerate(lines, 1):
            for pattern_tuple in patterns:
                pattern = pattern_tuple[0]
                description = pattern_tuple[1] if len(pattern_tuple) > 1 else title

                match = re.search(pattern, line, re.IGNORECASE)
                if match:
                    # Check for false positives (comments, test files)
                    if self._is_false_positive(line, file_path):
                        continue

                    # Determine severity based on context
                    severity = self._calculate_severity(
                        default_severity,
                        file_path,
                        category
                    )

                    finding = SecurityFinding(
                        rule_id=f"{category}-{len(self.findings) + 1:04d}",
                        severity=severity,
                        category=category,
                        title=title,
                        description=description,
                        file_path=file_path,
                        line_number=line_num,
                        code_snippet=line.strip()[:100],
                        recommendation=self._get_recommendation(category)
                    )

                    self.findings.append(finding)

    def _is_false_positive(self, line: str, file_path: str) -> bool:
        """Check if finding is likely a false positive."""
        # Skip comments
        stripped = line.strip()
        if stripped.startswith('#') or stripped.startswith('//') or stripped.startswith('*'):
            return True

        # Skip test files for some patterns
        if 'test' in file_path.lower() or 'spec' in file_path.lower():
            return True

        # Skip example/sample values
        lower_line = line.lower()
        if any(skip in lower_line for skip in ['example', 'sample', 'placeholder', 'xxx', 'your_']):
            return True

        return False

    def _calculate_severity(self, default: str, file_path: str, category: str) -> str:
        """Calculate severity based on context."""
        # Increase severity for production-related files
        if any(prod in file_path.lower() for prod in ['prod', 'production', 'deploy']):
            if default == 'high':
                return 'critical'
            if default == 'medium':
                return 'high'

        # Decrease severity for config examples
        if 'example' in file_path.lower() or 'sample' in file_path.lower():
            if default == 'critical':
                return 'high'
            if default == 'high':
                return 'medium'

        return default

    def _get_recommendation(self, category: str) -> str:
        """Get remediation recommendation for category."""
        recommendations = {
            'secrets': 'Remove hardcoded secrets. Use environment variables or a secrets manager (HashiCorp Vault, AWS Secrets Manager).',
            'injection': 'Use parameterized queries or prepared statements. Never concatenate user input into queries.',
            'xss': 'Always escape or sanitize user input before rendering. Use framework-provided escaping functions.',
            'path-traversal': 'Validate and sanitize file paths. Use allowlists for permitted directories.',
        }
        return recommendations.get(category, 'Review and remediate the security issue.')

    def _print_summary(self, result: Dict):
        """Print scan summary."""
        print("\n" + "=" * 60)
        print("SECURITY SCAN SUMMARY")
        print("=" * 60)
        print(f"Target: {result['target']}")
        print(f"Files scanned: {result['files_scanned']}")
        print(f"Scan duration: {result['scan_duration_seconds']}s")
        print(f"Total findings: {result['total_findings']}")
        print()

        if result['severity_counts']:
            print("Findings by severity:")
            for severity in ['critical', 'high', 'medium', 'low', 'info']:
                count = result['severity_counts'].get(severity, 0)
                if count > 0:
                    print(f"  {severity.upper()}: {count}")
        print("=" * 60)

        if result['total_findings'] > 0:
            print("\nTop findings:")
            for finding in result['findings'][:5]:
                print(f"\n  [{finding['severity'].upper()}] {finding['title']}")
                print(f"  File: {finding['file_path']}:{finding['line_number']}")
                print(f"  {finding['description']}")


def main():
    """Main entry point for CLI."""
    parser = argparse.ArgumentParser(
        description="Scan source code for security vulnerabilities",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s /path/to/project
  %(prog)s /path/to/project --severity high
  %(prog)s /path/to/project --output report.json --json
  %(prog)s /path/to/file.py --verbose
        """
    )

    parser.add_argument(
        "target",
        help="Directory or file to scan"
    )
    parser.add_argument(
        "--severity", "-s",
        choices=["critical", "high", "medium", "low", "info"],
        default="low",
        help="Minimum severity to report (default: low)"
    )
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Enable verbose output"
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output results as JSON"
    )
    parser.add_argument(
        "--output", "-o",
        help="Output file path"
    )

    args = parser.parse_args()

    scanner = SecurityScanner(
        target_path=args.target,
        severity_threshold=args.severity,
        verbose=args.verbose
    )

    result = scanner.scan()

    if args.json:
        output = json.dumps(result, indent=2)
        if args.output:
            with open(args.output, 'w') as f:
                f.write(output)
            print(f"\nResults written to {args.output}")
        else:
            print(output)
    elif args.output:
        with open(args.output, 'w') as f:
            json.dump(result, f, indent=2)
        print(f"\nResults written to {args.output}")

    # Exit with error code if critical/high findings
    if result.get('severity_counts', {}).get('critical', 0) > 0:
        sys.exit(2)
    if result.get('severity_counts', {}).get('high', 0) > 0:
        sys.exit(1)


if __name__ == "__main__":
    main()
