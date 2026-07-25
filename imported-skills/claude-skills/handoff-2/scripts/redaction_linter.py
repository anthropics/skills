#!/usr/bin/env python3
"""Redaction linter for handoff drafts.

Scans a markdown file for secrets and PII before save. Operationalizes
Matt's redaction sentence: "Redact any sensitive information, such as API
keys, passwords, or personally identifiable information."

Exit codes:
  0 — clean (or warn mode with findings)
  1 — findings in strict mode
  2 — usage / IO error

Stdlib-only. Per-line whitelist via inline marker:
  <!-- handoff:allow secret -->
"""


import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

WHITELIST_MARKER = "<!-- handoff:allow secret -->"


@dataclass
class Pattern:
    name: str
    regex: re.Pattern[str]
    suggestion: str
    severity: str = "high"  # high | medium | low


PATTERNS: list[Pattern] = [
    Pattern(
        "aws_access_key",
        re.compile(r"\bAKIA[0-9A-Z]{16}\b"),
        "Replace with <AWS_ACCESS_KEY_REDACTED>.",
    ),
    Pattern(
        "aws_secret_key",
        re.compile(r"(?i)aws.{0,20}(secret|access).{0,20}[=:]\s*['\"]?[A-Za-z0-9/+=]{40}['\"]?"),
        "Replace value with <AWS_SECRET_REDACTED>.",
    ),
    Pattern(
        "github_token",
        re.compile(r"\b(ghp|gho|ghu|ghs|ghr)_[A-Za-z0-9]{36,}\b"),
        "Replace with <GITHUB_TOKEN_REDACTED>.",
    ),
    Pattern(
        "openai_key",
        re.compile(r"\bsk-[A-Za-z0-9_\-]{20,}\b"),
        "Replace with <OPENAI_KEY_REDACTED>.",
    ),
    Pattern(
        "anthropic_key",
        re.compile(r"\bsk-ant-[A-Za-z0-9_\-]{20,}\b"),
        "Replace with <ANTHROPIC_KEY_REDACTED>.",
    ),
    Pattern(
        "slack_token",
        re.compile(r"\bxox[abprs]-[A-Za-z0-9-]{10,}\b"),
        "Replace with <SLACK_TOKEN_REDACTED>.",
    ),
    Pattern(
        "google_api_key",
        re.compile(r"\bAIza[0-9A-Za-z_\-]{35}\b"),
        "Replace with <GOOGLE_API_KEY_REDACTED>.",
    ),
    Pattern(
        "stripe_key",
        re.compile(r"\b(sk|pk|rk)_(live|test)_[A-Za-z0-9]{16,}\b"),
        "Replace with <STRIPE_KEY_REDACTED>.",
    ),
    Pattern(
        "private_key_block",
        re.compile(r"-----BEGIN (?:RSA |EC |DSA |OPENSSH |PGP )?PRIVATE KEY-----"),
        "Remove the entire private-key block. Reference its filesystem path instead.",
    ),
    Pattern(
        "jwt",
        re.compile(r"\beyJ[A-Za-z0-9_\-]{10,}\.[A-Za-z0-9_\-]{10,}\.[A-Za-z0-9_\-]{10,}\b"),
        "Replace with <JWT_REDACTED>.",
    ),
    Pattern(
        "env_secret_assignment",
        re.compile(
            r"(?i)\b(password|passwd|pwd|secret|token|api[_-]?key|access[_-]?key|client[_-]?secret|db[_-]?url|database[_-]?url)\b\s*[=:]\s*['\"]?[^\s'\"<>]{6,}['\"]?"
        ),
        "Replace the value with <REDACTED>.",
        "high",
    ),
    Pattern(
        "db_connection_string",
        re.compile(
            r"\b(postgres|postgresql|mysql|mongodb(?:\+srv)?|redis|amqp)://[^\s'\"<>]+:[^\s'\"<>@]+@[^\s'\"<>]+"
        ),
        "Strip the user:password portion of the connection string.",
    ),
    Pattern(
        "bearer_token",
        re.compile(r"(?i)\bauthorization\s*:\s*bearer\s+[A-Za-z0-9_\-\.]{20,}"),
        "Replace the token value with <BEARER_REDACTED>.",
    ),
    Pattern(
        "email_address",
        re.compile(r"\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}\b"),
        "Redact if this is a third party not on the project; keep your own / well-known team addresses.",
        "medium",
    ),
    Pattern(
        "phone_number",
        re.compile(
            r"(?<!\d)(?:\+?\d{1,3}[\s.-]?)?(?:\(\d{2,4}\)|\d{2,4})[\s.-]?\d{3,4}[\s.-]?\d{3,4}(?!\d)"
        ),
        "Redact if PII; this regex has false positives on long version strings.",
        "low",
    ),
    Pattern(
        "url_with_token",
        re.compile(r"https?://[^\s'\"<>]*(?:[?&](?:token|access_token|api_key|key)=)[^\s'\"<>&]+"),
        "Strip the token query parameter from the URL.",
    ),
    Pattern(
        "private_cidr",
        re.compile(
            r"(?<![\d.])(?:10\.\d{1,3}\.\d{1,3}\.\d{1,3}"
            r"|192\.168\.\d{1,3}\.\d{1,3}"
            r"|172\.(?:1[6-9]|2\d|3[01])\.\d{1,3}\.\d{1,3})(?:/\d{1,2})?(?![\d.])"
        ),
        "Redact internal IP addresses / CIDR ranges; reference the host by role instead.",
        "low",
    ),
]


@dataclass
class Finding:
    line_number: int
    pattern_name: str
    severity: str
    match: str
    suggestion: str
    line_text: str


@dataclass
class Report:
    findings: list[Finding] = field(default_factory=list)

    def by_severity(self) -> dict[str, int]:
        counts: dict[str, int] = {"high": 0, "medium": 0, "low": 0}
        for f in self.findings:
            counts[f.severity] = counts.get(f.severity, 0) + 1
        return counts


def scan_text(text: str) -> Report:
    report = Report()
    for line_number, raw_line in enumerate(text.splitlines(), start=1):
        if WHITELIST_MARKER in raw_line:
            continue
        for pattern in PATTERNS:
            for m in pattern.regex.finditer(raw_line):
                preview = m.group(0)
                if len(preview) > 80:
                    preview = preview[:77] + "..."
                report.findings.append(
                    Finding(
                        line_number=line_number,
                        pattern_name=pattern.name,
                        severity=pattern.severity,
                        match=preview,
                        suggestion=pattern.suggestion,
                        line_text=raw_line.strip()[:120],
                    )
                )
    return report


def scan_file(path: Path) -> Report:
    try:
        text = path.read_text(encoding="utf-8")
    except OSError as exc:
        print(f"Error reading {path}: {exc}", file=sys.stderr)
        sys.exit(2)
    return scan_text(text)


def _format_human(report: Report, mode: str, path: Path) -> str:
    if not report.findings:
        return f"OK: no findings in {path}."
    lines = [f"Found {len(report.findings)} potential secret/PII match(es) in {path}:"]
    lines.append("")
    for f in report.findings:
        lines.append(f"  L{f.line_number} [{f.severity}] {f.pattern_name}: {f.match}")
        lines.append(f"    line: {f.line_text}")
        lines.append(f"    fix : {f.suggestion}")
        lines.append("")
    counts = report.by_severity()
    lines.append(f"Severity counts: high={counts['high']} medium={counts['medium']} low={counts['low']}")
    if mode == "strict":
        lines.append("Mode: STRICT — save is blocked until findings are resolved.")
    else:
        lines.append("Mode: WARN — save proceeds; review findings before sharing the handoff.")
    lines.append("Tip: append `<!-- handoff:allow secret -->` to a line to whitelist it.")
    return "\n".join(lines)


def _report_json(report, mode: str, file_label: str) -> str:
    return json.dumps(
        {
            "file": file_label,
            "mode": mode,
            "findings": [
                {
                    "line": f.line_number,
                    "pattern": f.pattern_name,
                    "severity": f.severity,
                    "match": f.match,
                    "suggestion": f.suggestion,
                }
                for f in report.findings
            ],
            "counts": report.by_severity(),
        },
        indent=2,
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Scan a handoff draft for secrets and PII.")
    parser.add_argument("file", nargs="?", help="Path to the handoff markdown file.")
    parser.add_argument(
        "--mode",
        choices=["strict", "warn", "off"],
        default="strict",
        help="strict: exit 1 on findings; warn: exit 0; off: skip scan.",
    )
    parser.add_argument("--json", action="store_true", help="Emit JSON instead of human output.")
    parser.add_argument(
        "--sample",
        action="store_true",
        help="Run on a built-in fixture with planted secrets and exit.",
    )
    args = parser.parse_args(argv)

    if args.sample:
        fixture = (
            "# Sample handoff\n"
            "API key: AKIAIOSFODNN7EXAMPLE\n"
            "Token: ghp_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n"
            "PASSWORD=hunter2supersecret\n"
            "Contact: jane.doe@example.com\n"
            "URL: https://api.example.com/v1/data?token=abcdef1234567890\n"
            "Allowed: AKIAIOSFODNN7EXAMPLE <!-- handoff:allow secret -->\n"
        )
        report = scan_text(fixture)
        if args.json:
            print(_report_json(report, "strict", "<sample>"))
        else:
            print(_format_human(report, "strict", Path("<sample>")))
        return 1 if report.findings else 0

    if args.mode == "off":
        print("Redaction linter is off (--mode off).")
        return 0

    if not args.file:
        parser.error("file is required unless --sample or --mode off.")

    path = Path(args.file)
    if not path.exists():
        print(f"File not found: {path}", file=sys.stderr)
        return 2

    report = scan_file(path)

    if args.json:
        print(_report_json(report, args.mode, str(path)))
    else:
        print(_format_human(report, args.mode, path))

    if not report.findings:
        return 0
    if args.mode == "strict":
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
