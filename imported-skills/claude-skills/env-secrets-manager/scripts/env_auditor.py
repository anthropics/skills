#!/usr/bin/env python3
"""Scan env files and source code for likely secret exposure patterns."""

from __future__ import annotations

import argparse
import json
import os
import re
from pathlib import Path
from typing import Dict, Iterable, List

IGNORED_DIRS = {
    ".git",
    "node_modules",
    ".next",
    "dist",
    "build",
    "coverage",
    "venv",
    ".venv",
    "__pycache__",
}

SOURCE_EXTS = {
    ".env",
    ".py",
    ".ts",
    ".tsx",
    ".js",
    ".jsx",
    ".json",
    ".yaml",
    ".yml",
    ".toml",
    ".ini",
    ".sh",
    ".md",
}

PATTERNS = [
    ("critical", "openai_key", re.compile(r"\bsk-[A-Za-z0-9]{20,}\b")),
    ("critical", "github_pat", re.compile(r"\bghp_[A-Za-z0-9]{20,}\b")),
    ("critical", "aws_access_key_id", re.compile(r"\bAKIA[0-9A-Z]{16}\b")),
    ("high", "slack_token", re.compile(r"\bxox[baprs]-[A-Za-z0-9-]{10,}\b")),
    ("high", "private_key_block", re.compile(r"-----BEGIN (RSA |EC |OPENSSH )?PRIVATE KEY-----")),
    ("high", "generic_secret_assignment", re.compile(r"(?i)\b(secret|token|password|passwd|api[_-]?key)\b\s*[:=]\s*['\"]?[A-Za-z0-9_\-\/.+=]{8,}")),
    ("medium", "jwt_like", re.compile(r"\beyJ[A-Za-z0-9_-]{10,}\.[A-Za-z0-9_-]{10,}\.[A-Za-z0-9_-]{10,}\b")),
]


def iter_files(root: Path) -> Iterable[Path]:
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in IGNORED_DIRS]
        for name in filenames:
            p = Path(dirpath) / name
            if p.is_file():
                yield p


def is_candidate(path: Path) -> bool:
    if path.name.startswith(".env"):
        return True
    return path.suffix.lower() in SOURCE_EXTS


def scan_file(path: Path, max_bytes: int, root: Path) -> List[Dict[str, object]]:
    findings: List[Dict[str, object]] = []
    try:
        if path.stat().st_size > max_bytes:
            return findings
        text = path.read_text(encoding="utf-8", errors="ignore")
    except Exception:
        return findings

    for lineno, line in enumerate(text.splitlines(), start=1):
        for severity, kind, pattern in PATTERNS:
            if pattern.search(line):
                findings.append(
                    {
                        "severity": severity,
                        "pattern": kind,
                        "file": str(path.relative_to(root)),
                        "line": lineno,
                        "snippet": line.strip()[:180],
                    }
                )
    return findings


def severity_counts(findings: List[Dict[str, object]]) -> Dict[str, int]:
    counts = {"critical": 0, "high": 0, "medium": 0, "low": 0}
    for item in findings:
        sev = str(item.get("severity", "low"))
        counts[sev] = counts.get(sev, 0) + 1
    return counts


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Audit a repository for likely secret leaks in env files and source.")
    parser.add_argument("path", help="Path to repository root")
    parser.add_argument("--max-file-size-kb", type=int, default=512, help="Skip files larger than this size (default: 512)")
    parser.add_argument("--json", action="store_true", help="Output JSON")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = Path(args.path).expanduser().resolve()
    if not root.exists() or not root.is_dir():
        raise SystemExit(f"Path is not a directory: {root}")

    max_bytes = max(1, args.max_file_size_kb) * 1024
    findings: List[Dict[str, object]] = []

    for file_path in iter_files(root):
        if is_candidate(file_path):
            findings.extend(scan_file(file_path, max_bytes=max_bytes, root=root))

    report = {
        "root": str(root),
        "total_findings": len(findings),
        "severity_counts": severity_counts(findings),
        "findings": findings,
    }

    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print("Env/Secrets Audit Report")
        print(f"Root: {report['root']}")
        print(f"Total findings: {report['total_findings']}")
        print("Severity:")
        for sev, count in report["severity_counts"].items():
            print(f"- {sev}: {count}")
        print("")
        for item in findings[:200]:
            print(f"[{item['severity'].upper()}] {item['file']}:{item['line']} ({item['pattern']})")
            print(f"  {item['snippet']}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
