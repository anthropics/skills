#!/usr/bin/env python3
"""
validate_project.py — Validate a generated project directory for common issues.

Checks:
  - README.md exists and is non-empty
  - .gitignore exists
  - .env.example exists (if code references env vars)
  - Package manifest exists (package.json, requirements.txt, go.mod, etc.)
  - No .env file committed (secrets leak)
  - At least one test file exists
  - No TODO/FIXME placeholders in generated code

Usage:
    python3 validate_project.py /path/to/project
    python3 validate_project.py /path/to/project --format json
    python3 validate_project.py /path/to/project --strict
"""

import argparse
import json
import os
import re
import sys


MANIFESTS = [
    "package.json",
    "requirements.txt",
    "pyproject.toml",
    "go.mod",
    "Cargo.toml",
    "pubspec.yaml",
    "Gemfile",
    "pom.xml",
    "build.gradle",
    "build.gradle.kts",
]

CODE_EXTENSIONS = {
    ".py", ".js", ".ts", ".tsx", ".jsx", ".go", ".rs", ".rb",
    ".dart", ".java", ".kt", ".swift", ".cs", ".cpp", ".c",
}

TEST_PATTERNS = [
    r"test_.*\.py$",
    r".*_test\.py$",
    r".*\.test\.[jt]sx?$",
    r".*\.spec\.[jt]sx?$",
    r".*_test\.go$",
    r".*_test\.rs$",
    r".*_test\.dart$",
    r"test/.*",
    r"tests/.*",
    r"spec/.*",
    r"__tests__/.*",
]

PLACEHOLDER_PATTERNS = [
    r"\bTODO\b",
    r"\bFIXME\b",
    r"\bHACK\b",
    r"//\s*implement",
    r"#\s*implement",
    r'raise NotImplementedError',
    r"pass\s*$",
    r"\.\.\.  # placeholder",
]

ENV_VAR_PATTERNS = [
    r"process\.env\.\w+",
    r"os\.environ\[",
    r"os\.getenv\(",
    r"env\(",
    r"std::env::var",
    r"os\.Getenv\(",
    r"ENV\[",
    r"Platform\.environment\[",
]


def find_files(root):
    """Walk directory, skip hidden dirs and common vendor dirs."""
    skip = {".git", "node_modules", ".next", "__pycache__", "target", ".dart_tool",
            "build", "dist", ".venv", "venv", "vendor", ".turbo"}
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in skip]
        for f in filenames:
            yield os.path.join(dirpath, f)


def check_readme(root):
    path = os.path.join(root, "README.md")
    if not os.path.isfile(path):
        return {"name": "readme", "status": "FAIL", "message": "README.md missing"}
    size = os.path.getsize(path)
    if size < 50:
        return {"name": "readme", "status": "WARN", "message": f"README.md is only {size} bytes — likely incomplete"}
    return {"name": "readme", "status": "PASS", "message": f"README.md exists ({size} bytes)"}


def check_gitignore(root):
    path = os.path.join(root, ".gitignore")
    if not os.path.isfile(path):
        return {"name": "gitignore", "status": "FAIL", "message": ".gitignore missing"}
    return {"name": "gitignore", "status": "PASS", "message": ".gitignore exists"}


def check_env_example(root, all_files):
    uses_env = False
    for filepath in all_files:
        ext = os.path.splitext(filepath)[1]
        if ext not in CODE_EXTENSIONS:
            continue
        try:
            content = open(filepath, "r", encoding="utf-8", errors="ignore").read()
        except (OSError, UnicodeDecodeError):
            continue
        for pattern in ENV_VAR_PATTERNS:
            if re.search(pattern, content):
                uses_env = True
                break
        if uses_env:
            break

    if not uses_env:
        return {"name": "env_example", "status": "PASS", "message": "No env vars detected — .env.example not required"}

    path = os.path.join(root, ".env.example")
    if not os.path.isfile(path):
        return {"name": "env_example", "status": "FAIL", "message": "Code references env vars but .env.example is missing"}
    return {"name": "env_example", "status": "PASS", "message": ".env.example exists"}


def check_no_env_file(root):
    path = os.path.join(root, ".env")
    if os.path.isfile(path):
        return {"name": "no_env_committed", "status": "FAIL", "message": ".env file found — secrets may be committed"}
    return {"name": "no_env_committed", "status": "PASS", "message": "No .env file committed"}


def check_manifest(root):
    for manifest in MANIFESTS:
        if os.path.isfile(os.path.join(root, manifest)):
            return {"name": "manifest", "status": "PASS", "message": f"Package manifest found: {manifest}"}
    return {"name": "manifest", "status": "FAIL", "message": "No package manifest found (package.json, requirements.txt, go.mod, etc.)"}


def check_tests(all_files, root):
    for filepath in all_files:
        rel = os.path.relpath(filepath, root)
        for pattern in TEST_PATTERNS:
            if re.search(pattern, rel):
                return {"name": "tests", "status": "PASS", "message": f"Test file found: {rel}"}
    return {"name": "tests", "status": "FAIL", "message": "No test files found"}


def check_placeholders(all_files, root):
    findings = []
    for filepath in all_files:
        ext = os.path.splitext(filepath)[1]
        if ext not in CODE_EXTENSIONS:
            continue
        try:
            lines = open(filepath, "r", encoding="utf-8", errors="ignore").readlines()
        except (OSError, UnicodeDecodeError):
            continue
        for i, line in enumerate(lines, 1):
            for pattern in PLACEHOLDER_PATTERNS:
                if re.search(pattern, line):
                    rel = os.path.relpath(filepath, root)
                    findings.append(f"{rel}:{i}")
                    break

    if not findings:
        return {"name": "placeholders", "status": "PASS", "message": "No TODO/FIXME/placeholder code found"}
    if len(findings) <= 3:
        return {"name": "placeholders", "status": "WARN",
                "message": f"{len(findings)} placeholder(s) found: {', '.join(findings)}"}
    return {"name": "placeholders", "status": "FAIL",
            "message": f"{len(findings)} placeholders found (showing first 5): {', '.join(findings[:5])}"}


def run_checks(root, strict):
    all_files = list(find_files(root))
    checks = [
        check_readme(root),
        check_gitignore(root),
        check_manifest(root),
        check_env_example(root, all_files),
        check_no_env_file(root),
        check_tests(all_files, root),
        check_placeholders(all_files, root),
    ]

    passes = sum(1 for c in checks if c["status"] == "PASS")
    warns = sum(1 for c in checks if c["status"] == "WARN")
    fails = sum(1 for c in checks if c["status"] == "FAIL")

    if strict:
        overall = "PASS" if fails == 0 and warns == 0 else "FAIL"
    else:
        overall = "PASS" if fails == 0 else "FAIL"

    return {
        "project": root,
        "files_scanned": len(all_files),
        "checks": checks,
        "summary": {"pass": passes, "warn": warns, "fail": fails},
        "overall": overall,
    }


def print_report(result):
    print("=" * 60)
    print("PROJECT VALIDATION REPORT")
    print("=" * 60)
    print(f"Project: {result['project']}")
    print(f"Files scanned: {result['files_scanned']}")
    print()

    for check in result["checks"]:
        icon = {"PASS": "  \u2705", "WARN": "  \u26a0\ufe0f", "FAIL": "  \u274c"}[check["status"]]
        print(f"{icon} [{check['status']}] {check['name']}: {check['message']}")

    s = result["summary"]
    print()
    print(f"Results: {s['pass']} pass, {s['warn']} warn, {s['fail']} fail")

    indicator = "\u2705" if result["overall"] == "PASS" else "\u274c"
    print(f"Overall: {indicator} {result['overall']}")
    print("=" * 60)


def main():
    parser = argparse.ArgumentParser(
        description="Validate a generated project directory for common issues."
    )
    parser.add_argument("path", help="Path to the project directory to validate")
    parser.add_argument("--format", choices=["text", "json"], default="text",
                        help="Output format (default: text)")
    parser.add_argument("--strict", action="store_true",
                        help="Treat warnings as failures")
    args = parser.parse_args()

    if not os.path.isdir(args.path):
        print(f"Error: not a directory: {args.path}", file=sys.stderr)
        sys.exit(1)

    result = run_checks(os.path.abspath(args.path), args.strict)

    if args.format == "json":
        print(json.dumps(result, indent=2))
    else:
        print_report(result)

    sys.exit(0 if result["overall"] == "PASS" else 1)


if __name__ == "__main__":
    main()
