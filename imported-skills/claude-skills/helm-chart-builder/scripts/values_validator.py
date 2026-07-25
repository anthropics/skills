#!/usr/bin/env python3
"""
helm-chart-builder: Values Validator

Validate values.yaml files against Helm best practices — documentation coverage,
type consistency, naming conventions, default quality, and security.

Usage:
    python scripts/values_validator.py values.yaml
    python scripts/values_validator.py values.yaml --output json
    python scripts/values_validator.py values.yaml --strict
"""

import argparse
import json
import re
import sys
from pathlib import Path


# --- Demo values.yaml ---

DEMO_VALUES = """# Default values for demo-app
replicaCount: 1

image:
  repository: nginx
  tag: latest
  pullPolicy: Always

service:
  type: ClusterIP
  port: 80

ingress:
  enabled: false

resources: {}

PASSWORD: supersecret123
db_password: changeme
api-key: sk-12345

deeply:
  nested:
    structure:
      that:
        goes:
          too:
            deep: true

undocumented_value: something
AnotherValue: 42
snake_case_key: bad
"""


# --- Validation Rules ---

NAMING_PATTERN = re.compile(r"^[a-z][a-zA-Z0-9]*$")  # camelCase
SNAKE_CASE_PATTERN = re.compile(r"^[a-z][a-z0-9]*(_[a-z0-9]+)+$")  # snake_case
UPPER_CASE_PATTERN = re.compile(r"^[A-Z]")  # Starts with uppercase

SECRET_KEY_PATTERNS = [
    re.compile(r"(?:password|secret|token|apiKey|api_key|api-key|private_key|credentials)", re.IGNORECASE),
]

KNOWN_STRUCTURES = {
    "image": ["repository", "tag", "pullPolicy"],
    "service": ["type", "port"],
    "ingress": ["enabled"],
    "resources": [],
    "serviceAccount": ["create", "name"],
    "autoscaling": ["enabled", "minReplicas", "maxReplicas"],
}


def parse_values(content):
    """Parse values.yaml into structured data with metadata.

    Returns a list of entries with key paths, values, depth, and comment info.
    """
    entries = []
    key_stack = []
    indent_stack = [0]
    prev_comment = None

    for line_num, line in enumerate(content.splitlines(), 1):
        stripped = line.strip()

        # Track comments for documentation coverage
        if stripped.startswith("#"):
            prev_comment = stripped
            continue

        if not stripped:
            prev_comment = None
            continue

        indent = len(line) - len(line.lstrip())

        # Pop stack for dedented lines
        while len(indent_stack) > 1 and indent <= indent_stack[-1]:
            indent_stack.pop()
            if key_stack:
                key_stack.pop()

        # Parse key: value
        match = re.match(r"^(\S+)\s*:\s*(.*)", stripped)
        if match and not stripped.startswith("-"):
            key = match.group(1)
            raw_value = match.group(2).strip()

            # Check for inline comment
            inline_comment = None
            if "#" in raw_value:
                val_part, _, comment_part = raw_value.partition("#")
                raw_value = val_part.strip()
                inline_comment = comment_part.strip()

            # Build full key path
            full_path = ".".join(key_stack + [key])
            depth = len(key_stack) + 1

            # Determine value type
            value_type = "unknown"
            if not raw_value or raw_value == "":
                value_type = "map"
                key_stack.append(key)
                indent_stack.append(indent)
            elif raw_value in ("true", "false"):
                value_type = "boolean"
            elif raw_value == "null" or raw_value == "~":
                value_type = "null"
            elif raw_value == "{}":
                value_type = "empty_map"
            elif raw_value == "[]":
                value_type = "empty_list"
            elif re.match(r"^-?\d+$", raw_value):
                value_type = "integer"
            elif re.match(r"^-?\d+\.\d+$", raw_value):
                value_type = "float"
            elif raw_value.startswith('"') or raw_value.startswith("'"):
                value_type = "string"
            else:
                value_type = "string"

            has_doc = prev_comment is not None or inline_comment is not None

            entries.append({
                "key": key,
                "full_path": full_path,
                "value": raw_value,
                "value_type": value_type,
                "depth": depth,
                "line": line_num,
                "has_documentation": has_doc,
                "comment": prev_comment or inline_comment,
            })

            prev_comment = None
        else:
            prev_comment = None

    return entries


def validate_naming(entries):
    """Check key naming conventions."""
    findings = []

    for entry in entries:
        key = entry["key"]

        # Skip map entries (they're parent keys)
        if entry["value_type"] == "map":
            # Parent keys should still be camelCase
            pass

        if SNAKE_CASE_PATTERN.match(key):
            findings.append({
                "severity": "medium",
                "category": "naming",
                "message": f"Key '{entry['full_path']}' uses snake_case — Helm convention is camelCase",
                "fix": f"Rename to camelCase: {to_camel_case(key)}",
                "line": entry["line"],
            })
        elif UPPER_CASE_PATTERN.match(key) and not key.isupper():
            findings.append({
                "severity": "medium",
                "category": "naming",
                "message": f"Key '{entry['full_path']}' starts with uppercase — use camelCase",
                "fix": f"Rename: {key[0].lower() + key[1:]}",
                "line": entry["line"],
            })
        elif "-" in key:
            findings.append({
                "severity": "medium",
                "category": "naming",
                "message": f"Key '{entry['full_path']}' uses kebab-case — Helm convention is camelCase",
                "fix": f"Rename to camelCase: {to_camel_case(key)}",
                "line": entry["line"],
            })

    return findings


def validate_documentation(entries):
    """Check documentation coverage."""
    findings = []
    total = len(entries)
    documented = sum(1 for e in entries if e["has_documentation"])

    if total > 0:
        coverage = (documented / total) * 100
        if coverage < 50:
            findings.append({
                "severity": "high",
                "category": "documentation",
                "message": f"Only {coverage:.0f}% of values have comments ({documented}/{total})",
                "fix": "Add inline YAML comments explaining purpose, type, and valid options for each value",
                "line": 0,
            })
        elif coverage < 80:
            findings.append({
                "severity": "medium",
                "category": "documentation",
                "message": f"{coverage:.0f}% documentation coverage ({documented}/{total}) — aim for 80%+",
                "fix": "Add comments for undocumented values",
                "line": 0,
            })

    # Flag specific undocumented top-level keys
    for entry in entries:
        if entry["depth"] == 1 and not entry["has_documentation"]:
            findings.append({
                "severity": "low",
                "category": "documentation",
                "message": f"Top-level key '{entry['key']}' has no comment",
                "fix": f"Add a comment above '{entry['key']}' explaining its purpose",
                "line": entry["line"],
            })

    return findings


def validate_defaults(entries):
    """Check default value quality."""
    findings = []

    for entry in entries:
        # Check for :latest tag
        if entry["key"] == "tag" and entry["value"] in ("latest", '"latest"', "'latest'"):
            findings.append({
                "severity": "high",
                "category": "defaults",
                "message": f"image.tag defaults to 'latest' — not reproducible",
                "fix": "Use a specific version tag or reference .Chart.AppVersion in template",
                "line": entry["line"],
            })

        # Check pullPolicy
        if entry["key"] == "pullPolicy" and entry["value"] in ("Always", '"Always"', "'Always'"):
            findings.append({
                "severity": "low",
                "category": "defaults",
                "message": "imagePullPolicy defaults to 'Always' — 'IfNotPresent' is better for production",
                "fix": "Change default to IfNotPresent (Always is appropriate for :latest only)",
                "line": entry["line"],
            })

        # Check empty resources
        if entry["key"] == "resources" and entry["value_type"] == "empty_map":
            findings.append({
                "severity": "medium",
                "category": "defaults",
                "message": "resources defaults to {} — no requests or limits set",
                "fix": "Provide default resource requests (e.g., cpu: 100m, memory: 128Mi)",
                "line": entry["line"],
            })

    return findings


def validate_secrets(entries):
    """Check for secrets in default values."""
    findings = []

    for entry in entries:
        for pattern in SECRET_KEY_PATTERNS:
            if pattern.search(entry["full_path"]):
                val = entry["value"].strip("'\"")
                if val and val not in ("", "null", "~", "{}", "[]", "changeme", "CHANGEME", "TODO", '""', "''"):
                    findings.append({
                        "severity": "critical",
                        "category": "security",
                        "message": f"Potential secret with default value: {entry['full_path']} = {val[:30]}...",
                        "fix": "Remove default. Use empty string, null, or 'changeme' placeholder with comment",
                        "line": entry["line"],
                    })
                break

    return findings


def validate_depth(entries):
    """Check nesting depth."""
    findings = []
    max_depth = max((e["depth"] for e in entries), default=0)

    if max_depth > 4:
        deep_entries = [e for e in entries if e["depth"] > 4]
        for entry in deep_entries[:3]:  # Report first 3
            findings.append({
                "severity": "medium",
                "category": "structure",
                "message": f"Deeply nested key ({entry['depth']} levels): {entry['full_path']}",
                "fix": "Flatten structure — max 3-4 levels deep for usability",
                "line": entry["line"],
            })

    return findings


def to_camel_case(name):
    """Convert snake_case or kebab-case to camelCase."""
    parts = re.split(r"[-_]", name)
    return parts[0].lower() + "".join(p.capitalize() for p in parts[1:])


def generate_report(content, output_format="text", strict=False):
    """Generate full validation report."""
    entries = parse_values(content)
    findings = []

    findings.extend(validate_naming(entries))
    findings.extend(validate_documentation(entries))
    findings.extend(validate_defaults(entries))
    findings.extend(validate_secrets(entries))
    findings.extend(validate_depth(entries))

    if strict:
        # Elevate medium to high, low to medium
        for f in findings:
            if f["severity"] == "medium":
                f["severity"] = "high"
            elif f["severity"] == "low":
                f["severity"] = "medium"

    # Sort by severity
    severity_order = {"critical": 0, "high": 1, "medium": 2, "low": 3}
    findings.sort(key=lambda f: severity_order.get(f["severity"], 4))

    # Score
    deductions = {"critical": 25, "high": 15, "medium": 5, "low": 2}
    score = max(0, 100 - sum(deductions.get(f["severity"], 0) for f in findings))

    counts = {
        "critical": sum(1 for f in findings if f["severity"] == "critical"),
        "high": sum(1 for f in findings if f["severity"] == "high"),
        "medium": sum(1 for f in findings if f["severity"] == "medium"),
        "low": sum(1 for f in findings if f["severity"] == "low"),
    }

    # Stats
    total_keys = len(entries)
    documented = sum(1 for e in entries if e["has_documentation"])
    max_depth = max((e["depth"] for e in entries), default=0)

    result = {
        "score": score,
        "total_keys": total_keys,
        "documented_keys": documented,
        "documentation_coverage": f"{(documented / total_keys * 100):.0f}%" if total_keys > 0 else "N/A",
        "max_depth": max_depth,
        "findings": findings,
        "finding_counts": counts,
    }

    if output_format == "json":
        print(json.dumps(result, indent=2))
        return result

    # Text output
    print(f"\n{'=' * 60}")
    print(f"  Values.yaml Validation Report")
    print(f"{'=' * 60}")
    print(f"  Score: {score}/100")
    print(f"  Keys: {total_keys} | Documented: {documented} ({result['documentation_coverage']})")
    print(f"  Max Depth: {max_depth}")
    print()
    print(f"  Findings: {counts['critical']} critical | {counts['high']} high | {counts['medium']} medium | {counts['low']} low")
    print(f"{'─' * 60}")

    for f in findings:
        icon = {"critical": "!!!", "high": "!!", "medium": "!", "low": "~"}.get(f["severity"], "?")
        print(f"\n  {icon} {f['severity'].upper()} [{f['category']}]")
        print(f"  {f['message']}")
        if f.get("line", 0) > 0:
            print(f"  Line: {f['line']}")
        print(f"  Fix:  {f['fix']}")

    if not findings:
        print("\n  No issues found. Values file looks good.")

    print(f"\n{'=' * 60}\n")
    return result


def main():
    parser = argparse.ArgumentParser(
        description="helm-chart-builder: values.yaml best-practice validator"
    )
    parser.add_argument("valuesfile", nargs="?", help="Path to values.yaml (omit for demo)")
    parser.add_argument(
        "--output", "-o",
        choices=["text", "json"],
        default="text",
        help="Output format (default: text)",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Strict mode — elevate warnings to higher severity",
    )
    args = parser.parse_args()

    if args.valuesfile:
        path = Path(args.valuesfile)
        if not path.exists():
            print(f"Error: File not found: {args.valuesfile}", file=sys.stderr)
            sys.exit(1)
        content = path.read_text(encoding="utf-8")
    else:
        print("No values file provided. Running demo validation...\n")
        content = DEMO_VALUES

    generate_report(content, args.output, args.strict)


if __name__ == "__main__":
    main()
