#!/usr/bin/env python3
"""
helm-chart-builder: Chart Analyzer

Static analysis of Helm chart directories for structural issues, template
anti-patterns, missing labels, hardcoded values, and security baseline checks.

Usage:
    python scripts/chart_analyzer.py mychart/
    python scripts/chart_analyzer.py mychart/ --output json
    python scripts/chart_analyzer.py mychart/ --security
"""

import argparse
import json
import re
import sys
from pathlib import Path


# --- Analysis Rules ---

REQUIRED_FILES = [
    {"path": "Chart.yaml", "severity": "critical", "message": "Missing Chart.yaml — not a valid Helm chart"},
    {"path": "values.yaml", "severity": "high", "message": "Missing values.yaml — chart has no configurable defaults"},
    {"path": "templates/_helpers.tpl", "severity": "high", "message": "Missing _helpers.tpl — no shared label/name helpers"},
    {"path": "templates/NOTES.txt", "severity": "medium", "message": "Missing NOTES.txt — no post-install instructions for users"},
    {"path": ".helmignore", "severity": "low", "message": "Missing .helmignore — CI files, .git, tests may be packaged"},
]

CHART_YAML_CHECKS = [
    {"field": "apiVersion", "severity": "critical", "message": "Missing apiVersion in Chart.yaml"},
    {"field": "name", "severity": "critical", "message": "Missing name in Chart.yaml"},
    {"field": "version", "severity": "critical", "message": "Missing version in Chart.yaml"},
    {"field": "description", "severity": "medium", "message": "Missing description in Chart.yaml"},
    {"field": "appVersion", "severity": "medium", "message": "Missing appVersion in Chart.yaml — operators won't know what app version is deployed"},
    {"field": "type", "severity": "low", "message": "Missing type in Chart.yaml — defaults to 'application'"},
]

TEMPLATE_ANTI_PATTERNS = [
    {
        "id": "TP001",
        "severity": "high",
        "pattern": r'image:\s*["\']?[a-z][a-z0-9./-]+:[a-z0-9][a-z0-9._-]*["\']?\s*$',
        "message": "Hardcoded image tag in template — must use .Values.image.repository and .Values.image.tag",
        "fix": 'Use: image: "{{ .Values.image.repository }}:{{ .Values.image.tag | default .Chart.AppVersion }}"',
    },
    {
        "id": "TP002",
        "severity": "high",
        "pattern": r'replicas:\s*\d+\s*$',
        "message": "Hardcoded replica count — must be configurable via values",
        "fix": "Use: replicas: {{ .Values.replicaCount }}",
    },
    {
        "id": "TP003",
        "severity": "medium",
        "pattern": r'port:\s*\d+\s*$',
        "message": "Hardcoded port number — should be configurable via values",
        "fix": "Use: port: {{ .Values.service.port }}",
    },
    {
        "id": "TP004",
        "severity": "high",
        "pattern": r'(?:name|namespace):\s*[a-z][a-z0-9-]+\s*$',
        "message": "Hardcoded name/namespace — should use template helpers",
        "fix": 'Use: name: {{ include "mychart.fullname" . }}',
    },
    {
        "id": "TP005",
        "severity": "medium",
        "pattern": r'nodePort:\s*\d+',
        "message": "Hardcoded nodePort — should be configurable or avoided",
        "fix": "Use: nodePort: {{ .Values.service.nodePort }} with conditional",
    },
]

SECURITY_CHECKS = [
    {
        "id": "SC001",
        "severity": "critical",
        "check": "no_security_context",
        "message": "No securityContext found in any template — pods run as root with full capabilities",
        "fix": "Add pod and container securityContext with runAsNonRoot, readOnlyRootFilesystem, drop ALL capabilities",
    },
    {
        "id": "SC002",
        "severity": "critical",
        "check": "privileged_container",
        "message": "Privileged container detected — full host access",
        "fix": "Remove privileged: true. Use specific capabilities instead",
    },
    {
        "id": "SC003",
        "severity": "high",
        "check": "no_run_as_non_root",
        "message": "No runAsNonRoot: true — container may run as root",
        "fix": "Add runAsNonRoot: true to pod securityContext",
    },
    {
        "id": "SC004",
        "severity": "high",
        "check": "no_readonly_rootfs",
        "message": "No readOnlyRootFilesystem — container filesystem is writable",
        "fix": "Add readOnlyRootFilesystem: true and use emptyDir for writable paths",
    },
    {
        "id": "SC005",
        "severity": "medium",
        "check": "no_network_policy",
        "message": "No NetworkPolicy template — all pod-to-pod traffic allowed",
        "fix": "Add a NetworkPolicy template with default-deny ingress and explicit allow rules",
    },
    {
        "id": "SC006",
        "severity": "medium",
        "check": "automount_sa_token",
        "message": "automountServiceAccountToken not set to false — pod can access K8s API",
        "fix": "Set automountServiceAccountToken: false unless the pod needs K8s API access",
    },
    {
        "id": "SC007",
        "severity": "high",
        "check": "host_network",
        "message": "hostNetwork: true — pod shares host network namespace",
        "fix": "Remove hostNetwork unless absolutely required (e.g., CNI plugin)",
    },
    {
        "id": "SC008",
        "severity": "critical",
        "check": "host_pid_ipc",
        "message": "hostPID or hostIPC enabled — pod can see host processes/IPC",
        "fix": "Remove hostPID and hostIPC — never needed in application charts",
    },
]

LABEL_PATTERNS = [
    r"app\.kubernetes\.io/name",
    r"app\.kubernetes\.io/instance",
    r"app\.kubernetes\.io/version",
    r"app\.kubernetes\.io/managed-by",
    r"helm\.sh/chart",
]


# --- Demo Chart ---

DEMO_CHART_YAML = """apiVersion: v2
name: demo-app
version: 0.1.0
"""

DEMO_VALUES_YAML = """replicaCount: 1

image:
  repository: nginx
  tag: latest
  pullPolicy: Always

service:
  type: ClusterIP
  port: 80
"""

DEMO_DEPLOYMENT = """apiVersion: apps/v1
kind: Deployment
metadata:
  name: demo-app
spec:
  replicas: 3
  template:
    spec:
      containers:
        - name: demo-app
          image: nginx:1.25
          ports:
            - containerPort: 80
"""


def parse_yaml_simple(content):
    """Simple key-value parser for YAML (stdlib only)."""
    result = {}
    for line in content.splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        if ":" in stripped and not stripped.startswith("-"):
            key, _, val = stripped.partition(":")
            key = key.strip()
            val = val.strip().strip("'\"")
            if val:
                result[key] = val
    return result


def check_structure(chart_dir):
    """Check chart directory for required files."""
    findings = []
    for check in REQUIRED_FILES:
        path = chart_dir / check["path"]
        if not path.exists():
            findings.append({
                "id": "ST" + str(REQUIRED_FILES.index(check) + 1).zfill(3),
                "severity": check["severity"],
                "message": check["message"],
                "fix": f"Create {check['path']}",
                "file": check["path"],
            })
    return findings


def check_chart_yaml(chart_dir):
    """Validate Chart.yaml metadata."""
    findings = []
    chart_path = chart_dir / "Chart.yaml"
    if not chart_path.exists():
        return findings

    content = chart_path.read_text(encoding="utf-8")
    parsed = parse_yaml_simple(content)

    for check in CHART_YAML_CHECKS:
        if check["field"] not in parsed:
            findings.append({
                "id": "CY" + str(CHART_YAML_CHECKS.index(check) + 1).zfill(3),
                "severity": check["severity"],
                "message": check["message"],
                "fix": f"Add '{check['field']}:' to Chart.yaml",
                "file": "Chart.yaml",
            })

    # Check apiVersion value
    if parsed.get("apiVersion") == "v1":
        findings.append({
            "id": "CY007",
            "severity": "medium",
            "message": "apiVersion: v1 is Helm 2 format — use v2 for Helm 3",
            "fix": "Change apiVersion to v2",
            "file": "Chart.yaml",
        })

    # Check version is semver
    version = parsed.get("version", "")
    if version and not re.match(r"^\d+\.\d+\.\d+", version):
        findings.append({
            "id": "CY008",
            "severity": "high",
            "message": f"Version '{version}' is not valid semver",
            "fix": "Use semver format: MAJOR.MINOR.PATCH (e.g., 1.0.0)",
            "file": "Chart.yaml",
        })

    return findings


def check_templates(chart_dir):
    """Scan templates for anti-patterns."""
    findings = []
    templates_dir = chart_dir / "templates"
    if not templates_dir.exists():
        return findings

    template_files = list(templates_dir.glob("*.yaml")) + list(templates_dir.glob("*.yml")) + list(templates_dir.glob("*.tpl"))

    all_content = ""
    for tpl_file in template_files:
        content = tpl_file.read_text(encoding="utf-8")
        all_content += content + "\n"
        rel_path = tpl_file.relative_to(chart_dir)

        for rule in TEMPLATE_ANTI_PATTERNS:
            # Skip patterns that would false-positive on template expressions
            for match in re.finditer(rule["pattern"], content, re.MULTILINE):
                line = match.group(0).strip()
                # Skip if the line contains a template expression
                if "{{" in line or "}}" in line:
                    continue
                findings.append({
                    "id": rule["id"],
                    "severity": rule["severity"],
                    "message": rule["message"],
                    "fix": rule["fix"],
                    "file": str(rel_path),
                    "line": line[:80],
                })

    # Check for standard labels
    helpers_file = templates_dir / "_helpers.tpl"
    if helpers_file.exists():
        helpers_content = helpers_file.read_text(encoding="utf-8")
        for label_pattern in LABEL_PATTERNS:
            if not re.search(label_pattern, helpers_content) and not re.search(label_pattern, all_content):
                label_name = label_pattern.replace("\\.", ".")
                findings.append({
                    "id": "LB001",
                    "severity": "high",
                    "message": f"Standard label '{label_name}' not found in helpers or templates",
                    "fix": f"Add {label_name} to the labels helper in _helpers.tpl",
                    "file": "templates/_helpers.tpl",
                    "line": "(label not found)",
                })

    # Check for resource limits
    if "resources:" not in all_content and template_files:
        findings.append({
            "id": "TP006",
            "severity": "critical",
            "message": "No resource requests/limits in any template — pods can consume unlimited node resources",
            "fix": "Add resources section: {{ toYaml .Values.resources | nindent 12 }}",
            "file": "templates/",
            "line": "(no resources block found)",
        })

    # Check for probes
    if "livenessProbe" not in all_content and "readinessProbe" not in all_content and template_files:
        has_deployment = any("Deployment" in f.read_text(encoding="utf-8") for f in template_files if f.suffix in (".yaml", ".yml"))
        if has_deployment:
            findings.append({
                "id": "TP007",
                "severity": "high",
                "message": "No liveness/readiness probes — Kubernetes cannot detect unhealthy pods",
                "fix": "Add livenessProbe and readinessProbe with configurable values",
                "file": "templates/deployment.yaml",
                "line": "(no probes found)",
            })

    return findings


def check_security(chart_dir):
    """Run security-focused checks."""
    findings = []
    templates_dir = chart_dir / "templates"
    if not templates_dir.exists():
        return findings

    template_files = list(templates_dir.glob("*.yaml")) + list(templates_dir.glob("*.yml"))
    all_content = ""
    for tpl_file in template_files:
        all_content += tpl_file.read_text(encoding="utf-8") + "\n"

    for check in SECURITY_CHECKS:
        triggered = False

        if check["check"] == "no_security_context":
            if "securityContext" not in all_content and template_files:
                triggered = True
        elif check["check"] == "privileged_container":
            if re.search(r"privileged:\s*true", all_content):
                triggered = True
        elif check["check"] == "no_run_as_non_root":
            if "securityContext" in all_content and "runAsNonRoot" not in all_content:
                triggered = True
        elif check["check"] == "no_readonly_rootfs":
            if "securityContext" in all_content and "readOnlyRootFilesystem" not in all_content:
                triggered = True
        elif check["check"] == "no_network_policy":
            np_file = templates_dir / "networkpolicy.yaml"
            if not np_file.exists() and "NetworkPolicy" not in all_content:
                triggered = True
        elif check["check"] == "automount_sa_token":
            if "automountServiceAccountToken" not in all_content and template_files:
                triggered = True
        elif check["check"] == "host_network":
            if re.search(r"hostNetwork:\s*true", all_content):
                triggered = True
        elif check["check"] == "host_pid_ipc":
            if re.search(r"host(?:PID|IPC):\s*true", all_content):
                triggered = True

        if triggered:
            findings.append({
                "id": check["id"],
                "severity": check["severity"],
                "message": check["message"],
                "fix": check["fix"],
                "file": "templates/",
            })

    # Check for secrets in values.yaml
    values_path = chart_dir / "values.yaml"
    if values_path.exists():
        values_content = values_path.read_text(encoding="utf-8")
        for match in re.finditer(r"^(\s*\S*(?:password|secret|token|apiKey|api_key)\s*:\s*)(\S+)", values_content, re.MULTILINE | re.IGNORECASE):
            val = match.group(2).strip("'\"")
            if val and val not in ("null", "~", '""', "''", "changeme", "CHANGEME", "TODO"):
                findings.append({
                    "id": "SC009",
                    "severity": "critical",
                    "message": f"Potential secret in values.yaml default: {match.group(0).strip()[:60]}",
                    "fix": "Remove default secret values. Use empty string or null with documentation",
                    "file": "values.yaml",
                    "line": match.group(0).strip()[:80],
                })

    return findings


def analyze_chart(chart_dir, output_format="text", security_focus=False):
    """Run full chart analysis."""
    findings = []
    findings.extend(check_structure(chart_dir))
    findings.extend(check_chart_yaml(chart_dir))
    findings.extend(check_templates(chart_dir))

    if security_focus:
        findings.extend(check_security(chart_dir))
        # Filter to security-relevant items only
        security_ids = {"SC001", "SC002", "SC003", "SC004", "SC005", "SC006", "SC007", "SC008", "SC009"}
        security_severities = {"critical", "high"}
        findings = [f for f in findings if f["id"] in security_ids or f["severity"] in security_severities]
    else:
        findings.extend(check_security(chart_dir))

    # Deduplicate
    seen = set()
    unique = []
    for f in findings:
        key = (f["id"], f.get("line", ""), f.get("file", ""))
        if key not in seen:
            seen.add(key)
            unique.append(f)
    findings = unique

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

    # Chart metadata
    chart_yaml_path = chart_dir / "Chart.yaml"
    chart_meta = parse_yaml_simple(chart_yaml_path.read_text(encoding="utf-8")) if chart_yaml_path.exists() else {}

    result = {
        "score": score,
        "chart_name": chart_meta.get("name", chart_dir.name),
        "chart_version": chart_meta.get("version", "unknown"),
        "app_version": chart_meta.get("appVersion", "unknown"),
        "findings": findings,
        "finding_counts": counts,
    }

    if output_format == "json":
        print(json.dumps(result, indent=2))
        return result

    # Text output
    print(f"\n{'=' * 60}")
    print(f"  Helm Chart Analysis Report")
    print(f"{'=' * 60}")
    print(f"  Score: {score}/100")
    print(f"  Chart: {result['chart_name']} v{result['chart_version']}")
    print(f"  App Version: {result['app_version']}")
    print()
    print(f"  Findings: {counts['critical']} critical | {counts['high']} high | {counts['medium']} medium | {counts['low']} low")
    print(f"{'─' * 60}")

    for f in findings:
        icon = {"critical": "!!!", "high": "!!", "medium": "!", "low": "~"}.get(f["severity"], "?")
        print(f"\n  [{f['id']}] {icon} {f['severity'].upper()}")
        print(f"  {f['message']}")
        if "file" in f:
            print(f"  File: {f['file']}")
        if "line" in f:
            print(f"  Line: {f['line']}")
        print(f"  Fix:  {f['fix']}")

    if not findings:
        print("\n  No issues found. Chart looks good.")

    print(f"\n{'=' * 60}\n")
    return result


def run_demo():
    """Run analysis on demo chart data."""
    import tempfile
    import os

    with tempfile.TemporaryDirectory() as tmpdir:
        chart_dir = Path(tmpdir) / "demo-app"
        chart_dir.mkdir()
        (chart_dir / "Chart.yaml").write_text(DEMO_CHART_YAML)
        (chart_dir / "values.yaml").write_text(DEMO_VALUES_YAML)
        templates_dir = chart_dir / "templates"
        templates_dir.mkdir()
        (templates_dir / "deployment.yaml").write_text(DEMO_DEPLOYMENT)

        return chart_dir, analyze_chart


def main():
    parser = argparse.ArgumentParser(
        description="helm-chart-builder: Helm chart static analyzer"
    )
    parser.add_argument("chartdir", nargs="?", help="Path to Helm chart directory (omit for demo)")
    parser.add_argument(
        "--output", "-o",
        choices=["text", "json"],
        default="text",
        help="Output format (default: text)",
    )
    parser.add_argument(
        "--security",
        action="store_true",
        help="Security-focused analysis only",
    )
    args = parser.parse_args()

    if args.chartdir:
        chart_dir = Path(args.chartdir)
        if not chart_dir.is_dir():
            print(f"Error: Not a directory: {args.chartdir}", file=sys.stderr)
            sys.exit(1)
        analyze_chart(chart_dir, args.output, args.security)
    else:
        print("No chart directory provided. Running demo analysis...\n")
        import tempfile
        with tempfile.TemporaryDirectory() as tmpdir:
            chart_dir = Path(tmpdir) / "demo-app"
            chart_dir.mkdir()
            (chart_dir / "Chart.yaml").write_text(DEMO_CHART_YAML)
            (chart_dir / "values.yaml").write_text(DEMO_VALUES_YAML)
            templates_dir = chart_dir / "templates"
            templates_dir.mkdir()
            (templates_dir / "deployment.yaml").write_text(DEMO_DEPLOYMENT)
            analyze_chart(chart_dir, args.output, args.security)


if __name__ == "__main__":
    main()
