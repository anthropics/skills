#!/usr/bin/env python3
"""Audit existing SLO definitions for the common bugs.

Reads markdown or JSON SLO docs and reports:
  FAIL — definitely wrong (target ≥ 99.99 with no engineering investment plan,
         no SLI definition, no error budget policy, CPU-as-SLI)
  WARN — probably wrong (target ≤ 99.0, window outside 7-90 days)

Use as a pre-merge gate before SLOs go live.
"""
import argparse
import json
import os
import re
import sys

CPU_AS_SLI_PATTERNS = [
    r"\bcpu_usage\b",
    r"\bcpu_utilization\b",
    r"\bmemory_usage\b",
    r"\bmem_used\b",
    r"\bdisk_usage\b",
    r"\bdisk_full\b",
]

SLI_KEYWORDS = ("numerator", "denominator", "sli")
POLICY_KEYWORDS = ("policy", "error_budget", "error budget")


def _read(path):
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as f:
            return f.read()
    except OSError:
        return ""


def _parse_target(text):
    m = re.search(r"target[:\s\"]+(\d+(?:\.\d+)?)\s*%?", text, re.IGNORECASE)
    if m:
        return float(m.group(1))
    return None


def _parse_window_days(text):
    m = re.search(r"window[_\-\s]?days?[:\s\"]+(\d+)", text, re.IGNORECASE)
    if m:
        return int(m.group(1))
    m = re.search(r"window[:\s\"]+(\d+)\s*days?", text, re.IGNORECASE)
    if m:
        return int(m.group(1))
    return None


def _has_any(text, keywords):
    low = text.lower()
    return any(k in low for k in keywords)


def _has_cpu_as_sli(text):
    for pat in CPU_AS_SLI_PATTERNS:
        if re.search(pat, text, re.IGNORECASE):
            return True
    return False


# Embedded sample SLO doc — intentionally flawed (target too high, CPU-as-SLI,
# no error budget policy) so --sample exercises several finding paths.
SAMPLE_SLO_DOC = """# Checkout API SLO
target: 99.995%
window_days: 28
sli: cpu_usage below 80%
"""


def audit_text(text):
    findings = []
    target = _parse_target(text)
    window_days = _parse_window_days(text)

    if target is None:
        findings.append(("FAIL", "no_target", "no SLO target (X%) found in document"))
    else:
        if target >= 99.99:
            findings.append(("FAIL", "target_too_high",
                             f"target {target}% ≥ 99.99% — sustainable only with massive engineering investment; document the investment plan or lower"))
        elif target <= 99.0:
            findings.append(("WARN", "target_too_low",
                             f"target {target}% ≤ 99% — likely wrong SLI; users will notice"))

    if window_days is None:
        findings.append(("WARN", "no_window", "no compliance window found"))
    else:
        if window_days < 7:
            findings.append(("FAIL", "window_too_short",
                             f"window {window_days}d < 7d — statistical noise dominates"))
        elif window_days > 90:
            findings.append(("WARN", "window_too_long",
                             f"window {window_days}d > 90d — feedback too slow"))

    if not _has_any(text, SLI_KEYWORDS):
        findings.append(("FAIL", "no_sli_definition",
                         "no SLI definition (numerator/denominator) found"))
    if not _has_any(text, POLICY_KEYWORDS):
        findings.append(("FAIL", "no_error_budget_policy",
                         "no error budget policy reference found"))
    if _has_cpu_as_sli(text):
        findings.append(("FAIL", "cpu_as_sli",
                         "CPU/memory/disk-usage referenced — system metrics aren't user experience; pick a request-level SLI"))

    return findings


def audit_one(path):
    return audit_text(_read(path))


def _walk(target):
    if os.path.isfile(target):
        yield target
        return
    for r, _, files in os.walk(target):
        for f in files:
            if f.endswith((".md", ".json", ".yaml", ".yml")):
                yield os.path.join(r, f)


def audit(target):
    results = []
    for path in _walk(target):
        findings = audit_one(path)
        if findings:
            results.append({"path": path, "findings": findings})
    return results


def render_text(results):
    fails = sum(1 for r in results for f in r["findings"] if f[0] == "FAIL")
    warns = sum(1 for r in results for f in r["findings"] if f[0] == "WARN")
    print(f"SLO Review — {len(results)} doc(s) with findings, {fails} FAIL, {warns} WARN")
    print("")
    if not results:
        print("PASS: no issues detected.")
        return 0
    for r in results:
        print(f"== {r['path']}")
        for level, key, msg in r["findings"]:
            print(f"   [{level}] {key}: {msg}")
        print("")
    return 1 if fails else 0


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--slo-doc", help="Path to SLO doc or directory of docs")
    ap.add_argument("--format", choices=["text", "json"], default="text")
    ap.add_argument("--sample", action="store_true", help="Audit an embedded sample SLO doc")
    args = ap.parse_args()

    if args.sample:
        results = [{"path": "<embedded sample>", "findings": audit_text(SAMPLE_SLO_DOC)}]
    else:
        if not args.slo_doc:
            ap.error("--slo-doc is required (or use --sample)")
        if not os.path.exists(args.slo_doc):
            print(f"ERROR: not found: {args.slo_doc}", file=sys.stderr)
            return 2
        results = audit(args.slo_doc)
    if args.format == "json":
        print(json.dumps(results, indent=2))
        return 1 if any(f[0] == "FAIL" for r in results for f in r["findings"]) else 0
    return render_text(results)


if __name__ == "__main__":
    sys.exit(main())
