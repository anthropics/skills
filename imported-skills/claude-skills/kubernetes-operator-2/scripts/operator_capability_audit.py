#!/usr/bin/env python3
"""Score an operator against OperatorHub Capability Levels (1-5).

Walks an operator repo and detects evidence for each level. Level achieved =
highest level for which all required signals are present. Reports next-level
gaps as concrete advancement steps.

Levels:
  L1 Basic Install      — CRD + controller + Deployment manifest
  L2 Seamless Upgrades  — version conversion + PDB + leader election
  L3 Full Lifecycle     — backup/restore + finalizers + status conditions
  L4 Deep Insights      — /metrics endpoint + Prometheus rules
  L5 Auto Pilot         — HPA / VPA / autotuning logic referenced
"""
import argparse
import json
import os
import re
import sys


SIGNALS = {
    "L1": [
        ("crd_present", lambda files, contents: any("CustomResourceDefinition" in c for c in contents.values())),
        ("deployment_present", lambda files, contents: any(re.search(r"^kind:\s*Deployment", c, re.MULTILINE) for c in contents.values())),
        ("controller_code", lambda files, contents: any(p.endswith(".go") and "Reconcile" in c for p, c in contents.items())),
    ],
    "L2": [
        ("conversion_webhook", lambda files, contents: any("conversion" in c.lower() and "webhook" in c.lower() for c in contents.values())),
        ("leader_election", lambda files, contents: any("LeaderElection" in c or "leader-elect" in c for c in contents.values())),
        ("pdb_present", lambda files, contents: any(re.search(r"kind:\s*PodDisruptionBudget", c) for c in contents.values())),
    ],
    "L3": [
        ("finalizers", lambda files, contents: any("Finalizer" in c or "finalizers" in c for c in contents.values())),
        ("status_conditions", lambda files, contents: any("metav1.Condition" in c or "SetStatusCondition" in c for c in contents.values())),
        ("backup_restore_hint", lambda files, contents: any(re.search(r"\b(backup|restore|snapshot)\b", c, re.IGNORECASE) for c in contents.values())),
    ],
    "L4": [
        ("metrics_endpoint", lambda files, contents: any(re.search(r"/metrics|prometheus", c) for c in contents.values())),
        ("prometheus_rules", lambda files, contents: any(re.search(r"PrometheusRule|alert:", c) for c in contents.values())),
    ],
    "L5": [
        ("autoscaling_referenced", lambda files, contents: any(re.search(r"\bHorizontalPodAutoscaler|VerticalPodAutoscaler|autoscal", c) for c in contents.values())),
        ("autotune_logic", lambda files, contents: any(re.search(r"autotune|self-heal|anomaly", c, re.IGNORECASE) for c in contents.values())),
    ],
}

LEVEL_NAMES = {
    "L1": "Basic Install",
    "L2": "Seamless Upgrades",
    "L3": "Full Lifecycle",
    "L4": "Deep Insights",
    "L5": "Auto Pilot",
}

SCAN_EXTS = {".go", ".yaml", ".yml", ".md"}
SKIP_DIRS = {".git", "node_modules", "vendor", "bin", "dist", "__pycache__"}


def _walk(root):
    files = {}
    for r, dirs, fnames in os.walk(root):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS]
        for f in fnames:
            if os.path.splitext(f)[1] in SCAN_EXTS:
                p = os.path.join(r, f)
                try:
                    with open(p, "r", encoding="utf-8", errors="replace") as fh:
                        files[p] = fh.read()
                except OSError:
                    continue
    return files


def evaluate(operator_dir):
    contents = _walk(operator_dir)
    file_paths = list(contents.keys())
    results = {}
    achieved_max = None
    for level in ["L1", "L2", "L3", "L4", "L5"]:
        signals = SIGNALS[level]
        passing = []
        failing = []
        for key, check in signals:
            ok = check(file_paths, contents)
            (passing if ok else failing).append(key)
        all_pass = len(failing) == 0
        results[level] = {
            "name": LEVEL_NAMES[level],
            "passing": passing,
            "missing": failing,
            "achieved": all_pass,
        }
        if all_pass:
            achieved_max = level
        else:
            break
    return {"current_level": achieved_max, "details": results}


def render_text(report, operator_dir):
    print(f"Operator Capability Audit — {operator_dir}")
    current = report["current_level"]
    if current is None:
        print("Current level: BELOW_L1 (no operator structure detected)")
    else:
        print(f"Current level: {current} — {LEVEL_NAMES[current]}")
    print("")
    for level in ["L1", "L2", "L3", "L4", "L5"]:
        d = report["details"].get(level)
        if d is None:
            continue
        marker = "✓" if d["achieved"] else "✗"
        print(f"  {marker} {level} {d['name']}: pass={len(d['passing'])} miss={len(d['missing'])}")
        for k in d["missing"]:
            print(f"      - missing: {k}")
    print("")
    next_level = None
    for lv in ["L1", "L2", "L3", "L4", "L5"]:
        if lv == current:
            continue
        if not report["details"].get(lv, {}).get("achieved"):
            next_level = lv
            break
    if next_level:
        misses = report["details"][next_level]["missing"]
        print(f"Next: advance to {next_level} ({LEVEL_NAMES[next_level]}) by addressing:")
        for k in misses:
            print(f"  - {k}")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--operator-dir", required=True, help="Path to operator repo root")
    ap.add_argument("--format", choices=["text", "json"], default="text")
    args = ap.parse_args()

    if not os.path.isdir(args.operator_dir):
        print(f"ERROR: not a directory: {args.operator_dir}", file=sys.stderr)
        return 2
    report = evaluate(args.operator_dir)
    if args.format == "json":
        print(json.dumps(report, indent=2))
    else:
        render_text(report, args.operator_dir)
    return 0


if __name__ == "__main__":
    sys.exit(main())
