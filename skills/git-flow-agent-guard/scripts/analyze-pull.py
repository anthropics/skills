#!/usr/bin/env python3
"""Upstream Pull Reconciliation Analysis - detects overlapping file conflicts before merge/rebase."""
import argparse
import os
import sys

# Add lib to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "lib"))

from guard import ensure_log_dir, run_cmd, write_log


def analyze(target_branch: str) -> int:
    log_dir = ensure_log_dir()

    run_cmd(f"git fetch origin {target_branch}")
    base_hash = run_cmd(f"git merge-base HEAD origin/{target_branch}")
    local_hash = run_cmd("git rev-parse HEAD")
    upstream_hash = run_cmd(f"git rev-parse origin/{target_branch}")

    local_files = set(run_cmd(f"git diff --name-only {base_hash} HEAD").splitlines())
    upstream_files = set(run_cmd(f"git diff --name-only {base_hash} origin/{target_branch}").splitlines())

    overlapping = sorted(local_files.intersection(upstream_files))

    report = f"""# Upstream Pull Reconciliation Analysis

## Synchronization Metadata
- Local HEAD: `{local_hash[:7]}`
- Upstream (`origin/{target_branch}`): `{upstream_hash[:7]}`
- Common Ancestor Base: `{base_hash[:7]}`

## Divergence Metrics
- Local Modified Files: {len(local_files)}
- Upstream Modified Files: {len(upstream_files)}
- **Overlapping/Conflicting Files:** {len(overlapping)}

## Overlapping File Paths
"""
    if overlapping:
        for f in overlapping:
            report += f"- ⚠️ `{f}` (Requires agent reconciliation pass)\n"
    else:
        report += "No file overlaps detected. Clean rebase/merge expected.\n"

    log_path = write_log(log_dir, "LAST_PULL_ANALYSIS.md", report)
    print(f"Analysis written to {log_path} | Overlaps: {len(overlapping)}")
    return len(overlapping)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Analyze upstream pull for conflicts")
    parser.add_argument("--target", default="dev", help="Target branch to analyze (default: dev)")
    args = parser.parse_args()
    sys.exit(analyze(args.target))
