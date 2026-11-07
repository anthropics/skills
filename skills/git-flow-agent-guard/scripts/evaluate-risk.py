#!/usr/bin/env python3
"""Risk Evaluation Engine - scores change risk and gates auto-merging per SKILL.md matrix."""
import argparse
import json
import os
import sys
from typing import Dict

# Add lib to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "lib"))

from guard import (
    auto_merge_allowed,
    calculate_blast_radius,
    calculate_revert_cost,
    calculate_risk_scores,
    ensure_log_dir,
    get_changed_files,
    get_git_diff_stat,
    load_config,
    run_verification_commands,
    write_log,
)


def evaluate_diff(target_branch: str) -> Dict:
    log_dir = ensure_log_dir()
    config = load_config()

    diff_stat = get_git_diff_stat(target_branch)
    changed_files = get_changed_files(target_branch)
    files_changed = len(changed_files)

    dev_risk, main_risk = calculate_risk_scores(files_changed)
    blast_radius = calculate_blast_radius(files_changed)
    revert_cost = calculate_revert_cost(changed_files, config)

    # Auto-merge decision (main never auto-merges per SKILL.md)
    auto_merge = auto_merge_allowed(dev_risk, blast_radius, revert_cost, target_branch)

    # Run verification commands if configured
    verification_results = run_verification_commands(config)
    all_verification_passed = all(verification_results.values())

    result = {
        "dev_risk_score": dev_risk,
        "main_risk_score": main_risk,
        "blast_radius": blast_radius,
        "revert_cost": revert_cost,
        "auto_merge_dev_allowed": auto_merge and all_verification_passed,
        "verification": verification_results,
        "files_changed": files_changed,
        "changed_files": changed_files,
    }

    # Build detailed report
    verification_md = ""
    if verification_results:
        verification_md = "\n## Verification Results\n"
        for name, passed in verification_results.items():
            status = "✅ PASS" if passed else "❌ FAIL"
            verification_md += f"- **{name}:** {status}\n"
        if not all_verification_passed:
            verification_md += "\n⚠️ **Auto-merge blocked: verification failed**\n"

    report = f"""# Risk Evaluation Report

## Target Branch
- `{target_branch}`

## Change Metrics
- Files Changed: {files_changed}
- Diff Stat:
```
{diff_stat or "(no changes)"}
```

## Changed Files
{chr(10).join(f"- `{f}`" for f in changed_files) if changed_files else "No changes"}

## Risk Scores
- **Dev Risk (1-5):** {dev_risk}
- **Main Risk (1-5):** {main_risk}
- **Blast Radius:** {blast_radius}
- **Revert Cost:** {revert_cost}

## Auto-Merge Decision
- **Auto-merge to `{target_branch}` allowed:** {'✅ YES' if result["auto_merge_dev_allowed"] else '❌ NO (requires human review)'}
{verification_md}

## Decision Matrix Reference (SKILL.md)
| Dev Risk | Blast Radius | Revert Cost | Action |
|----------|--------------|-------------|--------|
| 1–3      | ANY          | ANY         | Auto-merge allowed |
| 4        | LOW          | LOW         | Auto-merge allowed |
| 4        | MEDIUM/HIGH  | ANY         | Human review required |
| 5        | ANY          | ANY         | Human review required |

> **Note:** `main` branch never auto-merges (requires human sign-off, remote CI, release candidate).
"""

    log_path = write_log(log_dir, "LAST_RISK_EVALUATION.md", report)

    # Print JSON for machine consumption
    print(json.dumps(result, indent=2))
    print(f"\nDetailed log written to {log_path}")
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Evaluate change risk for auto-merge gating")
    parser.add_argument("--target", default="dev", help="Target branch to evaluate against (default: dev)")
    args = parser.parse_args()
    evaluate_diff(args.target)
