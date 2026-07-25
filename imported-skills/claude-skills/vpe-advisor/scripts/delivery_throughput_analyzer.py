#!/usr/bin/env python3
"""delivery_throughput_analyzer.py — DORA 4 metrics + bottleneck identification.

Stdlib-only. Takes sprint metrics and outputs:
  - DORA 4 metrics verdict (Deployment Frequency, Lead Time, MTTR, Change Failure Rate)
  - Cycle time breakdown (PR creation -> first review -> approval -> merge -> deploy)
  - Top bottleneck (longest wait stage)
  - DORA performance level (Elite / High / Medium / Low) per metric and overall

Deterministic logic based on DORA thresholds.

Input schema (JSON):
{
  "team_name": "Platform Squad",
  "period_days": 30,
  "deployments_to_prod_in_period": 28,
  "median_lead_time_hours": 48,           # commit -> production
  "median_mttr_hours": 4,                  # incident detect -> resolved
  "incidents_caused_by_deploys": 3,
  "total_deploys_for_failure_rate": 28,
  "cycle_time_stages_median_hours": {
    "pr_creation_to_first_review": 18,
    "first_review_to_approval": 22,
    "approval_to_merge": 4,
    "merge_to_deploy": 4
  }
}

Usage:
    python delivery_throughput_analyzer.py                       # uses embedded sample
    python delivery_throughput_analyzer.py path/to/metrics.json
    python delivery_throughput_analyzer.py metrics.json --output json
"""

import argparse
import json
import sys
from typing import Any, Dict, List


SAMPLE: Dict[str, Any] = {
    "team_name": "Platform Squad",
    "period_days": 30,
    "deployments_to_prod_in_period": 28,
    "median_lead_time_hours": 48,
    "median_mttr_hours": 4,
    "incidents_caused_by_deploys": 3,
    "total_deploys_for_failure_rate": 28,
    "cycle_time_stages_median_hours": {
        "pr_creation_to_first_review": 18,
        "first_review_to_approval": 22,
        "approval_to_merge": 4,
        "merge_to_deploy": 4,
    },
}


# DORA thresholds (from Google's "State of DevOps" 2024-2025)
def deploy_freq_level(deploys_per_period: float, period_days: int) -> str:
    per_day = deploys_per_period / period_days if period_days else 0
    if per_day >= 1:
        return "Elite"
    if per_day >= 1 / 7:     # at least weekly
        return "High"
    if per_day >= 1 / 30:    # at least monthly
        return "Medium"
    return "Low"


def lead_time_level(hours: float) -> str:
    if hours < 1:
        return "Elite"
    if hours <= 24 * 7:      # within a week
        return "High"
    if hours <= 24 * 30:     # within a month
        return "Medium"
    return "Low"


def mttr_level(hours: float) -> str:
    if hours < 1:
        return "Elite"
    if hours <= 24:
        return "High"
    if hours <= 24 * 7:
        return "Medium"
    return "Low"


def failure_rate_level(rate: float) -> str:
    # rate is fraction (0.15 = 15%)
    if rate <= 0.15:
        return "Elite"
    if rate <= 0.30:
        return "High"
    if rate <= 0.45:
        return "Medium"
    return "Low"


LEVEL_RANK = {"Elite": 0, "High": 1, "Medium": 2, "Low": 3}


def overall_level(levels: List[str]) -> str:
    # Overall = worst metric (DORA-aligned: a team is only as good as its slowest dimension)
    worst = max(LEVEL_RANK.get(l, 3) for l in levels)
    for name, rank in LEVEL_RANK.items():
        if rank == worst:
            return name
    return "Low"


def identify_bottleneck(stages: Dict[str, float]) -> Dict[str, Any]:
    if not stages:
        return {"bottleneck_stage": None, "wait_hours": 0, "pct_of_cycle": 0}
    total = sum(stages.values())
    sorted_stages = sorted(stages.items(), key=lambda x: -x[1])
    top_stage, top_hours = sorted_stages[0]
    return {
        "bottleneck_stage": top_stage,
        "wait_hours": top_hours,
        "pct_of_cycle": round((top_hours / total) * 100, 1) if total else 0,
        "total_cycle_hours": total,
    }


# Bottleneck -> typical fix mapping
BOTTLENECK_FIXES = {
    "pr_creation_to_first_review": [
        "Establish reviewer rotation with a 24-hour SLA",
        "Use auto-assign tooling (e.g., CODEOWNERS) to distribute review load",
        "Cap WIP — engineers shouldn't open new PRs while their existing ones wait > 1 day for review",
    ],
    "first_review_to_approval": [
        "Define 'approval' criteria explicitly (one approver vs two, etc.)",
        "Split large PRs — anything > 400 lines gets reviewer fatigue",
        "Pair-review for changes that need two approvers; reduces async ping-pong",
    ],
    "approval_to_merge": [
        "Check for required-but-flaky CI checks; quarantine flaky tests",
        "Automate merge after approval + green CI (auto-merge bot)",
        "Reduce branch-protection ceremony if it's not adding safety",
    ],
    "merge_to_deploy": [
        "Move from scheduled deploys to continuous deployment (or progressive delivery with feature flags)",
        "Remove manual deploy approvals for low-risk changes",
        "Pair with engineering/feature-flags-architect for safe ramp-up patterns",
    ],
}


def analyze(metrics: Dict[str, Any]) -> Dict[str, Any]:
    period_days = metrics.get("period_days", 30)
    deploys = metrics.get("deployments_to_prod_in_period", 0)
    lead_time = metrics.get("median_lead_time_hours", 0)
    mttr = metrics.get("median_mttr_hours", 0)
    incidents = metrics.get("incidents_caused_by_deploys", 0)
    total_deploys = metrics.get("total_deploys_for_failure_rate", deploys or 1)

    df_level = deploy_freq_level(deploys, period_days)
    lt_level = lead_time_level(lead_time)
    mttr_l = mttr_level(mttr)
    failure_rate = incidents / total_deploys if total_deploys else 0
    fr_level = failure_rate_level(failure_rate)

    overall = overall_level([df_level, lt_level, mttr_l, fr_level])

    stages = metrics.get("cycle_time_stages_median_hours", {})
    bottleneck = identify_bottleneck(stages)
    fixes = BOTTLENECK_FIXES.get(bottleneck.get("bottleneck_stage"), [])

    return {
        "team_name": metrics.get("team_name"),
        "dora_metrics": {
            "deployment_frequency": {
                "value_per_day": round(deploys / period_days, 2) if period_days else 0,
                "value_per_period": deploys,
                "level": df_level,
            },
            "lead_time_for_changes": {
                "value_hours": lead_time,
                "level": lt_level,
            },
            "mean_time_to_recovery": {
                "value_hours": mttr,
                "level": mttr_l,
            },
            "change_failure_rate": {
                "value_pct": round(failure_rate * 100, 1),
                "incidents": incidents,
                "deploys": total_deploys,
                "level": fr_level,
            },
        },
        "overall_level": overall,
        "bottleneck": bottleneck,
        "recommended_fixes": fixes,
    }


def render_text(result: Dict[str, Any], source: str) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("DELIVERY THROUGHPUT — DORA METRICS")
    lines.append(f"Source: {source}")
    lines.append("=" * 72)
    lines.append("")
    lines.append(f"Team: {result['team_name']}")
    lines.append(f"Overall DORA level: {result['overall_level']}")
    lines.append("")
    lines.append("-" * 72)

    d = result["dora_metrics"]
    lines.append("DORA 4 METRICS:")
    lines.append("")
    lines.append(f"  Deployment Frequency:   {d['deployment_frequency']['value_per_day']}/day  ({d['deployment_frequency']['value_per_period']} total)    [{d['deployment_frequency']['level']}]")
    lines.append(f"  Lead Time for Changes:  {d['lead_time_for_changes']['value_hours']}h                                       [{d['lead_time_for_changes']['level']}]")
    lines.append(f"  Mean Time to Recovery:  {d['mean_time_to_recovery']['value_hours']}h                                       [{d['mean_time_to_recovery']['level']}]")
    lines.append(f"  Change Failure Rate:    {d['change_failure_rate']['value_pct']}%  ({d['change_failure_rate']['incidents']}/{d['change_failure_rate']['deploys']})                                [{d['change_failure_rate']['level']}]")
    lines.append("")
    lines.append("-" * 72)

    b = result["bottleneck"]
    if b["bottleneck_stage"]:
        lines.append("BOTTLENECK ANALYSIS:")
        lines.append("")
        lines.append(f"  Top wait stage: {b['bottleneck_stage']}")
        lines.append(f"  Wait time: {b['wait_hours']}h ({b['pct_of_cycle']}% of total cycle time {b['total_cycle_hours']}h)")
        lines.append("")
        lines.append("  Recommended fixes:")
        for f in result["recommended_fixes"]:
            lines.append(f"    • {f}")
        lines.append("")

    lines.append("-" * 72)
    lines.append("DORA REMINDER: 4 metrics measure the team, not the engineer. Use them to surface")
    lines.append("operating-model problems (review load, CI flakiness, manual gates), not for performance reviews.")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="DORA 4 metrics + bottleneck identification.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("path", nargs="?", help="Path to metrics JSON (uses embedded sample if omitted)")
    parser.add_argument("--output", choices=("text", "json"), default="text", help="Output format")
    args = parser.parse_args()

    if args.path:
        try:
            with open(args.path, "r", encoding="utf-8") as f:
                metrics = json.load(f)
            source = args.path
        except (IOError, OSError) as e:
            print(f"error: could not read {args.path}: {e}", file=sys.stderr)
            return 1
        except json.JSONDecodeError as e:
            print(f"error: invalid JSON in {args.path}: {e}", file=sys.stderr)
            return 1
    else:
        metrics = SAMPLE
        source = "<embedded sample: 30-day Platform Squad, 28 deploys>"

    result = analyze(metrics)

    if args.output == "json":
        print(json.dumps({"source": source, **result}, indent=2))
    else:
        print(render_text(result, source))

    return 0


if __name__ == "__main__":
    sys.exit(main())
