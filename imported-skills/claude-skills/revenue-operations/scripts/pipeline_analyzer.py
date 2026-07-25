#!/usr/bin/env python3
"""Pipeline Analyzer - Analyzes sales pipeline health for SaaS revenue teams.

Calculates pipeline coverage ratios, stage conversion rates, sales velocity,
deal aging risks, and concentration risks from pipeline data.

Usage:
    python pipeline_analyzer.py --input pipeline.json --format text
    python pipeline_analyzer.py --input pipeline.json --format json
"""

import argparse
import json
import sys
from datetime import datetime, date
from typing import Any


def safe_divide(numerator: float, denominator: float, default: float = 0.0) -> float:
    """Safely divide two numbers, returning default if denominator is zero."""
    if denominator == 0:
        return default
    return numerator / denominator


def parse_date(date_str: str) -> date:
    """Parse a date string in YYYY-MM-DD format."""
    return datetime.strptime(date_str, "%Y-%m-%d").date()


def get_quarter(d: date) -> str:
    """Return the quarter string for a given date (e.g., '2025-Q1')."""
    quarter = (d.month - 1) // 3 + 1
    return f"{d.year}-Q{quarter}"


def calculate_coverage_ratio(deals: list[dict], quota: float) -> dict[str, Any]:
    """Calculate pipeline coverage ratio against quota.

    Target: 3-4x pipeline coverage for healthy pipeline.
    """
    total_pipeline = sum(d["value"] for d in deals if d["stage"] != "Closed Won")
    ratio = safe_divide(total_pipeline, quota)

    if ratio >= 4.0:
        rating = "Strong"
    elif ratio >= 3.0:
        rating = "Healthy"
    elif ratio >= 2.0:
        rating = "At Risk"
    else:
        rating = "Critical"

    return {
        "total_pipeline_value": total_pipeline,
        "quota": quota,
        "coverage_ratio": round(ratio, 2),
        "rating": rating,
        "target": "3.0x - 4.0x",
    }


def calculate_stage_conversion_rates(
    deals: list[dict], stages: list[str]
) -> list[dict[str, Any]]:
    """Calculate stage-to-stage conversion rates.

    Measures the percentage of deals that progress from one stage to the next.
    """
    stage_order = {stage: i for i, stage in enumerate(stages)}
    stage_counts: dict[str, int] = {stage: 0 for stage in stages}

    for deal in deals:
        stage = deal["stage"]
        if stage in stage_order:
            stage_idx = stage_order[stage]
            # A deal at stage N has passed through all stages 0..N
            for i in range(stage_idx + 1):
                stage_counts[stages[i]] += 1

    conversions = []
    for i in range(len(stages) - 1):
        from_stage = stages[i]
        to_stage = stages[i + 1]
        from_count = stage_counts[from_stage]
        to_count = stage_counts[to_stage]
        rate = safe_divide(to_count, from_count) * 100

        conversions.append({
            "from_stage": from_stage,
            "to_stage": to_stage,
            "from_count": from_count,
            "to_count": to_count,
            "conversion_rate_pct": round(rate, 1),
        })

    return conversions


def calculate_sales_velocity(deals: list[dict]) -> dict[str, Any]:
    """Calculate sales velocity.

    Formula: (# opportunities x avg deal size x win rate) / avg sales cycle length
    Result is revenue per day.
    """
    if not deals:
        return {
            "num_opportunities": 0,
            "avg_deal_size": 0,
            "win_rate_pct": 0,
            "avg_cycle_days": 0,
            "velocity_per_day": 0,
            "velocity_per_month": 0,
        }

    won_deals = [d for d in deals if d["stage"] == "Closed Won"]
    open_deals = [d for d in deals if d["stage"] != "Closed Won"]
    all_considered = deals

    num_opportunities = len(all_considered)
    avg_deal_size = safe_divide(
        sum(d["value"] for d in all_considered), num_opportunities
    )
    win_rate = safe_divide(len(won_deals), num_opportunities)
    avg_cycle_days = safe_divide(
        sum(d["age_days"] for d in all_considered), num_opportunities
    )

    velocity_per_day = safe_divide(
        num_opportunities * avg_deal_size * win_rate, avg_cycle_days
    )

    return {
        "num_opportunities": num_opportunities,
        "avg_deal_size": round(avg_deal_size, 2),
        "win_rate_pct": round(win_rate * 100, 1),
        "avg_cycle_days": round(avg_cycle_days, 1),
        "velocity_per_day": round(velocity_per_day, 2),
        "velocity_per_month": round(velocity_per_day * 30, 2),
    }


def analyze_deal_aging(
    deals: list[dict], average_cycle_days: int, stages: list[str]
) -> dict[str, Any]:
    """Analyze deal aging and flag stale deals.

    Flags deals older than 2x the average cycle time.
    Uses stage-specific thresholds based on position in the pipeline.
    """
    aging_threshold = average_cycle_days * 2
    num_stages = len(stages)
    stage_order = {stage: i for i, stage in enumerate(stages)}

    # Stage-specific thresholds: early stages get more time, later stages less
    stage_thresholds: dict[str, int] = {}
    for i, stage in enumerate(stages):
        if stage == "Closed Won":
            continue
        # Progressive thresholds: first stage gets full cycle, last open stage gets 50%
        progress = safe_divide(i, num_stages - 1)
        threshold = int(average_cycle_days * (1.0 + (1.0 - progress)))
        stage_thresholds[stage] = threshold

    aging_deals = []
    healthy_deals = 0
    at_risk_deals = 0

    for deal in deals:
        if deal["stage"] == "Closed Won":
            continue

        stage = deal["stage"]
        age = deal["age_days"]
        threshold = stage_thresholds.get(stage, aging_threshold)

        if age > threshold:
            at_risk_deals += 1
            aging_deals.append({
                "id": deal["id"],
                "name": deal["name"],
                "stage": stage,
                "age_days": age,
                "threshold_days": threshold,
                "days_over": age - threshold,
                "value": deal["value"],
            })
        else:
            healthy_deals += 1

    aging_deals.sort(key=lambda x: x["days_over"], reverse=True)

    return {
        "global_aging_threshold_days": aging_threshold,
        "stage_thresholds": stage_thresholds,
        "total_open_deals": healthy_deals + at_risk_deals,
        "healthy_deals": healthy_deals,
        "at_risk_deals": at_risk_deals,
        "aging_deals": aging_deals,
    }


def assess_pipeline_risk(
    deals: list[dict], quota: float, stages: list[str]
) -> dict[str, Any]:
    """Assess overall pipeline risk.

    Checks for:
    - Concentration risk (>40% in single deal)
    - Stage distribution health
    - Coverage gap by quarter
    """
    open_deals = [d for d in deals if d["stage"] != "Closed Won"]
    total_pipeline = sum(d["value"] for d in open_deals)

    # Concentration risk
    concentration_risks = []
    for deal in open_deals:
        pct = safe_divide(deal["value"], total_pipeline) * 100
        if pct > 40:
            concentration_risks.append({
                "id": deal["id"],
                "name": deal["name"],
                "value": deal["value"],
                "pct_of_pipeline": round(pct, 1),
                "risk_level": "HIGH",
            })
        elif pct > 25:
            concentration_risks.append({
                "id": deal["id"],
                "name": deal["name"],
                "value": deal["value"],
                "pct_of_pipeline": round(pct, 1),
                "risk_level": "MEDIUM",
            })

    has_concentration_risk = any(
        r["risk_level"] == "HIGH" for r in concentration_risks
    )

    # Stage distribution
    stage_distribution: dict[str, dict] = {}
    for stage in stages:
        if stage == "Closed Won":
            continue
        stage_deals = [d for d in open_deals if d["stage"] == stage]
        count = len(stage_deals)
        value = sum(d["value"] for d in stage_deals)
        stage_distribution[stage] = {
            "count": count,
            "value": value,
            "pct_of_pipeline": round(safe_divide(value, total_pipeline) * 100, 1),
        }

    # Check for empty stages (unhealthy funnel)
    empty_stages = [
        stage for stage, data in stage_distribution.items() if data["count"] == 0
    ]

    # Coverage gap by quarter
    today = date.today()
    quarterly_coverage: dict[str, float] = {}
    for deal in open_deals:
        try:
            close_date = parse_date(deal["close_date"])
            quarter = get_quarter(close_date)
            quarterly_coverage[quarter] = (
                quarterly_coverage.get(quarter, 0) + deal["value"]
            )
        except (ValueError, KeyError):
            pass

    quarterly_target = quota / 4
    coverage_gaps = []
    for quarter, value in sorted(quarterly_coverage.items()):
        coverage = safe_divide(value, quarterly_target)
        if coverage < 3.0:
            coverage_gaps.append({
                "quarter": quarter,
                "pipeline_value": value,
                "quarterly_target": quarterly_target,
                "coverage_ratio": round(coverage, 2),
                "gap": "Below 3x target",
            })

    # Overall risk rating
    risk_factors = 0
    if has_concentration_risk:
        risk_factors += 2
    if len(empty_stages) > 0:
        risk_factors += 1
    if len(coverage_gaps) > 0:
        risk_factors += 1
    if safe_divide(total_pipeline, quota) < 3.0:
        risk_factors += 2

    if risk_factors >= 4:
        overall_risk = "HIGH"
    elif risk_factors >= 2:
        overall_risk = "MEDIUM"
    else:
        overall_risk = "LOW"

    return {
        "overall_risk": overall_risk,
        "risk_factors_count": risk_factors,
        "concentration_risks": concentration_risks,
        "has_concentration_risk": has_concentration_risk,
        "stage_distribution": stage_distribution,
        "empty_stages": empty_stages,
        "coverage_gaps": coverage_gaps,
    }


def analyze_pipeline(data: dict) -> dict[str, Any]:
    """Run complete pipeline analysis.

    Args:
        data: Pipeline data with deals, quota, stages, and average_cycle_days.

    Returns:
        Complete analysis results dictionary.
    """
    deals = data["deals"]
    quota = data["quota"]
    stages = data["stages"]
    average_cycle_days = data.get("average_cycle_days", 45)

    return {
        "coverage": calculate_coverage_ratio(deals, quota),
        "stage_conversions": calculate_stage_conversion_rates(deals, stages),
        "velocity": calculate_sales_velocity(deals),
        "aging": analyze_deal_aging(deals, average_cycle_days, stages),
        "risk": assess_pipeline_risk(deals, quota, stages),
    }


def format_currency(value: float) -> str:
    """Format a number as currency."""
    if value >= 1_000_000:
        return f"${value / 1_000_000:,.1f}M"
    elif value >= 1_000:
        return f"${value / 1_000:,.1f}K"
    return f"${value:,.0f}"


def format_text_report(results: dict) -> str:
    """Format analysis results as a human-readable text report."""
    lines = []
    lines.append("=" * 70)
    lines.append("PIPELINE ANALYSIS REPORT")
    lines.append("=" * 70)

    # Coverage
    cov = results["coverage"]
    lines.append("")
    lines.append("PIPELINE COVERAGE")
    lines.append("-" * 40)
    lines.append(f"  Total Pipeline:   {format_currency(cov['total_pipeline_value'])}")
    lines.append(f"  Quota Target:     {format_currency(cov['quota'])}")
    lines.append(f"  Coverage Ratio:   {cov['coverage_ratio']}x  (Target: {cov['target']})")
    lines.append(f"  Rating:           {cov['rating']}")

    # Stage Conversions
    lines.append("")
    lines.append("STAGE CONVERSION RATES")
    lines.append("-" * 40)
    for conv in results["stage_conversions"]:
        lines.append(
            f"  {conv['from_stage']} -> {conv['to_stage']}: "
            f"{conv['conversion_rate_pct']}% "
            f"({conv['to_count']}/{conv['from_count']})"
        )

    # Velocity
    vel = results["velocity"]
    lines.append("")
    lines.append("SALES VELOCITY")
    lines.append("-" * 40)
    lines.append(f"  Opportunities:    {vel['num_opportunities']}")
    lines.append(f"  Avg Deal Size:    {format_currency(vel['avg_deal_size'])}")
    lines.append(f"  Win Rate:         {vel['win_rate_pct']}%")
    lines.append(f"  Avg Cycle:        {vel['avg_cycle_days']} days")
    lines.append(f"  Velocity/Day:     {format_currency(vel['velocity_per_day'])}")
    lines.append(f"  Velocity/Month:   {format_currency(vel['velocity_per_month'])}")

    # Aging
    aging = results["aging"]
    lines.append("")
    lines.append("DEAL AGING ANALYSIS")
    lines.append("-" * 40)
    lines.append(f"  Total Open Deals: {aging['total_open_deals']}")
    lines.append(f"  Healthy:          {aging['healthy_deals']}")
    lines.append(f"  At Risk:          {aging['at_risk_deals']}")
    if aging["aging_deals"]:
        lines.append("")
        lines.append("  AGING DEALS (needs attention):")
        for deal in aging["aging_deals"]:
            lines.append(
                f"    - {deal['name']} ({deal['stage']}): "
                f"{deal['age_days']}d (threshold: {deal['threshold_days']}d, "
                f"+{deal['days_over']}d over) | {format_currency(deal['value'])}"
            )

    # Risk
    risk = results["risk"]
    lines.append("")
    lines.append("PIPELINE RISK ASSESSMENT")
    lines.append("-" * 40)
    lines.append(f"  Overall Risk:     {risk['overall_risk']}")
    lines.append(f"  Risk Factors:     {risk['risk_factors_count']}")

    if risk["concentration_risks"]:
        lines.append("")
        lines.append("  CONCENTRATION RISKS:")
        for cr in risk["concentration_risks"]:
            lines.append(
                f"    - {cr['name']}: {format_currency(cr['value'])} "
                f"({cr['pct_of_pipeline']}% of pipeline) [{cr['risk_level']}]"
            )

    if risk["empty_stages"]:
        lines.append("")
        lines.append(f"  EMPTY STAGES: {', '.join(risk['empty_stages'])}")

    lines.append("")
    lines.append("  STAGE DISTRIBUTION:")
    for stage, data in risk["stage_distribution"].items():
        bar = "#" * max(1, int(data["pct_of_pipeline"] / 2))
        lines.append(
            f"    {stage:20s} {data['count']:3d} deals  "
            f"{format_currency(data['value']):>10s}  "
            f"{data['pct_of_pipeline']:5.1f}%  {bar}"
        )

    if risk["coverage_gaps"]:
        lines.append("")
        lines.append("  COVERAGE GAPS BY QUARTER:")
        for gap in risk["coverage_gaps"]:
            lines.append(
                f"    - {gap['quarter']}: {gap['coverage_ratio']}x coverage "
                f"({format_currency(gap['pipeline_value'])} vs "
                f"{format_currency(gap['quarterly_target'])} target)"
            )

    lines.append("")
    lines.append("=" * 70)
    return "\n".join(lines)


# Embedded synthetic pipeline fixture for --sample.
SAMPLE_DATA = {
    "quota": 1000000,
    "average_cycle_days": 45,
    "stages": ["discovery", "demo", "proposal", "negotiation", "closed_won"],
    "deals": [
        {"id": "D-1", "name": "Acme renewal", "stage": "proposal",
         "value": 120000, "age_days": 30, "close_date": "2026-07-15"},
        {"id": "D-2", "name": "Globex new logo", "stage": "discovery",
         "value": 80000, "age_days": 10, "close_date": "2026-08-01"},
        # D-3 is intentionally stale (70d old vs 45d average cycle, closing
        # imminently) so the fixture exercises the at-risk/aging detection.
        {"id": "D-3", "name": "Initech expansion", "stage": "negotiation",
         "value": 200000, "age_days": 70, "close_date": "2026-06-30"},
        {"id": "D-4", "name": "Umbrella upsell", "stage": "closed_won",
         "value": 60000, "age_days": 50, "close_date": "2026-05-20"},
    ],
}


def main() -> None:
    """Main entry point for pipeline analyzer CLI."""
    parser = argparse.ArgumentParser(
        description="Analyze sales pipeline health for SaaS revenue teams."
    )
    parser.add_argument(
        "--input",
        help="Path to JSON file containing pipeline data",
    )
    parser.add_argument(
        "--format",
        choices=["json", "text"],
        default="text",
        help="Output format: json or text (default: text)",
    )
    parser.add_argument(
        "--sample",
        action="store_true",
        help="Analyze an embedded synthetic pipeline (no input file needed)",
    )

    args = parser.parse_args()

    if args.sample:
        if args.input:
            print("Warning: --sample specified; ignoring --input", file=sys.stderr)
        data = SAMPLE_DATA
    else:
        if not args.input:
            parser.error("--input is required (or use --sample)")
        try:
            with open(args.input, "r") as f:
                data = json.load(f)
        except FileNotFoundError:
            print(f"Error: File not found: {args.input}", file=sys.stderr)
            sys.exit(1)
        except json.JSONDecodeError as e:
            print(f"Error: Invalid JSON in {args.input}: {e}", file=sys.stderr)
            sys.exit(1)

    # Validate required fields
    required_fields = ["deals", "quota", "stages"]
    for field in required_fields:
        if field not in data:
            print(f"Error: Missing required field '{field}' in input data", file=sys.stderr)
            sys.exit(1)

    results = analyze_pipeline(data)

    if args.format == "json":
        print(json.dumps(results, indent=2))
    else:
        print(format_text_report(results))


if __name__ == "__main__":
    main()
