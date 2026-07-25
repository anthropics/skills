#!/usr/bin/env python3
"""GTM Efficiency Calculator - Calculates go-to-market efficiency metrics for SaaS.

Computes Magic Number, LTV:CAC, CAC Payback, Burn Multiple, Rule of 40,
and Net Dollar Retention with industry benchmarking and ratings.

Usage:
    python gtm_efficiency_calculator.py gtm_data.json --format text
    python gtm_efficiency_calculator.py gtm_data.json --format json
"""

import argparse
import json
import sys
from typing import Any


def safe_divide(numerator: float, denominator: float, default: float = 0.0) -> float:
    """Safely divide two numbers, returning default if denominator is zero."""
    if denominator == 0:
        return default
    return numerator / denominator


# --- Benchmark tables ---
# Each benchmark defines green/yellow/red thresholds
# and optional percentile placement guidance

BENCHMARKS = {
    "magic_number": {
        "green": {"min": 0.75, "label": ">0.75 - Efficient GTM spend"},
        "yellow": {"min": 0.50, "max": 0.75, "label": "0.50-0.75 - Acceptable efficiency"},
        "red": {"max": 0.50, "label": "<0.50 - Inefficient GTM spend"},
        "elite": 1.0,
        "description": "Net New ARR / Prior Period S&M Spend",
    },
    "ltv_cac_ratio": {
        "green": {"min": 3.0, "label": ">3:1 - Strong unit economics"},
        "yellow": {"min": 1.0, "max": 3.0, "label": "1:1-3:1 - Marginal unit economics"},
        "red": {"max": 1.0, "label": "<1:1 - Unsustainable unit economics"},
        "elite": 5.0,
        "description": "Customer LTV / Customer Acquisition Cost",
    },
    "cac_payback_months": {
        "green": {"max": 18, "label": "<18 months - Healthy payback"},
        "yellow": {"min": 18, "max": 24, "label": "18-24 months - Acceptable payback"},
        "red": {"min": 24, "label": ">24 months - Capital intensive"},
        "elite": 12,
        "description": "CAC / (ARPA x Gross Margin) in months",
    },
    "burn_multiple": {
        "green": {"max": 2.0, "label": "<2x - Capital efficient growth"},
        "yellow": {"min": 2.0, "max": 4.0, "label": "2-4x - Moderate burn"},
        "red": {"min": 4.0, "label": ">4x - Unsustainable burn"},
        "elite": 1.0,
        "description": "Net Burn / Net New ARR",
    },
    "rule_of_40": {
        "green": {"min": 40, "label": ">40% - Strong balance of growth & profitability"},
        "yellow": {"min": 20, "max": 40, "label": "20-40% - Acceptable balance"},
        "red": {"max": 20, "label": "<20% - Needs improvement"},
        "elite": 60,
        "description": "Revenue Growth % + FCF Margin %",
    },
    "ndr_pct": {
        "green": {"min": 110, "label": ">110% - Strong expansion revenue"},
        "yellow": {"min": 100, "max": 110, "label": "100-110% - Stable base"},
        "red": {"max": 100, "label": "<100% - Net revenue contraction"},
        "elite": 130,
        "description": "(Begin ARR + Expansion - Contraction - Churn) / Begin ARR",
    },
}


def rate_metric(metric_name: str, value: float) -> dict[str, str]:
    """Rate a metric as Green/Yellow/Red based on benchmark thresholds.

    Args:
        metric_name: Key into BENCHMARKS dict.
        value: The metric value to rate.

    Returns:
        Dict with rating color, label, and percentile guidance.
    """
    bench = BENCHMARKS.get(metric_name)
    if not bench:
        return {"rating": "Unknown", "label": "No benchmark available"}

    # For metrics where lower is better (cac_payback, burn_multiple)
    lower_is_better = metric_name in ("cac_payback_months", "burn_multiple")

    if lower_is_better:
        if "max" in bench["green"] and value <= bench["green"]["max"]:
            rating = "Green"
            label = bench["green"]["label"]
        elif "min" in bench.get("yellow", {}) and "max" in bench.get("yellow", {}):
            if bench["yellow"]["min"] <= value <= bench["yellow"]["max"]:
                rating = "Yellow"
                label = bench["yellow"]["label"]
            else:
                rating = "Red"
                label = bench["red"]["label"]
        else:
            rating = "Red"
            label = bench["red"]["label"]
    else:
        if "min" in bench["green"] and value >= bench["green"]["min"]:
            rating = "Green"
            label = bench["green"]["label"]
        elif "min" in bench.get("yellow", {}) and "max" in bench.get("yellow", {}):
            if bench["yellow"]["min"] <= value <= bench["yellow"]["max"]:
                rating = "Yellow"
                label = bench["yellow"]["label"]
            else:
                rating = "Red"
                label = bench["red"]["label"]
        else:
            rating = "Red"
            label = bench["red"]["label"]

    # Percentile placement (simplified)
    elite = bench.get("elite", 0)
    if lower_is_better:
        if elite > 0 and value > 0:
            if value <= elite:
                percentile = "Top 10%"
            elif rating == "Green":
                percentile = "Top 25%"
            elif rating == "Yellow":
                percentile = "Median"
            else:
                percentile = "Below median"
        else:
            percentile = "N/A"
    else:
        if elite > 0:
            if value >= elite:
                percentile = "Top 10%"
            elif rating == "Green":
                percentile = "Top 25%"
            elif rating == "Yellow":
                percentile = "Median"
            else:
                percentile = "Below median"
        else:
            percentile = "N/A"

    return {
        "rating": rating,
        "label": label,
        "percentile": percentile,
    }


def calculate_magic_number(net_new_arr: float, sm_spend: float) -> dict[str, Any]:
    """Calculate Magic Number.

    Formula: Net New ARR / Prior Period S&M Spend
    Target: >0.75

    Args:
        net_new_arr: Net new annual recurring revenue in the period.
        sm_spend: Sales & marketing spend in the prior period.

    Returns:
        Magic number value with rating and benchmark.
    """
    value = safe_divide(net_new_arr, sm_spend)
    benchmark = rate_metric("magic_number", value)

    return {
        "value": round(value, 2),
        "net_new_arr": net_new_arr,
        "sm_spend": sm_spend,
        "formula": "Net New ARR / Prior Period S&M Spend",
        "target": ">0.75",
        **benchmark,
    }


def calculate_ltv_cac(
    arpa_monthly: float,
    gross_margin_pct: float,
    annual_churn_rate_pct: float,
    cac: float,
) -> dict[str, Any]:
    """Calculate LTV:CAC Ratio.

    LTV = ARPA_monthly x 12 x Gross Margin / Annual Churn Rate
    Ratio = LTV / CAC
    Target: >3:1

    Args:
        arpa_monthly: Average revenue per account per month.
        gross_margin_pct: Gross margin as percentage (e.g., 78 for 78%).
        annual_churn_rate_pct: Annual churn rate as percentage (e.g., 8 for 8%).
        cac: Customer acquisition cost.

    Returns:
        LTV:CAC ratio with component values, rating, and benchmark.
    """
    gross_margin = gross_margin_pct / 100
    churn_rate = annual_churn_rate_pct / 100

    arpa_annual = arpa_monthly * 12
    ltv = safe_divide(arpa_annual * gross_margin, churn_rate)
    ratio = safe_divide(ltv, cac)

    benchmark = rate_metric("ltv_cac_ratio", ratio)

    return {
        "ratio": round(ratio, 1),
        "ltv": round(ltv, 2),
        "cac": cac,
        "arpa_monthly": arpa_monthly,
        "arpa_annual": arpa_annual,
        "gross_margin_pct": gross_margin_pct,
        "annual_churn_rate_pct": annual_churn_rate_pct,
        "formula": "LTV (ARPA x Gross Margin / Churn Rate) / CAC",
        "target": ">3:1",
        **benchmark,
    }


def calculate_cac_payback(
    cac: float, arpa_monthly: float, gross_margin_pct: float
) -> dict[str, Any]:
    """Calculate CAC Payback Period.

    Formula: CAC / (ARPA_monthly x Gross Margin) in months
    Target: <18 months

    Args:
        cac: Customer acquisition cost.
        arpa_monthly: Average revenue per account per month.
        gross_margin_pct: Gross margin as percentage.

    Returns:
        CAC payback months with rating and benchmark.
    """
    gross_margin = gross_margin_pct / 100
    monthly_contribution = arpa_monthly * gross_margin
    payback_months = safe_divide(cac, monthly_contribution)

    benchmark = rate_metric("cac_payback_months", payback_months)

    return {
        "months": round(payback_months, 1),
        "cac": cac,
        "arpa_monthly": arpa_monthly,
        "gross_margin_pct": gross_margin_pct,
        "monthly_contribution": round(monthly_contribution, 2),
        "formula": "CAC / (ARPA_monthly x Gross Margin)",
        "target": "<18 months",
        **benchmark,
    }


def calculate_burn_multiple(net_burn: float, net_new_arr: float) -> dict[str, Any]:
    """Calculate Burn Multiple.

    Formula: Net Burn / Net New ARR
    Target: <2x (lower is better)

    Args:
        net_burn: Net cash burn in the period.
        net_new_arr: Net new ARR added in the period.

    Returns:
        Burn multiple with rating and benchmark.
    """
    value = safe_divide(net_burn, net_new_arr)
    benchmark = rate_metric("burn_multiple", value)

    return {
        "value": round(value, 2),
        "net_burn": net_burn,
        "net_new_arr": net_new_arr,
        "formula": "Net Burn / Net New ARR",
        "target": "<2x",
        **benchmark,
    }


def calculate_rule_of_40(
    revenue_growth_pct: float, fcf_margin_pct: float
) -> dict[str, Any]:
    """Calculate Rule of 40.

    Formula: Revenue Growth % + FCF Margin %
    Target: >40%

    Args:
        revenue_growth_pct: Year-over-year revenue growth percentage.
        fcf_margin_pct: Free cash flow margin percentage.

    Returns:
        Rule of 40 score with rating and benchmark.
    """
    value = revenue_growth_pct + fcf_margin_pct
    benchmark = rate_metric("rule_of_40", value)

    return {
        "value": round(value, 1),
        "revenue_growth_pct": revenue_growth_pct,
        "fcf_margin_pct": fcf_margin_pct,
        "formula": "Revenue Growth % + FCF Margin %",
        "target": ">40%",
        **benchmark,
    }


def calculate_ndr(
    beginning_arr: float,
    expansion_arr: float,
    contraction_arr: float,
    churned_arr: float,
) -> dict[str, Any]:
    """Calculate Net Dollar Retention.

    Formula: (Beginning ARR + Expansion - Contraction - Churn) / Beginning ARR
    Target: >110%

    Args:
        beginning_arr: ARR at start of period.
        expansion_arr: Expansion revenue from existing customers.
        contraction_arr: Revenue lost from downgrades.
        churned_arr: Revenue lost from customer churn.

    Returns:
        NDR percentage with rating and benchmark.
    """
    ending_arr = beginning_arr + expansion_arr - contraction_arr - churned_arr
    ndr_pct = safe_divide(ending_arr, beginning_arr) * 100

    benchmark = rate_metric("ndr_pct", ndr_pct)

    return {
        "ndr_pct": round(ndr_pct, 1),
        "beginning_arr": beginning_arr,
        "expansion_arr": expansion_arr,
        "contraction_arr": contraction_arr,
        "churned_arr": churned_arr,
        "ending_arr": round(ending_arr, 2),
        "formula": "(Begin ARR + Expansion - Contraction - Churn) / Begin ARR",
        "target": ">110%",
        **benchmark,
    }


def generate_recommendations(metrics: dict) -> list[str]:
    """Generate strategic recommendations based on GTM efficiency metrics.

    Args:
        metrics: Dict of all calculated metric results.

    Returns:
        List of recommendation strings.
    """
    recs = []

    # Magic Number
    mn = metrics["magic_number"]
    if mn["rating"] == "Red":
        recs.append(
            f"Magic Number is {mn['value']} (target >0.75). GTM spend is inefficient. "
            "Audit channel ROI, optimize sales productivity, and consider reducing "
            "low-performing spend."
        )
    elif mn["rating"] == "Yellow":
        recs.append(
            f"Magic Number is {mn['value']}. GTM efficiency is acceptable but can improve. "
            "Focus on sales enablement and pipeline quality over quantity."
        )

    # LTV:CAC
    lc = metrics["ltv_cac"]
    if lc["rating"] == "Red":
        recs.append(
            f"LTV:CAC ratio is {lc['ratio']}:1 (target >3:1). Unit economics are unsustainable. "
            "Reduce CAC through better targeting, improve retention to increase LTV, "
            "or increase ARPA through pricing optimization."
        )
    elif lc["rating"] == "Yellow":
        recs.append(
            f"LTV:CAC ratio is {lc['ratio']}:1. Unit economics are marginal. "
            "Focus on reducing churn and expanding within existing accounts."
        )

    # CAC Payback
    cp = metrics["cac_payback"]
    if cp["rating"] == "Red":
        recs.append(
            f"CAC payback is {cp['months']} months (target <18). Capital recovery is too slow. "
            "Reduce acquisition costs or increase gross-margin-weighted ARPA."
        )

    # Burn Multiple
    bm = metrics["burn_multiple"]
    if bm["rating"] == "Red":
        recs.append(
            f"Burn multiple is {bm['value']}x (target <2x). Cash consumption relative to "
            "growth is unsustainable. Prioritize operating efficiency and path to profitability."
        )

    # Rule of 40
    r40 = metrics["rule_of_40"]
    if r40["rating"] == "Red":
        recs.append(
            f"Rule of 40 score is {r40['value']}% (target >40%). Balance of growth and "
            "profitability needs improvement. Either accelerate growth or improve margins."
        )

    # NDR
    ndr = metrics["ndr"]
    if ndr["rating"] == "Red":
        recs.append(
            f"NDR is {ndr['ndr_pct']}% (target >110%). Net revenue is contracting from "
            "the existing base. Prioritize churn reduction and expansion playbooks."
        )
    elif ndr["rating"] == "Yellow":
        recs.append(
            f"NDR is {ndr['ndr_pct']}%. Base is stable but not expanding. "
            "Invest in cross-sell/upsell motions and customer success capacity."
        )

    # Positive summary if everything is green
    green_count = sum(
        1 for m in metrics.values()
        if isinstance(m, dict) and m.get("rating") == "Green"
    )
    total_metrics = 6
    if green_count == total_metrics:
        recs.append(
            "All GTM efficiency metrics are in healthy ranges. Maintain current "
            "trajectory and optimize for best-in-class performance."
        )
    elif green_count >= 4:
        recs.append(
            f"{green_count}/{total_metrics} metrics are green. GTM efficiency is generally "
            "healthy. Address the yellow/red areas for continuous improvement."
        )

    return recs


def calculate_all_metrics(data: dict) -> dict[str, Any]:
    """Calculate all GTM efficiency metrics from input data.

    Args:
        data: Input data with revenue, costs, and customers sections.

    Returns:
        Complete GTM efficiency analysis results.
    """
    revenue = data["revenue"]
    costs = data["costs"]
    customers = data["customers"]

    metrics = {
        "magic_number": calculate_magic_number(
            net_new_arr=revenue["net_new_arr"],
            sm_spend=costs["sales_marketing_spend"],
        ),
        "ltv_cac": calculate_ltv_cac(
            arpa_monthly=revenue["arpa_monthly"],
            gross_margin_pct=costs["gross_margin_pct"],
            annual_churn_rate_pct=customers["annual_churn_rate_pct"],
            cac=costs["cac"],
        ),
        "cac_payback": calculate_cac_payback(
            cac=costs["cac"],
            arpa_monthly=revenue["arpa_monthly"],
            gross_margin_pct=costs["gross_margin_pct"],
        ),
        "burn_multiple": calculate_burn_multiple(
            net_burn=costs["net_burn"],
            net_new_arr=revenue["net_new_arr"],
        ),
        "rule_of_40": calculate_rule_of_40(
            revenue_growth_pct=revenue["revenue_growth_pct"],
            fcf_margin_pct=costs["fcf_margin_pct"],
        ),
        "ndr": calculate_ndr(
            beginning_arr=customers["beginning_arr"],
            expansion_arr=customers["expansion_arr"],
            contraction_arr=customers["contraction_arr"],
            churned_arr=customers["churned_arr"],
        ),
    }

    metrics["recommendations"] = generate_recommendations(metrics)

    return metrics


def format_currency(value: float) -> str:
    """Format a number as currency."""
    if abs(value) >= 1_000_000:
        return f"${value / 1_000_000:,.1f}M"
    elif abs(value) >= 1_000:
        return f"${value / 1_000:,.1f}K"
    return f"${value:,.0f}"


def format_text_report(results: dict) -> str:
    """Format analysis results as a human-readable text report."""
    lines = []
    lines.append("=" * 70)
    lines.append("GTM EFFICIENCY REPORT")
    lines.append("=" * 70)

    # Metric summary table
    metrics_order = [
        ("magic_number", "Magic Number", lambda m: f"{m['value']}"),
        ("ltv_cac", "LTV:CAC Ratio", lambda m: f"{m['ratio']}:1"),
        ("cac_payback", "CAC Payback", lambda m: f"{m['months']} months"),
        ("burn_multiple", "Burn Multiple", lambda m: f"{m['value']}x"),
        ("rule_of_40", "Rule of 40", lambda m: f"{m['value']}%"),
        ("ndr", "Net Dollar Retention", lambda m: f"{m['ndr_pct']}%"),
    ]

    lines.append("")
    lines.append("METRICS SUMMARY")
    lines.append("-" * 70)
    lines.append(f"  {'Metric':25s} {'Value':>12s} {'Rating':>8s} {'Target':>15s}")
    lines.append(f"  {'':25s} {'':>12s} {'':>8s} {'':>15s}")

    for key, name, fmt_fn in metrics_order:
        m = results[key]
        lines.append(
            f"  {name:25s} {fmt_fn(m):>12s} {m['rating']:>8s} {m['target']:>15s}"
        )

    # Detailed breakdown
    lines.append("")
    lines.append("DETAILED BREAKDOWN")
    lines.append("-" * 70)

    # Magic Number
    mn = results["magic_number"]
    lines.append("")
    lines.append(f"  MAGIC NUMBER: {mn['value']}")
    lines.append(f"    Net New ARR:         {format_currency(mn['net_new_arr'])}")
    lines.append(f"    S&M Spend:           {format_currency(mn['sm_spend'])}")
    lines.append(f"    Rating:              {mn['rating']} - {mn['label']}")
    lines.append(f"    Percentile:          {mn['percentile']}")

    # LTV:CAC
    lc = results["ltv_cac"]
    lines.append("")
    lines.append(f"  LTV:CAC RATIO: {lc['ratio']}:1")
    lines.append(f"    Customer LTV:        {format_currency(lc['ltv'])}")
    lines.append(f"    CAC:                 {format_currency(lc['cac'])}")
    lines.append(f"    ARPA (Monthly):      {format_currency(lc['arpa_monthly'])}")
    lines.append(f"    Gross Margin:        {lc['gross_margin_pct']}%")
    lines.append(f"    Churn Rate:          {lc['annual_churn_rate_pct']}%")
    lines.append(f"    Rating:              {lc['rating']} - {lc['label']}")
    lines.append(f"    Percentile:          {lc['percentile']}")

    # CAC Payback
    cp = results["cac_payback"]
    lines.append("")
    lines.append(f"  CAC PAYBACK: {cp['months']} months")
    lines.append(f"    CAC:                 {format_currency(cp['cac'])}")
    lines.append(f"    Monthly Contribution:{format_currency(cp['monthly_contribution'])}")
    lines.append(f"    Rating:              {cp['rating']} - {cp['label']}")
    lines.append(f"    Percentile:          {cp['percentile']}")

    # Burn Multiple
    bm = results["burn_multiple"]
    lines.append("")
    lines.append(f"  BURN MULTIPLE: {bm['value']}x")
    lines.append(f"    Net Burn:            {format_currency(bm['net_burn'])}")
    lines.append(f"    Net New ARR:         {format_currency(bm['net_new_arr'])}")
    lines.append(f"    Rating:              {bm['rating']} - {bm['label']}")
    lines.append(f"    Percentile:          {bm['percentile']}")

    # Rule of 40
    r40 = results["rule_of_40"]
    lines.append("")
    lines.append(f"  RULE OF 40: {r40['value']}%")
    lines.append(f"    Revenue Growth:      {r40['revenue_growth_pct']}%")
    lines.append(f"    FCF Margin:          {r40['fcf_margin_pct']}%")
    lines.append(f"    Rating:              {r40['rating']} - {r40['label']}")
    lines.append(f"    Percentile:          {r40['percentile']}")

    # NDR
    ndr = results["ndr"]
    lines.append("")
    lines.append(f"  NET DOLLAR RETENTION: {ndr['ndr_pct']}%")
    lines.append(f"    Beginning ARR:       {format_currency(ndr['beginning_arr'])}")
    lines.append(f"    Expansion:           +{format_currency(ndr['expansion_arr'])}")
    lines.append(f"    Contraction:         -{format_currency(ndr['contraction_arr'])}")
    lines.append(f"    Churn:               -{format_currency(ndr['churned_arr'])}")
    lines.append(f"    Ending ARR:          {format_currency(ndr['ending_arr'])}")
    lines.append(f"    Rating:              {ndr['rating']} - {ndr['label']}")
    lines.append(f"    Percentile:          {ndr['percentile']}")

    # Recommendations
    lines.append("")
    lines.append("RECOMMENDATIONS")
    lines.append("-" * 70)
    for i, rec in enumerate(results["recommendations"], 1):
        lines.append(f"  {i}. {rec}")

    lines.append("")
    lines.append("=" * 70)
    return "\n".join(lines)


def main() -> None:
    """Main entry point for GTM efficiency calculator CLI."""
    parser = argparse.ArgumentParser(
        description="Calculate GTM efficiency metrics for SaaS revenue teams."
    )
    parser.add_argument(
        "input",
        help="Path to JSON file containing GTM data",
    )
    parser.add_argument(
        "--format",
        choices=["json", "text"],
        default="text",
        help="Output format: json or text (default: text)",
    )

    args = parser.parse_args()

    try:
        with open(args.input, "r") as f:
            data = json.load(f)
    except FileNotFoundError:
        print(f"Error: File not found: {args.input}", file=sys.stderr)
        sys.exit(1)
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON in {args.input}: {e}", file=sys.stderr)
        sys.exit(1)

    required_sections = ["revenue", "costs", "customers"]
    for section in required_sections:
        if section not in data:
            print(
                f"Error: Missing required section '{section}' in input data",
                file=sys.stderr,
            )
            sys.exit(1)

    results = calculate_all_metrics(data)

    if args.format == "json":
        print(json.dumps(results, indent=2))
    else:
        print(format_text_report(results))


if __name__ == "__main__":
    main()
