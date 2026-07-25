#!/usr/bin/env python3
"""Forecast Accuracy Tracker - Measures forecast accuracy and bias for SaaS revenue teams.

Calculates MAPE (Mean Absolute Percentage Error), detects systematic forecasting
bias, analyzes accuracy trends, and provides category-level breakdowns.

Usage:
    python forecast_accuracy_tracker.py forecast_data.json --format text
    python forecast_accuracy_tracker.py forecast_data.json --format json
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


def calculate_mape(periods: list[dict]) -> float:
    """Calculate Mean Absolute Percentage Error.

    Formula: mean(|actual - forecast| / |actual|) x 100

    Args:
        periods: List of dicts with 'forecast' and 'actual' keys.

    Returns:
        MAPE as a percentage.
    """
    if not periods:
        return 0.0

    errors = []
    for p in periods:
        actual = p["actual"]
        forecast = p["forecast"]
        if actual != 0:
            errors.append(abs(actual - forecast) / abs(actual))

    if not errors:
        return 0.0

    return (sum(errors) / len(errors)) * 100


def calculate_weighted_mape(periods: list[dict]) -> float:
    """Calculate value-weighted MAPE.

    Weights each period's error by its actual value, giving more importance
    to larger periods.

    Args:
        periods: List of dicts with 'forecast' and 'actual' keys.

    Returns:
        Weighted MAPE as a percentage.
    """
    if not periods:
        return 0.0

    total_actual = sum(abs(p["actual"]) for p in periods)
    if total_actual == 0:
        return 0.0

    weighted_errors = 0.0
    for p in periods:
        actual = p["actual"]
        forecast = p["forecast"]
        if actual != 0:
            weight = abs(actual) / total_actual
            weighted_errors += weight * (abs(actual - forecast) / abs(actual))

    return weighted_errors * 100


def get_accuracy_rating(mape: float) -> dict[str, str]:
    """Return accuracy rating based on MAPE threshold.

    Ratings:
        Excellent: <10%
        Good: 10-15%
        Fair: 15-25%
        Poor: >25%
    """
    if mape < 10:
        return {"rating": "Excellent", "description": "Highly predictable, data-driven process"}
    elif mape < 15:
        return {"rating": "Good", "description": "Reliable forecasting with minor variance"}
    elif mape < 25:
        return {"rating": "Fair", "description": "Needs process improvement"}
    else:
        return {"rating": "Poor", "description": "Significant forecasting methodology gaps"}


def analyze_bias(periods: list[dict]) -> dict[str, Any]:
    """Analyze systematic forecasting bias.

    Positive bias = over-forecasting (forecast > actual, i.e., actual fell short)
    Negative bias = under-forecasting (forecast < actual, i.e., actual exceeded)

    Args:
        periods: List of dicts with 'forecast' and 'actual' keys.

    Returns:
        Bias analysis with direction, magnitude, and ratio.
    """
    if not periods:
        return {
            "direction": "None",
            "bias_pct": 0.0,
            "over_forecast_count": 0,
            "under_forecast_count": 0,
            "exact_count": 0,
            "bias_ratio": 0.0,
        }

    over_count = 0
    under_count = 0
    exact_count = 0
    total_bias = 0.0

    for p in periods:
        diff = p["forecast"] - p["actual"]
        total_bias += diff
        if diff > 0:
            over_count += 1
        elif diff < 0:
            under_count += 1
        else:
            exact_count += 1

    avg_bias = total_bias / len(periods)
    total_actual = sum(p["actual"] for p in periods)
    bias_pct = safe_divide(total_bias, total_actual) * 100

    if over_count > under_count:
        direction = "Over-forecasting"
    elif under_count > over_count:
        direction = "Under-forecasting"
    else:
        direction = "Balanced"

    bias_ratio = safe_divide(over_count, over_count + under_count)

    return {
        "direction": direction,
        "avg_bias_amount": round(avg_bias, 2),
        "bias_pct": round(bias_pct, 1),
        "over_forecast_count": over_count,
        "under_forecast_count": under_count,
        "exact_count": exact_count,
        "bias_ratio": round(bias_ratio, 2),
    }


def analyze_trend(periods: list[dict]) -> dict[str, Any]:
    """Analyze period-over-period accuracy trend.

    Determines if forecast accuracy is improving, stable, or declining
    by comparing error rates across consecutive periods.

    Args:
        periods: List of dicts with 'period', 'forecast', and 'actual' keys.

    Returns:
        Trend analysis with direction and period details.
    """
    if len(periods) < 2:
        return {
            "trend": "Insufficient data",
            "period_errors": [],
            "improving_periods": 0,
            "declining_periods": 0,
        }

    period_errors = []
    for p in periods:
        actual = p["actual"]
        forecast = p["forecast"]
        if actual != 0:
            error_pct = abs(actual - forecast) / abs(actual) * 100
        else:
            error_pct = 0.0
        period_errors.append({
            "period": p.get("period", "Unknown"),
            "error_pct": round(error_pct, 1),
            "forecast": forecast,
            "actual": actual,
        })

    improving = 0
    declining = 0
    for i in range(1, len(period_errors)):
        if period_errors[i]["error_pct"] < period_errors[i - 1]["error_pct"]:
            improving += 1
        elif period_errors[i]["error_pct"] > period_errors[i - 1]["error_pct"]:
            declining += 1

    if improving > declining:
        trend = "Improving"
    elif declining > improving:
        trend = "Declining"
    else:
        trend = "Stable"

    # Calculate recent vs historical MAPE
    midpoint = len(periods) // 2
    if midpoint > 0:
        early_mape = calculate_mape(periods[:midpoint])
        recent_mape = calculate_mape(periods[midpoint:])
        mape_change = recent_mape - early_mape
    else:
        early_mape = 0.0
        recent_mape = 0.0
        mape_change = 0.0

    return {
        "trend": trend,
        "period_errors": period_errors,
        "improving_periods": improving,
        "declining_periods": declining,
        "early_mape": round(early_mape, 1),
        "recent_mape": round(recent_mape, 1),
        "mape_change": round(mape_change, 1),
    }


def analyze_categories(category_breakdowns: dict) -> dict[str, Any]:
    """Analyze accuracy by category (rep, product, segment, etc.).

    Args:
        category_breakdowns: Dict of category_name -> list of
            {category, forecast, actual} dicts.

    Returns:
        Category-level MAPE and accuracy analysis.
    """
    results = {}

    for category_name, entries in category_breakdowns.items():
        category_results = []
        for entry in entries:
            actual = entry["actual"]
            forecast = entry["forecast"]
            if actual != 0:
                error_pct = abs(actual - forecast) / abs(actual) * 100
            else:
                error_pct = 0.0

            diff = forecast - actual
            if diff > 0:
                bias = "Over"
            elif diff < 0:
                bias = "Under"
            else:
                bias = "Exact"

            rating = get_accuracy_rating(error_pct)

            category_results.append({
                "category": entry["category"],
                "forecast": forecast,
                "actual": actual,
                "error_pct": round(error_pct, 1),
                "bias": bias,
                "variance": round(diff, 2),
                "rating": rating["rating"],
            })

        # Sort by error percentage (worst first)
        category_results.sort(key=lambda x: x["error_pct"], reverse=True)

        overall_mape = calculate_mape(entries)
        results[category_name] = {
            "entries": category_results,
            "overall_mape": round(overall_mape, 1),
            "overall_rating": get_accuracy_rating(overall_mape)["rating"],
        }

    return results


def generate_recommendations(
    mape: float, bias: dict, trend: dict, categories: dict
) -> list[str]:
    """Generate actionable recommendations based on analysis results.

    Args:
        mape: Overall MAPE percentage.
        bias: Bias analysis results.
        trend: Trend analysis results.
        categories: Category analysis results.

    Returns:
        List of recommendation strings.
    """
    recommendations = []

    # MAPE-based recommendations
    if mape > 25:
        recommendations.append(
            "CRITICAL: MAPE exceeds 25%. Implement structured forecasting methodology "
            "(e.g., weighted pipeline with stage-based probabilities)."
        )
    elif mape > 15:
        recommendations.append(
            "Forecast accuracy needs improvement. Consider implementing deal-level "
            "forecasting with commit/upside/pipeline categories."
        )

    # Bias-based recommendations
    if bias["direction"] == "Over-forecasting" and abs(bias["bias_pct"]) > 10:
        recommendations.append(
            f"Systematic over-forecasting detected ({bias['bias_pct']}% bias). "
            "Review deal qualification criteria and apply more conservative "
            "stage probabilities."
        )
    elif bias["direction"] == "Under-forecasting" and abs(bias["bias_pct"]) > 10:
        recommendations.append(
            f"Systematic under-forecasting detected ({bias['bias_pct']}% bias). "
            "Review upside deals more carefully and improve pipeline visibility."
        )

    # Trend-based recommendations
    if trend["trend"] == "Declining":
        recommendations.append(
            "Forecast accuracy is declining over time. Schedule a forecasting "
            "methodology review and retrain the team on forecasting best practices."
        )
    elif trend["trend"] == "Improving":
        recommendations.append(
            "Forecast accuracy is improving. Continue current methodology and "
            "document best practices for consistency."
        )

    # Category-based recommendations
    for cat_name, cat_data in categories.items():
        worst_entries = [
            e for e in cat_data["entries"] if e["error_pct"] > 25
        ]
        if worst_entries:
            names = ", ".join(e["category"] for e in worst_entries[:3])
            recommendations.append(
                f"High error rates in {cat_name}: {names}. "
                f"Provide targeted coaching on forecasting discipline."
            )

    if not recommendations:
        recommendations.append(
            "Forecasting performance is strong. Maintain current processes "
            "and continue monitoring for drift."
        )

    return recommendations


def track_forecast_accuracy(data: dict) -> dict[str, Any]:
    """Run complete forecast accuracy analysis.

    Args:
        data: Forecast data with periods and optional category breakdowns.

    Returns:
        Complete forecast accuracy analysis results.
    """
    periods = data["forecast_periods"]

    mape = calculate_mape(periods)
    weighted_mape = calculate_weighted_mape(periods)
    rating = get_accuracy_rating(mape)
    bias = analyze_bias(periods)
    trend = analyze_trend(periods)

    categories = {}
    if "category_breakdowns" in data:
        categories = analyze_categories(data["category_breakdowns"])

    recommendations = generate_recommendations(mape, bias, trend, categories)

    return {
        "mape": round(mape, 1),
        "weighted_mape": round(weighted_mape, 1),
        "accuracy_rating": rating,
        "bias": bias,
        "trend": trend,
        "category_breakdowns": categories,
        "recommendations": recommendations,
        "periods_analyzed": len(periods),
    }


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
    lines.append("FORECAST ACCURACY REPORT")
    lines.append("=" * 70)

    # Overall accuracy
    lines.append("")
    lines.append("OVERALL ACCURACY")
    lines.append("-" * 40)
    lines.append(f"  MAPE:              {results['mape']}%")
    lines.append(f"  Weighted MAPE:     {results['weighted_mape']}%")
    lines.append(f"  Rating:            {results['accuracy_rating']['rating']}")
    lines.append(f"  Assessment:        {results['accuracy_rating']['description']}")
    lines.append(f"  Periods Analyzed:  {results['periods_analyzed']}")

    # Bias analysis
    bias = results["bias"]
    lines.append("")
    lines.append("FORECAST BIAS")
    lines.append("-" * 40)
    lines.append(f"  Direction:         {bias['direction']}")
    lines.append(f"  Bias %:            {bias['bias_pct']}%")
    lines.append(f"  Avg Bias Amount:   {format_currency(bias['avg_bias_amount'])}")
    lines.append(f"  Over-forecast:     {bias['over_forecast_count']} periods")
    lines.append(f"  Under-forecast:    {bias['under_forecast_count']} periods")
    lines.append(f"  Bias Ratio:        {bias['bias_ratio']}")

    # Trend analysis
    trend = results["trend"]
    lines.append("")
    lines.append("ACCURACY TREND")
    lines.append("-" * 40)
    lines.append(f"  Trend:             {trend['trend']}")
    lines.append(f"  Improving:         {trend['improving_periods']} periods")
    lines.append(f"  Declining:         {trend['declining_periods']} periods")
    if trend.get("early_mape") is not None and trend["trend"] != "Insufficient data":
        lines.append(f"  Early MAPE:        {trend['early_mape']}%")
        lines.append(f"  Recent MAPE:       {trend['recent_mape']}%")
        lines.append(f"  MAPE Change:       {trend['mape_change']:+.1f}%")

    if trend.get("period_errors"):
        lines.append("")
        lines.append("  PERIOD DETAIL:")
        for pe in trend["period_errors"]:
            lines.append(
                f"    {pe['period']:12s}  "
                f"Forecast: {format_currency(pe['forecast']):>10s}  "
                f"Actual: {format_currency(pe['actual']):>10s}  "
                f"Error: {pe['error_pct']}%"
            )

    # Category breakdowns
    if results["category_breakdowns"]:
        lines.append("")
        lines.append("CATEGORY BREAKDOWN")
        lines.append("-" * 40)
        for cat_name, cat_data in results["category_breakdowns"].items():
            lines.append(
                f"\n  {cat_name.upper()} (Overall MAPE: {cat_data['overall_mape']}% "
                f"- {cat_data['overall_rating']})"
            )
            for entry in cat_data["entries"]:
                lines.append(
                    f"    {entry['category']:20s}  "
                    f"Error: {entry['error_pct']:5.1f}%  "
                    f"Bias: {entry['bias']:5s}  "
                    f"Rating: {entry['rating']}"
                )

    # Recommendations
    lines.append("")
    lines.append("RECOMMENDATIONS")
    lines.append("-" * 40)
    for i, rec in enumerate(results["recommendations"], 1):
        lines.append(f"  {i}. {rec}")

    lines.append("")
    lines.append("=" * 70)
    return "\n".join(lines)


def main() -> None:
    """Main entry point for forecast accuracy tracker CLI."""
    parser = argparse.ArgumentParser(
        description="Track and analyze forecast accuracy for SaaS revenue teams."
    )
    parser.add_argument(
        "input",
        help="Path to JSON file containing forecast data",
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

    if "forecast_periods" not in data:
        print("Error: Missing required field 'forecast_periods' in input data", file=sys.stderr)
        sys.exit(1)

    results = track_forecast_accuracy(data)

    if args.format == "json":
        print(json.dumps(results, indent=2))
    else:
        print(format_text_report(results))


if __name__ == "__main__":
    main()
