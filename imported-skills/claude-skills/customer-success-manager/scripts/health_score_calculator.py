#!/usr/bin/env python3
"""
Customer Health Score Calculator

Multi-dimensional weighted health scoring across usage, engagement, support,
and relationship dimensions. Produces Red/Yellow/Green classification with
trend analysis and segment-aware benchmarking.

Usage:
    python health_score_calculator.py customer_data.json
    python health_score_calculator.py customer_data.json --format json
"""

import argparse
import json
import sys
from typing import Any, Dict, List, Optional, Tuple


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

DIMENSION_WEIGHTS: Dict[str, float] = {
    "usage": 0.30,
    "engagement": 0.25,
    "support": 0.20,
    "relationship": 0.25,
}

# Segment-specific thresholds (green_min, yellow_min)
SEGMENT_THRESHOLDS: Dict[str, Dict[str, Tuple[int, int]]] = {
    "enterprise": {"green": (75, 100), "yellow": (50, 74), "red": (0, 49)},
    "mid-market": {"green": (70, 100), "yellow": (45, 69), "red": (0, 44)},
    "smb": {"green": (65, 100), "yellow": (40, 64), "red": (0, 39)},
}

# Benchmarks per segment for normalising raw metrics
SEGMENT_BENCHMARKS: Dict[str, Dict[str, Any]] = {
    "enterprise": {
        "login_frequency_target": 90,
        "feature_adoption_target": 80,
        "dau_mau_target": 0.50,
        "support_ticket_volume_max": 5,
        "meeting_attendance_target": 95,
        "nps_target": 9,
        "csat_target": 4.5,
        "open_tickets_max": 10,
        "escalation_rate_max": 0.25,
        "avg_resolution_hours_max": 72,
        "exec_sponsor_target": 90,
        "multi_threading_target": 5,
    },
    "mid-market": {
        "login_frequency_target": 80,
        "feature_adoption_target": 70,
        "dau_mau_target": 0.40,
        "support_ticket_volume_max": 8,
        "meeting_attendance_target": 85,
        "nps_target": 8,
        "csat_target": 4.0,
        "open_tickets_max": 15,
        "escalation_rate_max": 0.30,
        "avg_resolution_hours_max": 96,
        "exec_sponsor_target": 75,
        "multi_threading_target": 3,
    },
    "smb": {
        "login_frequency_target": 70,
        "feature_adoption_target": 60,
        "dau_mau_target": 0.30,
        "support_ticket_volume_max": 10,
        "meeting_attendance_target": 75,
        "nps_target": 7,
        "csat_target": 3.8,
        "open_tickets_max": 20,
        "escalation_rate_max": 0.40,
        "avg_resolution_hours_max": 120,
        "exec_sponsor_target": 60,
        "multi_threading_target": 2,
    },
}

RENEWAL_SENTIMENT_SCORES: Dict[str, float] = {
    "positive": 100.0,
    "neutral": 60.0,
    "negative": 20.0,
    "unknown": 50.0,
}


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def safe_divide(numerator: float, denominator: float, default: float = 0.0) -> float:
    """Return numerator / denominator, or *default* when denominator is zero."""
    if denominator == 0:
        return default
    return numerator / denominator


def clamp(value: float, lo: float = 0.0, hi: float = 100.0) -> float:
    """Clamp *value* between *lo* and *hi*."""
    return max(lo, min(hi, value))


def get_benchmarks(segment: str) -> Dict[str, Any]:
    """Return benchmarks for the given segment, falling back to mid-market."""
    return SEGMENT_BENCHMARKS.get(segment.lower(), SEGMENT_BENCHMARKS["mid-market"])


def get_thresholds(segment: str) -> Dict[str, Tuple[int, int]]:
    """Return classification thresholds for the given segment."""
    return SEGMENT_THRESHOLDS.get(segment.lower(), SEGMENT_THRESHOLDS["mid-market"])


def classify(score: float, segment: str) -> str:
    """Return 'green', 'yellow', or 'red' classification."""
    thresholds = get_thresholds(segment)
    if score >= thresholds["green"][0]:
        return "green"
    elif score >= thresholds["yellow"][0]:
        return "yellow"
    return "red"


def trend_direction(current: float, previous: Optional[float]) -> str:
    """Return trend direction string."""
    if previous is None:
        return "no_data"
    diff = current - previous
    if diff > 5:
        return "improving"
    elif diff < -5:
        return "declining"
    return "stable"


# ---------------------------------------------------------------------------
# Dimension Scoring
# ---------------------------------------------------------------------------


def score_usage(data: Dict[str, Any], benchmarks: Dict[str, Any]) -> Tuple[float, List[str]]:
    """Score the usage dimension (0-100).

    Metrics: login_frequency, feature_adoption, dau_mau_ratio.
    """
    recommendations: List[str] = []

    login = clamp(safe_divide(data.get("login_frequency", 0), benchmarks["login_frequency_target"]) * 100)
    adoption = clamp(safe_divide(data.get("feature_adoption", 0), benchmarks["feature_adoption_target"]) * 100)
    dau_mau = clamp(safe_divide(data.get("dau_mau_ratio", 0), benchmarks["dau_mau_target"]) * 100)

    score = round(login * 0.35 + adoption * 0.40 + dau_mau * 0.25, 1)

    if login < 60:
        recommendations.append("Login frequency below target -- schedule product engagement session")
    if adoption < 50:
        recommendations.append("Feature adoption is low -- recommend guided feature walkthrough")
    if dau_mau < 50:
        recommendations.append("DAU/MAU ratio indicates shallow usage -- investigate stickiness barriers")

    return score, recommendations


def score_engagement(data: Dict[str, Any], benchmarks: Dict[str, Any]) -> Tuple[float, List[str]]:
    """Score the engagement dimension (0-100).

    Metrics: support_ticket_volume (inverse), meeting_attendance, nps_score, csat_score.
    """
    recommendations: List[str] = []

    # Lower ticket volume is better -- invert
    ticket_vol = data.get("support_ticket_volume", 0)
    ticket_score = clamp((1.0 - safe_divide(ticket_vol, benchmarks["support_ticket_volume_max"])) * 100)

    attendance = clamp(safe_divide(data.get("meeting_attendance", 0), benchmarks["meeting_attendance_target"]) * 100)

    nps_raw = data.get("nps_score", 5)
    nps_score = clamp(safe_divide(nps_raw, benchmarks["nps_target"]) * 100)

    csat_raw = data.get("csat_score", 3.0)
    csat_score = clamp(safe_divide(csat_raw, benchmarks["csat_target"]) * 100)

    score = round(ticket_score * 0.20 + attendance * 0.30 + nps_score * 0.25 + csat_score * 0.25, 1)

    if attendance < 60:
        recommendations.append("Meeting attendance is low -- re-evaluate meeting cadence and agenda value")
    if nps_raw < 7:
        recommendations.append("NPS below threshold -- conduct a feedback deep-dive with customer")
    if csat_raw < 3.5:
        recommendations.append("CSAT is critically low -- escalate to support leadership")

    return score, recommendations


def score_support(data: Dict[str, Any], benchmarks: Dict[str, Any]) -> Tuple[float, List[str]]:
    """Score the support dimension (0-100).

    Metrics: open_tickets (inverse), escalation_rate (inverse), avg_resolution_hours (inverse).
    """
    recommendations: List[str] = []

    open_tix = data.get("open_tickets", 0)
    open_score = clamp((1.0 - safe_divide(open_tix, benchmarks["open_tickets_max"])) * 100)

    esc_rate = data.get("escalation_rate", 0)
    esc_score = clamp((1.0 - safe_divide(esc_rate, benchmarks["escalation_rate_max"])) * 100)

    res_hours = data.get("avg_resolution_hours", 0)
    res_score = clamp((1.0 - safe_divide(res_hours, benchmarks["avg_resolution_hours_max"])) * 100)

    score = round(open_score * 0.35 + esc_score * 0.35 + res_score * 0.30, 1)

    if open_tix > benchmarks["open_tickets_max"] * 0.5:
        recommendations.append("Open ticket count elevated -- prioritise ticket resolution")
    if esc_rate > benchmarks["escalation_rate_max"] * 0.5:
        recommendations.append("Escalation rate too high -- review support process and training")
    if res_hours > benchmarks["avg_resolution_hours_max"] * 0.5:
        recommendations.append("Resolution time exceeds SLA target -- engage support leadership")

    return score, recommendations


def score_relationship(data: Dict[str, Any], benchmarks: Dict[str, Any]) -> Tuple[float, List[str]]:
    """Score the relationship dimension (0-100).

    Metrics: executive_sponsor_engagement, multi_threading_depth, renewal_sentiment.
    """
    recommendations: List[str] = []

    exec_score = clamp(safe_divide(data.get("executive_sponsor_engagement", 0), benchmarks["exec_sponsor_target"]) * 100)

    threading = data.get("multi_threading_depth", 1)
    thread_score = clamp(safe_divide(threading, benchmarks["multi_threading_target"]) * 100)

    sentiment_str = data.get("renewal_sentiment", "unknown").lower()
    sentiment_score = RENEWAL_SENTIMENT_SCORES.get(sentiment_str, 50.0)

    score = round(exec_score * 0.35 + thread_score * 0.30 + sentiment_score * 0.35, 1)

    if exec_score < 50:
        recommendations.append("Executive sponsor engagement is weak -- schedule executive alignment meeting")
    if threading < 2:
        recommendations.append("Single-threaded relationship -- expand contacts across departments")
    if sentiment_str == "negative":
        recommendations.append("Renewal sentiment is negative -- initiate save plan immediately")

    return score, recommendations


# ---------------------------------------------------------------------------
# Main Scoring
# ---------------------------------------------------------------------------


def calculate_health_score(customer: Dict[str, Any]) -> Dict[str, Any]:
    """Calculate the overall health score for a single customer."""
    segment = customer.get("segment", "mid-market").lower()
    benchmarks = get_benchmarks(segment)

    # Score each dimension
    usage_score, usage_recs = score_usage(customer.get("usage", {}), benchmarks)
    engagement_score, engagement_recs = score_engagement(customer.get("engagement", {}), benchmarks)
    support_score, support_recs = score_support(customer.get("support", {}), benchmarks)
    relationship_score, relationship_recs = score_relationship(customer.get("relationship", {}), benchmarks)

    # Weighted overall
    overall = round(
        usage_score * DIMENSION_WEIGHTS["usage"]
        + engagement_score * DIMENSION_WEIGHTS["engagement"]
        + support_score * DIMENSION_WEIGHTS["support"]
        + relationship_score * DIMENSION_WEIGHTS["relationship"],
        1,
    )

    classification = classify(overall, segment)

    # Trend analysis
    prev = customer.get("previous_period", {})
    trends = {
        "usage": trend_direction(usage_score, prev.get("usage_score")),
        "engagement": trend_direction(engagement_score, prev.get("engagement_score")),
        "support": trend_direction(support_score, prev.get("support_score")),
        "relationship": trend_direction(relationship_score, prev.get("relationship_score")),
    }
    overall_prev = prev.get("overall_score")
    trends["overall"] = trend_direction(overall, overall_prev)

    # Combine recommendations
    all_recs = usage_recs + engagement_recs + support_recs + relationship_recs

    return {
        "customer_id": customer.get("customer_id", "unknown"),
        "name": customer.get("name", "Unknown"),
        "segment": segment,
        "arr": customer.get("arr", 0),
        "overall_score": overall,
        "classification": classification,
        "dimensions": {
            "usage": {"score": usage_score, "weight": "30%", "classification": classify(usage_score, segment)},
            "engagement": {"score": engagement_score, "weight": "25%", "classification": classify(engagement_score, segment)},
            "support": {"score": support_score, "weight": "20%", "classification": classify(support_score, segment)},
            "relationship": {"score": relationship_score, "weight": "25%", "classification": classify(relationship_score, segment)},
        },
        "trends": trends,
        "recommendations": all_recs,
    }


# ---------------------------------------------------------------------------
# Output Formatting
# ---------------------------------------------------------------------------

CLASSIFICATION_LABELS = {
    "green": "HEALTHY",
    "yellow": "NEEDS ATTENTION",
    "red": "AT RISK",
}


def format_text(results: List[Dict[str, Any]]) -> str:
    """Format results as human-readable text."""
    lines: List[str] = []
    lines.append("=" * 72)
    lines.append("CUSTOMER HEALTH SCORE REPORT")
    lines.append("=" * 72)
    lines.append("")

    # Portfolio summary
    total = len(results)
    green_count = sum(1 for r in results if r["classification"] == "green")
    yellow_count = sum(1 for r in results if r["classification"] == "yellow")
    red_count = sum(1 for r in results if r["classification"] == "red")
    avg_score = round(safe_divide(sum(r["overall_score"] for r in results), total), 1)

    lines.append(f"Portfolio Summary: {total} customers")
    lines.append(f"  Average Health Score: {avg_score}/100")
    lines.append(f"  Green (Healthy):       {green_count}")
    lines.append(f"  Yellow (Attention):     {yellow_count}")
    lines.append(f"  Red (At Risk):         {red_count}")
    lines.append("")

    for r in results:
        label = CLASSIFICATION_LABELS.get(r["classification"], "UNKNOWN")
        lines.append("-" * 72)
        lines.append(f"Customer: {r['name']} ({r['customer_id']})")
        lines.append(f"Segment:  {r['segment'].title()}  |  ARR: ${r['arr']:,.0f}")
        lines.append(f"Overall Score: {r['overall_score']}/100  [{label}]")
        lines.append("")

        lines.append("  Dimension Scores:")
        for dim_name, dim_data in r["dimensions"].items():
            dim_label = CLASSIFICATION_LABELS.get(dim_data["classification"], "")
            lines.append(f"    {dim_name.title():15s} {dim_data['score']:6.1f}/100  ({dim_data['weight']})  [{dim_label}]")

        lines.append("")
        lines.append("  Trends:")
        for dim_name, direction in r["trends"].items():
            arrow = {"improving": "+", "declining": "-", "stable": "=", "no_data": "?"}
            lines.append(f"    {dim_name.title():15s} {arrow.get(direction, '?')} {direction}")

        if r["recommendations"]:
            lines.append("")
            lines.append("  Recommendations:")
            for i, rec in enumerate(r["recommendations"], 1):
                lines.append(f"    {i}. {rec}")

        lines.append("")

    lines.append("=" * 72)
    return "\n".join(lines)


def format_json(results: List[Dict[str, Any]]) -> str:
    """Format results as JSON."""
    total = len(results)
    output = {
        "report": "customer_health_scores",
        "summary": {
            "total_customers": total,
            "average_score": round(safe_divide(sum(r["overall_score"] for r in results), total), 1),
            "green_count": sum(1 for r in results if r["classification"] == "green"),
            "yellow_count": sum(1 for r in results if r["classification"] == "yellow"),
            "red_count": sum(1 for r in results if r["classification"] == "red"),
        },
        "customers": results,
    }
    return json.dumps(output, indent=2)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


# Embedded synthetic fixture for --sample (two customers across segments).
SAMPLE_DATA = {
    "customers": [
        {
            "customer_id": "C-001",
            "name": "Acme Corp",
            "segment": "enterprise",
            "arr": 240000,
            "usage": {"dau_mau_ratio": 0.55, "license_utilization": 0.82},
            "engagement": {"qbr_attendance": 1.0, "champion_engaged": True},
            "support": {"open_tickets": 2, "csat": 4.6},
            "relationship": {"nps": 9, "exec_sponsor": True},
        },
        {
            "customer_id": "C-002",
            "name": "Globex Ltd",
            "segment": "smb",
            "arr": 18000,
            "usage": {"dau_mau_ratio": 0.12, "license_utilization": 0.35},
            "engagement": {"qbr_attendance": 0.0, "champion_engaged": False},
            "support": {"open_tickets": 7, "csat": 3.1},
            "relationship": {"nps": 4, "exec_sponsor": False},
        },
    ]
}


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Calculate multi-dimensional customer health scores with trend analysis."
    )
    parser.add_argument("input_file", nargs="?", help="Path to JSON file containing customer data")
    parser.add_argument(
        "--format",
        choices=["text", "json"],
        default="text",
        dest="output_format",
        help="Output format (default: text)",
    )
    parser.add_argument(
        "--sample",
        action="store_true",
        help="Run with an embedded synthetic customer fixture (no input file needed)",
    )
    args = parser.parse_args()

    if args.sample:
        if args.input_file:
            print("Warning: --sample specified; ignoring input_file", file=sys.stderr)
        data = SAMPLE_DATA
    else:
        if not args.input_file:
            parser.error("input_file is required (or use --sample)")
        try:
            with open(args.input_file, "r") as f:
                data = json.load(f)
        except FileNotFoundError:
            print(f"Error: File not found: {args.input_file}", file=sys.stderr)
            sys.exit(1)
        except json.JSONDecodeError as e:
            print(f"Error: Invalid JSON in {args.input_file}: {e}", file=sys.stderr)
            sys.exit(1)

    customers = data.get("customers", [])
    if not customers:
        print("Error: No customer records found in input file.", file=sys.stderr)
        sys.exit(1)

    results = [calculate_health_score(c) for c in customers]

    if args.output_format == "json":
        print(format_json(results))
    else:
        print(format_text(results))


if __name__ == "__main__":
    main()
