#!/usr/bin/env python3
"""
Churn Risk Analyzer

Identifies at-risk customer accounts by scoring behavioral signals across
usage decline, engagement drop, support issues, relationship signals, and
commercial factors. Produces risk tiers with intervention playbooks and
time-to-renewal urgency multipliers.

Usage:
    python churn_risk_analyzer.py customer_data.json
    python churn_risk_analyzer.py customer_data.json --format json
"""

import argparse
import json
import sys
from datetime import datetime
from typing import Any, Dict, List, Optional, Tuple


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

RISK_SIGNAL_WEIGHTS: Dict[str, float] = {
    "usage_decline": 0.30,
    "engagement_drop": 0.25,
    "support_issues": 0.20,
    "relationship_signals": 0.15,
    "commercial_factors": 0.10,
}

RISK_TIERS: List[Dict[str, Any]] = [
    {"name": "critical", "min": 80, "max": 100, "label": "CRITICAL", "action": "Immediate executive escalation"},
    {"name": "high", "min": 60, "max": 79, "label": "HIGH", "action": "Urgent CSM intervention"},
    {"name": "medium", "min": 40, "max": 59, "label": "MEDIUM", "action": "Proactive outreach"},
    {"name": "low", "min": 0, "max": 39, "label": "LOW", "action": "Standard monitoring"},
]

WARNING_SEVERITY: Dict[str, int] = {
    "critical": 4,
    "high": 3,
    "medium": 2,
    "low": 1,
}

# Intervention playbooks per tier
INTERVENTION_PLAYBOOKS: Dict[str, List[str]] = {
    "critical": [
        "Schedule executive-to-executive call within 48 hours",
        "Create detailed save plan with specific value milestones",
        "Offer concessions or contract restructuring if needed",
        "Assign dedicated rescue team (CSM + Solutions Engineer)",
        "Daily internal stand-up on account status until stabilised",
        "Prepare competitive displacement defence strategy",
    ],
    "high": [
        "Schedule urgent CSM call within 1 week",
        "Conduct root cause analysis on declining metrics",
        "Build 30-day recovery plan with measurable checkpoints",
        "Re-engage executive sponsor for alignment meeting",
        "Accelerate any pending feature requests or bug fixes",
        "Increase touch frequency to weekly until improvement",
    ],
    "medium": [
        "Schedule proactive check-in within 2 weeks",
        "Share relevant success stories and best practices",
        "Propose training session or product walkthrough",
        "Review current usage against success plan goals",
        "Identify and address any unvoiced concerns",
        "Bi-weekly monitoring until score improves to Low",
    ],
    "low": [
        "Maintain standard touch cadence",
        "Share product updates and new feature announcements",
        "Monitor health score trends monthly",
        "Proactively share relevant industry insights",
        "Prepare for upcoming renewal conversations (if within 90 days)",
    ],
}

SATISFACTION_TREND_SCORES: Dict[str, float] = {
    "improving": 10.0,
    "stable": 30.0,
    "declining": 70.0,
    "critical": 95.0,
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


def days_until(date_str: Optional[str]) -> Optional[int]:
    """Return days from today until *date_str* (ISO format), or None."""
    if not date_str:
        return None
    try:
        target = datetime.strptime(date_str[:10], "%Y-%m-%d")
        delta = (target - datetime.now()).days
        return max(delta, 0)
    except (ValueError, TypeError):
        return None


def renewal_urgency_multiplier(days_remaining: Optional[int]) -> float:
    """Return a multiplier (1.0 - 1.5) based on proximity to renewal.

    Closer renewals amplify the risk score.
    """
    if days_remaining is None:
        return 1.0
    if days_remaining <= 30:
        return 1.5
    elif days_remaining <= 60:
        return 1.35
    elif days_remaining <= 90:
        return 1.2
    elif days_remaining <= 180:
        return 1.1
    return 1.0


def get_risk_tier(score: float) -> Dict[str, Any]:
    """Return the risk tier dict matching the score."""
    for tier in RISK_TIERS:
        if tier["min"] <= score <= tier["max"]:
            return tier
    return RISK_TIERS[-1]  # default to low


# ---------------------------------------------------------------------------
# Signal Scoring
# ---------------------------------------------------------------------------


def score_usage_decline(data: Dict[str, Any]) -> Tuple[float, List[Dict[str, str]]]:
    """Score usage decline signals (0-100, higher = more risk)."""
    warnings: List[Dict[str, str]] = []

    login_trend = data.get("login_trend", 0)  # negative = decline
    feature_change = data.get("feature_adoption_change", 0)
    dau_mau_change = data.get("dau_mau_change", 0)

    # Convert declines to risk scores (0-100)
    login_risk = clamp(abs(min(login_trend, 0)) * 3.0)  # -33% => 100
    feature_risk = clamp(abs(min(feature_change, 0)) * 4.0)  # -25% => 100
    dau_mau_risk = clamp(abs(min(dau_mau_change, 0)) * 500)  # -0.20 => 100

    score = round(login_risk * 0.40 + feature_risk * 0.35 + dau_mau_risk * 0.25, 1)

    if login_trend <= -20:
        warnings.append({"severity": "critical", "signal": f"Login frequency dropped {abs(login_trend)}%"})
    elif login_trend <= -10:
        warnings.append({"severity": "high", "signal": f"Login frequency declined {abs(login_trend)}%"})
    elif login_trend < -5:
        warnings.append({"severity": "medium", "signal": f"Login frequency dipping {abs(login_trend)}%"})

    if feature_change <= -15:
        warnings.append({"severity": "high", "signal": f"Feature adoption dropped {abs(feature_change)}%"})
    elif feature_change < -5:
        warnings.append({"severity": "medium", "signal": f"Feature adoption declining {abs(feature_change)}%"})

    if dau_mau_change <= -0.10:
        warnings.append({"severity": "high", "signal": f"DAU/MAU ratio fell by {abs(dau_mau_change):.2f}"})

    return score, warnings


def score_engagement_drop(data: Dict[str, Any]) -> Tuple[float, List[Dict[str, str]]]:
    """Score engagement drop signals (0-100, higher = more risk)."""
    warnings: List[Dict[str, str]] = []

    cancellations = data.get("meeting_cancellations", 0)
    response_days = data.get("response_time_days", 1)
    nps_change = data.get("nps_change", 0)

    cancel_risk = clamp(cancellations * 25.0)  # 4 cancellations => 100
    response_risk = clamp((response_days - 1) * 15.0)  # 1 day baseline; 7+ days => 90+
    nps_risk = clamp(abs(min(nps_change, 0)) * 20.0)  # -5 => 100

    score = round(cancel_risk * 0.30 + response_risk * 0.35 + nps_risk * 0.35, 1)

    if cancellations >= 3:
        warnings.append({"severity": "critical", "signal": f"{cancellations} meeting cancellations -- customer disengaging"})
    elif cancellations >= 2:
        warnings.append({"severity": "high", "signal": f"{cancellations} meeting cancellations recently"})

    if response_days >= 7:
        warnings.append({"severity": "critical", "signal": f"Customer response time: {response_days} days -- going dark"})
    elif response_days >= 4:
        warnings.append({"severity": "high", "signal": f"Customer response time increasing: {response_days} days"})

    if nps_change <= -4:
        warnings.append({"severity": "critical", "signal": f"NPS dropped by {abs(nps_change)} points"})
    elif nps_change <= -2:
        warnings.append({"severity": "high", "signal": f"NPS declined by {abs(nps_change)} points"})

    return score, warnings


def score_support_issues(data: Dict[str, Any]) -> Tuple[float, List[Dict[str, str]]]:
    """Score support-related risk signals (0-100, higher = more risk)."""
    warnings: List[Dict[str, str]] = []

    escalations = data.get("open_escalations", 0)
    critical_unresolved = data.get("unresolved_critical", 0)
    sat_trend = data.get("satisfaction_trend", "stable").lower()

    esc_risk = clamp(escalations * 35.0)  # 3 escalations => 100
    critical_risk = clamp(critical_unresolved * 50.0)  # 2 unresolved critical => 100
    sat_risk = SATISFACTION_TREND_SCORES.get(sat_trend, 30.0)

    score = round(esc_risk * 0.35 + critical_risk * 0.35 + sat_risk * 0.30, 1)

    if critical_unresolved >= 2:
        warnings.append({"severity": "critical", "signal": f"{critical_unresolved} unresolved critical support tickets"})
    elif critical_unresolved >= 1:
        warnings.append({"severity": "high", "signal": "Unresolved critical support ticket"})

    if escalations >= 2:
        warnings.append({"severity": "high", "signal": f"{escalations} open escalations"})
    elif escalations >= 1:
        warnings.append({"severity": "medium", "signal": "Open support escalation"})

    if sat_trend == "critical":
        warnings.append({"severity": "critical", "signal": "Support satisfaction at critical levels"})
    elif sat_trend == "declining":
        warnings.append({"severity": "high", "signal": "Support satisfaction trending down"})

    return score, warnings


def score_relationship_signals(data: Dict[str, Any]) -> Tuple[float, List[Dict[str, str]]]:
    """Score relationship risk signals (0-100, higher = more risk)."""
    warnings: List[Dict[str, str]] = []
    risk_points = 0.0

    champion_left = data.get("champion_left", False)
    sponsor_change = data.get("sponsor_change", False)
    competitor_mentions = data.get("competitor_mentions", 0)

    if champion_left:
        risk_points += 45.0
        warnings.append({"severity": "critical", "signal": "Internal champion has left the organisation"})

    if sponsor_change:
        risk_points += 30.0
        warnings.append({"severity": "high", "signal": "Executive sponsor change detected"})

    if competitor_mentions >= 3:
        risk_points += 35.0
        warnings.append({"severity": "critical", "signal": f"Customer mentioned competitors {competitor_mentions} times"})
    elif competitor_mentions >= 1:
        risk_points += competitor_mentions * 12.0
        warnings.append({"severity": "medium", "signal": f"Customer mentioned competitor {competitor_mentions} time(s)"})

    score = clamp(risk_points)
    return round(score, 1), warnings


def score_commercial_factors(data: Dict[str, Any]) -> Tuple[float, List[Dict[str, str]]]:
    """Score commercial risk factors (0-100, higher = more risk)."""
    warnings: List[Dict[str, str]] = []
    risk_points = 0.0

    contract_type = data.get("contract_type", "annual").lower()
    pricing_complaints = data.get("pricing_complaints", False)
    budget_cuts = data.get("budget_cuts_mentioned", False)

    if contract_type == "month-to-month":
        risk_points += 30.0
        warnings.append({"severity": "medium", "signal": "Month-to-month contract -- low switching cost"})
    elif contract_type == "quarterly":
        risk_points += 15.0

    if pricing_complaints:
        risk_points += 35.0
        warnings.append({"severity": "high", "signal": "Customer has raised pricing complaints"})

    if budget_cuts:
        risk_points += 40.0
        warnings.append({"severity": "high", "signal": "Customer mentioned budget cuts or cost reduction"})

    score = clamp(risk_points)
    return round(score, 1), warnings


# ---------------------------------------------------------------------------
# Main Analysis
# ---------------------------------------------------------------------------


def analyse_churn_risk(customer: Dict[str, Any]) -> Dict[str, Any]:
    """Analyse churn risk for a single customer."""
    usage_score, usage_warnings = score_usage_decline(customer.get("usage_decline", {}))
    engagement_score, engagement_warnings = score_engagement_drop(customer.get("engagement_drop", {}))
    support_score, support_warnings = score_support_issues(customer.get("support_issues", {}))
    relationship_score, relationship_warnings = score_relationship_signals(customer.get("relationship_signals", {}))
    commercial_score, commercial_warnings = score_commercial_factors(customer.get("commercial_factors", {}))

    # Weighted raw score
    raw_score = (
        usage_score * RISK_SIGNAL_WEIGHTS["usage_decline"]
        + engagement_score * RISK_SIGNAL_WEIGHTS["engagement_drop"]
        + support_score * RISK_SIGNAL_WEIGHTS["support_issues"]
        + relationship_score * RISK_SIGNAL_WEIGHTS["relationship_signals"]
        + commercial_score * RISK_SIGNAL_WEIGHTS["commercial_factors"]
    )

    # Apply renewal urgency multiplier
    remaining = days_until(customer.get("contract_end_date"))
    multiplier = renewal_urgency_multiplier(remaining)
    adjusted_score = clamp(round(raw_score * multiplier, 1))

    tier = get_risk_tier(adjusted_score)

    # Collect and sort warnings by severity
    all_warnings = usage_warnings + engagement_warnings + support_warnings + relationship_warnings + commercial_warnings
    all_warnings.sort(key=lambda w: WARNING_SEVERITY.get(w["severity"], 0), reverse=True)

    playbook = INTERVENTION_PLAYBOOKS.get(tier["name"], [])

    return {
        "customer_id": customer.get("customer_id", "unknown"),
        "name": customer.get("name", "Unknown"),
        "segment": customer.get("segment", "unknown"),
        "arr": customer.get("arr", 0),
        "risk_score": adjusted_score,
        "raw_score": round(raw_score, 1),
        "risk_tier": tier["name"],
        "risk_label": tier["label"],
        "urgency_multiplier": multiplier,
        "days_to_renewal": remaining,
        "signal_scores": {
            "usage_decline": {"score": usage_score, "weight": "30%"},
            "engagement_drop": {"score": engagement_score, "weight": "25%"},
            "support_issues": {"score": support_score, "weight": "20%"},
            "relationship_signals": {"score": relationship_score, "weight": "15%"},
            "commercial_factors": {"score": commercial_score, "weight": "10%"},
        },
        "warning_signals": all_warnings,
        "recommended_actions": playbook,
    }


# ---------------------------------------------------------------------------
# Output Formatting
# ---------------------------------------------------------------------------


def format_text(results: List[Dict[str, Any]]) -> str:
    """Format results as human-readable text."""
    lines: List[str] = []
    lines.append("=" * 72)
    lines.append("CHURN RISK ANALYSIS REPORT")
    lines.append("=" * 72)
    lines.append("")

    total = len(results)
    critical_count = sum(1 for r in results if r["risk_tier"] == "critical")
    high_count = sum(1 for r in results if r["risk_tier"] == "high")
    medium_count = sum(1 for r in results if r["risk_tier"] == "medium")
    low_count = sum(1 for r in results if r["risk_tier"] == "low")
    total_arr_at_risk = sum(r["arr"] for r in results if r["risk_tier"] in ("critical", "high"))

    lines.append(f"Portfolio Summary: {total} customers analysed")
    lines.append(f"  Critical Risk: {critical_count}")
    lines.append(f"  High Risk:     {high_count}")
    lines.append(f"  Medium Risk:   {medium_count}")
    lines.append(f"  Low Risk:      {low_count}")
    lines.append(f"  ARR at Risk (Critical + High): ${total_arr_at_risk:,.0f}")
    lines.append("")

    # Sort by risk score descending
    sorted_results = sorted(results, key=lambda r: r["risk_score"], reverse=True)

    for r in sorted_results:
        lines.append("-" * 72)
        lines.append(f"Customer: {r['name']} ({r['customer_id']})")
        lines.append(f"Segment:  {r['segment'].title()}  |  ARR: ${r['arr']:,.0f}")
        renewal_str = f"{r['days_to_renewal']} days" if r["days_to_renewal"] is not None else "N/A"
        lines.append(f"Risk Score: {r['risk_score']}/100  [{r['risk_label']}]  |  Renewal: {renewal_str}")
        if r["urgency_multiplier"] > 1.0:
            lines.append(f"  ** Urgency multiplier applied: {r['urgency_multiplier']}x (renewal approaching)")
        lines.append("")

        lines.append("  Signal Scores:")
        for signal_name, signal_data in r["signal_scores"].items():
            display_name = signal_name.replace("_", " ").title()
            lines.append(f"    {display_name:25s} {signal_data['score']:6.1f}/100  ({signal_data['weight']})")

        if r["warning_signals"]:
            lines.append("")
            lines.append("  Warning Signals:")
            for w in r["warning_signals"]:
                severity_tag = w["severity"].upper()
                lines.append(f"    [{severity_tag}] {w['signal']}")

        if r["recommended_actions"]:
            lines.append("")
            lines.append("  Recommended Actions:")
            for i, action in enumerate(r["recommended_actions"], 1):
                lines.append(f"    {i}. {action}")

        lines.append("")

    lines.append("=" * 72)
    return "\n".join(lines)


def format_json(results: List[Dict[str, Any]]) -> str:
    """Format results as JSON."""
    total = len(results)
    output = {
        "report": "churn_risk_analysis",
        "summary": {
            "total_customers": total,
            "critical_count": sum(1 for r in results if r["risk_tier"] == "critical"),
            "high_count": sum(1 for r in results if r["risk_tier"] == "high"),
            "medium_count": sum(1 for r in results if r["risk_tier"] == "medium"),
            "low_count": sum(1 for r in results if r["risk_tier"] == "low"),
            "total_arr_at_risk": sum(r["arr"] for r in results if r["risk_tier"] in ("critical", "high")),
        },
        "customers": sorted(results, key=lambda r: r["risk_score"], reverse=True),
    }
    return json.dumps(output, indent=2)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Analyse churn risk with behavioral signal detection and intervention recommendations."
    )
    parser.add_argument("input_file", help="Path to JSON file containing customer data")
    parser.add_argument(
        "--format",
        choices=["text", "json"],
        default="text",
        dest="output_format",
        help="Output format (default: text)",
    )
    args = parser.parse_args()

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

    results = [analyse_churn_risk(c) for c in customers]

    if args.output_format == "json":
        print(format_json(results))
    else:
        print(format_text(results))


if __name__ == "__main__":
    main()
