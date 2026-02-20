#!/usr/bin/env python3
"""
Cognify Pain Point Scorer

Takes pain point data as JSON and outputs priority-scored rankings.
Used by the skill to provide consistent, reproducible scoring.

Usage:
  echo '{"pain_points": [...]}' | python score_pain_points.py
"""

import json
import sys


def score_pain_points(data: dict) -> list[dict]:
    """Score and rank pain points using the Cognify rubric."""
    scored = []
    for pp in data.get("pain_points", []):
        freq = pp.get("frequency", 1)
        impact = pp.get("impact", 1)
        solve = pp.get("solvability", 1)
        score = freq * impact * solve

        # Estimate hours saved
        base_hours = {5: 20, 3: 8, 1: 3}.get(freq, 5)
        hours_saved = round(base_hours * (impact / 3), 1)

        # Determine phase
        phase = {5: 1, 3: 2, 1: 3}.get(solve, 2)

        # Implementation hours
        impl_hours = {5: 12, 3: 24, 1: 48}.get(solve, 24)

        scored.append({
            "description": pp.get("description", ""),
            "category": pp.get("category", ""),
            "frequency": freq,
            "impact": impact,
            "solvability": solve,
            "priority_score": score,
            "estimated_hours_saved_monthly": hours_saved,
            "implementation_hours": impl_hours,
            "phase": phase,
        })

    scored.sort(key=lambda x: x["priority_score"], reverse=True)
    return scored


def calculate_roi(scored: list[dict], hourly_rate: float = 50.0) -> dict:
    """Calculate aggregate ROI from scored pain points."""
    total_hours = sum(p["estimated_hours_saved_monthly"] for p in scored[:5])
    total_savings = total_hours * hourly_rate
    total_platform = len(scored[:5]) * 150  # avg $150/mo per automation
    total_impl = sum(p["implementation_hours"] for p in scored[:5])
    impl_cost = total_impl * 150  # $150/hr consulting

    monthly_net = total_savings - total_platform
    payback = round(impl_cost / monthly_net, 1) if monthly_net > 0 else float("inf")
    annual_roi = round(((monthly_net * 12) - impl_cost) / impl_cost * 100, 1) if impl_cost > 0 else 0

    return {
        "monthly_hours_saved": round(total_hours, 1),
        "monthly_dollar_savings": round(total_savings, 2),
        "monthly_platform_cost": round(total_platform, 2),
        "monthly_net_value": round(monthly_net, 2),
        "implementation_cost": round(impl_cost, 2),
        "payback_months": payback,
        "annual_roi_percent": annual_roi,
    }


if __name__ == "__main__":
    data = json.load(sys.stdin)
    hourly_rate = data.get("avg_hourly_rate", 50.0)

    scored = score_pain_points(data)
    roi = calculate_roi(scored, hourly_rate)

    output = {
        "ranked_pain_points": scored,
        "roi_projection": roi,
        "recommendation_count": min(len(scored), 5),
    }

    print(json.dumps(output, indent=2))
