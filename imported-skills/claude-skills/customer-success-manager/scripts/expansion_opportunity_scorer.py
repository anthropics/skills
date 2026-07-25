#!/usr/bin/env python3
"""
Expansion Opportunity Scorer

Analyses customer product adoption depth, maps whitespace for unused
features/products, estimates revenue opportunities, and prioritises
expansion plays by effort vs impact.

Usage:
    python expansion_opportunity_scorer.py customer_data.json
    python expansion_opportunity_scorer.py customer_data.json --format json
"""

import argparse
import json
import sys
from typing import Any, Dict, List, Optional, Tuple


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

# Tier pricing multipliers (relative to current plan price)
TIER_UPLIFT: Dict[str, float] = {
    "starter": 1.0,
    "professional": 1.8,
    "enterprise": 3.0,
    "enterprise_plus": 4.5,
}

# Module revenue estimates as a fraction of base ARR
MODULE_REVENUE_FRACTION: Dict[str, float] = {
    "core_platform": 0.00,        # Already included in base
    "analytics_module": 0.15,
    "integrations_module": 0.12,
    "api_access": 0.10,
    "advanced_reporting": 0.18,
    "security_module": 0.20,
    "automation_module": 0.15,
    "collaboration_module": 0.10,
    "data_export": 0.08,
    "custom_workflows": 0.22,
    "sso_module": 0.08,
    "audit_module": 0.10,
}

# Effort classification for different expansion types
EFFORT_MAP: Dict[str, str] = {
    "upsell_tier": "medium",
    "cross_sell_module": "low",
    "seat_expansion": "low",
    "department_expansion": "high",
}

# Usage thresholds for recommendations
HIGH_USAGE_THRESHOLD = 75   # % usage indicates readiness for more
LOW_ADOPTION_THRESHOLD = 30  # % usage is too low to push expansion there


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


def estimate_seat_expansion_revenue(
    arr: float, licensed: int, active: int, segment: str
) -> Tuple[float, str]:
    """Estimate revenue from seat expansion.

    Returns (estimated_revenue, rationale).
    """
    utilisation = safe_divide(active, licensed)
    if utilisation >= 0.90:
        # Near capacity -- likely needs more seats
        growth_factor = {"enterprise": 0.25, "mid-market": 0.20, "smb": 0.15}
        factor = growth_factor.get(segment.lower(), 0.15)
        revenue = round(arr * factor, 0)
        return revenue, f"Seat utilisation at {utilisation:.0%} -- likely needs {int(licensed * factor)} additional seats"
    return 0.0, f"Seat utilisation at {utilisation:.0%} -- not yet at expansion threshold"


def estimate_tier_upgrade_revenue(
    arr: float, current_tier: str, available_tiers: List[str]
) -> Tuple[float, Optional[str], str]:
    """Estimate revenue from tier upgrade.

    Returns (estimated_revenue, target_tier, rationale).
    """
    current_mult = TIER_UPLIFT.get(current_tier.lower(), 1.0)
    best_revenue = 0.0
    best_tier = None
    rationale = "Already on highest tier"

    for tier in available_tiers:
        tier_mult = TIER_UPLIFT.get(tier.lower(), 1.0)
        if tier_mult > current_mult:
            # Calculate revenue as the incremental ARR from upgrading
            base_arr = safe_divide(arr, current_mult)
            upgrade_arr = base_arr * tier_mult
            incremental = upgrade_arr - arr
            if incremental > best_revenue:
                # Pick the next tier up (not skip tiers)
                if best_tier is None or tier_mult < TIER_UPLIFT.get(best_tier.lower(), 999):
                    best_revenue = round(incremental, 0)
                    best_tier = tier
                    rationale = f"Upgrade from {current_tier} to {tier} adds ${incremental:,.0f} ARR"

    return best_revenue, best_tier, rationale


def estimate_module_revenue(
    arr: float, product_usage: Dict[str, Dict[str, Any]]
) -> List[Dict[str, Any]]:
    """Identify cross-sell opportunities from unadopted modules.

    Returns list of opportunity dicts.
    """
    opportunities: List[Dict[str, Any]] = []

    for module_name, module_data in product_usage.items():
        adopted = module_data.get("adopted", False)
        usage_pct = module_data.get("usage_pct", 0)
        fraction = MODULE_REVENUE_FRACTION.get(module_name.lower(), 0.10)

        if not adopted and fraction > 0:
            revenue = round(arr * fraction, 0)
            opportunities.append({
                "module": module_name,
                "type": "cross_sell",
                "estimated_revenue": revenue,
                "effort": "low",
                "rationale": f"Module not adopted -- ${revenue:,.0f} potential ARR",
            })
        elif adopted and usage_pct < LOW_ADOPTION_THRESHOLD and fraction > 0:
            # Already adopted but underutilised -- focus on enablement, not expansion
            pass  # Skip -- needs enablement, not a sales motion

    return opportunities


def estimate_department_expansion_revenue(
    arr: float,
    current_departments: List[str],
    potential_departments: List[str],
    segment: str,
) -> List[Dict[str, Any]]:
    """Estimate revenue from expanding to new departments."""
    opportunities: List[Dict[str, Any]] = []
    current_set = {d.lower() for d in current_departments}
    per_dept_estimate = safe_divide(arr, max(len(current_departments), 1))

    for dept in potential_departments:
        if dept.lower() not in current_set:
            # Estimate each new department at the average per-department ARR
            revenue = round(per_dept_estimate * 0.8, 0)  # Slight discount for new dept
            opportunities.append({
                "department": dept,
                "type": "expansion",
                "estimated_revenue": revenue,
                "effort": "high",
                "rationale": f"Expand to {dept} department -- est. ${revenue:,.0f} ARR",
            })

    return opportunities


# ---------------------------------------------------------------------------
# Priority Scoring
# ---------------------------------------------------------------------------


def priority_score(revenue: float, effort: str) -> float:
    """Calculate priority score (higher = better).

    Favours high revenue with low effort.
    """
    effort_multiplier = {"low": 3.0, "medium": 2.0, "high": 1.0}
    mult = effort_multiplier.get(effort.lower(), 1.0)
    # Normalise revenue to a 0-100 scale (assume max single opportunity is $200k)
    rev_score = clamp(safe_divide(revenue, 2000.0))  # $200k => 100
    return round(rev_score * mult, 1)


# ---------------------------------------------------------------------------
# Main Analysis
# ---------------------------------------------------------------------------


def analyse_expansion(customer: Dict[str, Any]) -> Dict[str, Any]:
    """Analyse expansion opportunities for a single customer."""
    arr = customer.get("arr", 0)
    segment = customer.get("segment", "mid-market").lower()
    contract = customer.get("contract", {})
    product_usage = customer.get("product_usage", {})
    departments = customer.get("departments", {})

    all_opportunities: List[Dict[str, Any]] = []

    # 1. Seat expansion
    licensed = contract.get("licensed_seats", 0)
    active = contract.get("active_seats", 0)
    seat_rev, seat_rationale = estimate_seat_expansion_revenue(arr, licensed, active, segment)
    if seat_rev > 0:
        all_opportunities.append({
            "type": "expansion",
            "category": "seat_expansion",
            "estimated_revenue": seat_rev,
            "effort": "low",
            "rationale": seat_rationale,
            "priority_score": priority_score(seat_rev, "low"),
        })

    # 2. Tier upgrade
    current_tier = contract.get("plan_tier", "").lower()
    available_tiers = contract.get("available_tiers", [])
    tier_rev, target_tier, tier_rationale = estimate_tier_upgrade_revenue(arr, current_tier, available_tiers)
    if tier_rev > 0 and target_tier:
        all_opportunities.append({
            "type": "upsell",
            "category": "tier_upgrade",
            "target_tier": target_tier,
            "estimated_revenue": tier_rev,
            "effort": "medium",
            "rationale": tier_rationale,
            "priority_score": priority_score(tier_rev, "medium"),
        })

    # 3. Module cross-sell
    module_opps = estimate_module_revenue(arr, product_usage)
    for opp in module_opps:
        opp["category"] = "module_cross_sell"
        opp["priority_score"] = priority_score(opp["estimated_revenue"], opp["effort"])
        all_opportunities.append(opp)

    # 4. Department expansion
    current_depts = departments.get("current", [])
    potential_depts = departments.get("potential", [])
    dept_opps = estimate_department_expansion_revenue(arr, current_depts, potential_depts, segment)
    for opp in dept_opps:
        opp["category"] = "department_expansion"
        opp["priority_score"] = priority_score(opp["estimated_revenue"], opp["effort"])
        all_opportunities.append(opp)

    # Sort by priority score descending
    all_opportunities.sort(key=lambda o: o["priority_score"], reverse=True)

    # Adoption depth summary
    total_modules = len(product_usage)
    adopted_modules = sum(1 for m in product_usage.values() if m.get("adopted", False))
    avg_usage = round(
        safe_divide(
            sum(m.get("usage_pct", 0) for m in product_usage.values() if m.get("adopted", False)),
            max(adopted_modules, 1),
        ),
        1,
    )

    total_estimated_revenue = sum(o["estimated_revenue"] for o in all_opportunities)

    return {
        "customer_id": customer.get("customer_id", "unknown"),
        "name": customer.get("name", "Unknown"),
        "segment": segment,
        "arr": arr,
        "adoption_summary": {
            "total_modules": total_modules,
            "adopted_modules": adopted_modules,
            "adoption_rate": round(safe_divide(adopted_modules, total_modules) * 100, 1) if total_modules > 0 else 0,
            "avg_usage_pct": avg_usage,
            "seat_utilisation": round(safe_divide(active, max(licensed, 1)) * 100, 1),
            "current_tier": current_tier,
            "departments_covered": len(current_depts),
            "departments_potential": len(potential_depts),
        },
        "total_estimated_revenue": round(total_estimated_revenue, 0),
        "opportunity_count": len(all_opportunities),
        "opportunities": all_opportunities,
    }


# ---------------------------------------------------------------------------
# Output Formatting
# ---------------------------------------------------------------------------


def format_text(results: List[Dict[str, Any]]) -> str:
    """Format results as human-readable text."""
    lines: List[str] = []
    lines.append("=" * 72)
    lines.append("EXPANSION OPPORTUNITY REPORT")
    lines.append("=" * 72)
    lines.append("")

    total_rev = sum(r["total_estimated_revenue"] for r in results)
    total_opps = sum(r["opportunity_count"] for r in results)

    lines.append(f"Portfolio Summary: {len(results)} customers")
    lines.append(f"  Total Expansion Revenue Potential: ${total_rev:,.0f}")
    lines.append(f"  Total Opportunities Identified:    {total_opps}")
    lines.append("")

    # Sort customers by total estimated revenue descending
    sorted_results = sorted(results, key=lambda r: r["total_estimated_revenue"], reverse=True)

    for r in sorted_results:
        lines.append("-" * 72)
        lines.append(f"Customer: {r['name']} ({r['customer_id']})")
        lines.append(f"Segment:  {r['segment'].title()}  |  Current ARR: ${r['arr']:,.0f}")
        lines.append(f"Total Expansion Potential: ${r['total_estimated_revenue']:,.0f}  ({r['opportunity_count']} opportunities)")
        lines.append("")

        adoption = r["adoption_summary"]
        lines.append("  Adoption Summary:")
        lines.append(f"    Modules Adopted:    {adoption['adopted_modules']}/{adoption['total_modules']} ({adoption['adoption_rate']}%)")
        lines.append(f"    Avg Module Usage:   {adoption['avg_usage_pct']}%")
        lines.append(f"    Seat Utilisation:   {adoption['seat_utilisation']}%")
        lines.append(f"    Current Tier:       {adoption['current_tier'].title()}")
        lines.append(f"    Departments:        {adoption['departments_covered']} active, {adoption['departments_potential']} potential")

        if r["opportunities"]:
            lines.append("")
            lines.append("  Opportunities (ranked by priority):")
            for i, opp in enumerate(r["opportunities"], 1):
                opp_type = opp.get("type", "unknown").title()
                category = opp.get("category", "").replace("_", " ").title()
                rev = opp["estimated_revenue"]
                effort = opp.get("effort", "unknown").title()
                pri = opp.get("priority_score", 0)
                lines.append(f"    {i}. [{opp_type}] {category}")
                lines.append(f"       Revenue: ${rev:,.0f}  |  Effort: {effort}  |  Priority: {pri}")
                lines.append(f"       {opp.get('rationale', '')}")
        else:
            lines.append("")
            lines.append("  No expansion opportunities identified at this time.")

        lines.append("")

    lines.append("=" * 72)
    return "\n".join(lines)


def format_json(results: List[Dict[str, Any]]) -> str:
    """Format results as JSON."""
    total_rev = sum(r["total_estimated_revenue"] for r in results)
    total_opps = sum(r["opportunity_count"] for r in results)
    output = {
        "report": "expansion_opportunities",
        "summary": {
            "total_customers": len(results),
            "total_estimated_revenue": total_rev,
            "total_opportunities": total_opps,
        },
        "customers": sorted(results, key=lambda r: r["total_estimated_revenue"], reverse=True),
    }
    return json.dumps(output, indent=2)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Score expansion opportunities with adoption analysis and revenue estimation."
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

    results = [analyse_expansion(c) for c in customers]

    if args.output_format == "json":
        print(format_json(results))
    else:
        print(format_text(results))


if __name__ == "__main__":
    main()
