#!/usr/bin/env python3
"""customer_segmentation_designer.py — Design tiered segmentation + ICP fit scoring.

Stdlib-only. Takes a customer list and outputs:
  - Tier assignment (Strategic / Enterprise / Mid-market / SMB-long-tail)
  - ICP fit score per customer (0-10) based on weighted attributes
  - Differential investment recommendation per tier
  - Kill list (customers below investment-payback floor)

Deterministic logic. Same input -> same output.

Input schema (JSON):
{
  "customers": [
    {
      "name": "AcmeCorp",
      "arr_usd": 180000,
      "tenure_months": 18,
      "icp_fit_signals": {
        "in_target_industry": true,
        "in_target_size_range": true,
        "uses_target_workflow": true,
        "has_executive_sponsor": true,
        "advocates_publicly": false,
        "expansion_potential_high": true,
        "competitor_concentration_low": true
      },
      "annual_support_cost_usd": 8000   # CSM time + support time + custom work
    }
  ]
}

Usage:
    python customer_segmentation_designer.py                       # uses embedded sample
    python customer_segmentation_designer.py path/to/customers.json
    python customer_segmentation_designer.py customers.json --output json
"""

import argparse
import json
import sys
from typing import Any, Dict, List, Tuple


SAMPLE: Dict[str, Any] = {
    "customers": [
        {
            "name": "MegaCorp Industries",
            "arr_usd": 420_000,
            "tenure_months": 26,
            "icp_fit_signals": {
                "in_target_industry": True,
                "in_target_size_range": True,
                "uses_target_workflow": True,
                "has_executive_sponsor": True,
                "advocates_publicly": True,
                "expansion_potential_high": True,
                "competitor_concentration_low": True,
            },
            "annual_support_cost_usd": 35000,
        },
        {
            "name": "MidSize Co.",
            "arr_usd": 38_000,
            "tenure_months": 12,
            "icp_fit_signals": {
                "in_target_industry": True,
                "in_target_size_range": True,
                "uses_target_workflow": True,
                "has_executive_sponsor": False,
                "advocates_publicly": False,
                "expansion_potential_high": True,
                "competitor_concentration_low": True,
            },
            "annual_support_cost_usd": 4500,
        },
        {
            "name": "Misfit Customer LLC",
            "arr_usd": 12_000,
            "tenure_months": 8,
            "icp_fit_signals": {
                "in_target_industry": False,
                "in_target_size_range": True,
                "uses_target_workflow": False,
                "has_executive_sponsor": False,
                "advocates_publicly": False,
                "expansion_potential_high": False,
                "competitor_concentration_low": False,
            },
            "annual_support_cost_usd": 14000,
        },
        {
            "name": "Small Biz",
            "arr_usd": 2_400,
            "tenure_months": 4,
            "icp_fit_signals": {
                "in_target_industry": True,
                "in_target_size_range": False,
                "uses_target_workflow": True,
                "has_executive_sponsor": False,
                "advocates_publicly": False,
                "expansion_potential_high": False,
                "competitor_concentration_low": True,
            },
            "annual_support_cost_usd": 500,
        },
        {
            "name": "Enterprise Co",
            "arr_usd": 75_000,
            "tenure_months": 15,
            "icp_fit_signals": {
                "in_target_industry": True,
                "in_target_size_range": True,
                "uses_target_workflow": True,
                "has_executive_sponsor": True,
                "advocates_publicly": False,
                "expansion_potential_high": True,
                "competitor_concentration_low": True,
            },
            "annual_support_cost_usd": 9000,
        },
    ]
}


# ICP signal weights (sum to 10)
ICP_WEIGHTS = {
    "in_target_industry": 2.0,
    "in_target_size_range": 1.5,
    "uses_target_workflow": 2.0,
    "has_executive_sponsor": 1.5,
    "advocates_publicly": 1.0,
    "expansion_potential_high": 1.0,
    "competitor_concentration_low": 1.0,
}


# Tier definitions: ARR ranges + recommended coverage + investment
TIER_DEFINITIONS = [
    {
        "tier": "Strategic",
        "arr_min": 100_000,
        "coverage": "Named CSM + executive sponsor",
        "investment_per_account_yr_min": 20000,
        "investment_per_account_yr_max": 50000,
    },
    {
        "tier": "Enterprise",
        "arr_min": 20_000,
        "coverage": "Named CSM",
        "investment_per_account_yr_min": 5000,
        "investment_per_account_yr_max": 15000,
    },
    {
        "tier": "Mid-market",
        "arr_min": 5_000,
        "coverage": "Pooled CSM + automation",
        "investment_per_account_yr_min": 1000,
        "investment_per_account_yr_max": 3000,
    },
    {
        "tier": "SMB / Long-tail",
        "arr_min": 0,
        "coverage": "Tech-touch + self-serve",
        "investment_per_account_yr_min": 50,
        "investment_per_account_yr_max": 500,
    },
]


def assign_tier(arr: float) -> Dict[str, Any]:
    for t in TIER_DEFINITIONS:
        if arr >= t["arr_min"]:
            return t
    return TIER_DEFINITIONS[-1]


def icp_fit_score(signals: Dict[str, bool]) -> float:
    score = 0.0
    for signal, weight in ICP_WEIGHTS.items():
        if signals.get(signal, False):
            score += weight
    return round(score, 1)


def analyze_customer(c: Dict[str, Any]) -> Dict[str, Any]:
    arr = c.get("arr_usd", 0)
    tier_def = assign_tier(arr)
    fit_score = icp_fit_score(c.get("icp_fit_signals", {}))
    support_cost = c.get("annual_support_cost_usd", 0)

    # Investment-to-ARR ratio
    cost_ratio = (support_cost / arr) if arr else float("inf")

    # Kill list candidate: support cost > 50% of ARR AND ICP fit < 5
    kill_candidate = cost_ratio > 0.5 and fit_score < 5.0

    # Strategic upgrade candidate: at top of current tier + high ICP fit + expansion potential
    upgrade_signal = (
        fit_score >= 8.0
        and c.get("icp_fit_signals", {}).get("expansion_potential_high", False)
    )

    return {
        "name": c.get("name"),
        "arr_usd": arr,
        "tenure_months": c.get("tenure_months", 0),
        "tier": tier_def["tier"],
        "coverage": tier_def["coverage"],
        "investment_floor_yr": tier_def["investment_per_account_yr_min"],
        "investment_ceiling_yr": tier_def["investment_per_account_yr_max"],
        "icp_fit_score": fit_score,
        "annual_support_cost_usd": support_cost,
        "support_cost_pct_of_arr": round(cost_ratio * 100, 1) if cost_ratio != float("inf") else None,
        "kill_candidate": kill_candidate,
        "upgrade_candidate": upgrade_signal,
    }


def aggregate(customer_results: List[Dict[str, Any]]) -> Dict[str, Any]:
    by_tier: Dict[str, List[Dict[str, Any]]] = {t["tier"]: [] for t in TIER_DEFINITIONS}
    for r in customer_results:
        by_tier[r["tier"]].append(r)

    summary = []
    total_arr = sum(r["arr_usd"] for r in customer_results)
    for t in TIER_DEFINITIONS:
        tier_customers = by_tier[t["tier"]]
        tier_arr = sum(c["arr_usd"] for c in tier_customers)
        summary.append({
            "tier": t["tier"],
            "customer_count": len(tier_customers),
            "tier_arr": tier_arr,
            "tier_arr_pct_of_total": round((tier_arr / total_arr * 100) if total_arr else 0, 1),
            "coverage": t["coverage"],
            "investment_per_account_yr": f"${t['investment_per_account_yr_min']:,}-${t['investment_per_account_yr_max']:,}",
        })

    kill_list = [r for r in customer_results if r["kill_candidate"]]
    upgrade_list = [r for r in customer_results if r["upgrade_candidate"]]

    return {
        "tier_summary": summary,
        "kill_list": kill_list,
        "upgrade_list": upgrade_list,
        "total_arr": total_arr,
        "total_customers": len(customer_results),
    }


def analyze(payload: Dict[str, Any]) -> Dict[str, Any]:
    customers = [analyze_customer(c) for c in payload.get("customers", [])]
    return {
        "customers": customers,
        "summary": aggregate(customers),
    }


def render_text(result: Dict[str, Any], source: str) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("CUSTOMER SEGMENTATION DESIGN")
    lines.append(f"Source: {source}")
    lines.append("=" * 72)
    lines.append("")

    s = result["summary"]
    lines.append(f"Total customers: {s['total_customers']}  |  Total ARR: ${s['total_arr']:,.0f}")
    lines.append("")
    lines.append("TIER BREAKDOWN:")
    lines.append("")
    for t in s["tier_summary"]:
        lines.append(f"  {t['tier']:<20} {t['customer_count']:>3} customers  ${t['tier_arr']:>10,.0f}  ({t['tier_arr_pct_of_total']:.1f}% of ARR)")
        lines.append(f"    Coverage: {t['coverage']}")
        lines.append(f"    Investment per account/yr: {t['investment_per_account_yr']}")
        lines.append("")
    lines.append("-" * 72)

    if s["kill_list"]:
        lines.append(f"")
        lines.append(f"🔴 KILL LIST ({len(s['kill_list'])} customers): support cost > 50% of ARR AND ICP fit < 5")
        for k in s["kill_list"]:
            lines.append(f"   • {k['name']}: ARR ${k['arr_usd']:,.0f}, support ${k['annual_support_cost_usd']:,.0f} ({k['support_cost_pct_of_arr']}%), ICP fit {k['icp_fit_score']}/10")
        lines.append("")
        lines.append("   Recommendation: do not renew, OR downgrade to tech-touch, OR raise price to cost-recover.")
        lines.append("")

    if s["upgrade_list"]:
        lines.append(f"")
        lines.append(f"🟢 UPGRADE CANDIDATES ({len(s['upgrade_list'])} customers): high ICP fit + expansion potential")
        for u in s["upgrade_list"]:
            lines.append(f"   • {u['name']}: tier {u['tier']}, ICP fit {u['icp_fit_score']}/10, ARR ${u['arr_usd']:,.0f}")
        lines.append("")
        lines.append("   Recommendation: assign named CSM (if not already) + executive sponsor + expansion playbook.")
        lines.append("")

    lines.append("-" * 72)
    lines.append("PER-CUSTOMER DETAIL:")
    lines.append("")
    for c in result["customers"]:
        markers = ""
        if c["kill_candidate"]:
            markers += " 🔴"
        if c["upgrade_candidate"]:
            markers += " 🟢"
        lines.append(f"  {c['name']:<25} ${c['arr_usd']:>8,.0f}   {c['tier']:<20}  ICP fit: {c['icp_fit_score']}/10{markers}")
    lines.append("")
    lines.append("-" * 72)
    lines.append("REMINDER: Segmentation is a quarterly review. Customers migrate between tiers; ICP fit drifts.")
    lines.append("Pair this output with cs_coverage_calculator.py to size the CS team for the new segmentation.")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Design customer segmentation tiers + ICP fit scoring + differential investment.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("path", nargs="?", help="Path to customers JSON (uses embedded sample if omitted)")
    parser.add_argument("--output", choices=("text", "json"), default="text", help="Output format")
    args = parser.parse_args()

    if args.path:
        try:
            with open(args.path, "r", encoding="utf-8") as f:
                payload = json.load(f)
            source = args.path
        except (IOError, OSError) as e:
            print(f"error: could not read {args.path}: {e}", file=sys.stderr)
            return 1
        except json.JSONDecodeError as e:
            print(f"error: invalid JSON in {args.path}: {e}", file=sys.stderr)
            return 1
    else:
        payload = SAMPLE
        source = "<embedded sample: 5 mixed B2B SaaS customers>"

    result = analyze(payload)

    if args.output == "json":
        print(json.dumps({"source": source, **result}, indent=2))
    else:
        print(render_text(result, source))

    return 0


if __name__ == "__main__":
    sys.exit(main())
