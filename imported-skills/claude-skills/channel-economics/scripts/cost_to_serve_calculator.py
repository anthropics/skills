#!/usr/bin/env python3
"""cost_to_serve_calculator.py

Computes fully-loaded cost-to-serve per deal AND per dollar of ARR for a
single channel. Breaks out direct vs. allocated overhead. Surfaces "hidden"
costs the average team forgets (partner enablement time, certification
investment, channel-conflict overhead) by flagging line items left at $0.

Stdlib-only. Deterministic.

Usage:
    python cost_to_serve_calculator.py --sample
    python cost_to_serve_calculator.py --input channel.json --output markdown
"""
from __future__ import annotations

import argparse
import json
import sys
from typing import Any

# ---- Hidden-cost line items (most-forgotten) -----------------------------
HIDDEN_COST_KEYS = {
    "partner_enablement_time": "Partner enablement time (AE/SE hours co-selling)",
    "certification_investment": "Partner certification + training investment",
    "channel_conflict_overhead": "Channel-conflict resolution overhead",
    "channel_manager_attribution": "Channel manager headcount attribution",
}

# ---- Cost categories -----------------------------------------------------
DIRECT_COST_KEYS = [
    "sdr_attribution",
    "ae_attribution",
    "sales_engineer_attribution",
    "channel_manager_attribution",
    "customer_success_attribution",
    "support_attribution",
    "marketing_attribution",
    "partner_discount",
    "partner_MDF",
    "partner_enablement_time",
    "certification_investment",
    "channel_conflict_overhead",
    "tooling_attribution",
]


def _num(v: Any, default: float = 0.0) -> float:
    try:
        return float(v)
    except (TypeError, ValueError):
        return default


def compute_cost_to_serve(payload: dict) -> dict:
    channel_name = payload.get("channel_name", "unnamed-channel")
    deal_volume = _num(payload.get("deal_volume"), 0)
    gross_revenue = _num(payload.get("gross_revenue"), 0)
    costs = payload.get("costs", {}) or {}

    if deal_volume <= 0 or gross_revenue <= 0:
        return {
            "error": "deal_volume and gross_revenue must both be > 0",
            "channel_name": channel_name,
        }

    # Direct costs (sum)
    direct_total = 0.0
    direct_breakdown = {}
    for key in DIRECT_COST_KEYS:
        v = _num(costs.get(key), 0)
        direct_breakdown[key] = v
        direct_total += v

    # Allocated overhead — applied as % of gross revenue
    overhead_pct = _num(costs.get("overhead_allocation_pct"), 0)
    if overhead_pct < 0 or overhead_pct > 100:
        return {
            "error": f"overhead_allocation_pct must be 0..100, got {overhead_pct}",
            "channel_name": channel_name,
        }
    overhead_total = gross_revenue * (overhead_pct / 100.0)

    total_loaded_cost = direct_total + overhead_total

    cost_per_deal = total_loaded_cost / deal_volume
    cost_per_arr_dollar = total_loaded_cost / gross_revenue
    true_gross_margin_pct = (1.0 - cost_per_arr_dollar) * 100.0

    # Hidden-cost surfacing — flag any HIDDEN_COST_KEYS that are $0
    hidden_flags = []
    for k, label in HIDDEN_COST_KEYS.items():
        if direct_breakdown.get(k, 0) == 0:
            hidden_flags.append(
                f"'{k}' is $0 — likely understated. {label} is the most-forgotten "
                "channel cost in industry benchmarks."
            )

    # Double-counting validation
    warnings = []
    if (
        direct_breakdown.get("partner_discount", 0) > 0
        and direct_breakdown.get("partner_MDF", 0) > 0
        and direct_breakdown.get("partner_MDF", 0) > direct_breakdown.get("partner_discount", 0)
    ):
        warnings.append(
            "MDF spend exceeds partner discount — verify MDF is not double-counted "
            "as discount in your channel agreements."
        )
    if overhead_pct > 50:
        warnings.append(
            f"Overhead allocation of {overhead_pct:.1f}% is unusually high. "
            "Verify denominator (revenue vs. gross profit) is consistent across channels."
        )
    if overhead_pct < 5 and "partner" in channel_name.lower():
        warnings.append(
            f"Partner channel overhead allocation of {overhead_pct:.1f}% is unusually low. "
            "Channel manager, partner program, certification all live in YOUR P&L. "
            "Inconsistent allocation is the #1 source of false partner-margin lift."
        )

    return {
        "channel_name": channel_name,
        "deal_volume": deal_volume,
        "gross_revenue": gross_revenue,
        "direct_breakdown": direct_breakdown,
        "direct_total": round(direct_total, 2),
        "overhead_allocation_pct": overhead_pct,
        "overhead_total": round(overhead_total, 2),
        "total_loaded_cost": round(total_loaded_cost, 2),
        "cost_per_deal": round(cost_per_deal, 2),
        "cost_per_arr_dollar": round(cost_per_arr_dollar, 4),
        "true_gross_margin_pct": round(true_gross_margin_pct, 2),
        "hidden_cost_flags": hidden_flags,
        "warnings": warnings,
    }


def render_markdown(r: dict) -> str:
    if "error" in r:
        return f"# Cost-to-Serve\n\n**ERROR**: {r['error']}\n"

    lines = [
        f"# Cost-to-Serve — {r['channel_name']}",
        "",
        "## Inputs",
        f"- Deal volume (TTM): **{r['deal_volume']:,.0f}**",
        f"- Gross revenue (TTM): **${r['gross_revenue']:,.0f}**",
        f"- Overhead allocation: **{r['overhead_allocation_pct']:.1f}%**",
        "",
        "## Direct cost breakdown",
        "| Line item | $ |",
        "|---|---:|",
    ]
    for k, v in r["direct_breakdown"].items():
        lines.append(f"| {k} | {v:,.0f} |")
    lines += [
        f"| **Direct total** | **{r['direct_total']:,.0f}** |",
        f"| Allocated overhead | {r['overhead_total']:,.0f} |",
        f"| **Total loaded cost** | **{r['total_loaded_cost']:,.0f}** |",
        "",
        "## Result",
        f"- Cost-to-serve **per deal**: **${r['cost_per_deal']:,.2f}**",
        f"- Cost-to-serve **per $ ARR**: **${r['cost_per_arr_dollar']:.4f}**",
        f"- **True gross margin** (after channel-specific load): **{r['true_gross_margin_pct']:.2f}%**",
        "",
    ]
    if r["hidden_cost_flags"]:
        lines.append("## Hidden-cost flags")
        for f in r["hidden_cost_flags"]:
            lines.append(f"- {f}")
        lines.append("")
    if r["warnings"]:
        lines.append("## Warnings")
        for w in r["warnings"]:
            lines.append(f"- {w}")
        lines.append("")
    return "\n".join(lines)


SAMPLE = {
    "channel_name": "partner-led-EMEA",
    "deal_volume": 80,
    "gross_revenue": 4_000_000,
    "costs": {
        "sdr_attribution": 60_000,
        "ae_attribution": 240_000,
        "sales_engineer_attribution": 90_000,
        "channel_manager_attribution": 180_000,
        "customer_success_attribution": 120_000,
        "support_attribution": 70_000,
        "marketing_attribution": 50_000,
        "partner_discount": 600_000,
        "partner_MDF": 80_000,
        "partner_enablement_time": 40_000,
        "certification_investment": 20_000,
        "channel_conflict_overhead": 15_000,
        "tooling_attribution": 25_000,
        "overhead_allocation_pct": 15.0,
    },
}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--input", help="Path to JSON input file")
    ap.add_argument("--output", choices=["json", "markdown"], default="markdown")
    ap.add_argument("--sample", action="store_true", help="Run with embedded sample")
    args = ap.parse_args()

    if args.sample:
        payload = SAMPLE
    elif args.input:
        with open(args.input) as f:
            payload = json.load(f)
    else:
        ap.print_help()
        return 0

    result = compute_cost_to_serve(payload)
    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_markdown(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
