#!/usr/bin/env python3
"""program_budget_planner.py - Build a multi-period R&D program budget with F&A split.

Stdlib-only. Deterministic. NO LLM calls. Every output surfaces an explicit assumptions
block: budget math without disclosed assumptions is theatre.

Takes work-package line items, applies the F&A (indirect) rate to the F&A-eligible base
(MTDC-style: excludes capital equipment and the portion of subawards over $25k), computes
fully-loaded cost, and rolls up per period.

Usage:
    python3 program_budget_planner.py --sample
    python3 program_budget_planner.py --input program.json --fa-rate 0.55 --periods 4
    python3 program_budget_planner.py --input program.json --profile biotech --output json
"""

from __future__ import annotations

import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
try:
    import config_loader as _cfg
except ImportError:  # pragma: no cover
    _cfg = None

# Profile default F&A (indirect) rate and escalation assumption when not supplied in input.
PROFILES = {
    "pharma-rd": {"default_fa_rate": 0.50, "annual_escalation": 0.03},
    "biotech": {"default_fa_rate": 0.55, "annual_escalation": 0.04},
    "medtech": {"default_fa_rate": 0.45, "annual_escalation": 0.03},
    "deep-tech": {"default_fa_rate": 0.40, "annual_escalation": 0.03},
    "software-rd": {"default_fa_rate": 0.30, "annual_escalation": 0.04},
    "university-lab": {"default_fa_rate": 0.585, "annual_escalation": 0.025},
}

# Categories excluded from the F&A (MTDC) base.
FA_EXEMPT_CATEGORIES = {"capital_equipment", "subaward_over_25k", "tuition", "patient_care"}

SAMPLE = {
    "program": "Next-Gen Assay Platform",
    "periods": 4,
    "work_packages": [
        {"name": "Personnel (FTEs)", "category": "personnel", "amounts": [320000, 330000, 340000, 350000]},
        {"name": "Consumables", "category": "supplies", "amounts": [60000, 65000, 70000, 70000]},
        {"name": "Sequencer", "category": "capital_equipment", "amounts": [180000, 0, 0, 0]},
        {"name": "CRO subaward", "category": "subaward_over_25k", "amounts": [100000, 100000, 0, 0]},
        {"name": "Travel", "category": "travel", "amounts": [12000, 12000, 12000, 12000]},
    ],
}


def _period_sum(amounts: list, n: int, idx: int) -> float:
    return float(amounts[idx]) if idx < len(amounts) else 0.0


def plan_budget(data: dict, fa_rate: float, periods: int) -> dict:
    wps = data.get("work_packages", [])
    direct_by_period = [0.0] * periods
    fa_base_by_period = [0.0] * periods
    line_items = []

    for wp in wps:
        cat = wp.get("category", "other")
        amounts = wp.get("amounts", [])
        fa_eligible = cat not in FA_EXEMPT_CATEGORIES
        wp_total = 0.0
        for i in range(periods):
            amt = _period_sum(amounts, periods, i)
            direct_by_period[i] += amt
            if fa_eligible:
                fa_base_by_period[i] += amt
            wp_total += amt
        line_items.append({
            "name": wp.get("name", "UNNAMED"),
            "category": cat,
            "fa_eligible": fa_eligible,
            "total_direct": round(wp_total, 2),
        })

    fa_by_period = [round(b * fa_rate, 2) for b in fa_base_by_period]
    loaded_by_period = [round(direct_by_period[i] + fa_by_period[i], 2) for i in range(periods)]

    return {
        "program": data.get("program", "UNSPECIFIED"),
        "periods": periods,
        "fa_rate_applied": fa_rate,
        "line_items": line_items,
        "direct_by_period": [round(x, 2) for x in direct_by_period],
        "fa_base_by_period": [round(x, 2) for x in fa_base_by_period],
        "fa_by_period": fa_by_period,
        "fully_loaded_by_period": loaded_by_period,
        "total_direct": round(sum(direct_by_period), 2),
        "total_fa": round(sum(fa_by_period), 2),
        "total_fully_loaded": round(sum(loaded_by_period), 2),
        "assumptions": [
            f"F&A (indirect) rate applied: {fa_rate:.1%}. Confirm this is your negotiated NICRA, not an assumption.",
            f"F&A base excludes: {', '.join(sorted(FA_EXEMPT_CATEGORIES))} (MTDC-style base).",
            "Amounts are taken as-entered per period; no escalation applied unless baked into inputs.",
            "This is a planning estimate; a finance owner/controller validates the rate basis and booking.",
        ],
    }


def _render_human(r: dict) -> str:
    lines = [f"R&D Program Budget: {r['program']}  ({r['periods']} periods)",
             f"F&A rate applied: {r['fa_rate_applied']:.1%}", ""]
    lines.append("Line items:")
    for li in r["line_items"]:
        tag = "F&A-eligible" if li["fa_eligible"] else "F&A-EXEMPT"
        lines.append(f"  {li['name']:24s} {li['category']:20s} {tag:12s} ${li['total_direct']:,.0f}")
    lines.append("")
    hdr = "  " + "".join(f"P{i+1:>14}" for i in range(r["periods"]))
    lines.append("Per-period rollup:" )
    lines.append(hdr)
    lines.append("  direct      " + "".join(f"{v:>15,.0f}" for v in r["direct_by_period"]))
    lines.append("  F&A         " + "".join(f"{v:>15,.0f}" for v in r["fa_by_period"]))
    lines.append("  loaded      " + "".join(f"{v:>15,.0f}" for v in r["fully_loaded_by_period"]))
    lines.append("")
    lines.append(f"Total direct:        ${r['total_direct']:,.0f}")
    lines.append(f"Total F&A:           ${r['total_fa']:,.0f}")
    lines.append(f"Total fully-loaded:  ${r['total_fully_loaded']:,.0f}")
    lines.append("")
    lines.append("Assumptions (state these alongside the number):")
    for a in r["assumptions"]:
        lines.append(f"  - {a}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description="Build a multi-period R&D program budget with F&A split.")
    p.add_argument("--input", help="Path to JSON program with work_packages[]")
    p.add_argument("--profile", default=None, choices=list(PROFILES),
                   help="overrides onboarding default_profile")
    p.add_argument("--fa-rate", type=float, default=None, help="Override F&A rate (fraction, e.g. 0.55)")
    p.add_argument("--periods", type=int, default=None, help="Number of periods")
    p.add_argument("--output", choices=["human", "json"], default="human")
    p.add_argument("--sample", action="store_true", help="use the embedded sample")
    args = p.parse_args(argv)

    conf = _cfg.load_config() if _cfg else {}
    profile = args.profile or conf.get("default_profile", "biotech")
    data = SAMPLE if (args.sample or not args.input) else json.load(open(args.input))
    periods = args.periods or int(data.get("periods", 4))
    # F&A precedence: CLI flag > onboarding default_fa_rate (if set) > profile default
    if args.fa_rate is not None:
        fa_rate = args.fa_rate
    elif conf.get("default_fa_rate") is not None:
        fa_rate = float(conf["default_fa_rate"])
    else:
        fa_rate = PROFILES[profile]["default_fa_rate"]

    result = plan_budget(data, fa_rate, periods)
    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(_render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
