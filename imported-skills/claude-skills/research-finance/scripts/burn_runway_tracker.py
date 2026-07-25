#!/usr/bin/env python3
"""burn_runway_tracker.py - Compute R&D program burn, runway, and milestone-vs-cash alignment.

Stdlib-only. Deterministic. NO LLM calls. Surfaces the assumption behind every number.

Given cash-on-hand, a period ledger of actual spend, and upcoming milestones (each with a
period index and the cash needed to reach it), computes:
  - average + trailing burn rate
  - runway in periods and (approx) months
  - whether each value-inflection milestone is reachable before cash runs out

Usage:
    python3 burn_runway_tracker.py --sample
    python3 burn_runway_tracker.py --input ledger.json --threshold-months 6
    python3 burn_runway_tracker.py --input ledger.json --output json
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

SAMPLE = {
    "program": "Next-Gen Assay Platform",
    "cash_on_hand": 3200000,
    "period_label": "month",
    "actual_spend": [285000, 305000, 330000, 360000],
    "milestones": [
        {"name": "Analytical validation", "period_from_now": 3, "cumulative_cash_needed": 1000000},
        {"name": "First-in-human readiness", "period_from_now": 9, "cumulative_cash_needed": 3400000},
    ],
}


def analyze(data: dict, threshold_months: float) -> dict:
    spend = [float(x) for x in data.get("actual_spend", [])]
    cash = float(data.get("cash_on_hand", 0.0))
    label = data.get("period_label", "month")
    months_per_period = 1.0 if label == "month" else (3.0 if label == "quarter" else 1.0)

    if not spend:
        raise ValueError("actual_spend must contain at least one period.")

    avg_burn = sum(spend) / len(spend)
    trailing_n = min(3, len(spend))
    trailing_burn = sum(spend[-trailing_n:]) / trailing_n
    # Use trailing burn (more recent) as the forward run-rate.
    run_rate = trailing_burn if trailing_burn > 0 else avg_burn
    runway_periods = cash / run_rate if run_rate > 0 else float("inf")
    runway_months = runway_periods * months_per_period

    milestones_out = []
    for m in data.get("milestones", []):
        needed = float(m.get("cumulative_cash_needed", 0.0))
        period_from_now = float(m.get("period_from_now", 0))
        reachable_cash = needed <= cash
        reachable_time = period_from_now <= runway_periods
        verdict = "REACHABLE" if (reachable_cash and reachable_time) else "AT-RISK"
        milestones_out.append({
            "name": m.get("name", "UNNAMED"),
            "period_from_now": period_from_now,
            "cumulative_cash_needed": needed,
            "cash_covers": reachable_cash,
            "runway_covers_timing": reachable_time,
            "verdict": verdict,
        })

    flags = []
    if runway_months < threshold_months:
        flags.append(f"RUNWAY BELOW THRESHOLD: {runway_months:.1f} months < {threshold_months} month threshold.")
    if any(m["verdict"] == "AT-RISK" for m in milestones_out):
        flags.append("At least one value-inflection milestone is AT-RISK on current burn.")
    if trailing_burn > avg_burn * 1.15:
        flags.append(f"Burn accelerating: trailing burn ${trailing_burn:,.0f} > 115% of average ${avg_burn:,.0f}.")

    return {
        "program": data.get("program", "UNSPECIFIED"),
        "cash_on_hand": cash,
        "average_burn_per_period": round(avg_burn, 2),
        "trailing_burn_per_period": round(trailing_burn, 2),
        "forward_run_rate_used": round(run_rate, 2),
        "runway_periods": round(runway_periods, 2),
        "runway_months_approx": round(runway_months, 1),
        "milestones": milestones_out,
        "flags": flags,
        "assumptions": [
            f"Forward run-rate = trailing {trailing_n}-period burn (recent-weighted, not lifetime average).",
            f"Period label '{label}' => {months_per_period} month(s) per period.",
            "Runway assumes flat forward burn; a funded ramp or hiring plan changes this.",
            "Milestone cash needs are cumulative-from-now as supplied; verify against the program budget.",
        ],
    }


def _render_human(r: dict) -> str:
    lines = [f"Burn & Runway: {r['program']}", "",
             f"Cash on hand:            ${r['cash_on_hand']:,.0f}",
             f"Average burn/period:     ${r['average_burn_per_period']:,.0f}",
             f"Trailing burn/period:    ${r['trailing_burn_per_period']:,.0f}",
             f"Forward run-rate used:   ${r['forward_run_rate_used']:,.0f}",
             f"Runway:                  {r['runway_periods']} periods (~{r['runway_months_approx']} months)",
             ""]
    lines.append("Milestones:")
    for m in r["milestones"]:
        lines.append(f"  [{m['verdict']}] {m['name']}  (+{m['period_from_now']:.0f} periods, "
                     f"needs ${m['cumulative_cash_needed']:,.0f})")
    lines.append("")
    if r["flags"]:
        lines.append("Flags:")
        for f in r["flags"]:
            lines.append(f"  ! {f}")
        lines.append("")
    lines.append("Assumptions:")
    for a in r["assumptions"]:
        lines.append(f"  - {a}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description="Compute R&D program burn, runway, and milestone alignment.")
    p.add_argument("--input", help="Path to JSON ledger")
    p.add_argument("--threshold-months", type=float, default=None, help="runway alert threshold (months)")
    p.add_argument("--output", choices=["human", "json"], default="human")
    p.add_argument("--sample", action="store_true", help="use the embedded sample")
    args = p.parse_args(argv)

    conf = _cfg.load_config() if _cfg else {}
    threshold = args.threshold_months if args.threshold_months is not None \
        else float(conf.get("runway_threshold_months", 6.0))
    data = SAMPLE if (args.sample or not args.input) else json.load(open(args.input))
    try:
        result = analyze(data, threshold)
    except ValueError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2

    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(_render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
