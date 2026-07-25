#!/usr/bin/env python3
"""Compute error budget and multi-window burn-rate alert thresholds.

Per Google SRE Workbook (Chapter 5: Alerting on SLOs), reliable burn-rate
alerting uses TWO windows: a fast window (1h) for catastrophic burn and a
slow window (6h) to filter false positives. Optionally a 3-day window for
ticket-only (non-paging) alerts.

Outputs:
  - Allowed downtime in the SLO window
  - Burn-rate thresholds for fast/slow/ticket alert windows
  - PromQL-shaped alert rules ready to paste

References:
  https://sre.google/workbook/alerting-on-slos/
"""
import argparse
import json
import sys

# Per Google SRE Workbook Chapter 5: Table 5-3 recommended thresholds
# (severity, percent_of_monthly_budget, long_window, short_window_ratio)
DEFAULT_BURN_RATE_RULES = [
    {
        "name": "fast_burn",
        "severity": "page",
        "long_window_hours": 1,
        "short_window_hours": 1 / 12,
        "budget_pct_consumed": 2.0,
        "rationale": "2% of monthly budget burned in 1h => system on fire",
    },
    {
        "name": "slow_burn",
        "severity": "page",
        "long_window_hours": 6,
        "short_window_hours": 0.5,
        "budget_pct_consumed": 5.0,
        "rationale": "5% of monthly budget burned in 6h => sustained degradation",
    },
    {
        "name": "ticket_burn",
        "severity": "ticket",
        "long_window_hours": 72,
        "short_window_hours": 6,
        "budget_pct_consumed": 10.0,
        "rationale": "10% of monthly budget burned in 3d => trending bad",
    },
]


def compute(target_percent, window_days):
    if not 50 <= target_percent <= 100:
        raise ValueError(f"target must be between 50 and 100, got {target_percent}")
    if window_days < 1:
        raise ValueError("window-days must be >= 1")
    bad_fraction = (100 - target_percent) / 100
    window_minutes = window_days * 24 * 60
    budget_minutes = round(bad_fraction * window_minutes, 4)
    rules = []
    for rule in DEFAULT_BURN_RATE_RULES:
        burn_rate_threshold = (rule["budget_pct_consumed"] / 100) / (rule["long_window_hours"] / (window_days * 24))
        rules.append({
            "name": rule["name"],
            "severity": rule["severity"],
            "long_window": _fmt_hours(rule["long_window_hours"]),
            "short_window": _fmt_hours(rule["short_window_hours"]),
            "budget_pct_consumed": rule["budget_pct_consumed"],
            "burn_rate_threshold": round(burn_rate_threshold, 3),
            "rationale": rule["rationale"],
            "promql": _promql_rule(rule, burn_rate_threshold, target_percent),
        })
    return {
        "target_percent": target_percent,
        "window_days": window_days,
        "bad_fraction": round(bad_fraction, 6),
        "budget_minutes": budget_minutes,
        "budget_hours": round(budget_minutes / 60, 4),
        "alert_rules": rules,
    }


def _fmt_hours(hours):
    if hours < 1:
        return f"{int(round(hours * 60))}m"
    if hours < 24:
        return f"{int(round(hours))}h"
    return f"{int(round(hours / 24))}d"


def _promql_rule(rule, burn_rate, target_pct):
    long_w = _fmt_hours(rule["long_window_hours"])
    short_w = _fmt_hours(rule["short_window_hours"])
    return (
        f"# {rule['name']} ({rule['severity']})\n"
        f"# Burn rate threshold: {round(burn_rate, 3)}\n"
        f"(\n"
        f"  sli:rate{long_w} > {round(burn_rate, 3)} * (1 - {target_pct / 100})\n"
        f"  AND\n"
        f"  sli:rate{short_w} > {round(burn_rate, 3)} * (1 - {target_pct / 100})\n"
        f")"
    )


def render_text(result):
    print(f"Error Budget — target={result['target_percent']}%, window={result['window_days']}d")
    print("=" * 60)
    print(f"Allowed bad events:   {result['bad_fraction'] * 100:.4f}% of total")
    print(f"Allowed downtime:     {result['budget_minutes']:.2f} min  ({result['budget_hours']:.2f} hours)")
    print("")
    print("Multi-window burn-rate alerts (Google SRE Workbook):")
    print("")
    for r in result["alert_rules"]:
        print(f"  [{r['severity'].upper():6}]  {r['name']}")
        print(f"           windows:        {r['long_window']} long / {r['short_window']} short")
        print(f"           burn rate:      {r['burn_rate_threshold']}")
        print(f"           consumed:       {r['budget_pct_consumed']}% of monthly budget")
        print(f"           rationale:      {r['rationale']}")
        print("")
    print("PromQL-shaped rules:")
    print("")
    for r in result["alert_rules"]:
        print(r["promql"])
        print("")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--target", type=float, help="Target percent (e.g., 99.9)")
    ap.add_argument("--window-days", type=int, default=28, help="Window in days (default: 28)")
    ap.add_argument("--format", choices=["text", "json"], default="text")
    ap.add_argument("--sample", action="store_true", help="Run with embedded sample inputs (99.9%% / 28d)")
    args = ap.parse_args()

    if args.sample:
        target, window_days = 99.9, 28
    elif args.target is not None:
        target, window_days = args.target, args.window_days
    else:
        ap.error("--target is required (or use --sample)")

    try:
        result = compute(target, window_days)
    except ValueError as e:
        print(f"ERROR: {e}", file=sys.stderr)
        return 2

    if args.format == "json":
        print(json.dumps(result, indent=2))
    else:
        render_text(result)
    return 0


if __name__ == "__main__":
    sys.exit(main())
