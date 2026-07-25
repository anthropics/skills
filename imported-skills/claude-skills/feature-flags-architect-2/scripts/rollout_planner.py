#!/usr/bin/env python3
"""Generate a phased rollout schedule for a feature flag.

Strategies:
  ring    1% → 5% → 25% → 50% → 100% — risky launches
  linear  constant percent-per-day — medium risk
  log     fast early, slow tail — low risk
  cohort  named cohorts (internal → beta → free → paid → all) — entitlement-aware
"""
import argparse
import json
import math
import sys
from datetime import datetime, timedelta

DEFAULT_RING_STOPS = [1, 5, 25, 50, 100]
DEFAULT_COHORTS = ["internal", "beta", "free", "paid", "all"]


def _ring(target):
    return [s for s in DEFAULT_RING_STOPS if s <= target] + ([target] if target not in DEFAULT_RING_STOPS else [])


def _linear(target, days):
    if days < 1:
        return [target]
    step = target / days
    return [round((i + 1) * step, 2) for i in range(days)]


def _log_curve(target, days):
    if days < 1:
        return [target]
    out = []
    for i in range(days):
        frac = math.log1p(i + 1) / math.log1p(days)
        out.append(round(target * frac, 2))
    return out


def _dedupe_sorted(values):
    seen = set()
    out = []
    for v in values:
        if v not in seen:
            seen.add(v)
            out.append(v)
    return out


def build_schedule(strategy, target, duration_days, population, start_date):
    if strategy == "ring":
        percents = _ring(target)
    elif strategy == "linear":
        percents = _linear(target, duration_days)
    elif strategy == "log":
        percents = _log_curve(target, duration_days)
    elif strategy == "cohort":
        per_step = target / len(DEFAULT_COHORTS)
        percents = [round(per_step * (i + 1), 2) for i in range(len(DEFAULT_COHORTS))]
    else:
        raise ValueError(f"unknown strategy: {strategy}")

    percents = _dedupe_sorted(percents)
    n = len(percents)
    interval = max(1, duration_days // max(n - 1, 1))
    rows = []
    for i, pct in enumerate(percents):
        date = start_date + timedelta(days=i * interval)
        users = int(population * pct / 100)
        cohort = DEFAULT_COHORTS[min(i, len(DEFAULT_COHORTS) - 1)] if strategy == "cohort" else None
        rows.append({
            "phase": i + 1,
            "date": date.date().isoformat(),
            "percent": pct,
            "users": users,
            "cohort": cohort,
            "abort_if": "error_rate > baseline + 1pp OR p99_latency > baseline * 1.2",
            "verify": "compare metrics dashboard against control",
        })
    return rows


def render_markdown(rows, strategy, target, duration_days, population):
    print(f"# Rollout plan — strategy={strategy}, target={target}%, duration={duration_days}d, population={population:,}")
    print("")
    headers = ["Phase", "Date", "Percent", "Users", "Cohort", "Abort criteria", "Verify"]
    print("| " + " | ".join(headers) + " |")
    print("|" + "|".join(["---"] * len(headers)) + "|")
    for r in rows:
        cohort = r["cohort"] or "—"
        print(f"| {r['phase']} | {r['date']} | {r['percent']}% | {r['users']:,} | {cohort} | {r['abort_if']} | {r['verify']} |")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--population", type=int, required=True, help="Total user population")
    ap.add_argument("--target-percent", type=float, default=100, help="Final rollout percent (default: 100)")
    ap.add_argument("--duration-days", type=int, default=14, help="Total rollout duration (default: 14)")
    ap.add_argument("--strategy", choices=["ring", "linear", "log", "cohort"], default="ring")
    ap.add_argument("--start-date", default=None, help="ISO date YYYY-MM-DD (default: today)")
    ap.add_argument("--format", choices=["markdown", "json"], default="markdown")
    args = ap.parse_args()

    if not 0 < args.target_percent <= 100:
        print("ERROR: --target-percent must be in (0, 100]", file=sys.stderr)
        return 2
    if args.population < 1:
        print("ERROR: --population must be >= 1", file=sys.stderr)
        return 2

    start = datetime.fromisoformat(args.start_date) if args.start_date else datetime.utcnow()
    rows = build_schedule(args.strategy, args.target_percent, args.duration_days, args.population, start)

    if args.format == "json":
        print(json.dumps(rows, indent=2, default=str))
    else:
        render_markdown(rows, args.strategy, args.target_percent, args.duration_days, args.population)
    return 0


if __name__ == "__main__":
    sys.exit(main())
