#!/usr/bin/env python3
"""Score a webinar funnel 0-100 and identify the weakest stage.

Stdlib-only. Reads funnel numbers from a JSON file arg or stdin, compares each
stage's conversion rate against industry benchmarks, scores the funnel, and
names the bottleneck so you fix the stage that's actually broken.

Input JSON (all optional except where noted):
{
  "invited": 5000,            # optional (audience reached / list size)
  "page_visits": 1800,        # optional
  "registrations": 620,       # required
  "attended_live": 180,       # required
  "cta_clicks": 40,           # optional
  "conversions": 14,          # optional (SQOs, trials, demos booked...)
  "audience": "owned_cold",   # one of: customers, warm, owned_cold, paid_cold
  "runtime_min": 45,          # optional
  "avg_watch_min": 26         # optional
}

Usage:
  python webinar_funnel_scorer.py data.json   # score a JSON file
  cat data.json | python webinar_funnel_scorer.py -   # read JSON from stdin
  python webinar_funnel_scorer.py             # runs on embedded sample data
  python webinar_funnel_scorer.py --sample    # explicit demo mode
"""

import argparse
import json
import sys

# Benchmark "good" conversion rates per stage, by audience temperature.
# Each value is the rate considered solid; we score relative to it.
BENCHMARKS = {
    "customers":  {"page_cvr": 0.40, "show_up": 0.50, "cta": 0.25, "convert": 0.12},
    "warm":       {"page_cvr": 0.35, "show_up": 0.42, "cta": 0.22, "convert": 0.10},
    "owned_cold": {"page_cvr": 0.25, "show_up": 0.35, "cta": 0.18, "convert": 0.07},
    "paid_cold":  {"page_cvr": 0.18, "show_up": 0.28, "cta": 0.15, "convert": 0.05},
}

STAGE_LABELS = {
    "page_cvr": "Landing page -> registration",
    "show_up": "Registration -> live attendance",
    "watch": "Attendee watch-time",
    "cta": "Attendee -> CTA click",
    "convert": "Attendee -> conversion",
}

SAMPLE = {
    "invited": 5000,
    "page_visits": 1800,
    "registrations": 620,
    "attended_live": 150,
    "cta_clicks": 33,
    "conversions": 9,
    "audience": "owned_cold",
    "runtime_min": 45,
    "avg_watch_min": 24,
}


def safe_div(a, b):
    return (a / b) if b else None


def stage_score(actual, benchmark):
    """Score a single stage 0-100: 100 if at/above benchmark, scaled below."""
    if actual is None or benchmark in (None, 0):
        return None
    return max(0, min(100, round((actual / benchmark) * 100)))


def analyze(d):
    audience = d.get("audience", "owned_cold")
    bm = BENCHMARKS.get(audience, BENCHMARKS["owned_cold"])

    regs = d.get("registrations")
    att = d.get("attended_live")
    if regs is None or att is None:
        raise ValueError("registrations and attended_live are required")

    rates = {
        "page_cvr": safe_div(regs, d.get("page_visits")),
        "show_up": safe_div(att, regs),
        "watch": safe_div(d.get("avg_watch_min"), d.get("runtime_min")),
        "cta": safe_div(d.get("cta_clicks"), att),
        "convert": safe_div(d.get("conversions"), att),
    }

    # Watch-time benchmark is a flat 0.6 of runtime (good engagement).
    bm_full = dict(bm)
    bm_full["watch"] = 0.60

    scores = {}
    for stage, actual in rates.items():
        scores[stage] = stage_score(actual, bm_full.get(stage))

    scored = {k: v for k, v in scores.items() if v is not None}
    overall = round(sum(scored.values()) / len(scored)) if scored else 0

    # Weakest scored stage = the bottleneck.
    bottleneck = min(scored, key=scored.get) if scored else None

    return {
        "audience": audience,
        "overall_score": overall,
        "stage_rates": {k: (round(v, 3) if v is not None else None)
                        for k, v in rates.items()},
        "stage_scores": scores,
        "benchmarks": bm_full,
        "bottleneck": bottleneck,
        "bottleneck_label": STAGE_LABELS.get(bottleneck) if bottleneck else None,
    }


def fmt_pct(x):
    return f"{x*100:.0f}%" if isinstance(x, (int, float)) else "n/a"


def print_summary(r):
    print("=" * 56)
    print(f"WEBINAR FUNNEL SCORE: {r['overall_score']}/100   "
          f"(audience: {r['audience']})")
    print("=" * 56)
    print(f"{'Stage':<34}{'Rate':>8}{'Bench':>8}{'Score':>7}")
    print("-" * 56)
    for stage in ["page_cvr", "show_up", "watch", "cta", "convert"]:
        rate = r["stage_rates"].get(stage)
        bench = r["benchmarks"].get(stage)
        score = r["stage_scores"].get(stage)
        label = STAGE_LABELS.get(stage, stage)
        score_s = f"{score}" if score is not None else "  -"
        flag = "  <-- weakest" if stage == r["bottleneck"] else ""
        print(f"{label:<34}{fmt_pct(rate):>8}{fmt_pct(bench):>8}{score_s:>7}{flag}")
    print("-" * 56)
    if r["bottleneck"]:
        print(f"BOTTLENECK: {r['bottleneck_label']}")
        print("Fix this stage first — it's dragging the funnel most.")
    print()


def main():
    parser = argparse.ArgumentParser(
        description="Score a webinar funnel 0-100 against audience-temperature "
                    "benchmarks and name the bottleneck stage.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "examples:\n"
            "  python3 webinar_funnel_scorer.py data.json          # score a JSON file\n"
            "  cat data.json | python3 webinar_funnel_scorer.py -  # read JSON from stdin\n"
            "  python3 webinar_funnel_scorer.py                    # embedded sample data\n"
            "  python3 webinar_funnel_scorer.py --sample           # explicit demo mode"
        ),
    )
    parser.add_argument(
        "file",
        nargs="?",
        help="Path to a funnel JSON file, or '-' to read JSON from stdin. "
             "Omit to run on embedded sample data.",
    )
    parser.add_argument(
        "--sample",
        action="store_true",
        help="Run on the embedded sample funnel data and exit.",
    )
    args = parser.parse_args()

    try:
        if args.sample:
            data = SAMPLE
        elif args.file == "-":
            # Explicit stdin. Only read here so we never block when no input exists.
            raw = sys.stdin.read().strip()
            data = json.loads(raw) if raw else SAMPLE
        elif args.file:
            with open(args.file) as f:
                data = json.load(f)
        else:
            data = SAMPLE
            print("(no input given — running on embedded sample data)\n")
    except (OSError, json.JSONDecodeError) as exc:
        print(f"Error reading input: {exc}", file=sys.stderr)
        sys.exit(2)

    try:
        result = analyze(data)
    except ValueError as exc:
        print(f"Error: {exc}", file=sys.stderr)
        sys.exit(2)
    print_summary(result)
    print("JSON:")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
