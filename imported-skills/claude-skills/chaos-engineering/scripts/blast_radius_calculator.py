#!/usr/bin/env python3
"""Compute blast radius and risk score for a chaos experiment.

Inputs: traffic share affected, user population, duration, baseline availability,
expected impacted availability. Outputs expected affected users, error budget
consumed, and a GREEN / YELLOW / RED risk score with PROCEED / REDUCE / ABORT
recommendation.
"""
import argparse
import json
import sys


def calculate(traffic_share, user_pop, duration_min, baseline_avail, impacted_avail, monthly_budget_min):
    if not 0 <= traffic_share <= 1:
        raise ValueError("traffic-share must be between 0 and 1")
    if not 0 < impacted_avail <= 1:
        raise ValueError("impacted-availability must be between 0 (exclusive) and 1")
    if not 0 < baseline_avail <= 1:
        raise ValueError("baseline-availability must be between 0 (exclusive) and 1")
    affected_users = int(user_pop * traffic_share)
    delta_avail = max(baseline_avail - impacted_avail, 0.0)
    error_budget_consumed_min = round(duration_min * traffic_share * delta_avail, 4)
    pct_of_monthly_budget = round(100 * error_budget_consumed_min / monthly_budget_min, 2) if monthly_budget_min > 0 else 0
    if pct_of_monthly_budget < 1:
        risk = "GREEN"
        recommendation = "PROCEED"
    elif pct_of_monthly_budget < 10:
        risk = "YELLOW"
        recommendation = "PROCEED with explicit owner sign-off; consider reducing traffic share"
    else:
        risk = "RED"
        recommendation = "ABORT or REDUCE — blast radius exceeds 10% of monthly error budget"
    return {
        "inputs": {
            "traffic_share": traffic_share,
            "user_pop": user_pop,
            "duration_min": duration_min,
            "baseline_availability": baseline_avail,
            "impacted_availability": impacted_avail,
            "monthly_budget_min": monthly_budget_min,
        },
        "expected_affected_users": affected_users,
        "expected_availability_delta": round(delta_avail, 4),
        "error_budget_consumed_min": error_budget_consumed_min,
        "pct_of_monthly_budget": pct_of_monthly_budget,
        "risk": risk,
        "recommendation": recommendation,
    }


def render_text(result):
    print("Blast Radius Calculator")
    print("=" * 40)
    i = result["inputs"]
    print(f"Traffic share affected:   {i['traffic_share'] * 100:.2f}%")
    print(f"User population:          {i['user_pop']:,}")
    print(f"Duration:                 {i['duration_min']} min")
    print(f"Baseline availability:    {i['baseline_availability']}")
    print(f"Impacted availability:    {i['impacted_availability']}")
    print(f"Monthly error budget:     {i['monthly_budget_min']} min")
    print("")
    print(f"Expected affected users:  {result['expected_affected_users']:,}")
    print(f"Availability delta:       {result['expected_availability_delta']}")
    print(f"Error budget consumed:    {result['error_budget_consumed_min']} min ({result['pct_of_monthly_budget']}% of monthly)")
    print("")
    print(f"Risk:           {result['risk']}")
    print(f"Recommendation: {result['recommendation']}")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--traffic-share", type=float, help="Fraction (0-1) of traffic affected")
    ap.add_argument("--user-pop", type=int, help="Total user population")
    ap.add_argument("--duration-min", type=int, help="Experiment duration in minutes")
    ap.add_argument("--sample", action="store_true",
                    help="Run with embedded sample inputs (5%% traffic, 100k users, 30 min)")
    ap.add_argument("--baseline-availability", type=float, default=0.999, help="Baseline availability (default: 0.999)")
    ap.add_argument("--expected-impact-availability", type=float, default=0.95, dest="impact_avail",
                    help="Availability under fault (default: 0.95)")
    ap.add_argument("--monthly-budget-min", type=float, default=43.2,
                    help="Monthly error budget in minutes (default: 43.2 for 99.9%% on 30 days)")
    ap.add_argument("--format", choices=["text", "json"], default="text")
    args = ap.parse_args()

    if args.sample:
        traffic_share, user_pop, duration_min = 0.05, 100000, 30
    elif None not in (args.traffic_share, args.user_pop, args.duration_min):
        traffic_share, user_pop, duration_min = args.traffic_share, args.user_pop, args.duration_min
    else:
        ap.error("--traffic-share, --user-pop and --duration-min are required (or use --sample)")

    try:
        result = calculate(
            traffic_share, user_pop, duration_min,
            args.baseline_availability, args.impact_avail, args.monthly_budget_min,
        )
    except ValueError as e:
        print(f"ERROR: {e}", file=sys.stderr)
        return 2

    if args.format == "json":
        print(json.dumps(result, indent=2))
    else:
        render_text(result)
    return 0 if result["risk"] != "RED" else 1


if __name__ == "__main__":
    sys.exit(main())
