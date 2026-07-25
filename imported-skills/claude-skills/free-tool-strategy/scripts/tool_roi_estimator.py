#!/usr/bin/env python3
"""
tool_roi_estimator.py — Estimates ROI of building a free marketing tool.

Models the return from a free tool given build cost, maintenance, expected traffic,
conversion rate, and lead value. Outputs ROI timeline, break-even month, and
minimum traffic needed to justify the investment.

Usage:
    python3 tool_roi_estimator.py                    # runs embedded sample
    python3 tool_roi_estimator.py params.json        # uses your params
    echo '{"build_cost": 5000, "lead_value": 200}' | python3 tool_roi_estimator.py

JSON input format:
    {
        "build_cost": 5000,              # One-time engineering cost ($) — dev time × rate
        "monthly_maintenance": 150,      # Ongoing server, API, ops cost per month ($)
        "traffic_month_1": 500,          # Expected organic sessions in month 1
        "traffic_growth_rate": 0.15,     # Monthly organic traffic growth rate (0.15 = 15%)
        "tool_completion_rate": 0.55,    # % of visitors who complete the tool (0.55 = 55%)
        "lead_capture_rate": 0.10,       # % of completions who give email (0.10 = 10%)
        "lead_to_trial_rate": 0.08,      # % of leads who start a trial
        "trial_to_paid_rate": 0.25,      # % of trials who become paid customers
        "ltv": 1200,                     # Customer LTV ($)
        "months_to_model": 24,           # How many months to project
        "seo_ramp_months": 3,            # Months before organic traffic kicks in (0 if PH/HN spike)
        "backlink_value_monthly": 200,   # Estimated value of earned backlinks (DA × niche rate)
        "tool_name": "ROI Calculator"    # For display only
    }
"""

import json
import math
import sys


# ---------------------------------------------------------------------------
# Core calculations
# ---------------------------------------------------------------------------

def traffic_at_month(params, month):
    """
    Traffic grows from near-zero during SEO ramp, then compounds.
    Month 1 = launch spike (Product Hunt / HN etc.) if ramp=0, or baseline.
    """
    ramp = params.get("seo_ramp_months", 3)
    base = params["traffic_month_1"]
    growth = params["traffic_growth_rate"]

    if month <= ramp:
        # Linear ramp to base traffic during SEO warmup
        return round(base * (month / ramp), 0) if ramp > 0 else base
    else:
        # Compound growth after ramp
        months_since_ramp = month - ramp
        return round(base * ((1 + growth) ** months_since_ramp), 0)


def leads_at_month(params, sessions):
    completion_rate = params["tool_completion_rate"]
    lead_capture_rate = params["lead_capture_rate"]
    completions = sessions * completion_rate
    leads = completions * lead_capture_rate
    return round(leads, 1)


def customers_at_month(params, leads):
    trial_rate = params["lead_to_trial_rate"]
    paid_rate = params["trial_to_paid_rate"]
    customers = leads * trial_rate * paid_rate
    return round(customers, 2)


def revenue_at_month(params, customers):
    return round(customers * params["ltv"], 2)


def cost_at_month(params, month):
    """
    Month 1: build cost + maintenance.
    Subsequent months: maintenance only.
    """
    maintenance = params["monthly_maintenance"]
    backlink_value = params.get("backlink_value_monthly", 0)
    if month == 1:
        return params["build_cost"] + maintenance
    return maintenance  # backlink value is additive, not a cost


def backlink_value_at_month(params, month):
    """Backlinks grow slowly — assume linear ramp over 6 months."""
    max_val = params.get("backlink_value_monthly", 0)
    ramp = 6
    if month >= ramp:
        return max_val
    return round(max_val * (month / ramp), 2)


def build_projection(params):
    months = params["months_to_model"]
    rows = []
    cumulative_cost = 0
    cumulative_revenue = 0
    cumulative_backlink_value = 0

    for m in range(1, months + 1):
        sessions = traffic_at_month(params, m)
        leads = leads_at_month(params, sessions)
        customers = customers_at_month(params, leads)
        revenue = revenue_at_month(params, customers)
        cost = cost_at_month(params, m)
        bl_value = backlink_value_at_month(params, m)

        cumulative_cost += cost
        cumulative_revenue += revenue
        cumulative_backlink_value += bl_value
        total_value = cumulative_revenue + cumulative_backlink_value
        cumulative_net = total_value - cumulative_cost

        rows.append({
            "month": m,
            "sessions": int(sessions),
            "leads": leads,
            "customers": customers,
            "revenue": revenue,
            "cost": round(cost, 2),
            "backlink_value": bl_value,
            "cumulative_cost": round(cumulative_cost, 2),
            "cumulative_revenue": round(cumulative_revenue, 2),
            "cumulative_backlink_value": round(cumulative_backlink_value, 2),
            "cumulative_net": round(cumulative_net, 2),
        })

    return rows


def find_break_even_month(projection):
    for row in projection:
        if row["cumulative_net"] >= 0:
            return row["month"]
    return None


def calculate_minimum_traffic(params):
    """
    What monthly traffic volume is needed to break even within 12 months?
    Solve for traffic where 12-month cumulative net >= 0.
    Uses binary search.
    """
    target_months = 12
    total_cost_12mo = params["build_cost"] + params["monthly_maintenance"] * target_months

    # Revenue per session (steady state, month 12)
    completion = params["tool_completion_rate"]
    lead_cap = params["lead_capture_rate"]
    trial = params["lead_to_trial_rate"]
    paid = params["trial_to_paid_rate"]
    ltv = params["ltv"]
    bl_monthly = params.get("backlink_value_monthly", 0)

    revenue_per_session = completion * lead_cap * trial * paid * ltv

    # Total sessions needed over 12 months (ignoring ramp for simplification)
    if revenue_per_session <= 0:
        return None

    # With backlink value: total_value = sessions_total × revenue_per_session + 12 × bl_monthly
    # sessions_total = total needed
    total_bl_value = bl_monthly * 12 * 0.5  # ramp factor
    needed_from_sessions = max(0, total_cost_12mo - total_bl_value)
    min_monthly_sessions = needed_from_sessions / (target_months * 0.6 * revenue_per_session)
    # 0.6 factor: first 3 months lower traffic during ramp

    return round(min_monthly_sessions, 0)


def calculate_roi_summary(projection, params):
    if not projection:
        return {}
    last = projection[-1]
    total_cost = last["cumulative_cost"]
    total_revenue = last["cumulative_revenue"]
    total_value = total_revenue + last["cumulative_backlink_value"]
    net = last["cumulative_net"]
    roi = (net / total_cost * 100) if total_cost > 0 else 0
    total_leads = sum(r["leads"] for r in projection)
    total_customers = sum(r["customers"] for r in projection)
    cost_per_lead = total_cost / total_leads if total_leads > 0 else 0

    return {
        "total_cost": round(total_cost, 2),
        "total_revenue": round(total_revenue, 2),
        "total_value_with_backlinks": round(total_value, 2),
        "net_benefit": round(net, 2),
        "roi_pct": round(roi, 1),
        "total_leads": round(total_leads, 0),
        "total_customers": round(total_customers, 1),
        "cost_per_lead": round(cost_per_lead, 2),
    }


# ---------------------------------------------------------------------------
# Formatting
# ---------------------------------------------------------------------------

def fc(value):
    return f"${value:,.2f}"


def fp(value):
    return f"{value:.1f}%"


def fi(value):
    return f"{int(value):,}"


def print_report(params, projection, summary, break_even, min_traffic):
    tool_name = params.get("tool_name", "Free Tool")
    months = params["months_to_model"]

    print("\n" + "=" * 65)
    print(f"FREE TOOL ROI ESTIMATOR — {tool_name.upper()}")
    print("=" * 65)

    print("\n📊 INPUT PARAMETERS")
    print(f"  Build cost (one-time):          {fc(params['build_cost'])}")
    print(f"  Monthly maintenance:            {fc(params['monthly_maintenance'])}")
    print(f"  Starting monthly traffic:       {fi(params['traffic_month_1'])} sessions")
    print(f"  Monthly traffic growth:         {fp(params['traffic_growth_rate'] * 100)}")
    print(f"  SEO ramp period:               {params.get('seo_ramp_months', 3)} months")
    print(f"  Tool completion rate:           {fp(params['tool_completion_rate'] * 100)}")
    print(f"  Lead capture rate:             {fp(params['lead_capture_rate'] * 100)} (of completions)")
    print(f"  Lead → trial rate:             {fp(params['lead_to_trial_rate'] * 100)}")
    print(f"  Trial → paid rate:             {fp(params['trial_to_paid_rate'] * 100)}")
    print(f"  LTV:                           {fc(params['ltv'])}")
    print(f"  Backlink value (monthly):      {fc(params.get('backlink_value_monthly', 0))}")

    print(f"\n📈 {months}-MONTH SUMMARY")
    print(f"  Total investment:               {fc(summary['total_cost'])}")
    print(f"  Revenue from leads:             {fc(summary['total_revenue'])}")
    print(f"  Backlink value:                 {fc(summary.get('total_value_with_backlinks', 0) - summary['total_revenue'])}")
    print(f"  Total value generated:          {fc(summary.get('total_value_with_backlinks', summary['total_revenue']))}")
    print(f"  Net benefit:                    {fc(summary['net_benefit'])}")
    print(f"  ROI:                            {fp(summary['roi_pct'])}")

    print(f"\n🎯 LEAD & CUSTOMER METRICS")
    print(f"  Total leads generated:          {fi(summary['total_leads'])}")
    print(f"  Total customers acquired:       {round(summary['total_customers'], 1)}")
    print(f"  Cost per lead:                  {fc(summary['cost_per_lead'])}")
    print(f"  CAC via tool:                   {fc(summary['total_cost'] / max(summary['total_customers'], 0.01))}")

    print(f"\n⏱  BREAK-EVEN ANALYSIS")
    if break_even:
        print(f"  Break-even month:               Month {break_even}")
        assessment = "🟢 Fast payback" if break_even <= 6 else "🟡 Moderate" if break_even <= 12 else "🔴 Long payback"
        print(f"  Assessment:                     {assessment}")
    else:
        print(f"  Break-even month:               Not reached in {months} months ⚠️")
        print(f"  Action needed: Increase traffic, improve completion/capture rate, or reduce build cost")

    if min_traffic:
        print(f"  Min traffic for 12-mo break-even: {fi(min_traffic)} sessions/month")
        current = params["traffic_month_1"]
        if current >= min_traffic:
            print(f"  Your projected traffic ({fi(current)}/mo) exceeds minimum ✅")
        else:
            gap = min_traffic - current
            print(f"  Traffic gap: need {fi(gap)} more sessions/month than projected ⚠️")

    print(f"\n📅 MONTHLY PROJECTION")
    print(f"  {'Mo':>3}  {'Sessions':>9}  {'Leads':>6}  {'Custs':>6}  {'Revenue':>9}  {'Cum Net':>10}")
    print(f"  {'-'*3}  {'-'*9}  {'-'*6}  {'-'*6}  {'-'*9}  {'-'*10}")
    for row in projection:
        net = row["cumulative_net"]
        net_str = fc(net) if net >= 0 else f"({fc(abs(net))})"
        be_marker = " ← break-even" if row["month"] == break_even else ""
        print(f"  {row['month']:>3}  {fi(row['sessions']):>9}  {row['leads']:>6.1f}  {row['customers']:>6.2f}"
              f"  {fc(row['revenue']):>9}  {net_str:>10}{be_marker}")

    print("\n" + "=" * 65)

    # Recommendations
    print("\n💡 RECOMMENDATIONS")
    roi = summary["roi_pct"]
    if roi > 200:
        print("  ✅ Strong ROI case — build it, invest in distribution")
    elif roi > 50:
        print("  🟡 Positive ROI but slim — validate keyword volume before committing full build cost")
        print("     Consider: MVP version (no-code) to test demand before full dev investment")
    else:
        print("  🔴 ROI case is weak — investigate:")
        print("     1. Is the target keyword validated? (check search volume)")
        print("     2. Can you reduce build cost? (no-code MVP first)")
        print("     3. Is the lead-to-customer conversion realistic?")
        print("     4. Is the LTV accurate?")

    completion = params["tool_completion_rate"]
    if completion < 0.40:
        print("  ⚠️  Low completion rate — reconsider UX or number of required inputs")
    if params["lead_capture_rate"] < 0.05:
        print("  ⚠️  Low lead capture — check gate placement (should be after value is delivered)")
    if break_even and break_even > 18:
        print("  ⚠️  Long break-even — prioritize launch distribution to accelerate traffic ramp")


# ---------------------------------------------------------------------------
# Default sample
# ---------------------------------------------------------------------------

DEFAULT_PARAMS = {
    "tool_name": "SaaS ROI Calculator",
    "build_cost": 4000,
    "monthly_maintenance": 100,
    "traffic_month_1": 600,
    "traffic_growth_rate": 0.12,
    "seo_ramp_months": 3,
    "tool_completion_rate": 0.55,
    "lead_capture_rate": 0.12,
    "lead_to_trial_rate": 0.08,
    "trial_to_paid_rate": 0.25,
    "ltv": 1400,
    "months_to_model": 18,
    "backlink_value_monthly": 150,
}


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    import argparse

    parser = argparse.ArgumentParser(
        description="Estimates ROI of building a free marketing tool. "
                    "Models return given build cost, maintenance, traffic, "
                    "conversion rate, and lead value."
    )
    parser.add_argument(
        "file", nargs="?", default=None,
        help="Path to a JSON file with tool parameters. "
             "If omitted, reads from stdin or runs embedded sample."
    )
    args = parser.parse_args()

    params = None

    if args.file:
        try:
            with open(args.file) as f:
                params = json.load(f)
        except Exception as e:
            print(f"Error reading file: {e}", file=sys.stderr)
            sys.exit(1)
    elif not sys.stdin.isatty():
        raw = sys.stdin.read().strip()
        if raw:
            try:
                params = json.loads(raw)
            except Exception as e:
                print(f"Error reading stdin: {e}", file=sys.stderr)
                sys.exit(1)
        else:
            print("No input provided — running with sample parameters.\n")
            params = DEFAULT_PARAMS
    else:
        print("No input provided — running with sample parameters.\n")
        params = DEFAULT_PARAMS

    # Fill defaults for any missing keys
    for k, v in DEFAULT_PARAMS.items():
        params.setdefault(k, v)

    projection = build_projection(params)
    summary = calculate_roi_summary(projection, params)
    break_even = find_break_even_month(projection)
    min_traffic = calculate_minimum_traffic(params)

    print_report(params, projection, summary, break_even, min_traffic)

    # JSON output
    json_output = {
        "inputs": params,
        "results": {
            "roi_pct": summary["roi_pct"],
            "break_even_month": break_even,
            "total_leads": summary["total_leads"],
            "total_customers": summary["total_customers"],
            "cost_per_lead": summary["cost_per_lead"],
            "net_benefit": summary["net_benefit"],
            "min_monthly_traffic_for_12mo_breakeven": min_traffic,
        }
    }

    print("\n--- JSON Output ---")
    print(json.dumps(json_output, indent=2))


if __name__ == "__main__":
    main()
