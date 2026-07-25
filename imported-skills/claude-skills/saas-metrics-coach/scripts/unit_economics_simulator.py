#!/usr/bin/env python3
"""
Unit Economics Simulator - Project SaaS metrics forward 12 months.

Usage:
    python unit_economics_simulator.py --mrr 50000 --growth 10 --churn 3 --cac 2000
    python unit_economics_simulator.py --mrr 50000 --growth 10 --churn 3 --cac 2000 --json
"""

import json
import sys
import argparse


def simulate(
    mrr,
    monthly_growth_pct,
    monthly_churn_pct,
    cac,
    gross_margin=0.70,
    sm_spend_pct=0.30,
    months=12,
):
    """
    Simulate unit economics forward.
    
    Args:
        mrr: Starting MRR
        monthly_growth_pct: Expected monthly growth rate (%)
        monthly_churn_pct: Expected monthly churn rate (%)
        cac: Customer acquisition cost
        gross_margin: Gross margin (0-1)
        sm_spend_pct: Sales & marketing as % of revenue (0-1)
        months: Number of months to project
    
    Returns:
        dict with monthly projections and summary
    """
    results = {
        "inputs": {
            "starting_mrr": mrr,
            "monthly_growth_pct": monthly_growth_pct,
            "monthly_churn_pct": monthly_churn_pct,
            "cac": cac,
            "gross_margin": gross_margin,
            "sm_spend_pct": sm_spend_pct,
        },
        "projections": [],
        "summary": {},
    }
    
    current_mrr = mrr
    cumulative_sm_spend = 0
    cumulative_gross_profit = 0
    
    for month in range(1, months + 1):
        # Calculate growth and churn
        growth_rate = monthly_growth_pct / 100
        churn_rate = monthly_churn_pct / 100
        
        # Net growth = growth - churn
        net_growth_rate = growth_rate - churn_rate
        new_mrr = current_mrr * (1 + net_growth_rate)
        
        # Revenue and costs
        monthly_revenue = current_mrr
        gross_profit = monthly_revenue * gross_margin
        sm_spend = monthly_revenue * sm_spend_pct
        net_profit = gross_profit - sm_spend
        
        # Accumulate
        cumulative_sm_spend += sm_spend
        cumulative_gross_profit += gross_profit
        
        # ARR
        arr = current_mrr * 12
        
        results["projections"].append({
            "month": month,
            "mrr": round(current_mrr, 2),
            "arr": round(arr, 2),
            "monthly_revenue": round(monthly_revenue, 2),
            "gross_profit": round(gross_profit, 2),
            "sm_spend": round(sm_spend, 2),
            "net_profit": round(net_profit, 2),
            "growth_rate_pct": round(net_growth_rate * 100, 2),
        })
        
        current_mrr = new_mrr
    
    # Summary
    final_mrr = results["projections"][-1]["mrr"]
    final_arr = results["projections"][-1]["arr"]
    total_revenue = sum(p["monthly_revenue"] for p in results["projections"])
    total_net_profit = sum(p["net_profit"] for p in results["projections"])
    
    results["summary"] = {
        "starting_mrr": mrr,
        "ending_mrr": round(final_mrr, 2),
        "ending_arr": round(final_arr, 2),
        "mrr_growth_pct": round(((final_mrr - mrr) / mrr) * 100, 2),
        "total_revenue_12m": round(total_revenue, 2),
        "total_gross_profit_12m": round(cumulative_gross_profit, 2),
        "total_sm_spend_12m": round(cumulative_sm_spend, 2),
        "total_net_profit_12m": round(total_net_profit, 2),
        "avg_monthly_growth_pct": round((monthly_growth_pct - monthly_churn_pct), 2),
    }
    
    return results


def format_report(results):
    """Format simulation results as human-readable report."""
    lines = []
    lines.append("\n" + "=" * 70)
    lines.append("UNIT ECONOMICS SIMULATION - 12 MONTH PROJECTION")
    lines.append("=" * 70)
    
    # Inputs
    inputs = results["inputs"]
    lines.append("\n📊 INPUTS")
    lines.append(f"  Starting MRR: ${inputs['starting_mrr']:,.0f}")
    lines.append(f"  Monthly Growth: {inputs['monthly_growth_pct']}%")
    lines.append(f"  Monthly Churn: {inputs['monthly_churn_pct']}%")
    lines.append(f"  CAC: ${inputs['cac']:,.0f}")
    lines.append(f"  Gross Margin: {inputs['gross_margin']*100:.0f}%")
    lines.append(f"  S&M Spend: {inputs['sm_spend_pct']*100:.0f}% of revenue")
    
    # Summary
    summary = results["summary"]
    lines.append("\n📈 12-MONTH SUMMARY")
    lines.append(f"  Starting MRR: ${summary['starting_mrr']:,.0f}")
    lines.append(f"  Ending MRR: ${summary['ending_mrr']:,.0f}")
    lines.append(f"  Ending ARR: ${summary['ending_arr']:,.0f}")
    lines.append(f"  MRR Growth: {summary['mrr_growth_pct']:+.1f}%")
    lines.append(f"  Total Revenue: ${summary['total_revenue_12m']:,.0f}")
    lines.append(f"  Total Gross Profit: ${summary['total_gross_profit_12m']:,.0f}")
    lines.append(f"  Total S&M Spend: ${summary['total_sm_spend_12m']:,.0f}")
    lines.append(f"  Total Net Profit: ${summary['total_net_profit_12m']:,.0f}")
    
    # Monthly breakdown (first 3, last 3)
    lines.append("\n📅 MONTHLY PROJECTIONS")
    lines.append(f"{'Month':<8} {'MRR':<12} {'ARR':<12} {'Revenue':<12} {'Net Profit':<12}")
    lines.append("-" * 70)
    
    projs = results["projections"]
    for p in projs[:3]:
        lines.append(
            f"{p['month']:<8} ${p['mrr']:<11,.0f} ${p['arr']:<11,.0f} "
            f"${p['monthly_revenue']:<11,.0f} ${p['net_profit']:<11,.0f}"
        )
    
    if len(projs) > 6:
        lines.append("  ...")
    
    for p in projs[-3:]:
        lines.append(
            f"{p['month']:<8} ${p['mrr']:<11,.0f} ${p['arr']:<11,.0f} "
            f"${p['monthly_revenue']:<11,.0f} ${p['net_profit']:<11,.0f}"
        )
    
    lines.append("\n" + "=" * 70 + "\n")
    
    return "\n".join(lines)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Simulate SaaS unit economics over 12 months"
    )
    parser.add_argument("--mrr", type=float, required=True, help="Starting MRR")
    parser.add_argument(
        "--growth", type=float, required=True, help="Monthly growth rate (pct)"
    )
    parser.add_argument(
        "--churn", type=float, required=True, help="Monthly churn rate (pct)"
    )
    parser.add_argument("--cac", type=float, required=True, help="Customer acquisition cost")
    parser.add_argument(
        "--gross-margin", type=float, default=70, help="Gross margin %% (default: 70)"
    )
    parser.add_argument(
        "--sm-spend", type=float, default=30, help="S&M spend as %% of revenue (default: 30)"
    )
    parser.add_argument(
        "--months", type=int, default=12, help="Months to project (default: 12)"
    )
    parser.add_argument("--json", action="store_true", help="Output JSON format")
    
    args = parser.parse_args()
    
    results = simulate(
        mrr=args.mrr,
        monthly_growth_pct=args.growth,
        monthly_churn_pct=args.churn,
        cac=args.cac,
        gross_margin=args.gross_margin / 100 if args.gross_margin > 1 else args.gross_margin,
        sm_spend_pct=args.sm_spend / 100 if args.sm_spend > 1 else args.sm_spend,
        months=args.months,
    )
    
    if args.json:
        print(json.dumps(results, indent=2))
    else:
        print(format_report(results))
