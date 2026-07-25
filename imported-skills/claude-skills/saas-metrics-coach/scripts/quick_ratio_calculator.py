#!/usr/bin/env python3
"""
Quick Ratio Calculator - SaaS growth efficiency metric.

Quick Ratio = (New MRR + Expansion MRR) / (Churned MRR + Contraction MRR)

A ratio > 4 indicates healthy, efficient growth.
A ratio < 1 means you're losing revenue faster than gaining it.

Usage:
    python quick_ratio_calculator.py --new-mrr 10000 --expansion 2000 --churned 3000 --contraction 500
    python quick_ratio_calculator.py --new-mrr 10000 --expansion 2000 --churned 3000 --contraction 500 --json
"""

import json
import sys
import argparse


def calculate_quick_ratio(new_mrr, expansion_mrr, churned_mrr, contraction_mrr):
    """
    Calculate Quick Ratio and provide interpretation.
    
    Args:
        new_mrr: New MRR from new customers
        expansion_mrr: Expansion MRR from existing customers (upsells)
        churned_mrr: MRR lost from churned customers
        contraction_mrr: MRR lost from downgrades
    
    Returns:
        dict with quick ratio and analysis
    """
    # Calculate components
    growth_mrr = new_mrr + expansion_mrr
    lost_mrr = churned_mrr + contraction_mrr
    
    # Quick Ratio
    if lost_mrr == 0:
        quick_ratio = float('inf') if growth_mrr > 0 else 0
        quick_ratio_display = "∞" if growth_mrr > 0 else "0"
    else:
        quick_ratio = growth_mrr / lost_mrr
        quick_ratio_display = f"{quick_ratio:.2f}"
    
    # Status assessment
    if lost_mrr == 0 and growth_mrr > 0:
        status = "EXCELLENT"
        interpretation = "No revenue loss - perfect retention with growth"
    elif quick_ratio >= 4:
        status = "EXCELLENT"
        interpretation = "Strong, efficient growth - gaining revenue 4x faster than losing it"
    elif quick_ratio >= 2:
        status = "HEALTHY"
        interpretation = "Good growth efficiency - gaining revenue 2x+ faster than losing it"
    elif quick_ratio >= 1:
        status = "WATCH"
        interpretation = "Marginal growth - barely gaining more than losing"
    else:
        status = "CRITICAL"
        interpretation = "Losing revenue faster than gaining - growth is unsustainable"
    
    # Breakdown percentages
    if growth_mrr > 0:
        new_pct = (new_mrr / growth_mrr) * 100
        expansion_pct = (expansion_mrr / growth_mrr) * 100
    else:
        new_pct = expansion_pct = 0
    
    if lost_mrr > 0:
        churned_pct = (churned_mrr / lost_mrr) * 100
        contraction_pct = (contraction_mrr / lost_mrr) * 100
    else:
        churned_pct = contraction_pct = 0
    
    results = {
        "quick_ratio": quick_ratio if quick_ratio != float('inf') else None,
        "quick_ratio_display": quick_ratio_display,
        "status": status,
        "interpretation": interpretation,
        "components": {
            "growth_mrr": round(growth_mrr, 2),
            "lost_mrr": round(lost_mrr, 2),
            "new_mrr": round(new_mrr, 2),
            "expansion_mrr": round(expansion_mrr, 2),
            "churned_mrr": round(churned_mrr, 2),
            "contraction_mrr": round(contraction_mrr, 2),
        },
        "breakdown": {
            "new_mrr_pct": round(new_pct, 1),
            "expansion_mrr_pct": round(expansion_pct, 1),
            "churned_mrr_pct": round(churned_pct, 1),
            "contraction_mrr_pct": round(contraction_pct, 1),
        },
    }
    
    return results


def format_report(results):
    """Format quick ratio results as human-readable report."""
    lines = []
    lines.append("\n" + "=" * 70)
    lines.append("QUICK RATIO ANALYSIS")
    lines.append("=" * 70)
    
    # Quick Ratio
    lines.append(f"\n⚡ QUICK RATIO: {results['quick_ratio_display']}")
    lines.append(f"   Status: {results['status']}")
    lines.append(f"   {results['interpretation']}")
    
    # Components
    comp = results["components"]
    lines.append("\n📊 COMPONENTS")
    lines.append(f"  Growth MRR (New + Expansion): ${comp['growth_mrr']:,.2f}")
    lines.append(f"    • New MRR: ${comp['new_mrr']:,.2f}")
    lines.append(f"    • Expansion MRR: ${comp['expansion_mrr']:,.2f}")
    lines.append(f"  Lost MRR (Churned + Contraction): ${comp['lost_mrr']:,.2f}")
    lines.append(f"    • Churned MRR: ${comp['churned_mrr']:,.2f}")
    lines.append(f"    • Contraction MRR: ${comp['contraction_mrr']:,.2f}")
    
    # Breakdown
    bd = results["breakdown"]
    lines.append("\n📈 GROWTH BREAKDOWN")
    lines.append(f"  New customers: {bd['new_mrr_pct']:.1f}%")
    lines.append(f"  Expansion: {bd['expansion_mrr_pct']:.1f}%")
    
    lines.append("\n📉 LOSS BREAKDOWN")
    lines.append(f"  Churn: {bd['churned_mrr_pct']:.1f}%")
    lines.append(f"  Contraction: {bd['contraction_mrr_pct']:.1f}%")
    
    # Benchmarks
    lines.append("\n🎯 BENCHMARKS")
    lines.append("  < 1.0  = CRITICAL (losing revenue faster than gaining)")
    lines.append("  1-2    = WATCH (marginal growth)")
    lines.append("  2-4    = HEALTHY (good growth efficiency)")
    lines.append("  > 4    = EXCELLENT (strong, efficient growth)")
    
    lines.append("\n" + "=" * 70 + "\n")
    
    return "\n".join(lines)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Calculate SaaS Quick Ratio (growth efficiency metric)"
    )
    parser.add_argument(
        "--new-mrr", type=float, required=True, help="New MRR from new customers"
    )
    parser.add_argument(
        "--expansion", type=float, default=0, help="Expansion MRR from upsells (default: 0)"
    )
    parser.add_argument(
        "--churned", type=float, required=True, help="Churned MRR from lost customers"
    )
    parser.add_argument(
        "--contraction", type=float, default=0, help="Contraction MRR from downgrades (default: 0)"
    )
    parser.add_argument("--json", action="store_true", help="Output JSON format")
    
    args = parser.parse_args()
    
    results = calculate_quick_ratio(
        new_mrr=args.new_mrr,
        expansion_mrr=args.expansion,
        churned_mrr=args.churned,
        contraction_mrr=args.contraction,
    )
    
    if args.json:
        print(json.dumps(results, indent=2))
    else:
        print(format_report(results))
