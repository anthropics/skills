#!/usr/bin/env python3
"""
Portfolio Analyzer — Product portfolio BCG matrix classification and investment analysis.

For each product, classifies into BCG quadrant (Star, Cash Cow, Question Mark, Dog)
and generates investment recommendations (Invest / Maintain / Kill).

Usage:
    python portfolio_analyzer.py                     # Run with built-in sample data
    python portfolio_analyzer.py --input data.json   # Run with your data
    python portfolio_analyzer.py --json              # Output raw JSON

JSON input format: see sample_data() function below.
"""

import json
import sys
import argparse
from typing import Optional


# ---------------------------------------------------------------------------
# Sample data
# ---------------------------------------------------------------------------

def sample_data() -> dict:
    """
    Sample portfolio. Replace with real product data.

    Fields:
      name              Product name
      revenue_quarterly Current quarter revenue (any consistent currency)
      revenue_prev_q    Revenue last quarter (for QoQ calculation)
      market_growth_pct Annual market growth rate (percent, e.g. 12.5 for 12.5%)
      your_market_share Your estimated market share (percent, e.g. 8.0 for 8%)
      largest_competitor_share  Largest competitor's share (percent)
      eng_capacity_pct  % of total engineering capacity allocated (0-100)
      d30_retention     Optional D30 retention rate (decimal, e.g. 0.45)
      nps               Optional NPS score (-100 to 100)
      notes             Optional free text notes for the report
    """
    return {
        "company": "Acme Corp",
        "total_engineering_headcount": 45,
        "products": [
            {
                "name": "CorePlatform",
                "revenue_quarterly": 480000,
                "revenue_prev_q": 430000,
                "market_growth_pct": 22.0,
                "your_market_share": 18.0,
                "largest_competitor_share": 12.0,
                "eng_capacity_pct": 35,
                "d30_retention": 0.61,
                "nps": 52,
                "notes": "Our flagship. Leading market share in fast-growing segment.",
            },
            {
                "name": "ReportingModule",
                "revenue_quarterly": 290000,
                "revenue_prev_q": 285000,
                "market_growth_pct": 5.0,
                "your_market_share": 22.0,
                "largest_competitor_share": 18.0,
                "eng_capacity_pct": 25,
                "d30_retention": 0.58,
                "nps": 38,
                "notes": "Mature product, strong margins, slow market.",
            },
            {
                "name": "MobileApp",
                "revenue_quarterly": 95000,
                "revenue_prev_q": 78000,
                "market_growth_pct": 35.0,
                "your_market_share": 3.5,
                "largest_competitor_share": 24.0,
                "eng_capacity_pct": 28,
                "d30_retention": 0.31,
                "nps": 22,
                "notes": "High growth market. We're far behind on share. Bet or exit.",
            },
            {
                "name": "LegacyConnector",
                "revenue_quarterly": 62000,
                "revenue_prev_q": 68000,
                "market_growth_pct": -3.0,
                "your_market_share": 8.0,
                "largest_competitor_share": 35.0,
                "eng_capacity_pct": 12,
                "d30_retention": 0.42,
                "nps": 14,
                "notes": "Declining market. Customers are on long-term contracts.",
            },
        ],
    }


# ---------------------------------------------------------------------------
# BCG Classification
# ---------------------------------------------------------------------------

# Growth rate threshold: markets growing faster than this are "high growth"
GROWTH_THRESHOLD_PCT = 10.0

# Market share ratio threshold: ratio > 1.0 means you lead the market
SHARE_RATIO_THRESHOLD = 1.0


def bcg_quadrant(market_growth_pct: float, share_ratio: float) -> str:
    high_growth = market_growth_pct >= GROWTH_THRESHOLD_PCT
    leading_share = share_ratio >= SHARE_RATIO_THRESHOLD

    if high_growth and leading_share:
        return "Star"
    elif not high_growth and leading_share:
        return "Cash Cow"
    elif high_growth and not leading_share:
        return "Question Mark"
    else:
        return "Dog"


def quadrant_emoji(quadrant: str) -> str:
    return {
        "Star": "⭐",
        "Cash Cow": "🐄",
        "Question Mark": "❓",
        "Dog": "🐕",
    }.get(quadrant, "?")


def investment_posture(quadrant: str, qoq_growth: float, retention: Optional[float]) -> str:
    """
    Invest / Maintain / Kill recommendation with nuance.
    """
    if quadrant == "Star":
        return "Invest"
    elif quadrant == "Cash Cow":
        # If cash cow is declining fast or retention is poor, consider killing
        if qoq_growth < -0.10 or (retention is not None and retention < 0.30):
            return "Kill"
        return "Maintain"
    elif quadrant == "Question Mark":
        # Fast QoQ growth signals the bet might pay off → Invest
        # Flat or slow QoQ with weak retention → Kill
        if qoq_growth >= 0.15 and (retention is None or retention >= 0.25):
            return "Invest"
        elif qoq_growth < 0.05 or (retention is not None and retention < 0.20):
            return "Kill"
        return "Evaluate"  # Needs explicit strategic decision
    else:  # Dog
        if qoq_growth > 0.10 and (retention is None or retention >= 0.35):
            return "Evaluate"  # Surprising momentum — verify before killing
        return "Kill"


def posture_color(posture: str) -> str:
    return {
        "Invest": "✓",
        "Maintain": "◑",
        "Kill": "✗",
        "Evaluate": "⚠",
    }.get(posture, "?")


# ---------------------------------------------------------------------------
# Product analysis
# ---------------------------------------------------------------------------

def analyze_product(p: dict) -> dict:
    revenue_q = p.get("revenue_quarterly", 0)
    revenue_prev = p.get("revenue_prev_q", revenue_q)
    qoq_growth = (revenue_q - revenue_prev) / revenue_prev if revenue_prev else 0.0

    your_share = p.get("your_market_share", 0)
    competitor_share = p.get("largest_competitor_share", 1)
    share_ratio = your_share / competitor_share if competitor_share else 0.0

    market_growth = p.get("market_growth_pct", 0)
    retention = p.get("d30_retention")
    nps = p.get("nps")
    eng_pct = p.get("eng_capacity_pct", 0)

    quadrant = bcg_quadrant(market_growth, share_ratio)
    posture = investment_posture(quadrant, qoq_growth, retention)

    # Alignment score: how well does engineering investment match the recommended posture?
    # Invest products should have high eng allocation; Kill products should have low.
    alignment_score = _compute_alignment(posture, eng_pct)

    return {
        "name": p.get("name", "Unknown"),
        "revenue_quarterly": revenue_q,
        "revenue_prev_q": revenue_prev,
        "qoq_growth": qoq_growth,
        "market_growth_pct": market_growth,
        "your_market_share": your_share,
        "largest_competitor_share": competitor_share,
        "share_ratio": share_ratio,
        "eng_capacity_pct": eng_pct,
        "d30_retention": retention,
        "nps": nps,
        "quadrant": quadrant,
        "posture": posture,
        "alignment_score": alignment_score,
        "notes": p.get("notes", ""),
        "findings": _product_findings(quadrant, posture, qoq_growth, share_ratio,
                                      market_growth, retention, nps, eng_pct),
    }


def _compute_alignment(posture: str, eng_pct: float) -> float:
    """
    Returns 0.0-1.0 score. High = engineering allocation matches strategic posture.
    """
    targets = {"Invest": 0.35, "Maintain": 0.15, "Kill": 0.05, "Evaluate": 0.20}
    target = targets.get(posture, 0.20)
    deviation = abs(eng_pct / 100 - target)
    return max(0.0, 1.0 - (deviation / 0.35))


def _product_findings(
    quadrant: str, posture: str,
    qoq_growth: float, share_ratio: float, market_growth: float,
    retention: Optional[float], nps: Optional[int], eng_pct: float
) -> list:
    findings = []

    if quadrant == "Star":
        if eng_pct < 30:
            findings.append(f"⚠ Star product getting only {eng_pct}% of eng capacity — likely underinvested. Stars need fuel.")
        else:
            findings.append(f"✓ Star product with {eng_pct}% eng allocation — appropriate investment.")
        if share_ratio < 1.5:
            findings.append(f"◑ Share ratio {share_ratio:.1f}x — leading but not dominant. Accelerate to widen the gap.")
        else:
            findings.append(f"✓ Share ratio {share_ratio:.1f}x — strong lead. Defend aggressively.")

    elif quadrant == "Cash Cow":
        if eng_pct > 25:
            findings.append(f"⚠ Cash Cow getting {eng_pct}% of eng — overinvested. Reduce to 10-15% max. Redeploy to Stars.")
        else:
            findings.append(f"✓ Cash Cow with {eng_pct}% eng — appropriate. Don't innovate, just maintain.")
        if qoq_growth < -0.05:
            findings.append(f"⚠ Revenue declining {abs(qoq_growth):.0%} QoQ — monitor for transition to Dog.")
        else:
            findings.append(f"✓ Revenue stable (QoQ: {qoq_growth:+.0%}) — milk this.")

    elif quadrant == "Question Mark":
        findings.append(f"⚠ Fast market ({market_growth:.0f}% growth) but only {share_ratio:.1f}x relative share.")
        findings.append(f"  Decision required: Invest to capture share or exit. 'Maintain' loses share every quarter.")
        if qoq_growth >= 0.15:
            findings.append(f"✓ QoQ growth {qoq_growth:+.0%} — momentum building. Investment may be justified.")
        elif qoq_growth < 0.05:
            findings.append(f"✗ QoQ growth {qoq_growth:+.0%} — stalled despite hot market. Strong exit signal.")

    elif quadrant == "Dog":
        findings.append(f"✗ Low share ({share_ratio:.1f}x) in slow/declining market ({market_growth:.0f}% growth).")
        if eng_pct > 10:
            findings.append(f"✗ Dog consuming {eng_pct}% of eng capacity. Set a sunset date. Migrate customers.")
        if qoq_growth > 0:
            findings.append(f"◑ Slight QoQ growth ({qoq_growth:+.0%}) — verify whether this is genuine or contract timing.")

    if retention is not None:
        if retention < 0.30:
            findings.append(f"✗ D30 retention {retention:.0%} — users not finding value. Weak unit economics for any posture.")
        elif retention >= 0.50:
            findings.append(f"✓ D30 retention {retention:.0%} — users find value. Supports investment or stable maintenance.")

    if nps is not None:
        if nps < 0:
            findings.append(f"✗ NPS {nps} — net detractors. Word of mouth is negative. Fix before scaling.")
        elif nps >= 40:
            findings.append(f"✓ NPS {nps} — strong promoter base. Harness for referrals.")

    return findings


# ---------------------------------------------------------------------------
# Portfolio-level analysis
# ---------------------------------------------------------------------------

def analyze_portfolio(data: dict) -> dict:
    products = [analyze_product(p) for p in data.get("products", [])]

    total_revenue = sum(p["revenue_quarterly"] for p in products)
    total_eng = sum(p["eng_capacity_pct"] for p in products)

    # Revenue by quadrant
    quadrant_revenue = {}
    quadrant_eng = {}
    for p in products:
        q = p["quadrant"]
        quadrant_revenue[q] = quadrant_revenue.get(q, 0) + p["revenue_quarterly"]
        quadrant_eng[q] = quadrant_eng.get(q, 0) + p["eng_capacity_pct"]

    # Portfolio health score
    health = _portfolio_health(products, total_revenue, total_eng)

    # Portfolio-level findings
    portfolio_findings = _portfolio_findings(products, total_revenue, quadrant_revenue, quadrant_eng)

    return {
        "company": data.get("company", "Unknown"),
        "total_engineering_headcount": data.get("total_engineering_headcount"),
        "products": products,
        "total_revenue_quarterly": total_revenue,
        "quadrant_summary": {
            q: {
                "count": sum(1 for p in products if p["quadrant"] == q),
                "revenue": quadrant_revenue.get(q, 0),
                "revenue_pct": quadrant_revenue.get(q, 0) / total_revenue if total_revenue else 0,
                "eng_pct": quadrant_eng.get(q, 0),
            }
            for q in ["Star", "Cash Cow", "Question Mark", "Dog"]
        },
        "portfolio_health_score": health,
        "portfolio_findings": portfolio_findings,
    }


def _portfolio_health(products: list, total_revenue: float, total_eng: float) -> float:
    """
    Portfolio health 0-1. Penalizes:
    - No Stars (no growth engine)
    - Dogs consuming > 20% of eng
    - Poor alignment scores
    - Revenue concentrated in Dogs/Question Marks
    """
    score = 1.0

    quadrants = [p["quadrant"] for p in products]
    has_star = "Star" in quadrants
    has_cash_cow = "Cash Cow" in quadrants

    if not has_star:
        score -= 0.25  # No growth engine is a serious problem
    if not has_cash_cow:
        score -= 0.10  # No cash generator means funding stars from burn

    # Dog eng allocation penalty
    dog_eng = sum(p["eng_capacity_pct"] for p in products if p["quadrant"] == "Dog")
    if dog_eng > 20:
        score -= 0.20
    elif dog_eng > 10:
        score -= 0.10

    # Revenue in dogs penalty
    if total_revenue > 0:
        dog_rev_pct = sum(p["revenue_quarterly"] for p in products if p["quadrant"] == "Dog") / total_revenue
        if dog_rev_pct > 0.30:
            score -= 0.15

    # Average alignment score
    avg_alignment = sum(p["alignment_score"] for p in products) / len(products) if products else 0
    score -= (1 - avg_alignment) * 0.20

    return max(0.0, min(1.0, score))


def _portfolio_findings(
    products: list, total_revenue: float,
    quadrant_revenue: dict, quadrant_eng: dict
) -> list:
    findings = []

    stars = [p for p in products if p["quadrant"] == "Star"]
    cows = [p for p in products if p["quadrant"] == "Cash Cow"]
    questions = [p for p in products if p["quadrant"] == "Question Mark"]
    dogs = [p for p in products if p["quadrant"] == "Dog"]

    if not stars:
        findings.append("✗ CRITICAL: No Star products. You have no growth engine. Identify a Question Mark to invest in or revisit your market positioning.")
    elif len(stars) == 1:
        findings.append(f"◑ Single Star ({stars[0]['name']}). Portfolio is fragile — one product drives all growth. Diversify.")
    else:
        findings.append(f"✓ {len(stars)} Star products — healthy growth engine.")

    if not cows:
        findings.append("⚠ No Cash Cow products. Stars are consuming capital without a self-funding mechanism. Watch burn rate.")
    else:
        cow_rev = quadrant_revenue.get("Cash Cow", 0)
        cow_pct = cow_rev / total_revenue if total_revenue else 0
        findings.append(f"✓ Cash Cow revenue: {cow_pct:.0%} of total — funds Star investment.")

    if questions:
        findings.append(f"⚠ {len(questions)} Question Mark(s): {', '.join(p['name'] for p in questions)}.")
        findings.append("  Each needs a binary decision: invest to win share, or exit. Set a 2-quarter deadline.")

    if dogs:
        dog_eng_total = sum(p["eng_capacity_pct"] for p in dogs)
        findings.append(f"✗ {len(dogs)} Dog product(s): {', '.join(p['name'] for p in dogs)} consuming {dog_eng_total}% of eng capacity.")
        findings.append(f"  That's {dog_eng_total}% of your engineers on declining products. Set sunset dates.")

    # Alignment check
    misaligned = [p for p in products if p["alignment_score"] < 0.50]
    if misaligned:
        findings.append(f"⚠ Engineering allocation misaligned on: {', '.join(p['name'] for p in misaligned)}.")
        findings.append("  Rebalance: move capacity from Dogs/Cows to Stars.")

    return findings


# ---------------------------------------------------------------------------
# Report rendering
# ---------------------------------------------------------------------------

def fmt_currency(n: float) -> str:
    if n >= 1_000_000:
        return f"${n/1_000_000:.1f}M"
    elif n >= 1_000:
        return f"${n/1_000:.0f}K"
    return f"${n:.0f}"


def render_report(result: dict) -> str:
    lines = []
    lines.append("=" * 65)
    lines.append(f"  PORTFOLIO ANALYZER — {result['company']}")
    lines.append(f"  Total Quarterly Revenue: {fmt_currency(result['total_revenue_quarterly'])}")
    if result.get("total_engineering_headcount"):
        lines.append(f"  Engineering Headcount: {result['total_engineering_headcount']}")
    lines.append("=" * 65)
    lines.append("")

    # Portfolio health
    health = result["portfolio_health_score"]
    bar_len = 40
    filled = round(health * bar_len)
    bar = "█" * filled + "░" * (bar_len - filled)
    lines.append(f"  Portfolio Health: {health:.0%}")
    lines.append(f"  [{bar}]")
    lines.append("")

    # Quadrant summary
    lines.append("  QUADRANT SUMMARY")
    lines.append("  " + "-" * 55)
    header = f"  {'Quadrant':<15} {'Count':>5} {'Revenue':>10} {'Rev%':>6} {'Eng%':>6}"
    lines.append(header)
    lines.append("  " + "-" * 55)
    total_rev = result["total_revenue_quarterly"]
    for q in ["Star", "Cash Cow", "Question Mark", "Dog"]:
        qs = result["quadrant_summary"][q]
        emoji = quadrant_emoji(q)
        label = f"{emoji} {q}"
        rev_pct = f"{qs['revenue_pct']:.0%}" if qs["count"] else "-"
        eng = f"{qs['eng_pct']}%" if qs["count"] else "-"
        rev = fmt_currency(qs["revenue"]) if qs["count"] else "-"
        lines.append(f"  {label:<15} {qs['count']:>5} {rev:>10} {rev_pct:>6} {eng:>6}")
    lines.append("")

    # Per-product breakdown
    lines.append("  PRODUCT BREAKDOWN")
    lines.append("  " + "-" * 65)
    for p in result["products"]:
        emoji = quadrant_emoji(p["quadrant"])
        pc = posture_color(p["posture"])
        lines.append(
            f"  {emoji} {p['name']} — {p['quadrant']} → {pc} {p['posture']}"
        )
        lines.append(
            f"     Revenue: {fmt_currency(p['revenue_quarterly'])}/qtr  "
            f"QoQ: {p['qoq_growth']:+.0%}  "
            f"Mkt growth: {p['market_growth_pct']:+.0f}%"
        )
        lines.append(
            f"     Share ratio: {p['share_ratio']:.1f}x  "
            f"Eng: {p['eng_capacity_pct']}%  "
            f"Alignment: {p['alignment_score']:.0%}"
        )
        if p.get("d30_retention") is not None:
            lines.append(
                f"     D30 retention: {p['d30_retention']:.0%}  "
                f"NPS: {p['nps'] if p['nps'] is not None else 'N/A'}"
            )
        if p.get("notes"):
            lines.append(f"     Note: {p['notes']}")
        for f in p.get("findings", []):
            lines.append(f"     {f}")
        lines.append("")

    # Portfolio-level findings
    lines.append("  PORTFOLIO FINDINGS")
    lines.append("  " + "-" * 65)
    for f in result.get("portfolio_findings", []):
        lines.append(f"  {f}")
    lines.append("")
    lines.append("=" * 65)

    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Portfolio Analyzer — BCG matrix classification and investment recommendations",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument(
        "--input", "-i",
        metavar="FILE",
        help="JSON file with portfolio data (default: built-in sample data)",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output raw JSON result",
    )
    args = parser.parse_args()

    if args.input:
        try:
            with open(args.input) as f:
                data = json.load(f)
        except FileNotFoundError:
            print(f"Error: file not found: {args.input}", file=sys.stderr)
            sys.exit(1)
        except json.JSONDecodeError as e:
            print(f"Error: invalid JSON: {e}", file=sys.stderr)
            sys.exit(1)
    else:
        print("No input file provided — running with sample data.\n")
        data = sample_data()

    result = analyze_portfolio(data)

    if args.json:
        # Make result JSON-serializable
        def clean(obj):
            if isinstance(obj, dict):
                return {k: clean(v) for k, v in obj.items()}
            elif isinstance(obj, list):
                return [clean(v) for v in obj]
            elif isinstance(obj, float):
                return round(obj, 4)
            return obj
        print(json.dumps(clean(result), indent=2))
    else:
        print(render_report(result))


if __name__ == "__main__":
    main()
