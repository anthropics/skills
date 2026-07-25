#!/usr/bin/env python3
"""data_asset_valuator.py — Value a B2B customer data corpus + productization viability.

Stdlib-only. Takes a corpus profile and computes:
  - Strategic value score (0-10)
  - Defensibility moat strength (NONE / WEAK / MEDIUM / STRONG)
  - M&A multiplier (ARR uplift range in strategic-buyer scenarios)
  - Productization paths (benchmark / embedding / direct license) with risk profile
  - Contractual constraint impact (% of corpus blocked from productization)

Input schema (JSON):
{
  "data_type": "sales-engagement",       // descriptive
  "customer_count": 380,
  "time_history_years": 2.3,
  "exclusivity": "high",                  // none | low | medium | high
  "freshness": "real-time",               // batch-daily | batch-weekly | near-real-time | real-time
  "msa_carveouts_count": 47,              // # of customers with data-use carve-outs blocking productization
  "anonymization_audit_passed": false,    // k-anonymity >=5 confirmed
  "company_arr_m": 12,                    // company ARR in millions for M&A multiplier math
  "regulated_data_present": false
}

Usage:
    python data_asset_valuator.py                       # uses embedded B2B sample
    python data_asset_valuator.py path/to/corpus.json
    python data_asset_valuator.py corpus.json --output json
"""

import argparse
import json
import sys
from typing import Any, Dict, List


SAMPLE: Dict[str, Any] = {
    "data_type": "Sales engagement logs (email, calls, meetings)",
    "customer_count": 380,
    "time_history_years": 2.3,
    "exclusivity": "high",
    "freshness": "real-time",
    "msa_carveouts_count": 47,
    "anonymization_audit_passed": False,
    "company_arr_m": 12,
    "regulated_data_present": False,
}


EXCLUSIVITY_SCORE = {"none": 0, "low": 2, "medium": 5, "high": 9}
FRESHNESS_SCORE = {"batch-weekly": 2, "batch-daily": 5, "near-real-time": 7, "real-time": 9}


def strategic_value(profile: Dict[str, Any]) -> Dict[str, Any]:
    """Computes strategic value score and moat strength."""
    customers = profile.get("customer_count", 0)
    history = profile.get("time_history_years", 0)
    excl = profile.get("exclusivity", "none")
    fresh = profile.get("freshness", "batch-weekly")

    excl_score = EXCLUSIVITY_SCORE.get(excl, 0)
    fresh_score = FRESHNESS_SCORE.get(fresh, 0)

    # Customer cohort breadth
    if customers >= 500:
        cohort_score = 10
    elif customers >= 200:
        cohort_score = 8
    elif customers >= 100:
        cohort_score = 6
    elif customers >= 50:
        cohort_score = 4
    else:
        cohort_score = 2

    # Time history depth
    if history >= 5:
        history_score = 10
    elif history >= 3:
        history_score = 8
    elif history >= 2:
        history_score = 6
    elif history >= 1:
        history_score = 4
    else:
        history_score = 2

    # Composite
    composite = (excl_score * 2 + fresh_score + cohort_score + history_score) / 5
    composite = round(composite, 1)

    # Moat strength derived from exclusivity + cohort
    if excl_score >= 8 and cohort_score >= 8:
        moat = "STRONG"
        moat_explain = "Exclusivity + breadth means replicating requires 2+ years of customer cohort acquisition."
    elif excl_score >= 5 and cohort_score >= 6:
        moat = "MEDIUM"
        moat_explain = "Defensible but a well-funded competitor with 18-24 months can match."
    elif excl_score >= 2:
        moat = "WEAK"
        moat_explain = "Some unique characteristics but largely replicable from public or commercially-available sources."
    else:
        moat = "NONE"
        moat_explain = "Not a moat — same data is available elsewhere."

    return {
        "composite_score": composite,
        "max_score": 10.0,
        "components": {
            "exclusivity": excl_score,
            "freshness": fresh_score,
            "cohort_breadth": cohort_score,
            "history_depth": history_score,
        },
        "moat_strength": moat,
        "moat_explanation": moat_explain,
    }


def ma_multiplier(profile: Dict[str, Any], strategic: Dict[str, Any]) -> Dict[str, Any]:
    """Computes M&A multiplier range based on moat + corpus characteristics."""
    moat = strategic["moat_strength"]
    arr = profile.get("company_arr_m", 0)
    carveouts = profile.get("msa_carveouts_count", 0)
    customers = profile.get("customer_count", 1)
    carveout_pct = (carveouts / customers * 100) if customers else 0

    # Base multiplier by moat
    base = {
        "STRONG": (1.4, 1.7),
        "MEDIUM": (1.15, 1.35),
        "WEAK": (1.0, 1.1),
        "NONE": (1.0, 1.0),
    }
    low, high = base.get(moat, (1.0, 1.0))

    # Penalty for high carve-out %
    if carveout_pct > 25:
        low *= 0.85
        high *= 0.85
        carveout_note = f"{carveout_pct:.1f}% carve-out rate reduces multiplier ~15% (data is partially un-productizable)."
    elif carveout_pct > 10:
        low *= 0.95
        high *= 0.95
        carveout_note = f"{carveout_pct:.1f}% carve-out rate reduces multiplier ~5%."
    else:
        carveout_note = f"{carveout_pct:.1f}% carve-out rate — within tolerable range, no material multiplier impact."

    low_arr = round(arr * low, 1) if arr else None
    high_arr = round(arr * high, 1) if arr else None

    return {
        "multiplier_low": round(low, 2),
        "multiplier_high": round(high, 2),
        "carveout_pct": round(carveout_pct, 1),
        "carveout_note": carveout_note,
        "valuation_low_m": low_arr,
        "valuation_high_m": high_arr,
        "valuation_note": (
            f"Strategic-buyer scenario: ARR ${arr}M × ({low:.2f} - {high:.2f}) = ${low_arr}M - ${high_arr}M ARR-equivalent."
            if arr else "Provide company_arr_m to compute valuation range."
        ),
    }


def productization_paths(profile: Dict[str, Any], strategic: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Returns ranked productization paths with risk and viability."""
    customers = profile.get("customer_count", 0)
    carveouts = profile.get("msa_carveouts_count", 0)
    carveout_pct = (carveouts / customers * 100) if customers else 0
    anon_passed = profile.get("anonymization_audit_passed", False)
    regulated = profile.get("regulated_data_present", False)
    moat = strategic["moat_strength"]

    paths = []

    # Path 1: Industry benchmark report
    benchmark_risk = "LOW"
    benchmark_blockers = []
    if not anon_passed:
        benchmark_blockers.append("Anonymization audit (k-anonymity ≥ 5) required before publication")
    if regulated:
        benchmark_risk = "MEDIUM"
        benchmark_blockers.append("Regulated data present — additional compliance review required")
    paths.append({
        "path": "Industry benchmark report (anonymized aggregates)",
        "risk": benchmark_risk,
        "revenue_potential": "Low ($50K-$500K/yr) but high credibility lift",
        "viability": "HIGH" if not regulated else "MEDIUM",
        "blockers": benchmark_blockers or ["No structural blockers"],
        "first_step": (
            "Run anonymization audit on top-3 metrics; draft quarterly benchmark report; "
            "send to customers as opt-in value-add before public release."
        ),
    })

    # Path 2: Anonymized embedding endpoint
    embed_risk = "MEDIUM"
    embed_blockers = []
    if not anon_passed:
        embed_blockers.append("Anonymization audit required; embeddings can leak training data")
    if carveout_pct > 0:
        embed_blockers.append(
            f"{int(carveouts)} customers have MSA carve-outs blocking productized use of their data"
        )
    if regulated:
        embed_risk = "HIGH"
        embed_blockers.append("Regulated data present — embeddings may retain re-identifiable signal")
    paths.append({
        "path": "Anonymized embedding endpoint (AI features for customers)",
        "risk": embed_risk,
        "revenue_potential": "Medium ($500K-$3M/yr) as platform feature OR add-on",
        "viability": "HIGH" if moat in ("STRONG", "MEDIUM") and not regulated else "MEDIUM",
        "blockers": embed_blockers,
        "first_step": (
            "Pilot embedding endpoint with 3 design-partner customers; memorization tests; "
            "DPA addendum covering training-data flow."
        ),
    })

    # Path 3: Direct data licensing
    license_risk = "HIGH"
    license_blockers = []
    if carveout_pct > 10:
        license_blockers.append(
            f"{carveout_pct:.1f}% of customers ({int(carveouts)}) have MSA carve-outs — direct licensing is "
            "legally infeasible without re-papering or carve-out-excluded dataset"
        )
    license_blockers.append("Requires GDPR Art. 26 joint-controller analysis if EU customers present")
    if regulated:
        license_blockers.append("Regulated data licensing requires framework-specific consent + DPA")
    paths.append({
        "path": "Direct data licensing (to AI labs, data brokers, or industry players)",
        "risk": license_risk,
        "revenue_potential": "High ($2M-$20M/yr) at scale but high customer-trust cost",
        "viability": "LOW" if carveout_pct > 10 or regulated else "MEDIUM",
        "blockers": license_blockers,
        "first_step": (
            "First decide if customer trust impact is acceptable. If yes: re-paper 47 carve-out customers "
            "OR build carve-out-excluded dataset; engage data broker counsel; draft customer comms plan."
        ),
    })

    return paths


def recommend_path(paths: List[Dict[str, Any]]) -> str:
    """Picks the highest-viability lowest-risk path as the recommended starting point."""
    # Score: viability rank * 10 + (4 - risk_rank)
    viability_rank = {"HIGH": 3, "MEDIUM": 2, "LOW": 1}
    risk_rank = {"LOW": 3, "MEDIUM": 2, "HIGH": 1}

    scored = [
        (viability_rank.get(p["viability"], 0) * 10 + risk_rank.get(p["risk"], 0), p)
        for p in paths
    ]
    scored.sort(key=lambda x: -x[0])
    return scored[0][1]["path"]


def analyze(profile: Dict[str, Any]) -> Dict[str, Any]:
    strategic = strategic_value(profile)
    ma = ma_multiplier(profile, strategic)
    paths = productization_paths(profile, strategic)
    recommended = recommend_path(paths)
    return {
        "strategic_value": strategic,
        "ma_multiplier": ma,
        "productization_paths": paths,
        "recommended_starting_path": recommended,
    }


def render_text(result: Dict[str, Any], profile: Dict[str, Any], source: str) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("DATA ASSET VALUATION")
    lines.append(f"Source: {source}")
    lines.append("=" * 72)
    lines.append("")
    lines.append(f"Corpus: {profile.get('data_type')}")
    lines.append(f"  Customers: {profile.get('customer_count')} | History: {profile.get('time_history_years')} years")
    lines.append(f"  Exclusivity: {profile.get('exclusivity')} | Freshness: {profile.get('freshness')}")
    lines.append(f"  MSA carve-outs: {profile.get('msa_carveouts_count')} customer(s)")
    lines.append(f"  Anonymization audit passed: {profile.get('anonymization_audit_passed')}")
    lines.append(f"  Regulated data present: {profile.get('regulated_data_present')}")
    lines.append("")
    lines.append("-" * 72)

    sv = result["strategic_value"]
    lines.append(f"STRATEGIC VALUE: {sv['composite_score']} / {sv['max_score']}")
    lines.append("  Components:")
    for k, v in sv["components"].items():
        lines.append(f"    {k:<20} {v}/10")
    lines.append(f"  Moat strength: {sv['moat_strength']}")
    for line in _wrap(f"  {sv['moat_explanation']}", 2):
        lines.append(line)
    lines.append("")
    lines.append("-" * 72)

    ma = result["ma_multiplier"]
    lines.append(f"M&A MULTIPLIER (strategic-buyer scenario):")
    lines.append(f"  Range: {ma['multiplier_low']}x – {ma['multiplier_high']}x ARR")
    if ma.get("valuation_low_m") is not None:
        lines.append(f"  Valuation impact: ${ma['valuation_low_m']}M – ${ma['valuation_high_m']}M ARR-equivalent")
    for line in _wrap(f"  {ma['carveout_note']}", 2):
        lines.append(line)
    lines.append("")
    lines.append("-" * 72)
    lines.append("PRODUCTIZATION PATHS:")
    lines.append("")

    for i, p in enumerate(result["productization_paths"], 1):
        lines.append(f"  [{i}] {p['path']}")
        lines.append(f"      Risk: {p['risk']} | Viability: {p['viability']} | Revenue: {p['revenue_potential']}")
        lines.append(f"      Blockers:")
        for b in p["blockers"]:
            lines.append(f"        - {b}")
        lines.append(f"      First step:")
        for line in _wrap(p["first_step"], 8):
            lines.append(line)
        lines.append("")

    lines.append("-" * 72)
    lines.append(f"RECOMMENDED STARTING PATH: {result['recommended_starting_path']}")
    lines.append("")
    lines.append("REMINDER: This valuation is a triage. Any actual productization, licensing, or M&A use")
    lines.append("requires legal + data privacy review. Customer-trust impact is often the binding constraint,")
    lines.append("not legal feasibility.")
    return "\n".join(lines)


def _wrap(text: str, indent: int, width: int = 70) -> List[str]:
    import textwrap
    return textwrap.wrap(text, width=width, initial_indent=" " * indent, subsequent_indent=" " * indent) or [" " * indent + text]


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Value a B2B customer data corpus + productization paths.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("path", nargs="?", help="Path to corpus JSON (uses embedded sample if omitted)")
    parser.add_argument("--output", choices=("text", "json"), default="text", help="Output format")
    args = parser.parse_args()

    if args.path:
        try:
            with open(args.path, "r", encoding="utf-8") as f:
                profile = json.load(f)
            source = args.path
        except (IOError, OSError) as e:
            print(f"error: could not read {args.path}: {e}", file=sys.stderr)
            return 1
        except json.JSONDecodeError as e:
            print(f"error: invalid JSON in {args.path}: {e}", file=sys.stderr)
            return 1
    else:
        profile = SAMPLE
        source = "<embedded sample: B2B SaaS sales engagement, 380 customers, 47 carve-outs>"

    result = analyze(profile)

    if args.output == "json":
        print(json.dumps({"source": source, "profile": profile, **result}, indent=2))
    else:
        print(render_text(result, profile, source))

    return 0


if __name__ == "__main__":
    sys.exit(main())
