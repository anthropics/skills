#!/usr/bin/env python3
"""retention_decomposition_analyzer.py — Honest retention decomposition for B2B SaaS.

Stdlib-only. Takes cohort data and outputs:
  - Gross Revenue Retention (GRR), Net Revenue Retention (NRR), Logo Retention by cohort
  - Contraction vs Expansion separation (NRR alone hides churn)
  - Churn root-cause categorization (7-category taxonomy)
  - Health verdict per cohort with thresholds

Deterministic logic derived from inputs. No projections.

Input schema (JSON):
{
  "cohorts": [
    {
      "name": "2025-Q1",
      "starting_arr": 2400000,         # ARR of customers acquired in this cohort
      "starting_customer_count": 80,
      "renewed_arr": 2280000,           # ARR retained at 1-year mark (after churn + contraction)
      "renewed_customer_count": 72,
      "expansion_arr": 360000,          # ARR from upsells / seat additions in same cohort
      "contraction_arr": 80000,         # ARR lost from downsells (without churn)
      "churn_reasons": {                # logo-count by category
        "product_fit": 3,
        "competitor_loss": 2,
        "no_value_realized": 1,
        "pricing": 1,
        "champion_left": 1,
        "company_event": 0,
        "tactical_failure": 0
      }
    }
  ]
}

Usage:
    python retention_decomposition_analyzer.py                       # uses embedded sample
    python retention_decomposition_analyzer.py path/to/cohorts.json
    python retention_decomposition_analyzer.py cohorts.json --output json
"""

import argparse
import json
import sys
from typing import Any, Dict, List


# 7-category churn taxonomy
CHURN_CATEGORIES = {
    "product_fit": "Product didn't solve customer's actual job-to-be-done",
    "competitor_loss": "Lost to a competitor with better fit or price",
    "no_value_realized": "Customer never reached time-to-value; onboarding gap",
    "pricing": "Price-driven churn (too expensive, or perceived as low value)",
    "champion_left": "Internal champion changed roles or left the company",
    "company_event": "Customer's company event (M&A, layoffs, shutdown) — not preventable",
    "tactical_failure": "Service / support failure — preventable with better CS execution",
}

# Health thresholds (B2B SaaS baseline)
THRESHOLDS = {
    "grr": {"healthy": 0.90, "concerning": 0.85, "critical": 0.80},
    "nrr": {"healthy": 1.10, "concerning": 1.00, "critical": 0.95},
    "logo": {"healthy": 0.85, "concerning": 0.75, "critical": 0.65},
}


SAMPLE: Dict[str, Any] = {
    "cohorts": [
        {
            "name": "2025-Q1",
            "starting_arr": 2_400_000,
            "starting_customer_count": 80,
            "renewed_arr": 2_280_000,
            "renewed_customer_count": 72,
            "expansion_arr": 360_000,
            "contraction_arr": 80_000,
            "churn_reasons": {
                "product_fit": 3,
                "competitor_loss": 2,
                "no_value_realized": 1,
                "pricing": 1,
                "champion_left": 1,
                "company_event": 0,
                "tactical_failure": 0,
            },
        },
        {
            "name": "2025-Q2",
            "starting_arr": 3_100_000,
            "starting_customer_count": 95,
            "renewed_arr": 2_790_000,
            "renewed_customer_count": 81,
            "expansion_arr": 280_000,
            "contraction_arr": 165_000,
            "churn_reasons": {
                "product_fit": 6,
                "competitor_loss": 3,
                "no_value_realized": 2,
                "pricing": 2,
                "champion_left": 1,
                "company_event": 0,
                "tactical_failure": 0,
            },
        },
    ]
}


def analyze_cohort(cohort: Dict[str, Any]) -> Dict[str, Any]:
    starting_arr = cohort.get("starting_arr", 0)
    renewed_arr = cohort.get("renewed_arr", 0)
    expansion = cohort.get("expansion_arr", 0)
    contraction = cohort.get("contraction_arr", 0)
    starting_count = cohort.get("starting_customer_count", 0)
    renewed_count = cohort.get("renewed_customer_count", 0)

    # GRR = (starting_arr - churn - contraction) / starting_arr
    # renewed_arr already reflects churn but NOT contraction (per schema)
    grr = (renewed_arr - contraction) / starting_arr if starting_arr else 0
    # NRR = GRR + expansion / starting
    nrr = grr + (expansion / starting_arr) if starting_arr else 0
    logo = renewed_count / starting_count if starting_count else 0

    return {
        "cohort": cohort.get("name"),
        "starting_arr": starting_arr,
        "renewed_arr": renewed_arr,
        "expansion_arr": expansion,
        "contraction_arr": contraction,
        "gross_retention": round(grr, 4),
        "net_retention": round(nrr, 4),
        "logo_retention": round(logo, 4),
        "expansion_pct": round((expansion / starting_arr * 100) if starting_arr else 0, 1),
        "contraction_pct": round((contraction / starting_arr * 100) if starting_arr else 0, 1),
        "churn_customers": starting_count - renewed_count,
        "churn_reasons": cohort.get("churn_reasons", {}),
    }


def verdict(grr: float, nrr: float, logo: float) -> Dict[str, str]:
    def bucket(value: float, kind: str) -> str:
        t = THRESHOLDS[kind]
        if value >= t["healthy"]:
            return "HEALTHY"
        if value >= t["concerning"]:
            return "CONCERNING"
        if value >= t["critical"]:
            return "POOR"
        return "CRITICAL"

    grr_v = bucket(grr, "grr")
    nrr_v = bucket(nrr, "nrr")
    logo_v = bucket(logo, "logo")

    # Special detection: NRR healthy but GRR poor → leaky bucket masked by expansion
    overall = "HEALTHY"
    notes: List[str] = []
    if nrr >= THRESHOLDS["nrr"]["healthy"] and grr < THRESHOLDS["grr"]["concerning"]:
        overall = "LEAKY BUCKET"
        notes.append(
            "NRR looks healthy but GRR is poor: expansion is masking churn. "
            "Fix retention before celebrating NRR."
        )
    elif "CRITICAL" in (grr_v, nrr_v, logo_v):
        overall = "CRITICAL"
    elif "POOR" in (grr_v, nrr_v, logo_v):
        overall = "POOR"
    elif "CONCERNING" in (grr_v, nrr_v, logo_v):
        overall = "CONCERNING"

    return {
        "grr_verdict": grr_v,
        "nrr_verdict": nrr_v,
        "logo_verdict": logo_v,
        "overall": overall,
        "notes": " | ".join(notes) if notes else "",
    }


def churn_root_cause_summary(cohort_results: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Aggregate churn reasons across all cohorts; identify top drivers."""
    totals: Dict[str, int] = {k: 0 for k in CHURN_CATEGORIES}
    for r in cohort_results:
        for cat, count in (r.get("churn_reasons") or {}).items():
            if cat in totals:
                totals[cat] += count

    total_churn = sum(totals.values())
    if total_churn == 0:
        return {"total_churn_customers": 0, "top_drivers": [], "preventable_pct": 0.0}

    ranked = sorted(totals.items(), key=lambda x: -x[1])
    top_drivers = [
        {
            "category": cat,
            "description": CHURN_CATEGORIES[cat],
            "count": cnt,
            "pct": round((cnt / total_churn) * 100, 1),
        }
        for cat, cnt in ranked if cnt > 0
    ][:3]

    # Preventable = product_fit, no_value_realized, tactical_failure (within CS control)
    # Less preventable = competitor_loss, pricing, champion_left (mixed)
    # Not preventable = company_event
    preventable_count = totals["product_fit"] + totals["no_value_realized"] + totals["tactical_failure"]
    preventable_pct = round((preventable_count / total_churn) * 100, 1)

    return {
        "total_churn_customers": total_churn,
        "top_drivers": top_drivers,
        "preventable_pct": preventable_pct,
    }


def analyze(payload: Dict[str, Any]) -> Dict[str, Any]:
    cohort_results = []
    for cohort in payload.get("cohorts", []):
        result = analyze_cohort(cohort)
        result["verdict"] = verdict(
            result["gross_retention"],
            result["net_retention"],
            result["logo_retention"],
        )
        cohort_results.append(result)

    return {
        "cohorts": cohort_results,
        "churn_summary": churn_root_cause_summary(cohort_results),
    }


def render_text(result: Dict[str, Any], source: str) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("RETENTION DECOMPOSITION")
    lines.append(f"Source: {source}")
    lines.append("=" * 72)
    lines.append("")

    for c in result["cohorts"]:
        v = c["verdict"]
        lines.append(f"📊 Cohort {c['cohort']}  —  {v['overall']}")
        lines.append(f"   Starting ARR: ${c['starting_arr']:,.0f}")
        lines.append(f"   Renewed ARR:  ${c['renewed_arr']:,.0f}")
        lines.append("")
        lines.append(f"   GRR: {c['gross_retention']*100:5.1f}%  [{v['grr_verdict']}]   (healthy ≥ 90%)")
        lines.append(f"   NRR: {c['net_retention']*100:5.1f}%  [{v['nrr_verdict']}]   (healthy ≥ 110%)")
        lines.append(f"   Logo: {c['logo_retention']*100:4.1f}%  [{v['logo_verdict']}]   (healthy ≥ 85%)")
        lines.append("")
        lines.append(f"   Contraction: {c['contraction_pct']:.1f}%   |   Expansion: {c['expansion_pct']:.1f}%")
        lines.append(f"   Customers churned: {c['churn_customers']}")
        if v["notes"]:
            lines.append("")
            lines.append(f"   ⚠️  {v['notes']}")
        lines.append("")
        lines.append("-" * 72)

    cs = result["churn_summary"]
    lines.append("")
    lines.append(f"CHURN ROOT-CAUSE TAXONOMY (across all cohorts)")
    lines.append(f"  Total customers churned: {cs['total_churn_customers']}")
    if cs["total_churn_customers"] > 0:
        lines.append(f"  Preventable (CS-controllable): {cs['preventable_pct']}%")
        lines.append("")
        lines.append("  Top drivers:")
        for d in cs["top_drivers"]:
            lines.append(f"    {d['category']:<20} {d['count']:>3} ({d['pct']}%)  — {d['description']}")
    lines.append("")
    lines.append("-" * 72)
    lines.append("HONEST READ: NRR is the vanity metric; GRR is the truth metric. If GRR < 85% and NRR > 100%,")
    lines.append("you have a leaky bucket masked by upsells. Fix retention before scaling acquisition.")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Decompose retention honestly (GRR vs NRR) and categorize churn root causes.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("path", nargs="?", help="Path to cohorts JSON (uses embedded sample if omitted)")
    parser.add_argument("--output", choices=("text", "json"), default="text", help="Output format")
    args = parser.parse_args()

    if args.path:
        try:
            with open(args.path, "r", encoding="utf-8") as f:
                payload = json.load(f)
            source = args.path
        except (IOError, OSError) as e:
            print(f"error: could not read {args.path}: {e}", file=sys.stderr)
            return 1
        except json.JSONDecodeError as e:
            print(f"error: invalid JSON in {args.path}: {e}", file=sys.stderr)
            return 1
    else:
        payload = SAMPLE
        source = "<embedded sample: 2 quarterly B2B SaaS cohorts>"

    result = analyze(payload)

    if args.output == "json":
        print(json.dumps({"source": source, **result}, indent=2))
    else:
        print(render_text(result, source))

    return 0


if __name__ == "__main__":
    sys.exit(main())
