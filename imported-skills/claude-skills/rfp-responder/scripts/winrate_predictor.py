#!/usr/bin/env python3
"""winrate_predictor.py - Shipley-derived winrate estimate + bid/no-bid verdict.

Stdlib only. Deterministic factor model.

Inputs (JSON):
  {
    "requirement_fit_pct_strong": 60.0,     # % of requirements matched at STRONG
    "requirement_fit_pct_partial": 30.0,    # % at PARTIAL
    "requirement_fit_pct_gap":     10.0,    # % at GAP
    "incumbent_advantage": "none|weak|strong",
    "relationship_strength": "cold|warm|champion",
    "decision_criteria_alignment_pct": 75.0,
    "late_entry": true|false,                # entered after RFP issued, no prior engagement
    "competitor_count": 3,
    "deal_size_vs_avg": "below|at|above"
  }

Factor model (Shipley-derived, opinionated, industry-tunable):

  base = 0.03 * fit_strong - 0.02 * fit_gap + 0.005 * fit_partial
        (STRONG counts 3x, PARTIAL 1x, GAP -2x in Shipley capture math;
         encoded here as a linear bounded score centered to produce a
         baseline win-rate in the 5-80% range)

  Incumbent penalty:
    none   ->  0
    weak   -> -10
    strong -> -30

  Relationship lift:
    cold      ->   0
    warm      ->  +10
    champion  ->  +25

  Late entry: -15 if true, 0 otherwise

  Decision-criteria alignment:
    pct >= 80 -> +10
    50 <= pct < 80 -> 0
    pct < 50 -> -10

  Competitor count:
    1 (you're sole vendor)         -> +20
    2                              -> +5
    3                              ->  0
    4-5                            -> -10
    6+                             -> -20

  Deal size vs avg:
    at      ->  0
    above   -> -5   (bigger deals attract more scrutiny + more competitors)
    below   ->  0

Industry profile shifts the base rate (the structural reality that government RFPs
are harder than enterprise software):
    enterprise-software: base_shift = +5
    saas:                base_shift = 0
    services:            base_shift = -5
    government:          base_shift = -15
    healthcare:          base_shift = -10

Verdict:
    < 20%   -> NO-BID
    20-34%  -> PARTNER-BID (find a partner who closes the structural gap)
    35-100% -> BID

Confidence band: +/- 12 percentage points (wider on small-sample factor inputs).

Usage:
    python winrate_predictor.py --sample
    python winrate_predictor.py --input deal.json --profile enterprise-software
    python winrate_predictor.py --input deal.json --profile government --output json
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any


PROFILES: dict[str, dict[str, float]] = {
    "enterprise-software": {"base_shift": 5.0},
    "saas":                {"base_shift": 0.0},
    "services":            {"base_shift": -5.0},
    "government":          {"base_shift": -15.0},
    "healthcare":          {"base_shift": -10.0},
}


SAMPLE_INPUT = {
    "requirement_fit_pct_strong": 60.0,
    "requirement_fit_pct_partial": 25.0,
    "requirement_fit_pct_gap": 15.0,
    "incumbent_advantage": "weak",
    "relationship_strength": "warm",
    "decision_criteria_alignment_pct": 75.0,
    "late_entry": False,
    "competitor_count": 3,
    "deal_size_vs_avg": "at",
}


def incumbent_factor(level: str) -> float:
    return {"none": 0.0, "weak": -10.0, "strong": -30.0}.get(level, 0.0)


def relationship_factor(level: str) -> float:
    return {"cold": 0.0, "warm": 10.0, "champion": 25.0}.get(level, 0.0)


def alignment_factor(pct: float) -> float:
    if pct >= 80.0:
        return 10.0
    if pct < 50.0:
        return -10.0
    return 0.0


def competitor_factor(count: int) -> float:
    if count <= 1:
        return 20.0
    if count == 2:
        return 5.0
    if count == 3:
        return 0.0
    if count <= 5:
        return -10.0
    return -20.0


def deal_size_factor(size: str) -> float:
    return {"at": 0.0, "above": -5.0, "below": 0.0}.get(size, 0.0)


def base_from_fit(strong: float, partial: float, gap: float) -> float:
    """STRONG 3x, PARTIAL 1x, GAP -2x; calibrated to land in 5-80% range at extremes."""
    raw = 0.03 * strong * 3.0 + 0.01 * partial - 0.02 * gap * 2.0
    # Center to a sensible baseline. raw of 9 = 100% strong -> ~45 baseline.
    return max(0.0, min(80.0, raw * 5.0))


def predict(payload: dict[str, Any], profile: str) -> dict[str, Any]:
    prof = PROFILES.get(profile, PROFILES["saas"])
    strong = float(payload.get("requirement_fit_pct_strong", 0.0))
    partial = float(payload.get("requirement_fit_pct_partial", 0.0))
    gap = float(payload.get("requirement_fit_pct_gap", 0.0))

    base = base_from_fit(strong, partial, gap)
    inc = incumbent_factor(payload.get("incumbent_advantage", "none"))
    rel = relationship_factor(payload.get("relationship_strength", "cold"))
    late = -15.0 if payload.get("late_entry", False) else 0.0
    align = alignment_factor(float(payload.get("decision_criteria_alignment_pct", 50.0)))
    comp = competitor_factor(int(payload.get("competitor_count", 3)))
    size = deal_size_factor(payload.get("deal_size_vs_avg", "at"))

    estimate = base + inc + rel + late + align + comp + size + prof["base_shift"]
    estimate = max(0.0, min(100.0, estimate))

    band_lo = max(0.0, estimate - 12.0)
    band_hi = min(100.0, estimate + 12.0)

    if estimate < 20.0:
        verdict = "NO-BID"
        rationale = ("Estimated winrate below the 20% no-bid threshold. "
                     "Pursuing this RFP burns sales-engineering capacity without "
                     "a credible path to win.")
    elif estimate < 35.0:
        verdict = "PARTNER-BID"
        rationale = ("Estimate in the 20-34% band. Bid only with a partner who closes "
                     "the structural gap (incumbent, late-entry, MANDATORY-GAP, or "
                     "regulatory-fit deficit). Solo bid not recommended.")
    else:
        verdict = "BID"
        rationale = ("Estimate above 35%. Pursue with full Shipley capture discipline: "
                     "win-themes laddered across requirements, MANDATORY GAPs closed pre-submission, "
                     "proof-points sourced, executive sponsor named.")

    return {
        "profile": profile,
        "winrate_estimate_pct": round(estimate, 1),
        "confidence_band_pct": [round(band_lo, 1), round(band_hi, 1)],
        "verdict": verdict,
        "rationale": rationale,
        "factor_breakdown": {
            "base_from_fit": round(base, 1),
            "incumbent_advantage": round(inc, 1),
            "relationship_strength": round(rel, 1),
            "late_entry": round(late, 1),
            "decision_criteria_alignment": round(align, 1),
            "competitor_count": round(comp, 1),
            "deal_size_vs_avg": round(size, 1),
            "industry_profile_shift": round(prof["base_shift"], 1),
        },
    }


def render_markdown(result: dict[str, Any]) -> str:
    out: list[str] = []
    out.append("# Shipley-Derived Winrate Estimate\n")
    out.append(f"**Profile:** {result['profile']}")
    band = result["confidence_band_pct"]
    out.append(f"**Estimate:** {result['winrate_estimate_pct']}% (band: {band[0]}% – {band[1]}%)")
    out.append(f"**Verdict:** **{result['verdict']}**\n")
    out.append(f"> {result['rationale']}\n")
    out.append("## Factor breakdown\n")
    out.append("| Factor | Contribution (pp) |")
    out.append("|---|---|")
    for k, v in result["factor_breakdown"].items():
        sign = "+" if v >= 0 else ""
        out.append(f"| {k} | {sign}{v} |")
    out.append("")
    out.append("## Reading the estimate\n")
    out.append("- Estimate is **directional**, not an oracle. Treat the band as the honest range.")
    out.append("- A high score does NOT override a MANDATORY GAP — close the gap or no-bid.")
    out.append("- A low score with a champion + named executive sponsor can be reconsidered, "
               "but document the rationale before committing pursuit budget.")
    return "\n".join(out) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Shipley-derived winrate estimate + bid/no-bid verdict."
    )
    parser.add_argument("--input", help="Path to deal-context JSON.")
    parser.add_argument("--profile", choices=list(PROFILES.keys()), default="saas",
                        help="Industry profile (default: saas).")
    parser.add_argument("--output", choices=["json", "markdown"], default="markdown")
    parser.add_argument("--sample", action="store_true", help="Use built-in synthetic input.")
    args = parser.parse_args(argv)

    if args.sample:
        payload = SAMPLE_INPUT
    elif args.input:
        path = Path(args.input)
        if not path.exists():
            print(f"ERROR: input file not found: {args.input}", file=sys.stderr)
            return 1
        payload = json.loads(path.read_text(encoding="utf-8"))
    else:
        parser.print_help()
        return 0

    result = predict(payload, args.profile)
    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_markdown(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
