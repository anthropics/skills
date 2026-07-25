#!/usr/bin/env python3
"""mechanism_matcher.py — NIH mechanism shortlist from career stage + scope + prelim.

Stdlib-only. The skill must NOT recommend mechanisms by career stage alone —
that's the most common mistake. Matching is 3-dimensional:

  (career_stage, project_scope, preliminary_data, environment) → mechanism shortlist

See references/nih_mechanism_matching.md for the full matrix.

NO LLM CALLS. Pure rule-based lookup.

Usage:
    python mechanism_matcher.py --career-stage early_career --prelim-data pilot \\
      --environment r01_eligible --scope single_site
    python mechanism_matcher.py --sample
"""

import argparse
import json
import sys
from typing import Any, Dict, List


VALID_CAREER_STAGES = ["pre_doctoral", "postdoctoral", "early_career", "independent", "senior"]
VALID_PRELIM = ["none", "pilot", "strong", "validated"]
VALID_ENVIRONMENTS = ["r01_eligible", "mid_tier", "resource_constrained", "industry_collab"]
VALID_SCOPES = ["solo_pilot", "single_site", "multi_aim", "multi_site", "program_scale", "high_risk"]


MECHANISMS = {
    "F31": {"budget": "$40-50k stipend + tuition × 2-3 yr", "prelim": "None-pilot", "best_for": "Pre-doc training"},
    "F32": {"budget": "$48-58k stipend × 2-3 yr", "prelim": "None-pilot", "best_for": "Postdoc training"},
    "T32": {"budget": "Institutional × 5-yr renewable", "prelim": "Institutional", "best_for": "Pre-doc/postdoc cohort"},
    "R03": {"budget": "$50k × 2 yr", "prelim": "None-pilot", "best_for": "Small pilot studies"},
    "R21": {"budget": "$275k DC × 2 yr", "prelim": "None-pilot", "best_for": "Pilot/exploratory R&D"},
    "R34": {"budget": "$450k × 3 yr", "prelim": "Pilot", "best_for": "Clinical trial planning"},
    "R61/R33": {"budget": "Phased ($250k + $500k × 2 yr)", "prelim": "Pilot", "best_for": "Phased innovation"},
    "K01": {"budget": "$100k × 5 yr", "prelim": "Pilot", "best_for": "Mentored research scientist"},
    "K08": {"budget": "$100k × 5 yr", "prelim": "Pilot", "best_for": "Mentored clinical scientist"},
    "K23": {"budget": "$100k × 5 yr", "prelim": "Pilot", "best_for": "Mentored patient-oriented research"},
    "K99/R00": {"budget": "$90k + $250k × 3 yr", "prelim": "Strong", "best_for": "Postdoc → independence transition"},
    "R01": {"budget": "$250-499k DC × 4-5 yr", "prelim": "Strong", "best_for": "Hypothesis-driven research"},
    "R15": {"budget": "$300k total × 3 yr", "prelim": "Pilot", "best_for": "Resource-constrained institutions only"},
    "R35": {"budget": "$750k × 5-8 yr", "prelim": "Validated", "best_for": "Senior outstanding investigators"},
    "P01": {"budget": "Multi-PI, $1-2M/yr × 5 yr", "prelim": "Validated", "best_for": "Program project (3+ PIs)"},
    "P30": {"budget": "Core facility funding × 5 yr", "prelim": "Validated", "best_for": "Multi-investigator core"},
    "U01": {"budget": "Cooperative agreement, varies", "prelim": "Strong-validated", "best_for": "Multi-site collaborative"},
    "DP1": {"budget": "$700k × 5 yr", "prelim": "None (visionary)", "best_for": "Pioneer Award — high-risk individual"},
    "DP2": {"budget": "$300k × 5 yr", "prelim": "Pilot", "best_for": "New Innovator — early-career high-risk"},
}


def match(career_stage: str, prelim_data: str, environment: str, scope: str) -> Dict[str, Any]:
    if career_stage not in VALID_CAREER_STAGES:
        raise ValueError(f"Invalid --career-stage. Pick from: {VALID_CAREER_STAGES}")
    if prelim_data not in VALID_PRELIM:
        raise ValueError(f"Invalid --prelim-data. Pick from: {VALID_PRELIM}")
    if environment not in VALID_ENVIRONMENTS:
        raise ValueError(f"Invalid --environment. Pick from: {VALID_ENVIRONMENTS}")
    if scope not in VALID_SCOPES:
        raise ValueError(f"Invalid --scope. Pick from: {VALID_SCOPES}")

    recommendations: List[Dict[str, Any]] = []
    warnings: List[str] = []

    # === Pre-doctoral ===
    if career_stage == "pre_doctoral":
        if prelim_data in ("none", "pilot") and scope in ("solo_pilot", "single_site"):
            recommendations.append({"mechanism": "F31", "rationale": "Pre-doc + pilot scope → NRSA individual fellowship"})
            recommendations.append({"mechanism": "T32", "rationale": "Pre-doc + institutional context → T32 training slot if available"})
        else:
            warnings.append("Pre-doctoral PI eligibility is limited. Consider co-investigator role on mentor's grant.")

    # === Postdoctoral ===
    elif career_stage == "postdoctoral":
        if prelim_data == "none":
            recommendations.append({"mechanism": "F32", "rationale": "Postdoc + no prelim → NRSA F32 fellowship"})
        if prelim_data == "pilot":
            recommendations.append({"mechanism": "F32", "rationale": "Postdoc + pilot data → F32"})
            recommendations.append({"mechanism": "K99/R00", "rationale": "Postdoc + pilot → K99/R00 candidate prep (top mechanism)"})
        if prelim_data == "strong":
            recommendations.append({"mechanism": "K99/R00", "rationale": "Strong prelim + postdoc-transitioning → K99/R00 is the highest-value mechanism for this stage"})

    # === Early career ===
    elif career_stage == "early_career":
        if prelim_data in ("none", "pilot"):
            if environment == "resource_constrained":
                recommendations.append({"mechanism": "R15", "rationale": "Resource-constrained env + early career → R15 (specifically targets this; R01 not competitive without env match)"})
            recommendations.append({"mechanism": "K01", "rationale": "Early career + pilot prelim → K-series for career development"})
            recommendations.append({"mechanism": "K08", "rationale": "Early career (clinical) + pilot → K08 mentored clinical"})
            recommendations.append({"mechanism": "K23", "rationale": "Early career patient-oriented → K23"})
            recommendations.append({"mechanism": "R21", "rationale": "Early career + pilot scope → R21 exploratory"})
        if prelim_data == "strong" and scope in ("single_site", "multi_aim"):
            recommendations.append({"mechanism": "R01", "rationale": "Strong prelim + independent scope → R01 (the qualifying R01)"})
            if scope == "multi_aim":
                warnings.append("Multi-aim R01 at early career is ambitious; consider mentored R01 with senior co-PI")
        if scope == "high_risk":
            recommendations.append({"mechanism": "DP2", "rationale": "Early career + high-risk → New Innovator (DP2)"})

    # === Independent ===
    elif career_stage == "independent":
        if prelim_data in ("none", "pilot") and scope == "solo_pilot":
            recommendations.append({"mechanism": "R03", "rationale": "Independent + pilot scope → R03 small pilot"})
            recommendations.append({"mechanism": "R21", "rationale": "Independent + exploratory → R21"})
            warnings.append("R01 NOT recommended without strong prelim — reviewers will reject as premature")
        if prelim_data == "strong":
            if scope == "multi_aim" or scope == "single_site":
                recommendations.append({"mechanism": "R01", "rationale": "Independent + strong prelim + hypothesis-driven → R01 (standard)"})
            if scope == "multi_site":
                recommendations.append({"mechanism": "U01", "rationale": "Multi-site + strong prelim → U01 cooperative agreement"})
        if prelim_data == "validated" and scope == "multi_site":
            recommendations.append({"mechanism": "U01", "rationale": "Validated + multi-site → U01"})
            recommendations.append({"mechanism": "R01", "rationale": "Validated + multi-site → R01 alternate path"})
        if scope == "high_risk":
            recommendations.append({"mechanism": "DP1", "rationale": "High-risk + independent → Pioneer Award"})
        if scope == "single_site" and prelim_data == "pilot":
            recommendations.append({"mechanism": "R34", "rationale": "Clinical trial planning + pilot → R34"})

    # === Senior PI ===
    elif career_stage == "senior":
        if scope == "program_scale":
            recommendations.append({"mechanism": "R35", "rationale": "Senior + program scope → R35 outstanding investigator (unrestricted by topic)"})
            recommendations.append({"mechanism": "P01", "rationale": "Senior + multi-PI program → P01"})
        if scope == "multi_site":
            recommendations.append({"mechanism": "U01", "rationale": "Senior + multi-site → U01"})
        if "core" in scope or scope == "program_scale":
            recommendations.append({"mechanism": "P30", "rationale": "Senior + core facility → P30"})
        if scope in ("multi_aim", "single_site") and prelim_data in ("strong", "validated"):
            recommendations.append({"mechanism": "R01", "rationale": "Senior PI continuing R01 portfolio"})

    if not recommendations:
        warnings.append("No mechanism shortlist matched. Likely inputs are inconsistent (e.g., pre-doctoral + senior-scope). Re-check the answer combinations.")

    # Enrich with mechanism details
    enriched = []
    for rec in recommendations:
        m = rec["mechanism"]
        info = MECHANISMS.get(m, {})
        enriched.append({
            "mechanism": m,
            "rationale": rec["rationale"],
            "budget": info.get("budget", ""),
            "prelim_needed": info.get("prelim", ""),
            "best_for": info.get("best_for", ""),
        })

    return {
        "inputs": {
            "career_stage": career_stage,
            "prelim_data": prelim_data,
            "environment": environment,
            "scope": scope,
        },
        "recommendations": enriched,
        "warnings": warnings,
        "program_officer_note": "MANDATORY: contact program officer at top institute before writing. Find via https://www.nih.gov/institutes-nih/list-nih-institutes-centers-offices",
    }


def render_human(result: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append("Inputs:")
    for k, v in result["inputs"].items():
        out.append(f"  {k}: {v}")
    out.append("")
    if result["recommendations"]:
        out.append(f"Recommended mechanisms ({len(result['recommendations'])}):")
        for r in result["recommendations"]:
            out.append(f"")
            out.append(f"  → {r['mechanism']}")
            out.append(f"    Rationale: {r['rationale']}")
            out.append(f"    Budget:    {r['budget']}")
            out.append(f"    Prelim:    {r['prelim_needed']}")
            out.append(f"    Best for:  {r['best_for']}")
    else:
        out.append("No mechanisms recommended (see warnings)")
    if result["warnings"]:
        out.append("")
        out.append("Warnings:")
        for w in result["warnings"]:
            out.append(f"  ! {w}")
    out.append("")
    out.append(result["program_officer_note"])
    return "\n".join(out)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--career-stage", choices=VALID_CAREER_STAGES)
    parser.add_argument("--prelim-data", choices=VALID_PRELIM)
    parser.add_argument("--environment", choices=VALID_ENVIRONMENTS)
    parser.add_argument("--scope", choices=VALID_SCOPES)
    parser.add_argument("--sample", action="store_true")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if args.sample:
        result = match("early_career", "pilot", "r01_eligible", "single_site")
    elif args.career_stage and args.prelim_data and args.environment and args.scope:
        try:
            result = match(args.career_stage, args.prelim_data, args.environment, args.scope)
        except ValueError as e:
            print(f"error: {e}", file=sys.stderr); return 2
    else:
        parser.print_help(); return 0

    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
