#!/usr/bin/env python3
"""sub_use_case_router.py — Deterministic search-strategy from intake answers.

Stdlib-only. Routes to one of 5 patent search strategies based on grill-me
intake answers, returning a query plan + ranking heuristic + DOCX emphasis.

The 5 sub-use-cases:
  - novelty       — am I novel enough to file
  - fto           — will I get sued if I ship
  - landscape     — who else plays here
  - diligence     — does target really own X
  - litigation    — kill a specific patent

Each gets a fundamentally different search strategy, ranking heuristic, and
DOCX emphasis (which sections expand vs abbreviate).

NO LLM CALLS. Pure rule-based routing.

Usage:
    python sub_use_case_router.py --sub-use-case novelty --jurisdictions "" --risk strict --known-art "US10000000B2"
    python sub_use_case_router.py --sub-use-case fto --jurisdictions "US,EP" --risk strict
    python sub_use_case_router.py --sample
"""

import argparse
import json
import sys
from typing import Any, Dict, List, Optional


VALID_SUB_USE_CASES = ["novelty", "fto", "landscape", "diligence", "litigation"]
VALID_RISK = ["strict", "signal-gathering"]


# Strategy templates per sub-use-case
STRATEGIES = {
    "novelty": {
        "query_count": 6,
        "sources": ["google_patents", "espacenet"],
        "filters": {"date_filter": "any", "active_only": False},
        "queries": [
            {"type": "narrow_keyword", "count": 3, "source": "google_patents"},
            {"type": "broad_concept", "count": 2, "source": "google_patents+espacenet"},
            {"type": "cpc_class", "count": 1, "source": "google_patents", "after_initial": True},
        ],
        "ranking_heuristic": "claim_text_overlap_with_invention_description",
        "verdict_scale": ["NOVEL", "POTENTIALLY NOVEL", "NOT NOVEL"],
        "docx_emphasis": {
            "executive_summary": "expanded",
            "closest_prior_art": "expanded",
            "patent_landscape": "abbreviated",
            "citation_graph_signals": "if_lens_only",
            "geographic_coverage": "abbreviated",
            "fto_flags": "skip",
            "strategy_recommendations": "claim_differentiation_focus",
            "audit_log": "standard",
        },
        "legal_disclaimer_mandatory": True,
    },
    "fto": {
        "query_count": 12,  # scales with jurisdiction count
        "sources": ["google_patents", "espacenet", "uspto"],
        "filters": {"date_filter": "priority_lt_today", "active_only": True, "jurisdiction_filtered": True},
        "queries": [
            {"type": "jurisdiction_filtered", "count": "2-3 per jurisdiction"},
            {"type": "active_status_filter", "applied_to_all": True},
            {"type": "cpc_class", "count": 1, "after_initial": True},
        ],
        "ranking_heuristic": "claim_by_claim_infringement_risk",
        "verdict_scale": ["CLEAR (per jurisdiction)", "FLAGGED", "HIGH RISK"],
        "docx_emphasis": {
            "executive_summary": "expanded",
            "closest_prior_art": "abbreviated",
            "patent_landscape": "abbreviated",
            "citation_graph_signals": "if_lens_only",
            "geographic_coverage": "expanded",
            "fto_flags": "expanded_main_section",
            "strategy_recommendations": "design_around_jurisdiction_focus",
            "audit_log": "standard",
        },
        "legal_disclaimer_mandatory": True,
    },
    "landscape": {
        "query_count": 9,
        "sources": ["google_patents", "espacenet", "lens"],
        "filters": {"date_filter": "10_year_window"},
        "queries": [
            {"type": "broad_technology", "count": "2-3"},
            {"type": "cpc_class_extraction", "count": 1, "after_initial": True},
            {"type": "per_top_filer", "count": "1 per top-5 filer"},
            {"type": "lens_citation_graph", "count": "if_byok_available"},
        ],
        "ranking_heuristic": "filer_count_plus_recency",
        "verdict_scale": ["CONCENTRATED", "COMPETITIVE", "EMERGING"],
        "docx_emphasis": {
            "executive_summary": "standard",
            "closest_prior_art": "abbreviated",
            "patent_landscape": "expanded_main_section",
            "citation_graph_signals": "expanded_if_lens",
            "geographic_coverage": "expanded",
            "fto_flags": "skip",
            "strategy_recommendations": "who_to_watch_focus",
            "audit_log": "standard",
        },
        "legal_disclaimer_mandatory": False,
    },
    "diligence": {
        "query_count": 10,
        "sources": ["google_patents", "uspto"],
        "filters": {"date_filter": "any", "assignee_focused": True},
        "queries": [
            {"type": "assignee_search", "count": "2-3"},
            {"type": "subsidiary_search", "count": "if_org_chart_provided"},
            {"type": "inventor_search", "count": "for_key_inventors"},
            {"type": "assignment_recordation", "count": "for_ownership_verification"},
            {"type": "family_resolution", "applied_to_all": True},
        ],
        "ranking_heuristic": "family_grouped_then_citation_count",
        "verdict_scale": ["PORTFOLIO VERIFIED", "PARTIAL VERIFICATION", "OWNERSHIP RISK"],
        "docx_emphasis": {
            "executive_summary": "expanded",
            "closest_prior_art": "abbreviated",
            "patent_landscape": "expanded_as_portfolio_table",
            "citation_graph_signals": "if_lens_only",
            "geographic_coverage": "expanded",
            "fto_flags": "skip",
            "strategy_recommendations": "red_flags_in_portfolio",
            "audit_log": "standard",
        },
        "legal_disclaimer_mandatory": False,
    },
    "litigation": {
        "query_count": 7,
        "sources": ["google_patents", "espacenet", "lens"],
        "filters": {"date_filter": "before_target_priority_date"},
        "queries": [
            {"type": "fetch_target_patent", "extract": ["priority_date", "claims", "cpc_classes"]},
            {"type": "cpc_class_with_date_filter", "count": 2},
            {"type": "claim_language_with_date_filter", "count": 2},
            {"type": "lens_forward_citations", "count": "if_byok_available"},
        ],
        "ranking_heuristic": "knock_out_potential_claim_by_claim",
        "verdict_scale": ["KNOCK-OUT FOUND", "STRONG OBVIOUSNESS COMBINATION", "WEAK OBVIOUSNESS", "NO MATERIAL ART"],
        "docx_emphasis": {
            "executive_summary": "expanded",
            "closest_prior_art": "expanded_as_knock_out_candidates",
            "patent_landscape": "abbreviated",
            "citation_graph_signals": "expanded_if_lens",
            "geographic_coverage": "abbreviated",
            "fto_flags": "skip",
            "strategy_recommendations": "per_claim_invalidity_analysis",
            "audit_log": "standard",
        },
        "legal_disclaimer_mandatory": False,
    },
}


def route(sub_use_case: str, jurisdictions: List[str], risk: Optional[str], known_art: Optional[str]) -> Dict[str, Any]:
    if sub_use_case not in STRATEGIES:
        raise ValueError(f"Invalid sub-use-case '{sub_use_case}'. Pick from: {list(STRATEGIES.keys())}")
    strategy = STRATEGIES[sub_use_case].copy()
    strategy["sub_use_case"] = sub_use_case
    strategy["jurisdictions_input"] = jurisdictions
    strategy["risk_input"] = risk
    strategy["known_art_input"] = known_art

    notes: List[str] = []

    # FTO scales query count with jurisdictions
    if sub_use_case == "fto" and jurisdictions:
        per_jurisdiction = 3
        strategy["query_count"] = len(jurisdictions) * per_jurisdiction + 2  # + CPC + active filter
        notes.append(f"FTO query count scaled to {strategy['query_count']} for {len(jurisdictions)} jurisdiction(s)")

    # Risk modifies ranking
    if risk == "strict":
        notes.append("Strict risk: aggressive ranking; surface verdict-grade hits only")
    elif risk == "signal-gathering":
        notes.append("Signal-gathering risk: prioritize breadth + visualization over verdict")

    # Known art enables anchored search
    if known_art and known_art.lower() != "none":
        notes.append(f"Known art anchor: {known_art} — adjacent searches will reference this hit")

    # Lens.org availability check (not asked here; flag in audit only)
    notes.append("Lens.org BYOK: required for Citation Graph section. Check at runtime.")

    if strategy["legal_disclaimer_mandatory"]:
        notes.append("LEGAL DISCLAIMER MANDATORY: include in DOCX Sections 1, 7, 8")

    strategy["operational_notes"] = notes
    return strategy


def render_human(result: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"Sub-use-case:               {result['sub_use_case']}")
    out.append(f"Jurisdictions:              {result.get('jurisdictions_input', []) or '(N/A for this sub-use-case)'}")
    out.append(f"Risk tolerance:             {result.get('risk_input', '(not specified)')}")
    out.append(f"Known art:                  {result.get('known_art_input', '(none)')}")
    out.append("")
    out.append(f"Total query count:          {result['query_count']}")
    out.append(f"Sources:                    {', '.join(result['sources'])}")
    out.append(f"Filters:                    {result['filters']}")
    out.append("")
    out.append("Query plan:")
    for q in result["queries"]:
        out.append(f"  - {q}")
    out.append("")
    out.append(f"Ranking heuristic:          {result['ranking_heuristic']}")
    out.append(f"Verdict scale:              {' / '.join(result['verdict_scale'])}")
    out.append(f"Legal disclaimer mandatory: {result['legal_disclaimer_mandatory']}")
    out.append("")
    out.append("DOCX section emphasis:")
    for section, emphasis in result["docx_emphasis"].items():
        out.append(f"  {section:<30s} {emphasis}")
    out.append("")
    if result.get("operational_notes"):
        out.append("Operational notes:")
        for n in result["operational_notes"]:
            out.append(f"  - {n}")
    return "\n".join(out)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--sub-use-case", choices=VALID_SUB_USE_CASES)
    parser.add_argument("--jurisdictions", help="Comma-separated jurisdiction codes (US,EP,CN,JP,KR,PCT,worldwide)")
    parser.add_argument("--risk", choices=VALID_RISK)
    parser.add_argument("--known-art", help="Patent number or paper citation if user has seen prior art")
    parser.add_argument("--sample", action="store_true", help="Run sample (FTO with US+EP jurisdictions, strict risk)")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if args.sample:
        result = route("fto", ["US", "EP"], "strict", "US10000000B2")
    elif args.sub_use_case:
        jurisdictions = [j.strip() for j in args.jurisdictions.split(",") if j.strip()] if args.jurisdictions else []
        try:
            result = route(args.sub_use_case, jurisdictions, args.risk, args.known_art)
        except ValueError as e:
            print(f"error: {e}", file=sys.stderr); return 2
    else:
        parser.print_help(); return 0

    if args.output == "json":
        print(json.dumps(result, indent=2, default=str))
    else:
        print(render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
