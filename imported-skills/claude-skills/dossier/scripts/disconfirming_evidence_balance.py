#!/usr/bin/env python3
"""disconfirming_evidence_balance.py — Enforce ≥30% disconfirming search budget.

Stdlib-only. The dossier skill's non-negotiable: ≥30% of Phase 4 searches must
be classified as disconfirming (would refute the hypothesis if results favorable).

Reads from a dossier session JSON (created by `citation_tracker.py`) and:
  - Returns PASS if disconfirming_ratio >= 0.30
  - Returns WARN if 0.20 <= ratio < 0.30 (recoverable; surface to user)
  - Returns FAIL if ratio < 0.20 (confirmation bias; halt + remediate)

Outputs suggested disconfirming queries to add (based on antonym-pivot heuristic
from references/hypothesis_testing_discipline.md).

NO LLM CALLS. Pure ratio math + heuristic suggestions.

Usage:
    python disconfirming_evidence_balance.py --session dossier-MS-20260515
    python disconfirming_evidence_balance.py --session ... --output json
    python disconfirming_evidence_balance.py --sample
"""

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional


SESSIONS_DIR = Path.home() / ".dossier_sessions"
MIN_RATIO = 0.30
WARN_RATIO = 0.20


# Antonym-pivot heuristics for constructing disconfirming queries
DISCONFIRMING_PIVOTS = {
    "consolidating": ["diversifying", "splitting", "decentralizing"],
    "growing": ["shrinking", "declining", "stagnating"],
    "winning": ["losing", "failing", "underperforming"],
    "successful": ["failed", "unsuccessful", "struggling"],
    "expanding": ["contracting", "exiting", "retreating from"],
    "strong": ["weak", "missing"],
    "leading": ["trailing", "lagging"],
    "innovating": ["copying", "lagging behind"],
    "investing in": ["divesting", "exiting"],
    "hiring": ["laying off", "departures from"],
}


def suggest_disconfirming_queries(hypothesis: str, supporting_queries: List[str]) -> List[str]:
    """Heuristic: for each supporting term, suggest antonym-pivoted disconfirming."""
    suggestions: List[str] = []
    hyp_lower = hypothesis.lower()
    for pivot, antonyms in DISCONFIRMING_PIVOTS.items():
        if pivot in hyp_lower:
            for antonym in antonyms[:2]:  # first 2 only to avoid noise
                disconfirming = hyp_lower.replace(pivot, antonym)
                suggestions.append(disconfirming)
    if not suggestions:
        # Generic fallback patterns
        suggestions.append(f"counter-evidence to: {hypothesis}")
        suggestions.append(f"critics of {hypothesis}")
        suggestions.append(f"failures contradicting {hypothesis}")
    return suggestions[:5]


def analyze(session_data: Dict[str, Any]) -> Dict[str, Any]:
    c = session_data.get("counts", {})
    total = c.get("searches", 0)
    supporting = c.get("supporting_searches", 0)
    disconfirming = c.get("disconfirming_searches", 0)
    inconclusive = c.get("inconclusive_searches", 0)

    if total == 0:
        return {
            "verdict": "INSUFFICIENT_DATA",
            "ratio": 0.0,
            "total_searches": 0,
            "supporting": 0,
            "disconfirming": 0,
            "inconclusive": 0,
            "rule_floor": MIN_RATIO,
            "message": "No searches recorded yet. Run Phase 4 first.",
            "remediation_needed": False,
        }

    ratio = disconfirming / total
    needed_disconfirming = max(0, int((MIN_RATIO * total) - disconfirming + 0.999))  # ceiling

    if ratio >= MIN_RATIO:
        verdict = "PASS"
        message = f"Disconfirming ratio {ratio:.0%} meets ≥{MIN_RATIO:.0%} floor. Decision-grade balance OK."
        remediation_needed = False
        suggested = []
    elif ratio >= WARN_RATIO:
        verdict = "WARN"
        message = (
            f"Disconfirming ratio {ratio:.0%} is below ≥{MIN_RATIO:.0%} floor "
            f"but above {WARN_RATIO:.0%} threshold. Recoverable — add {needed_disconfirming} "
            f"disconfirming queries to reach floor."
        )
        remediation_needed = True
        suggested = suggest_disconfirming_queries(
            session_data.get("hypothesis", ""),
            [s["query"] for s in session_data.get("searches", []) if s.get("classification") == "supporting"]
        )
    else:
        verdict = "FAIL"
        message = (
            f"Disconfirming ratio {ratio:.0%} below {WARN_RATIO:.0%} — confirmation bias risk is real. "
            f"HALT + add {needed_disconfirming} disconfirming queries before generating DOCX. "
            f"A SUPPORTED verdict at this ratio is not credible."
        )
        remediation_needed = True
        suggested = suggest_disconfirming_queries(
            session_data.get("hypothesis", ""),
            [s["query"] for s in session_data.get("searches", []) if s.get("classification") == "supporting"]
        )

    return {
        "verdict": verdict,
        "ratio": ratio,
        "rule_floor": MIN_RATIO,
        "total_searches": total,
        "supporting": supporting,
        "disconfirming": disconfirming,
        "inconclusive": inconclusive,
        "disconfirming_needed_to_reach_floor": needed_disconfirming,
        "message": message,
        "remediation_needed": remediation_needed,
        "suggested_disconfirming_queries": suggested,
    }


SAMPLE_SESSION = {
    "session": "sample-dossier",
    "subject": "Microsoft",
    "hypothesis": "Microsoft is consolidating AI spend on Foundry platform",
    "counts": {
        "searches": 10,
        "supporting_searches": 8,
        "disconfirming_searches": 2,
        "inconclusive_searches": 0,
    },
    "searches": [
        {"query": "Microsoft Foundry adoption 2026", "classification": "supporting"},
        {"query": "Microsoft AI consolidation strategy", "classification": "supporting"},
    ],
}


def render_human(result: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"Disconfirming evidence balance: {result['verdict']}")
    out.append(f"  Total searches:                  {result['total_searches']}")
    out.append(f"  Supporting:                      {result['supporting']}")
    out.append(f"  Disconfirming:                   {result['disconfirming']}")
    out.append(f"  Inconclusive:                    {result['inconclusive']}")
    out.append(f"  Ratio (disconfirming/total):     {result['ratio']:.0%}")
    out.append(f"  Rule floor:                      {result['rule_floor']:.0%}")
    if result.get('disconfirming_needed_to_reach_floor', 0) > 0:
        out.append(f"  Disconfirming queries to add:    {result['disconfirming_needed_to_reach_floor']}")
    out.append("")
    out.append(result["message"])
    if result.get("suggested_disconfirming_queries"):
        out.append("")
        out.append("Suggested disconfirming queries (antonym-pivot from hypothesis):")
        for q in result["suggested_disconfirming_queries"]:
            out.append(f"  - {q}")
    return "\n".join(out)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--session", help="Session name (in ~/.dossier_sessions/)")
    parser.add_argument("--sample", action="store_true", help="Analyze embedded sample data (10 searches, 80% supporting)")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if args.sample:
        data = SAMPLE_SESSION
    elif args.session:
        p = SESSIONS_DIR / f"{args.session}.json"
        if not p.exists():
            print(f"error: session not found at {p}", file=sys.stderr); return 2
        try:
            data = json.loads(p.read_text(encoding="utf-8"))
        except json.JSONDecodeError as e:
            print(f"error: invalid session JSON: {e}", file=sys.stderr); return 2
    else:
        parser.print_help(); return 0

    result = analyze(data)
    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_human(result))

    if result["verdict"] == "FAIL":
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
