#!/usr/bin/env python3
"""framework_recommender.py — Heuristic PICO/SPIDER/Decomposition picker.

Stdlib-only. Given a research question, suggests which literature-review
framework to use, with confidence + rationale + starter sub-area questions.

Heuristic keyword signals:
  - "compared to", "vs", "versus", "better than" → PICO (Comparison signal)
  - "intervention", "treatment", "drug", "therapy" → PICO (Intervention)
  - "experience", "perception", "lived", "meaning" → SPIDER (Phenomenon)
  - "qualitative", "interview", "ethnography" → SPIDER (Design)
  - "system", "model", "algorithm", "architecture" → Decomposition (Solution)
  - "benchmark", "evaluation", "metric" → Decomposition (Evaluation)
  - Multiple signals across frameworks → Hybrid
  - No strong signal → PICO (default)

NO LLM CALLS. Pure regex + keyword counting.

Usage:
    python framework_recommender.py --question "How do LLMs perform on clinical reasoning compared to physicians?"
    python framework_recommender.py --question "..." --output json
    python framework_recommender.py --sample
"""

import argparse
import json
import re
import sys
from typing import Any, Dict, List


PICO_SIGNALS = {
    "comparison": ["compared to", "vs", "versus", "better than", "compared with", "relative to"],
    "intervention": ["intervention", "treatment", "drug", "therapy", "drug therapy", "regimen"],
    "outcome": ["outcome", "efficacy", "effectiveness", "accuracy", "mortality", "survival"],
    "population": ["patients", "subjects", "cohort", "participants"],
}

SPIDER_SIGNALS = {
    "phenomenon": ["experience", "perception", "meaning", "lived", "narrative", "perspective"],
    "design": ["qualitative", "interview", "ethnography", "phenomenology", "grounded theory"],
    "sample": ["women's", "men's", "clinicians", "students", "patients with"],  # demographic-context
    "evaluation": ["thematic", "narrative analysis", "lived experience"],
}

DECOMPOSITION_SIGNALS = {
    "solution": ["system", "model", "algorithm", "architecture", "method", "approach", "framework"],
    "evaluation": ["benchmark", "evaluation", "metric", "performance", "accuracy"],
    "problem": ["challenge", "problem", "issue with", "limitations of"],
    "limitations": ["limitations", "failure mode", "edge case", "robustness"],
}


def count_signals(text: str, signal_map: Dict[str, List[str]]) -> Dict[str, int]:
    text_lower = text.lower()
    counts: Dict[str, int] = {}
    for component, phrases in signal_map.items():
        component_count = 0
        for phrase in phrases:
            # Allow optional plural 's' / 'ed' / 'ing' suffix for single-word phrases (not multi-word)
            if " " in phrase:
                pattern = re.compile(rf"\b{re.escape(phrase)}\b", re.IGNORECASE)
            else:
                pattern = re.compile(rf"\b{re.escape(phrase)}(?:s|es|ed|ing)?\b", re.IGNORECASE)
            component_count += len(pattern.findall(text_lower))
        counts[component] = component_count
    return counts


def recommend(question: str) -> Dict[str, Any]:
    pico = count_signals(question, PICO_SIGNALS)
    spider = count_signals(question, SPIDER_SIGNALS)
    decomp = count_signals(question, DECOMPOSITION_SIGNALS)

    pico_total = sum(pico.values())
    spider_total = sum(spider.values())
    decomp_total = sum(decomp.values())

    total = pico_total + spider_total + decomp_total

    # Confidence: ratio of dominant framework to total
    if total == 0:
        framework = "PICO"
        confidence = "low"
        rationale = "No strong framework signals detected — defaulting to PICO (covers ~70% of questions)"
    elif pico_total >= 2 and spider_total >= 2:
        framework = "Hybrid (PICO + SPIDER)"
        confidence = "medium"
        rationale = f"Both PICO ({pico_total} signals) and SPIDER ({spider_total}) detected — question spans quantitative + qualitative"
    elif pico_total >= 2 and decomp_total >= 2:
        framework = "Hybrid (PICO + Decomposition)"
        confidence = "medium"
        rationale = f"Both PICO ({pico_total}) and Decomposition ({decomp_total}) — clinical + technology evaluation"
    elif decomp_total > pico_total and decomp_total > spider_total:
        framework = "Decomposition"
        confidence = "high" if decomp_total >= 3 else "medium"
        active = [k for k, v in decomp.items() if v > 0]
        rationale = f"Decomposition signals dominate ({decomp_total} total, components: {', '.join(active)})"
    elif spider_total > pico_total and spider_total > decomp_total:
        framework = "SPIDER"
        confidence = "high" if spider_total >= 3 else "medium"
        active = [k for k, v in spider.items() if v > 0]
        rationale = f"SPIDER signals dominate ({spider_total} total, components: {', '.join(active)})"
    else:
        framework = "PICO"
        confidence = "high" if pico_total >= 3 else "medium" if pico_total >= 1 else "low"
        active = [k for k, v in pico.items() if v > 0]
        rationale = f"PICO signals dominate ({pico_total} total, components: {', '.join(active) if active else 'default'})"

    # Sub-area starter questions (template — actual generation needs LLM context)
    starter_questions = generate_starter_questions(question, framework)

    return {
        "question": question,
        "framework": framework,
        "confidence": confidence,
        "rationale": rationale,
        "signal_counts": {"PICO": pico, "SPIDER": spider, "Decomposition": decomp},
        "starter_sub_areas": starter_questions,
    }


def generate_starter_questions(question: str, framework: str) -> List[str]:
    """Template-driven sub-area starter questions per framework."""
    if framework.startswith("PICO") or "PICO" in framework:
        return [
            "Population: who is being studied? (define inclusion + exclusion)",
            "Intervention: what is being tested? (specify dose / variant / version)",
            "Comparison: against what baseline? (placebo / standard / alternative)",
            "Outcome: what is being measured? (primary + secondary endpoints)",
            "Cross-cutting: methodological quality or population variation",
        ]
    elif framework.startswith("SPIDER") or "SPIDER" in framework:
        return [
            "Sample: who has the experience? (define context)",
            "Phenomenon: what experience or perception? (be specific)",
            "Design: what qualitative methods? (interviews / observation / artifacts)",
            "Evaluation: what kind of analysis? (thematic / narrative / phenomenological)",
            "Cross-cutting: cultural or temporal variation in the phenomenon",
        ]
    elif framework.startswith("Decomposition"):
        return [
            "Problem: what challenge is being addressed? (constraints + objectives)",
            "Solution: what is the proposed approach? (architecture + key innovation)",
            "Evaluation: how is it being measured? (benchmarks + metrics + baselines)",
            "Limitations: where does it fail? (edge cases + failure modes)",
            "Cross-cutting: scalability or deployment considerations",
        ]
    else:  # Hybrid
        return [
            "Primary framework components (from dominant signals)",
            "Secondary framework components (from cross-cutting signals)",
            "Comparison or evaluation dimension",
            "Outcome or impact dimension",
            "Cross-cutting: methodological consistency across paradigms",
        ]


def render_human(result: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"Question:        {result['question']}")
    out.append("")
    out.append(f"Recommended:     {result['framework']}")
    out.append(f"Confidence:      {result['confidence']}")
    out.append(f"Rationale:       {result['rationale']}")
    out.append("")
    out.append("Signal counts:")
    for fw, components in result["signal_counts"].items():
        total = sum(components.values())
        active = ", ".join(f"{k}={v}" for k, v in components.items() if v > 0) or "(none)"
        out.append(f"  {fw:<18s} total={total}  ({active})")
    out.append("")
    out.append("Starter sub-area questions:")
    for q in result["starter_sub_areas"]:
        out.append(f"  - {q}")
    return "\n".join(out)


SAMPLE_QUESTION = "How do large language models perform on clinical reasoning tasks compared to physicians?"


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--question", help="Research question text")
    parser.add_argument("--sample", action="store_true", help="Run on embedded sample question")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if args.sample:
        result = recommend(SAMPLE_QUESTION)
    elif args.question:
        result = recommend(args.question)
    else:
        parser.print_help(); return 0

    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
