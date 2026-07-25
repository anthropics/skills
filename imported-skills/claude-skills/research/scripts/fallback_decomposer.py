#!/usr/bin/env python3
"""
fallback_decomposer.py — Heuristic question decomposer for the fallback workflow.

Given a research question, returns 3-5 sub-questions using the
what / why / how / who / what's next framework. Deterministic + stdlib only.

The output is a starting point; the orchestrator + user should refine before
search budget is committed.

Usage:
  python fallback_decomposer.py --question "How are health systems integrating LLM-based clinical decision support in 2026?"
  python fallback_decomposer.py --question "..." --output json
  python fallback_decomposer.py --sample
"""

import argparse
import json
import re


FRAMEWORK = [
    ("what",        "What is {topic} — definition, scope, and current state?"),
    ("why",         "Why does {topic} matter now — the forces driving attention or change?"),
    ("how",         "How is {topic} being implemented or applied — methods, players, examples?"),
    ("who",         "Who are the key actors in {topic} — leaders, critics, regulators, adopters?"),
    ("whats_next",  "What's next for {topic} — near-term trajectory, open questions, watchpoints?"),
]


def _extract_topic(question: str) -> str:
    """Strip leading 'research', interrogatives, framing verbs to surface the topic noun phrase."""
    q = question.strip().rstrip("?").strip()
    q = re.sub(
        r"^(can you |could you |please |i need to |i want to |help me )",
        "", q, flags=re.IGNORECASE,
    ).strip()
    q = re.sub(
        r"^(research |look into |investigate |find me information on |"
        r"find information on |do some research on |what do we know about |"
        r"what is |what's |how are |how is |how do |why is |why are |"
        r"who is |who are |when |where |tell me about )",
        "", q, flags=re.IGNORECASE,
    ).strip()
    q = re.sub(r"\s+", " ", q)
    return q or question.strip().rstrip("?")


def decompose(question: str, n: int = 5) -> dict:
    """Build 3-5 sub-questions from the framework. n is capped at 5 and floored at 3."""
    n = max(3, min(5, n))
    topic = _extract_topic(question)
    selected = FRAMEWORK[:n]
    sub_questions = [
        {"label": label, "question": template.format(topic=topic)}
        for label, template in selected
    ]
    return {
        "question": question,
        "extracted_topic": topic,
        "sub_question_count": len(sub_questions),
        "framework": "what/why/how/who/what's next",
        "sub_questions": sub_questions,
        "note": ("Starting point only. Refine sub-questions with the user "
                 "before committing search budget. Drop any that don't fit; "
                 "rewrite ones that do."),
    }


def render_human(result: dict) -> str:
    lines = [
        f"Question: {result['question']}",
        f"Extracted topic: {result['extracted_topic']}",
        f"Framework: {result['framework']}",
        f"Sub-questions ({result['sub_question_count']}):",
    ]
    for i, sq in enumerate(result["sub_questions"], 1):
        lines.append(f"  {i}. [{sq['label']}] {sq['question']}")
    lines.append("")
    lines.append(f"Note: {result['note']}")
    return "\n".join(lines)


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--question", help="The research question to decompose.")
    p.add_argument("--n", type=int, default=5, help="Number of sub-questions (3-5; default 5).")
    p.add_argument("--output", choices=["human", "json"], default="human")
    p.add_argument("--sample", action="store_true", help="Run with built-in sample question.")
    args = p.parse_args()

    if args.sample:
        args.question = "How are health systems integrating LLM-based clinical decision support in 2026?"

    if not args.question:
        p.error("either --question or --sample is required")

    result = decompose(args.question, n=args.n)

    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_human(result))


if __name__ == "__main__":
    main()
