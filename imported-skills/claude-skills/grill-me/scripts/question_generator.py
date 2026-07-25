#!/usr/bin/env python3
"""question_generator.py — Generate forcing questions from extracted decision branches.

Stdlib-only. Takes a plan doc, runs decision_tree_extractor, then generates
forcing questions per Matt Pocock's grill-me discipline:

  - Each question maps to one decision branch
  - Each question proposes a recommended answer
  - Questions ordered by dependency (independent first, dependent last)
  - One question per turn (output is a list, not a paragraph)

Template per question:
  Q: [forcing question]
  Recommended: [recommendation with 1-sentence rationale]

Question templates by branch kind:
  - intent  -> "You said you'll X. Why X and not Y?"
  - choice  -> "Between X and Y, which one and why?"
  - open    -> "X is marked TBD. What's blocking the decision?"
  - tradeoff -> "Trade-off between A and B. Which side are you optimizing for?"
  - dependency -> "X depends on Y. Is Y locked in? If not, ask about Y first."
  - question -> "[original question] — what's your current answer?"

Usage:
    python question_generator.py                          # uses embedded sample
    python question_generator.py path/to/plan.md
    python question_generator.py plan.md --output json
"""

import argparse
import json
import sys
import os
from typing import Any, Dict, List

# Import extractor as a module
_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)
from decision_tree_extractor import extract_branches, SAMPLE_PLAN  # noqa: E402


QUESTION_TEMPLATES = {
    "intent": "Why this approach and not the obvious alternative?",
    "choice": "Which side of the choice, and what's the deciding criterion?",
    "open": "What's blocking this decision? What would unblock it today?",
    "tradeoff": "Which side of the trade-off are you optimizing for, and what's the kill criterion?",
    "dependency": "Is the dependency locked in? If not, that decision comes first.",
    "question": "What's your current best answer, even if uncertain?",
}

RECOMMENDED_TEMPLATES = {
    "intent": "State the alternative explicitly + 1 sentence why you rejected it.",
    "choice": "Pick the option that aligns with the constraint you can't change (budget, deadline, team).",
    "open": "Name the missing input. Estimate when it arrives. Decide now under uncertainty if it won't arrive in time.",
    "tradeoff": "Choose the side that's reversible later. Trade-offs are usually one-way; pick the one with the escape hatch.",
    "dependency": "Resolve the upstream decision first. Then re-evaluate this one.",
    "question": "Even a 60%-confidence answer is better than 'we'll figure it out later'.",
}


def _detect_dependencies(branches: List[Dict[str, Any]]) -> List[int]:
    """Reorder: dependency branches go AFTER what they depend on (best-effort)."""
    dep_indices = [i for i, b in enumerate(branches) if b["kind"] == "dependency"]
    non_dep_indices = [i for i, b in enumerate(branches) if b["kind"] != "dependency"]
    return non_dep_indices + dep_indices


def generate_questions(branches: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    ordered = _detect_dependencies(branches)
    questions: List[Dict[str, Any]] = []
    for n, idx in enumerate(ordered, start=1):
        b = branches[idx]
        q_template = QUESTION_TEMPLATES.get(b["kind"], "What's the current state?")
        r_template = RECOMMENDED_TEMPLATES.get(b["kind"], "State your best answer.")
        questions.append({
            "n": n,
            "line": b["line"],
            "branch_kind": b["kind"],
            "context": b["context"],
            "question": f"L{b['line']}: {b['context']} -> {q_template}",
            "recommended": r_template,
        })
    return questions


def analyze(text: str) -> Dict[str, Any]:
    branches = extract_branches(text)
    questions = generate_questions(branches)
    return {
        "total_questions": len(questions),
        "branch_kinds": sorted(set(b["kind"] for b in branches)),
        "questions": questions,
    }


def render_text(r: Dict[str, Any]) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("FORCING QUESTION GENERATOR (one at a time, per Matt's grill-me)")
    lines.append("=" * 72)
    lines.append("")
    lines.append(f"Total questions: {r['total_questions']}")
    lines.append(f"Branch kinds: {r['branch_kinds']}")
    lines.append("")
    lines.append("-" * 72)
    for q in r["questions"]:
        lines.append(f"  Q{q['n']:>2d}: {q['question']}")
        lines.append(f"        Recommended: {q['recommended']}")
        lines.append("")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Generate forcing questions from a plan/design document.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("path", nargs="?", help="Path to markdown plan (uses embedded sample if omitted)")
    parser.add_argument("--output", choices=("text", "json"), default="text", help="Output format")
    args = parser.parse_args()

    if args.path:
        try:
            with open(args.path, "r", encoding="utf-8") as f:
                text = f.read()
        except (IOError, OSError) as e:
            print(f"error: {e}", file=sys.stderr)
            return 1
    else:
        text = SAMPLE_PLAN

    result = analyze(text)
    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_text(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
