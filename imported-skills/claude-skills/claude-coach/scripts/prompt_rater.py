#!/usr/bin/env python3
"""
prompt_rater.py — score a user prompt 0-10 across four dimensions and emit a
structured rating with a recommended rewrite.

Dimensions:
  - clarity      : is the ask unambiguous?
  - constraint   : is there at least one measurable constraint (length, format, audience, deadline)?
  - format       : is the desired output shape specified?
  - audience     : is the reader/role named or implied?

Stdlib-only. Heuristic-only — no LLM calls. The output is designed to be
consumed by the claude-coach skill's "rate that prompt" flow.

Usage:
    python3 prompt_rater.py --prompt "Can you help me with my email?"
    python3 prompt_rater.py --prompt "..." --json
    python3 prompt_rater.py --sample
"""

import argparse
import json
import re
import sys
from dataclasses import dataclass, field, asdict

CLARITY_VERBS = ("write", "draft", "summarize", "review", "compare", "explain", "translate", "rewrite", "list", "rank", "score", "outline", "design", "debug", "refactor", "test")
LENGTH_TOKENS = (r"\b\d+\s*(words?|sentences?|paragraphs?|bullets?|lines?|pages?|tokens?)\b", r"one\s+(sentence|paragraph|line)", r"short", r"brief", r"detailed")
FORMAT_TOKENS = (r"\bmarkdown\b", r"\btable\b", r"\bjson\b", r"\byaml\b", r"\bcsv\b", r"\bbullet\b", r"\blist\b", r"\bcode\b", r"\bemail\b", r"\bmemo\b", r"\boutline\b")
AUDIENCE_TOKENS = (r"\bfor\s+(my|a|the)\s+[A-Za-z][A-Za-z\- ]+\b", r"\btargeting\s+\w+", r"\bnon-technical\b", r"\btechnical\b", r"\bexecutive\w*\b", r"\bjunior\b", r"\bsenior\b", r"\bteam\b", r"\bcustomer\w*\b", r"\bremote workers\b")
ROLE_TOKENS = (r"you are\b", r"act as\b", r"as a\b")


@dataclass
class Rating:
    prompt: str
    clarity: int = 0
    constraint: int = 0
    fmt: int = 0
    audience: int = 0
    score: int = 0
    what_worked: str = ""
    what_to_improve: str = ""
    better_version: str = ""
    breakdown: dict[str, str] = field(default_factory=dict)


def _has_any(text: str, patterns) -> bool:
    return any(re.search(p, text, re.IGNORECASE) for p in patterns)


def _verb_strength(text: str) -> int:
    hits = sum(1 for v in CLARITY_VERBS if re.search(rf"\b{v}\b", text, re.IGNORECASE))
    return min(hits, 2)


def rate(prompt: str) -> Rating:
    p = prompt.strip()
    rating = Rating(prompt=p)

    verb_score = _verb_strength(p)
    length_ok = _has_any(p, LENGTH_TOKENS)
    ends_with_question = p.endswith("?")
    is_vague_open = ends_with_question and len(p.split()) < 8

    rating.clarity = max(0, min(3, verb_score + (0 if is_vague_open else 1) + (1 if len(p.split()) >= 6 else 0)))
    rating.constraint = 2 if length_ok or _has_any(p, (r"\bno\s+(more|less)\s+than\b", r"\bmust\b", r"\bcannot\b", r"\bavoid\b", r"\bonly\b")) else 0
    rating.fmt = 2 if _has_any(p, FORMAT_TOKENS) else 0
    rating.audience = 2 if (_has_any(p, AUDIENCE_TOKENS) or _has_any(p, ROLE_TOKENS)) else 0

    raw = rating.clarity + rating.constraint + rating.fmt + rating.audience
    rating.score = min(10, raw + (1 if len(p.split()) >= 12 else 0))

    rating.breakdown = {
        "clarity": f"{rating.clarity}/3",
        "constraint": f"{rating.constraint}/2",
        "format": f"{rating.fmt}/2",
        "audience": f"{rating.audience}/2",
        "length_bonus": "+1" if len(p.split()) >= 12 else "+0",
    }

    if rating.score >= 8:
        rating.what_worked = "Specific action verb, named constraint, and clear audience."
        rating.what_to_improve = "Already well-formed. Optionally request a self-critique pass after the first draft."
        rating.better_version = p
    elif rating.score >= 5:
        worked = []
        if rating.clarity >= 2:
            worked.append("clear action")
        if rating.constraint:
            worked.append("named constraint")
        if rating.fmt:
            worked.append("output format specified")
        if rating.audience:
            worked.append("audience implied")
        rating.what_worked = ", ".join(worked) or "concrete enough to act on"
        if not rating.audience:
            rating.what_to_improve = "Name the audience or role explicitly."
        elif not rating.constraint:
            rating.what_to_improve = "Add a measurable constraint (e.g. word count, must-include, must-avoid)."
        elif not rating.fmt:
            rating.what_to_improve = "Specify the output shape (markdown table, JSON, bullets, prose)."
        else:
            rating.what_to_improve = "Tighten with one more constraint to cut iteration."
        rating.better_version = _augment(p, rating)
    else:
        rating.what_worked = "There is a topic to anchor on."
        rating.what_to_improve = "Replace the open question with a concrete ask: action verb + length + audience + format."
        rating.better_version = _augment(p, rating, aggressive=True)

    return rating


def _augment(prompt: str, rating: Rating, aggressive: bool = False) -> str:
    additions: list[str] = []
    if not rating.constraint:
        additions.append("in 200 words")
    if not rating.audience:
        additions.append("for a non-technical reader")
    if not rating.fmt:
        additions.append("as markdown bullets")
    if not additions:
        return prompt
    base = prompt.rstrip(" .?")
    suffix = ", ".join(additions)
    if aggressive and not any(v in prompt.lower() for v in CLARITY_VERBS):
        base = f"Write a focused response to: {base}"
    return f"{base}, {suffix}."


def render_human(r: Rating) -> str:
    return (
        f"**Their prompt:** {r.prompt}\n"
        f"**Score:** {r.score}/10  ({r.breakdown})\n"
        f"**What worked:** {r.what_worked}\n"
        f"**What to improve:** {r.what_to_improve}\n"
        f"**Better version:** {r.better_version}"
    )


def sample_run(as_json: bool = False) -> int:
    samples = [
        "Can you help me with my email?",
        "Write a 200-word product description for a noise-cancelling headphone targeting remote workers, focused on the focus-time benefit, no marketing fluff.",
        "thoughts?",
    ]
    ratings = [rate(s) for s in samples]
    if as_json:
        print(json.dumps([asdict(r) for r in ratings], indent=2))
        return 0
    for r in ratings:
        print(render_human(r))
        print("-" * 60)
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Score a prompt 0-10 and emit a structured rating.")
    parser.add_argument("--prompt", type=str, help="Prompt text to rate")
    parser.add_argument("--json", action="store_true", help="Emit JSON instead of human-readable text")
    parser.add_argument("--sample", action="store_true", help="Run against a built-in set of sample prompts")
    args = parser.parse_args(argv)

    if args.sample:
        return sample_run(args.json)

    if not args.prompt:
        parser.error("--prompt is required unless --sample is passed")

    r = rate(args.prompt)
    if args.json:
        print(json.dumps(asdict(r), indent=2))
    else:
        print(render_human(r))
    return 0


if __name__ == "__main__":
    sys.exit(main())
