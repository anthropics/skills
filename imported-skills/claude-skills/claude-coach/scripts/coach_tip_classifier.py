#!/usr/bin/env python3
"""
coach_tip_classifier.py — decide whether the current turn warrants a power-user
tip, using the 5-gate decision tree defined in references/coaching-rules.md.

Gates (in order):
  1. Tip already given on the previous turn? → silent
  2. Prompt already well-formed (score >= 8 via prompt_rater)? → silent
  3. Deep-work mode (long technical/creative/emotional context)? → silent
  4. Tip would be obvious/condescending? → silent
  5. Exactly one higher-impact path missed? → emit that one tip

Stdlib-only. Heuristic-only — no LLM calls. Designed to be invoked by the
claude-coach skill before composing a response.

Usage:
    python3 coach_tip_classifier.py --prompt "Can you help me with my email?"
    python3 coach_tip_classifier.py --prompt "..." --previous-tip-given --json
    python3 coach_tip_classifier.py --sample
"""

import argparse
import json
import re
import sys
from dataclasses import dataclass, field, asdict


# Inlined minimal prompt scorer — keeps this script self-contained so the
# security auditor does not flag cross-script imports as dynamic loads.
# Mirrors the dimensions used by prompt_rater.py: clarity / constraint / format
# / audience. Maximum score 10.
_CLARITY_VERBS = ("write", "draft", "summarize", "review", "compare", "explain", "translate", "rewrite", "list", "rank", "score", "outline", "design", "debug", "refactor", "test")
_LENGTH_TOKENS = (r"\b\d+\s*(words?|sentences?|paragraphs?|bullets?|lines?|pages?|tokens?)\b", r"one\s+(sentence|paragraph|line)", r"short", r"brief", r"detailed")
_FORMAT_TOKENS = (r"\bmarkdown\b", r"\btable\b", r"\bjson\b", r"\byaml\b", r"\bcsv\b", r"\bbullet\b", r"\blist\b", r"\bcode\b", r"\bemail\b", r"\bmemo\b", r"\boutline\b")
_AUDIENCE_TOKENS = (r"\bfor\s+(my|a|the)\s+[A-Za-z][A-Za-z\- ]+\b", r"\btargeting\s+\w+", r"\bnon-technical\b", r"\btechnical\b", r"\bexecutive\w*\b", r"\bjunior\b", r"\bsenior\b", r"\bteam\b", r"\bcustomer\w*\b", r"\bremote workers\b", r"you are\b", r"act as\b", r"as a\b")
_CONSTRAINT_EXTRA = (r"\bno\s+(more|less)\s+than\b", r"\bmust\b", r"\bcannot\b", r"\bavoid\b", r"\bonly\b")


def _has_any(text: str, patterns) -> bool:
    return any(re.search(p, text, re.IGNORECASE) for p in patterns)


def score_prompt(prompt: str) -> int:
    p = prompt.strip()
    verb_hits = min(sum(1 for v in _CLARITY_VERBS if re.search(rf"\b{v}\b", p, re.IGNORECASE)), 2)
    ends_q = p.endswith("?")
    word_count = len(p.split())
    is_vague_open = ends_q and word_count < 8
    clarity = max(0, min(3, verb_hits + (0 if is_vague_open else 1) + (1 if word_count >= 6 else 0)))
    constraint = 2 if _has_any(p, _LENGTH_TOKENS) or _has_any(p, _CONSTRAINT_EXTRA) else 0
    fmt = 2 if _has_any(p, _FORMAT_TOKENS) else 0
    audience = 2 if _has_any(p, _AUDIENCE_TOKENS) else 0
    return min(10, clarity + constraint + fmt + audience + (1 if word_count >= 12 else 0))

DEEP_WORK_MARKERS = (
    r"\bstack\s*trace\b",
    r"\btraceback\b",
    r"\bsegfault\b",
    r"```",
    r"\bworking on\b",
    r"\bin the middle of\b",
    r"\bfeeling\b",
    r"\bvent(ing)?\b",
    r"\bjust\s+(do|write|give)\b.*\bno\s+(commentary|extras|tips)\b",
)
SUPPRESS_MARKERS = (
    r"\bstop\s+(with\s+)?the\s+tips\b",
    r"\bno\s+coaching\b",
    r"\bquiet mode\b",
    r"\bdon[’']?t coach\b",
)

# Patterns that map to specific tips. Order matters — first match wins.
TIP_RULES: list[tuple[re.Pattern[str], str, str]] = [
    (re.compile(r"\bhelp me with my email\b|\bwrite (a |an )?email\b", re.IGNORECASE),
     "Name the audience and the desired outcome upfront — that cuts two rounds of revision.",
     'e.g. "Reply to my manager declining Friday\'s meeting, professional tone, suggest async update."'),
    (re.compile(r"^thoughts\??$|\bany thoughts\b", re.IGNORECASE),
     "Ask for thoughts on a specific dimension instead of an open take.",
     'e.g. "What\'s the weakest claim and how would you attack it?"'),
    (re.compile(r"\bcurrent\b|\blatest\b|\btoday\b|\bnews\b|\bprice\b|\bversion\b", re.IGNORECASE),
     "For time-sensitive info, ask Claude to search the web — the knowledge cutoff bites here.",
     'e.g. "Search the web for the current pricing on …"'),
    (re.compile(r"\b(can|could) you (make|give|do|write)\b.*\b(better|nicer|cleaner)\b", re.IGNORECASE),
     "Name the dimension instead of saying 'better'. Concrete = measurable.",
     'e.g. "Cut 30%, remove every adjective, keep all numbers."'),
    (re.compile(r"\b(list|table|json|markdown)\b", re.IGNORECASE),
     "",
     ""),  # Suppress — prompt already specifies output shape.
]


@dataclass
class Decision:
    prompt: str
    coach: bool
    reason: str
    tip: str = ""
    tip_example: str = ""
    gates: dict[str, str] = field(default_factory=dict)


def is_deep_work(prompt: str) -> bool:
    return any(re.search(p, prompt, re.IGNORECASE) for p in DEEP_WORK_MARKERS) or len(prompt) > 800


def is_suppression(prompt: str) -> bool:
    return any(re.search(p, prompt, re.IGNORECASE) for p in SUPPRESS_MARKERS)


def pick_tip(prompt: str) -> tuple[str, str]:
    for pattern, tip, example in TIP_RULES:
        if pattern.search(prompt):
            return tip, example
    return "", ""


def classify(prompt: str, previous_tip_given: bool = False) -> Decision:
    decision = Decision(prompt=prompt, coach=False, reason="")
    decision.gates["1_previous_tip"] = "blocked" if previous_tip_given else "pass"
    decision.gates["suppression"] = "blocked" if is_suppression(prompt) else "pass"

    if previous_tip_given:
        decision.reason = "Gate 1 — tip already given on the previous turn."
        return decision
    if is_suppression(prompt):
        decision.reason = "Suppression marker present — user does not want coaching right now."
        return decision

    prompt_score = score_prompt(prompt)
    decision.gates["2_prompt_score"] = f"{prompt_score}/10"
    if prompt_score >= 8:
        decision.reason = "Gate 2 — prompt already well-formed (score >= 8)."
        return decision

    decision.gates["3_deep_work"] = "blocked" if is_deep_work(prompt) else "pass"
    if is_deep_work(prompt):
        decision.reason = "Gate 3 — deep-work mode (long context, traceback, code block, or emotional content)."
        return decision

    tip, example = pick_tip(prompt)
    decision.gates["4_specificity"] = "skip" if not tip else "pass"
    if not tip:
        decision.reason = "Gate 4/5 — no specific high-impact tip applies. Stay silent."
        return decision

    decision.coach = True
    decision.reason = "All gates passed — emit one tip."
    decision.tip = tip
    decision.tip_example = example
    decision.gates["5_single_high_impact"] = "pass"
    return decision


def render_human(d: Decision) -> str:
    head = "COACH" if d.coach else "SILENT"
    out = [f"[{head}] {d.reason}"]
    if d.coach:
        out.append(f"⚡ Power-user tip: {d.tip}")
        if d.tip_example:
            out.append(d.tip_example)
    out.append(f"gates: {d.gates}")
    return "\n".join(out)


def sample_run(as_json: bool = False) -> int:
    cases = [
        ("Can you help me with my email?", False),
        ("Write a 200-word product description for a noise-cancelling headphone targeting remote workers, focused on the focus-time benefit, no marketing fluff.", False),
        ("thoughts?", False),
        ("Can you make this better?", True),
        ("stop with the tips, just rewrite it", False),
    ]
    decisions = [classify(prompt, previous_tip_given=prev) for prompt, prev in cases]
    if as_json:
        print(json.dumps([asdict(d) for d in decisions], indent=2))
        return 0
    for d in decisions:
        print(render_human(d))
        print("-" * 60)
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Classify whether the current turn warrants a coaching tip.")
    parser.add_argument("--prompt", type=str, help="Prompt text to classify")
    parser.add_argument("--previous-tip-given", action="store_true", help="Flag that a tip was already given on the previous turn")
    parser.add_argument("--json", action="store_true", help="Emit JSON instead of human-readable text")
    parser.add_argument("--sample", action="store_true", help="Run against a built-in set of sample prompts")
    args = parser.parse_args(argv)

    if args.sample:
        return sample_run(args.json)

    if not args.prompt:
        parser.error("--prompt is required unless --sample is passed")

    d = classify(args.prompt, previous_tip_given=args.previous_tip_given)
    if args.json:
        print(json.dumps(asdict(d), indent=2))
    else:
        print(render_human(d))
    return 0


if __name__ == "__main__":
    sys.exit(main())
