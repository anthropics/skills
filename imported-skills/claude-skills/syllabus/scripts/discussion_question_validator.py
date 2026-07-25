#!/usr/bin/env python3
"""discussion_question_validator.py — Bloom higher-order quality check.

Stdlib-only. Validates each discussion question against Bloom's revised
taxonomy (Anderson & Krathwohl 2001). Flags:

  - Recall-only questions (any audience): "what did authors find?", "summarize", etc.
  - Below-audience questions (e.g., grad-doctoral course with undergrad-intro questions)
  - Above-audience questions (e.g., undergrad-intro course with doctoral-level questions)

Suggests upgrades by replacing low-tier verbs with audience-appropriate Bloom verbs.

NO LLM CALLS. Pure regex + verb classification.

Usage:
    python discussion_question_validator.py --questions-file /tmp/questions.json --audience grad_masters
    python discussion_question_validator.py --question "What did the authors find?" --audience undergrad_intro
    python discussion_question_validator.py --sample
"""

import argparse
import json
import re
import sys
from typing import Any, Dict, List, Optional


VALID_AUDIENCES = ["undergrad_intro", "undergrad_advanced", "grad_masters", "grad_doctoral", "professional", "mixed"]


# Bloom's revised taxonomy verb classification
BLOOM_VERBS = {
    "remember": ["identify", "list", "recall", "name", "define", "label", "match", "recognize", "state", "what is", "what are", "what did", "describe what"],
    "understand": ["explain", "summarize", "classify", "compare", "contrast", "describe how", "interpret", "paraphrase", "translate"],
    "apply": ["use", "apply", "demonstrate", "implement", "execute", "carry out", "how could you use", "how would you apply", "how could this be applied", "what would happen if"],
    "analyze": ["compare", "contrast", "examine", "differentiate", "organize", "what patterns", "why do", "what connections", "deconstruct"],
    "evaluate": ["judge", "critique", "defend", "justify", "argue", "is this", "should we", "which is better", "do you agree", "evaluate the"],
    "create": ["design", "propose", "construct", "develop", "formulate", "create a", "design a", "what would you propose", "how would you redesign"],
}

# Audience → minimum acceptable Bloom level
AUDIENCE_MIN_BLOOM = {
    "undergrad_intro": 1,       # Remember+ acceptable, but apply+ preferred
    "undergrad_advanced": 2,    # Understand+
    "grad_masters": 3,          # Apply+
    "grad_doctoral": 4,         # Analyze+
    "professional": 3,          # Apply+ (practice-oriented)
    "mixed": 2,                 # Understand+ (lowest bucket present)
}

BLOOM_LEVEL_ORDER = ["remember", "understand", "apply", "analyze", "evaluate", "create"]


def classify_question(question: str) -> Dict[str, Any]:
    """Classify question by Bloom level."""
    q_lower = question.lower()
    detected_levels: List[str] = []
    matched_phrases: Dict[str, List[str]] = {}

    for level, verbs in BLOOM_VERBS.items():
        for verb in verbs:
            if re.search(rf"\b{re.escape(verb)}\b", q_lower):
                if level not in detected_levels:
                    detected_levels.append(level)
                matched_phrases.setdefault(level, []).append(verb)

    if not detected_levels:
        # Default heuristic: if starts with "what/why/how", probably understand or apply
        if q_lower.strip().startswith(("what", "why", "how")):
            detected_levels = ["understand"]
            matched_phrases["understand"] = ["(inferred from interrogative)"]
        else:
            detected_levels = ["unknown"]

    # Highest Bloom level detected
    highest_level = "unknown"
    highest_idx = -1
    for level in detected_levels:
        if level in BLOOM_LEVEL_ORDER:
            idx = BLOOM_LEVEL_ORDER.index(level)
            if idx > highest_idx:
                highest_idx = idx
                highest_level = level

    return {
        "question": question,
        "detected_levels": detected_levels,
        "highest_level": highest_level,
        "highest_level_index": highest_idx,
        "matched_phrases": matched_phrases,
    }


def validate_against_audience(question: str, audience: str) -> Dict[str, Any]:
    if audience not in VALID_AUDIENCES:
        raise ValueError(f"Invalid audience '{audience}'. Pick from: {VALID_AUDIENCES}")
    classification = classify_question(question)
    min_required_idx = AUDIENCE_MIN_BLOOM[audience] - 1  # convert level to 0-indexed
    detected_idx = classification["highest_level_index"]

    if detected_idx == -1:
        verdict = "WARN"
        message = f"Could not detect Bloom level. Manual review recommended."
    elif detected_idx < min_required_idx:
        verdict = "FAIL"
        required_level = BLOOM_LEVEL_ORDER[min_required_idx]
        message = (
            f"Question level '{classification['highest_level']}' is BELOW required minimum "
            f"'{required_level}' for {audience}. Rework with verbs from higher Bloom levels."
        )
    elif detected_idx > min_required_idx + 2:
        verdict = "WARN"
        target_level = BLOOM_LEVEL_ORDER[min_required_idx]
        message = (
            f"Question level '{classification['highest_level']}' may be ABOVE typical "
            f"{audience} level. Consider whether students can engage at {target_level} level."
        )
    else:
        verdict = "PASS"
        message = f"Question level '{classification['highest_level']}' appropriate for {audience}."

    suggested_upgrades: List[str] = []
    if verdict == "FAIL":
        target_level = BLOOM_LEVEL_ORDER[min_required_idx]
        suggested_upgrades = [
            f"Replace verb with: {', '.join(BLOOM_VERBS[target_level][:5])}",
            f"Pattern: '{BLOOM_VERBS[target_level][0]} [the {target_level} concept]...'",
        ]

    return {
        "verdict": verdict,
        "audience": audience,
        "min_required_level": BLOOM_LEVEL_ORDER[min_required_idx] if min_required_idx >= 0 else "unknown",
        "classification": classification,
        "message": message,
        "suggested_upgrades": suggested_upgrades,
    }


SAMPLE_QUESTIONS = [
    {"question": "What did the authors find?", "audience": "undergrad_intro"},
    {"question": "What did the authors find?", "audience": "grad_doctoral"},
    {"question": "How could you apply this method to clinical decision support for sepsis?", "audience": "grad_masters"},
    {"question": "Design a follow-up study that would test whether MUFA:SFA ratio specifically drives the lipidomic shift.", "audience": "grad_doctoral"},
    {"question": "Why does the Mediterranean diet improve lipoprotein profiles?", "audience": "undergrad_intro"},
]


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--question", help="Single question to validate")
    parser.add_argument("--questions-file", help="JSON file with [{question, audience}, ...] entries")
    parser.add_argument("--audience", choices=VALID_AUDIENCES, help="Course audience for the question(s)")
    parser.add_argument("--sample", action="store_true")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    results: List[Dict[str, Any]] = []
    try:
        if args.sample:
            for sq in SAMPLE_QUESTIONS:
                results.append(validate_against_audience(sq["question"], sq["audience"]))
        elif args.question and args.audience:
            results.append(validate_against_audience(args.question, args.audience))
        elif args.questions_file:
            from pathlib import Path
            p = Path(args.questions_file)
            if not p.exists():
                print(f"error: {args.questions_file} not found", file=sys.stderr); return 2
            data = json.loads(p.read_text(encoding="utf-8"))
            for item in data:
                results.append(validate_against_audience(item["question"], item["audience"]))
        else:
            parser.print_help(); return 0
    except ValueError as e:
        print(f"error: {e}", file=sys.stderr); return 2

    if args.output == "json":
        print(json.dumps(results, indent=2))
    else:
        for r in results:
            marker = {"PASS": "[ok]", "WARN": "[warn]", "FAIL": "[FAIL]"}[r["verdict"]]
            print(f"{marker} ({r['audience']:<20s}) {r['classification']['question'][:80]}")
            print(f"      Highest Bloom level: {r['classification']['highest_level']}; required: {r['min_required_level']}")
            print(f"      → {r['message']}")
            if r["suggested_upgrades"]:
                print(f"      Suggested upgrades:")
                for s in r["suggested_upgrades"]:
                    print(f"        - {s}")
            print()
    fail_count = sum(1 for r in results if r["verdict"] == "FAIL")
    return 1 if fail_count > 0 else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
