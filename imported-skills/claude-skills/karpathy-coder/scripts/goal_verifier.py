#!/usr/bin/env python3
"""
goal_verifier.py — Check if a plan has verifiable success criteria.

Karpathy Principle #4 (Goal-Driven Execution): "Define success criteria.
Loop until verified. Don't tell it what to do — give it success criteria
and watch it go."

Reads a markdown plan and scores:
  - Does each step have a verification check?
  - Are success criteria concrete (test, assertion, measurement)?
  - Are there vague criteria ("make it work", "looks good")?
  - Is there a final verification step?

Usage:
    python goal_verifier.py plan.md
    python goal_verifier.py plan.md --json

Scoring:
    Each plan step gets 0-3 points:
      3 = concrete verification (test assertion, metric, command)
      2 = reasonable verification (manual check, visual)
      1 = vague verification ("should work", "looks right")
      0 = no verification mentioned
"""
from __future__ import annotations
import argparse
import json
import re
import sys
from pathlib import Path

CONCRETE_VERIFY = re.compile(
    r"\b(?:test\s+pass|assert|assertEqual|expect\(|\.toBe|\.toEqual|"
    r"exit\s+code\s*[=:]\s*0|status\s*[=:]\s*200|curl\s|"
    r"grep\s|diff\s|python.*test|npm\s+test|pytest|jest|"
    r"measure|benchmark|metric|latency\s*<|throughput\s*>)\b",
    re.I,
)
REASONABLE_VERIFY = re.compile(
    r"\b(?:verify|check|confirm|inspect|review|compare|validate|"
    r"run\s+and\s+see|manually|open\s+in\s+browser|visual|screenshot)\b",
    re.I,
)
VAGUE_VERIFY = re.compile(
    r"\b(?:should\s+work|looks?\s+(?:good|right|fine|ok)|"
    r"seems?\s+(?:correct|fine)|hopefully|probably\s+works?)\b",
    re.I,
)
STEP_PATTERN = re.compile(r"^(?:\d+[\.\)]\s+|[-*]\s+\[.\]\s+|[-*]\s+(?:Step\s+\d+))", re.M)
VERIFY_LABEL = re.compile(r"(?:verify|check|success\s+criteria|done\s+when|acceptance)\s*:", re.I)


def extract_steps(text):
    """Extract plan steps from markdown."""
    lines = text.splitlines()
    steps = []
    current_step = None
    current_body = []

    for line in lines:
        if STEP_PATTERN.match(line.strip()):
            if current_step:
                steps.append({"title": current_step, "body": "\n".join(current_body)})
            current_step = line.strip()
            current_body = []
        elif current_step:
            current_body.append(line)

    if current_step:
        steps.append({"title": current_step, "body": "\n".join(current_body)})

    return steps


def score_step(step):
    """Score a step's verification quality (0-3)."""
    full_text = step["title"] + "\n" + step["body"]

    if CONCRETE_VERIFY.search(full_text):
        return 3, "concrete"
    if VERIFY_LABEL.search(full_text) and REASONABLE_VERIFY.search(full_text):
        return 2, "reasonable"
    if REASONABLE_VERIFY.search(full_text):
        return 2, "reasonable"
    if VAGUE_VERIFY.search(full_text):
        return 1, "vague"
    return 0, "none"


def analyze_plan(text, source):
    """Analyze a plan for verification quality."""
    steps = extract_steps(text)

    if not steps:
        return {
            "status": "ok",
            "source": source,
            "steps_found": 0,
            "message": "No numbered/bulleted plan steps found. Is this a plan?",
            "verdict": "NO_PLAN",
            "score": 0,
            "max_score": 0,
            "step_results": [],
        }

    step_results = []
    total_score = 0
    max_score = len(steps) * 3

    for step in steps:
        pts, level = score_step(step)
        total_score += pts
        step_results.append({
            "title": step["title"][:120],
            "score": pts,
            "level": level,
            "has_verify_label": bool(VERIFY_LABEL.search(step["body"])),
        })

    # Check for final verification
    has_final = False
    if steps:
        last_full = steps[-1]["title"] + steps[-1]["body"]
        if re.search(r"\b(?:final|end-to-end|full.*test|regression|all.*pass)\b", last_full, re.I):
            has_final = True

    pct = (total_score / max_score * 100) if max_score > 0 else 0
    if pct >= 70:
        verdict = "STRONG"
    elif pct >= 40:
        verdict = "WEAK"
    else:
        verdict = "MISSING"

    return {
        "status": "ok",
        "source": source,
        "steps_found": len(steps),
        "score": total_score,
        "max_score": max_score,
        "percentage": round(pct, 1),
        "has_final_verification": has_final,
        "verdict": verdict,
        "step_results": step_results,
        "recommendations": _recommendations(step_results, has_final),
    }


def _recommendations(step_results, has_final):
    recs = []
    none_steps = [s for s in step_results if s["level"] == "none"]
    vague_steps = [s for s in step_results if s["level"] == "vague"]

    if none_steps:
        recs.append(f"{len(none_steps)} step(s) have no verification. Add 'verify: [check]' to each.")
    if vague_steps:
        recs.append(f"{len(vague_steps)} step(s) have vague criteria. Replace 'should work' with a concrete check.")
    if not has_final:
        recs.append("No final/end-to-end verification step. Add one at the end.")
    if not recs:
        recs.append("Plan has strong verification coverage. Good to go.")
    return recs


def main():
    p = argparse.ArgumentParser(
        description="Check if a plan has verifiable success criteria (Karpathy Principle #4).",
        epilog="Scores each step 0-3 based on verification quality.",
    )
    p.add_argument("input", nargs="?", default="-", help="Markdown plan file, or - for stdin")
    p.add_argument("--json", action="store_true", help="JSON output")
    args = p.parse_args()

    if args.input == "-":
        text = sys.stdin.read()
        source = "stdin"
    else:
        path = Path(args.input)
        if not path.exists():
            print(f"[error] {path} not found", file=sys.stderr)
            sys.exit(1)
        text = path.read_text(encoding="utf-8", errors="replace")
        source = str(path)

    result = analyze_plan(text, source)

    if args.json:
        print(json.dumps(result, indent=2))
        return

    print(f"Goal Verifier — {source}")
    print(f"Steps: {result['steps_found']}  Score: {result['score']}/{result['max_score']} ({result['percentage']}%)")
    print(f"Verdict: {result['verdict']}")
    print()

    for sr in result["step_results"]:
        icon = {"concrete": "+", "reasonable": "~", "vague": "?", "none": "!"}[sr["level"]]
        print(f"  [{icon}] {sr['title'][:100]}  ({sr['level']}, {sr['score']}/3)")

    print()
    for rec in result["recommendations"]:
        print(f"  -> {rec}")


if __name__ == "__main__":
    main()
