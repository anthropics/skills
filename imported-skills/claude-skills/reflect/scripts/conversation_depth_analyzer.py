#!/usr/bin/env python3
"""conversation_depth_analyzer.py — Detect implicit reflect-trigger signals.

Stdlib-only. Analyzes a conversation transcript and reports:

  - turn count (User: + Assistant: pairs)
  - detail-mode turns (turns dominated by implementation specifics)
  - frustration markers (signs of user stuck-ness)
  - dead-end signals (pivots within short span)
  - implicit-trigger verdict: whether the conversation matches reflect-skill auto-invocation criteria

The skill OFFERS reflection when implicit signals fire; it does NOT auto-invoke.

NO LLM CALLS. Pure regex + counting.

Usage:
    python conversation_depth_analyzer.py --conversation /tmp/transcript.txt
    python conversation_depth_analyzer.py --conversation /tmp/transcript.txt --output json
    python conversation_depth_analyzer.py --sample
"""

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any, Dict, List


TURN_RE = re.compile(r"^\s*(User|Assistant):\s*", re.MULTILINE)

DETAIL_MARKERS = [
    r"\bimplementation\b",
    r"\bcode\b",
    r"\bfunction\b",
    r"\bclass\b",
    r"\bvariable\b",
    r"\b(syntax|method|parameter|argument)\b",
    r"\bdebug\b",
    r"\berror\b",
    r"`[^`]+`",  # backtick-quoted code references
]

FRUSTRATION_MARKERS = [
    r"\b(ugh|argh|frustrated|stuck)\b",
    r"\bnot working\b",
    r"\bdoesn'?t work\b",
    r"\bgoing in circles\b",
    r"\bstill (broken|failing|wrong)\b",
    r"\bwhy isn'?t\b",
    r"\bthis is (weird|strange|odd|confusing)\b",
]

DEAD_END_MARKERS = [
    r"\bnope\b",
    r"\bthat didn'?t work\b",
    r"\b(let's|let me) try (something|a) (else|different)\b",
    r"\bback to\b",
    r"\bnever mind\b",
    r"\bscratch that\b",
]


def count_turns(text: str) -> Dict[str, int]:
    matches = TURN_RE.findall(text)
    user_turns = sum(1 for m in matches if m == "User")
    assistant_turns = sum(1 for m in matches if m == "Assistant")
    return {
        "total_turns": len(matches),
        "user_turns": user_turns,
        "assistant_turns": assistant_turns,
    }


def count_pattern_hits(text: str, patterns: List[str]) -> int:
    return sum(len(re.findall(p, text, re.IGNORECASE)) for p in patterns)


def detect_detail_mode_run(text: str) -> int:
    """Count consecutive turns that have detail markers but no strategic check-in."""
    blocks = TURN_RE.split(text)
    consecutive_detail = 0
    max_consecutive = 0
    for block in blocks:
        if not block.strip():
            continue
        if any(re.search(p, block, re.IGNORECASE) for p in DETAIL_MARKERS):
            consecutive_detail += 1
            max_consecutive = max(max_consecutive, consecutive_detail)
        else:
            consecutive_detail = 0
    return max_consecutive


def analyze(text: str) -> Dict[str, Any]:
    turns = count_turns(text)
    detail_mode_max = detect_detail_mode_run(text)
    frustration_count = count_pattern_hits(text, FRUSTRATION_MARKERS)
    dead_end_count = count_pattern_hits(text, DEAD_END_MARKERS)

    signals: List[str] = []
    if detail_mode_max >= 5:
        signals.append(f"Detail-mode run of {detail_mode_max} consecutive turns")
    if turns["total_turns"] >= 20:
        signals.append(f"Long conversation: {turns['total_turns']} turns total")
    if frustration_count >= 2:
        signals.append(f"Frustration markers: {frustration_count} occurrences")
    if dead_end_count >= 2:
        signals.append(f"Dead-end / pivot markers: {dead_end_count} occurrences")

    should_offer_reflect = len(signals) >= 2 or detail_mode_max >= 10

    return {
        "turns": turns,
        "max_consecutive_detail_turns": detail_mode_max,
        "frustration_hits": frustration_count,
        "dead_end_hits": dead_end_count,
        "trigger_signals": signals,
        "implicit_trigger_verdict": (
            "OFFER_REFLECT" if should_offer_reflect else "NO_TRIGGER"
        ),
        "note": (
            "Skill should OFFER reflection (ask user if they want to step back), not auto-invoke"
            if should_offer_reflect
            else "No implicit trigger signal — only explicit phrases should invoke"
        ),
    }


SAMPLE_CONVERSATION = """User: Help me implement a sorting function.
Assistant: Sure. What language and what type of data?
User: Python, sorting a list of dicts by 'name' key.
Assistant: Here's the basic syntax: `sorted(items, key=lambda x: x['name'])`
User: That doesn't work — getting a TypeError.
Assistant: Can you share the exact error? Maybe some items don't have 'name'.
User: Ugh, still broken. Same error.
Assistant: Try adding a default: `key=lambda x: x.get('name', '')`.
User: Nope, that didn't work either. Different error now: KeyError on 'name'.
Assistant: That's strange. Let me look at your input data.
User: Frustrated. Let's try something else.
Assistant: OK let me reconsider. Are you sure the data is a list of dicts?
User: I think so. It's coming from an API.
Assistant: Let me check the API response shape. Add `print(type(items[0]))` first.
User: It's a string, not a dict.
Assistant: That's the issue. The API returns JSON strings; you need to parse them first.
User: This is weird, why isn't this working from the start?
Assistant: Let's go back to the data shape question first.
User: Going in circles. I'm stuck.
"""


def render_human(result: Dict[str, Any]) -> str:
    out: List[str] = []
    t = result["turns"]
    out.append(f"Conversation depth analysis:")
    out.append(f"  Total turns:                   {t['total_turns']}  (user: {t['user_turns']}, assistant: {t['assistant_turns']})")
    out.append(f"  Max consecutive detail turns:  {result['max_consecutive_detail_turns']}")
    out.append(f"  Frustration markers:           {result['frustration_hits']}")
    out.append(f"  Dead-end / pivot markers:      {result['dead_end_hits']}")
    out.append("")
    out.append(f"Implicit-trigger verdict: {result['implicit_trigger_verdict']}")
    if result["trigger_signals"]:
        out.append("Signals detected:")
        for s in result["trigger_signals"]:
            out.append(f"  - {s}")
    out.append("")
    out.append(result["note"])
    return "\n".join(out)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--conversation", help="Path to conversation transcript text file")
    parser.add_argument("--sample", action="store_true", help="Run on embedded sample (stuck-debugging scenario)")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if args.sample:
        text = SAMPLE_CONVERSATION
    elif args.conversation:
        p = Path(args.conversation)
        if not p.exists():
            print(f"error: {args.conversation} not found", file=sys.stderr)
            return 2
        text = p.read_text(encoding="utf-8")
    else:
        parser.print_help()
        return 0

    result = analyze(text)
    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
