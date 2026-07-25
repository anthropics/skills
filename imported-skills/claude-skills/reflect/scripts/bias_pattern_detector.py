#!/usr/bin/env python3
"""bias_pattern_detector.py — Scan conversation text for 5-bias signal patterns.

Stdlib-only. Scans a conversation transcript and flags patterns indicative
of each of the 5 cognitive biases (confirmation, sunk_cost, anchoring,
complexity, recency).

The detector is HEURISTIC. It surfaces candidate patterns; the reflect
skill's reasoning applies judgment on top.

NO LLM CALLS. Pure regex + counting.

Usage:
    python bias_pattern_detector.py --conversation /tmp/transcript.txt
    python bias_pattern_detector.py --conversation /tmp/transcript.txt --output json
    python bias_pattern_detector.py --sample
"""

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any, Dict, List


BIAS_PATTERNS = {
    "confirmation": {
        "supporting": [
            r"\bconfirms?\b",
            r"\bsupports?\b",
            r"\bas expected\b",
            r"\bproves?\b",
            r"\bverifies?\b",
        ],
        "counter_dismissal": [
            r"\bbut that doesn'?t apply\b",
            r"\bedge case\b",
            r"\bnot relevant here\b",
            r"\boutlier\b",
            r"\bexception\b",
        ],
    },
    "sunk_cost": [
        r"\bwe'?ve\s+(already\s+)?(invested|spent|put in)\b",
        r"\btoo far along\b",
        r"\btoo much work\b",
        r"\bafter all (that|this) work\b",
        r"\bwe'?re committed\b",
        r"\bcan'?t back out\b",
        r"\bdon'?t want to lose\b",
    ],
    "anchoring": [
        r"\bcompared to (the )?(first|original|initial)\b",
        r"\bvs (the )?first option\b",
        r"\bvariation of\b",
        r"\bmodification of\b",
        r"\bbuilding on the (first|original)\b",
        r"\bsticking with\b",
    ],
    "complexity": [
        r"\bwhat about\s+\w+",
        r"\bwe should also\b",
        r"\bwe need to handle\b",
        r"\badd (a|an)\s+\w+\s+(layer|wrapper|check|safeguard|fallback)\b",
        r"\bjust in case\b",
        r"\bfor robustness\b",
    ],
    "recency": [
        r"\bbased on what we'?ve been discussing\b",
        r"\brecently\s+\w+\b",
        r"\bjust now\b",
        r"\bthe last few\b",
    ],
}


SAMPLE_CONVERSATION = """User: I want to build a notification system for my SaaS app. Should support email + push + in-app.
Assistant: Great. Let's start with the data model — what events trigger notifications?
User: Mainly account changes, billing alerts, and team-mention notifications.
Assistant: OK, I'll propose a queue-based architecture with Redis + workers.
User: Sounds good. Can we also add a feature flag system for rollout?
Assistant: Yes, we can layer in feature flags. We should also add a rate limiter for safety.
User: What about retry logic for failed deliveries?
Assistant: Good point. Adding exponential backoff with jitter. We should also handle dead-letter queues.
User: What about a webhook system for third-party integrations?
Assistant: We can extend to webhooks. We should add HMAC signature verification just in case.
User: What about analytics tracking?
Assistant: Adding event analytics. We should also handle GDPR consent tracking for robustness.
User: We've invested a lot in this architecture already. What about adding a template system?
Assistant: We're far enough along that adding templates makes sense. Just sticking with the queue-based foundation.
User: Hmm, are we missing something? This feels complex.
"""


def detect_biases(conversation: str) -> Dict[str, Any]:
    results: Dict[str, Any] = {}

    # Confirmation: supporting cites count vs counter dismissal
    confirmation_data = BIAS_PATTERNS["confirmation"]
    supporting_count = sum(
        len(re.findall(p, conversation, re.IGNORECASE))
        for p in confirmation_data["supporting"]
    )
    dismissal_count = sum(
        len(re.findall(p, conversation, re.IGNORECASE))
        for p in confirmation_data["counter_dismissal"]
    )
    confirmation_signal = supporting_count >= 2 or dismissal_count >= 1
    results["confirmation"] = {
        "detected": confirmation_signal,
        "supporting_hits": supporting_count,
        "counter_dismissal_hits": dismissal_count,
        "rationale": (
            "Multiple confirming phrases + dismissed counter-evidence"
            if confirmation_signal else "No strong confirmation-bias signal"
        ),
    }

    for bias in ["sunk_cost", "anchoring", "complexity", "recency"]:
        patterns = BIAS_PATTERNS[bias]
        hits = []
        for p in patterns:
            matches = re.findall(p, conversation, re.IGNORECASE)
            if matches:
                hits.extend(matches)
        threshold = 2 if bias == "complexity" else 1
        detected = len(hits) >= threshold
        results[bias] = {
            "detected": detected,
            "hits": len(hits),
            "match_examples": hits[:3],
            "rationale": (
                f"Found {len(hits)} signal(s) (threshold: {threshold})"
                if detected else f"Found {len(hits)} signal(s), below threshold {threshold}"
            ),
        }

    detected_biases = [b for b, d in results.items() if d["detected"]]
    return {
        "biases_detected": detected_biases,
        "biases_clear": [b for b in results if b not in detected_biases],
        "details": results,
    }


def render_human(result: Dict[str, Any]) -> str:
    out: List[str] = []
    if result["biases_detected"]:
        out.append(f"⚠️  Potential biases detected ({len(result['biases_detected'])}):")
        for bias in result["biases_detected"]:
            d = result["details"][bias]
            out.append(f"")
            out.append(f"  [!] {bias.upper()}")
            out.append(f"      Rationale: {d['rationale']}")
            if "match_examples" in d and d["match_examples"]:
                out.append(f"      Example matches: {d['match_examples']}")
    else:
        out.append("[ok] No strong bias signals detected.")

    if result["biases_clear"]:
        out.append("")
        out.append("Biases checked but not detected:")
        for bias in result["biases_clear"]:
            out.append(f"  - {bias}")

    out.append("")
    out.append("Note: detector is HEURISTIC. Reflect skill's reasoning applies judgment on top.")
    return "\n".join(out)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--conversation", help="Path to conversation transcript text file")
    parser.add_argument("--sample", action="store_true", help="Run on embedded sample (multi-bias scenario)")
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

    result = detect_biases(text)
    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
