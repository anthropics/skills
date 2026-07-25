#!/usr/bin/env python3
"""directional_recommendation_validator.py — Verify reflect output ends with discipline.

Stdlib-only. Validates that a reflect-skill output:

  1. Ends with a directional recommendation: Continue / Pivot / Pause
  2. The recommendation is SPECIFIC (not vague)
  3. Uses flowing prose (no markdown headers or bullet lists in the body)
  4. Cites specific evidence (turn references, specific decision points)
  5. Doesn't include manufactured-problem language without specific evidence

Outputs PASS / WARN / FAIL with rule-by-rule findings.

NO LLM CALLS. Pure regex + heuristic detection.

Usage:
    python directional_recommendation_validator.py --output /tmp/reflect_output.txt
    python directional_recommendation_validator.py --sample-pass
    python directional_recommendation_validator.py --sample-fail
"""

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any, Dict, List


RECOMMENDATION_PATTERNS = {
    "continue": [
        r"\bcontinue\b\.?\s*$",
        r"\bcontinue\s+(this|the)\s",
        r"\bkeep\s+going\b",
        r"\bstay\s+(on|with)\s+this\b",
        r"\bproceed\b",
    ],
    "pivot": [
        r"\bpivot\s+(to|toward|away from)\b",
        r"\bchange\s+(direction|course|approach)\b",
        r"\bredirect\b",
        r"\bswitch\s+to\b",
    ],
    "pause": [
        r"\bpause\s+(for|to|until)\b",
        r"\bstop\s+(to|and)\s+(answer|consider|address)\b",
        r"\bhalt\s+(for|to|until)\b",
        r"\bwait\s+(to|until|for)\s+(answer|resolve|clarify)\b",
    ],
}

VAGUE_REASSURANCE_PATTERNS = [
    r"\blooks good\b",
    r"\bon the right track\b",
    r"\bseems fine\b",
    r"\bnothing major\b",
    r"\bnot too bad\b",
    r"\bgenerally okay\b",
]

MANUFACTURED_PROBLEM_HEDGES = [
    r"\bmight be worth\b",
    r"\bcould consider\b",
    r"\bperhaps reconsider\b",
    r"\bsome (drift|issues?) (potentially|might)\b",
    r"\bworth questioning\b",
    r"\bsome assumptions\b",
]

HEADER_PATTERNS = [
    r"^#+\s",
    r"^\*\*[A-Z][^*]+\*\*\s*$",
    r"^[A-Z][A-Z ]+:\s*$",
]

BULLET_PATTERNS = [
    r"^\s*[-*+]\s",
    r"^\s*\d+\.\s",
]

EVIDENCE_PATTERNS = [
    r"\b(turn|message|line)\s+\d+\b",
    r"\bat\s+turn\s+\d+\b",
    r"\bin\s+(turn|message)\s+\d+\b",
    r"\bin\s+the\s+(first|second|third|fourth|fifth|earlier|later)\s+(turn|message|exchange)\b",
    r"\boriginal\s+(goal|frame|framing)\b",
    r"\bat\s+the\s+(start|beginning|outset)\b",
]


def validate(output: str) -> Dict[str, Any]:
    findings: List[Dict[str, str]] = []

    def add(rule: str, level: str, message: str) -> None:
        findings.append({"rule": rule, "level": level, "message": message})

    # Rule 1: Closing recommendation present
    output_lower = output.lower()
    last_chunk = output[-400:]
    last_chunk_lower = last_chunk.lower()
    detected_recommendation = None
    for rec_type, patterns in RECOMMENDATION_PATTERNS.items():
        for p in patterns:
            if re.search(p, last_chunk_lower, re.IGNORECASE):
                detected_recommendation = rec_type
                break
        if detected_recommendation:
            break

    if detected_recommendation:
        add("closing-recommendation", "PASS", f"Detected '{detected_recommendation}' recommendation in closing.")
    else:
        add("closing-recommendation", "FAIL", "No Continue / Pivot / Pause recommendation detected in closing 400 chars.")

    # Rule 2: Vague reassurance
    vague_hits = sum(1 for p in VAGUE_REASSURANCE_PATTERNS if re.search(p, output_lower, re.IGNORECASE))
    if vague_hits >= 2:
        add("vague-reassurance", "FAIL", f"Output contains {vague_hits} vague-reassurance phrases. Replace with specific reasoning.")
    elif vague_hits == 1:
        add("vague-reassurance", "WARN", f"Output contains 1 vague phrase. Consider replacing with specific reasoning.")
    else:
        add("vague-reassurance", "PASS", "No vague-reassurance phrases detected.")

    # Rule 3: Manufactured-problem hedging
    hedge_hits = sum(1 for p in MANUFACTURED_PROBLEM_HEDGES if re.search(p, output_lower, re.IGNORECASE))
    if hedge_hits >= 3:
        add("manufactured-problems", "WARN", f"{hedge_hits} hedge phrases detected ('might be worth', 'could consider', etc.). Verify each cites specific evidence.")
    elif hedge_hits >= 1:
        add("manufactured-problems", "PASS", f"{hedge_hits} hedge phrase(s). Verify each cites specific evidence.")
    else:
        add("manufactured-problems", "PASS", "No manufactured-problem hedge phrases.")

    # Rule 4: Headers detection (should NOT be present)
    header_count = 0
    for p in HEADER_PATTERNS:
        header_count += len(re.findall(p, output, re.MULTILINE))
    if header_count >= 2:
        add("no-headers", "FAIL", f"Output contains {header_count} headers. Reflect output should be flowing prose, no headers.")
    elif header_count == 1:
        add("no-headers", "WARN", "One header detected. Verify it's part of a quote, not output structure.")
    else:
        add("no-headers", "PASS", "No headers in output (flowing prose confirmed).")

    # Rule 5: Bullet lists detection (should NOT be present in main body)
    bullet_count = 0
    for p in BULLET_PATTERNS:
        bullet_count += len(re.findall(p, output, re.MULTILINE))
    if bullet_count >= 3:
        add("no-bullets", "FAIL", f"Output contains {bullet_count} bullet-list items. Reflect output should be flowing prose.")
    elif bullet_count >= 1:
        add("no-bullets", "WARN", f"{bullet_count} bullet items detected. Verify these are part of a recommendation list, not body structure.")
    else:
        add("no-bullets", "PASS", "No bullet lists in output (flowing prose confirmed).")

    # Rule 6: Specific evidence references
    evidence_count = sum(len(re.findall(p, output_lower, re.IGNORECASE)) for p in EVIDENCE_PATTERNS)
    if evidence_count >= 3:
        add("specific-evidence", "PASS", f"{evidence_count} specific evidence references (turn numbers, original goal, etc.).")
    elif evidence_count >= 1:
        add("specific-evidence", "WARN", f"Only {evidence_count} specific evidence reference(s). Consider adding more for anchoring.")
    else:
        add("specific-evidence", "FAIL", "No specific evidence references (turn numbers, original goal anchors). Output is too vague.")

    return finalize(findings)


def finalize(findings: List[Dict[str, str]]) -> Dict[str, Any]:
    counts = {"PASS": 0, "WARN": 0, "FAIL": 0}
    for f in findings:
        counts[f["level"]] += 1
    if counts["FAIL"] > 0:
        verdict = "FAIL"
    elif counts["WARN"] > 0:
        verdict = "WARN"
    else:
        verdict = "PASS"
    return {"verdict": verdict, "counts": counts, "findings": findings}


SAMPLE_PASS_OUTPUT = """Re-reading from the original goal at turn 3 — clarify the auth flow — the current direction is solid. Three specific reasons.

First, the auth flow has been narrowed from generic OAuth to a specific Google plus GitHub combination at turn 9, which matches the user base stated at turn 3. The narrowing is principled, not arbitrary.

Second, the bias check finds no anchoring — passwordless authentication was explicitly considered at turn 11 and rejected for reasons specific to the team's expertise. The rejection cites evidence (team has not deployed magic-link systems before) rather than dismissing the alternative without engagement.

Third, the original goal at turn 3 connects directly to the current implementation work at turns 14-18. No drift has occurred. Recent decisions (rate limiting at turn 16, session storage at turn 17) are tactical refinements within the original strategic frame, not shifts away from it.

Continue.
"""

SAMPLE_FAIL_OUTPUT = """## Reflection

Some things to consider:

- The conversation might be drifting
- We could potentially reconsider some assumptions
- Some aspects look good

Looks good overall! On the right track.
"""


def render_human(result: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"Reflect-output validation verdict: {result['verdict']}")
    c = result["counts"]
    out.append(f"  PASS: {c['PASS']}  WARN: {c['WARN']}  FAIL: {c['FAIL']}")
    out.append("")
    out.append("Findings:")
    for f in result["findings"]:
        marker = {"PASS": "[ok]", "WARN": "[warn]", "FAIL": "[FAIL]"}[f["level"]]
        out.append(f"  {marker} {f['rule']}: {f['message']}")
    return "\n".join(out)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--output", help="Path to reflect-skill output text file")
    parser.add_argument("--sample-pass", action="store_true", help="Validate embedded honest validation sample")
    parser.add_argument("--sample-fail", action="store_true", help="Validate embedded vague-reassurance sample")
    parser.add_argument("--output-format", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if args.sample_pass:
        text = SAMPLE_PASS_OUTPUT
    elif args.sample_fail:
        text = SAMPLE_FAIL_OUTPUT
    elif args.output:
        p = Path(args.output)
        if not p.exists():
            print(f"error: {args.output} not found", file=sys.stderr)
            return 2
        text = p.read_text(encoding="utf-8")
    else:
        parser.print_help()
        return 0

    result = validate(text)
    if args.output_format == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_human(result))
    return 0 if result["verdict"] != "FAIL" else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
