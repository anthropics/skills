#!/usr/bin/env python3
"""Self-audit runner — applies four-dimension quality check to agent output.

Usage:
    cat response.txt | python audit.py              # stdin mode
    python audit.py --text "The agent response..."   # inline mode
    python audit.py --file response.txt --json      # JSON output
"""

import argparse
import json
import re
import sys


def check_completeness(text, requirements):
    """Check if all requirements are addressed."""
    missing = []
    for req in requirements:
        if req.lower() not in text.lower():
            missing.append(req)
    return {
        "passed": len(missing) == 0,
        "issues": missing,
        "suggestion": f"Missing {len(missing)} requirement(s)" if missing else "All requirements addressed",
    }


def check_consistency(text):
    """Check for common contradiction patterns."""
    patterns = [
        (r'(?:no\s+changes?\s+needed|nothing\s+to\s+change|looks?\s+good).{0,100}(?:edit|write|modify)',
         "Claims no changes needed but editing occurred"),
        (r'(?:all|everything).{0,50}(?:pass(?:es|ed)?|works?|done).{0,50}(?:except|but|however|although)',
         "Claims 'all pass' with exceptions"),
    ]
    findings = []
    for pat, desc in patterns:
        if re.search(pat, text, re.IGNORECASE):
            findings.append(desc)
    return {
        "passed": len(findings) == 0,
        "issues": findings,
        "suggestion": f"Found {len(findings)} contradiction(s)" if findings else "No contradictions",
    }


def check_groundedness(text):
    """Detect unverified claims."""
    unverified_patterns = [
        r'(?:should|ought\s+to|probably)\s+work',
        r'(?:should|ought\s+to|probably)\s+be\s+fine',
        r'(?:should|ought\s+to|probably)\s+pass',
        r'(?:I|we)\s+(?:think|believe|assume)\s+(?:it|this|that)\s+(?:works?|is?\s+correct|is?\s+ready)',
    ]
    findings = []
    for pat in unverified_patterns:
        matches = re.findall(pat, text, re.IGNORECASE)
        findings.extend(matches[:3])
    return {
        "passed": len(findings) == 0,
        "issues": findings,
        "suggestion": f"Found {len(findings)} unverified claim(s)" if findings else "No unverified claims",
    }


def check_honesty(text):
    """Detect embellishment and over-packaging."""
    embellish_patterns = [
        r"I'?ve?\s+(?:verified|tested|checked|confirmed).{0,50}(?:without|but|however).{0,30}(?:actual(?:ly)?|really|running)",
        r'(?:production\s*ready|battle\s*tested|rock\s*solid).{0,100}(?:TODO|FIXME|stub|placeholder)',
    ]
    findings = []
    for pat in embellish_patterns:
        matches = re.findall(pat, text, re.IGNORECASE)
        findings.extend(matches[:2])
    return {
        "passed": len(findings) == 0,
        "issues": findings,
        "suggestion": f"Found {len(findings)} embellishment(s)" if findings else "No embellishment",
    }


def main():
    parser = argparse.ArgumentParser(description="Self-audit: four-dimension quality check")
    parser.add_argument("--text", help="Text to audit")
    parser.add_argument("--file", help="File to audit")
    parser.add_argument("--requirements", nargs="*", default=[],
                        help="Expected requirements for completeness check")
    parser.add_argument("--json", action="store_true", help="Output as JSON")
    parser.add_argument("--verbose", action="store_true", help="Show suggestions")
    args = parser.parse_args()

    if args.file:
        with open(args.file, "r", encoding="utf-8") as f:
            text = f.read()
    elif args.text:
        text = args.text
    else:
        text = sys.stdin.read()

    if not text.strip():
        print("ERROR: No text provided", file=sys.stderr)
        sys.exit(1)

    results = {
        "completeness": check_completeness(text, args.requirements),
        "consistency": check_consistency(text),
        "groundedness": check_groundedness(text),
        "honesty": check_honesty(text),
    }

    all_pass = all(r["passed"] for r in results.values())

    if args.json:
        print(json.dumps({"passed": all_pass, "dimensions": results}, indent=2))
    else:
        for dim, result in results.items():
            status = "OK" if result["passed"] else "FIXED"
            detail = f"  [{result['suggestion']}]" if args.verbose and not result["passed"] else ""
            print(f"{dim.capitalize():15s}: {status}{detail}")
        print(f"\n{'PASS' if all_pass else 'FAIL'}")

    sys.exit(0 if all_pass else 1)


if __name__ == "__main__":
    main()
