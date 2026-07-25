#!/usr/bin/env python3
"""draft_safety_validator.py — Enforce the NEVER-SEND rule on every triage run.

Stdlib-only. Post-flight check that scans the per-run triage log for any
send-shaped tool call. If any are detected → FAIL → halt → alert user.

This is the deterministic enforcement of the non-negotiable safety property:
  "The skill creates drafts. It NEVER sends."

The skill body is the first line of defense (the skill must not invoke send
verbs). This validator is the second line: even if the body's discipline broke,
this catches it before the user discovers a sent email.

Send-shape tool patterns detected (case-insensitive):

  Gmail-style:
    gmail.users.messages.send | users.messages.send | gmail.send

  Outlook / Microsoft Graph:
    me/sendMail | sendMail | me/messages/.*?/send | outlook.send | graph.sendMail

  Generic verbs:
    send_email | send_mail | send_message | sendMessage | dispatch_email

Allowed (drafts and reads, NOT flagged):

  drafts.create | SaveAsDraft | get_message | list_messages | search_messages | etc.

NO LLM CALLS. Pure regex pattern matching.

Usage:
    python draft_safety_validator.py --action-log /path/to/triage-log.md
    python draft_safety_validator.py --action-log /path/to/log.md --output json
    python draft_safety_validator.py --sample-pass
    python draft_safety_validator.py --sample-fail
"""

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any, Dict, List


# Patterns that indicate a SEND operation (FAIL if matched)
SEND_PATTERNS = [
    re.compile(r"\bgmail\.users\.messages\.send\b", re.IGNORECASE),
    re.compile(r"\busers\.messages\.send\b", re.IGNORECASE),
    re.compile(r"\bgmail\.send\b", re.IGNORECASE),
    re.compile(r"\bme/sendMail\b", re.IGNORECASE),
    re.compile(r"(?<![A-Za-z_])sendMail(?![A-Za-z_])"),
    re.compile(r"\bme/messages/[^/\s]+?/send\b", re.IGNORECASE),
    re.compile(r"\boutlook\.send\b", re.IGNORECASE),
    re.compile(r"\bgraph\.sendMail\b", re.IGNORECASE),
    re.compile(r"\bsend_email\b", re.IGNORECASE),
    re.compile(r"\bsend_mail\b", re.IGNORECASE),
    re.compile(r"\bsend_message\b", re.IGNORECASE),
    re.compile(r"(?<![A-Za-z_])sendMessage(?![A-Za-z_])"),
    re.compile(r"\bdispatch_email\b", re.IGNORECASE),
    re.compile(r"\btransmit_email\b", re.IGNORECASE),
]

# Patterns that explicitly look like drafts/reads (used for context — NOT flagged)
DRAFT_INDICATORS = [
    re.compile(r"\bdrafts\.create\b", re.IGNORECASE),
    re.compile(r"\bSaveAsDraft\b"),
    re.compile(r"\bdrafts\.update\b", re.IGNORECASE),
    re.compile(r"\busers\.drafts\b", re.IGNORECASE),
]


SAMPLE_PASS_LOG = """# Triage Log — 2026-05-15 (Morning)

## Emails Processed (12)

- alice@example.com: classified Active Conversations
- bob@example.com: classified New Opportunities, recommendation TAKE IT
- newsletter@digest.com: skipped (low priority)

## Drafts Created (3)

- gmail.users.drafts.create -> draft_id=abc123 (alice@example.com thread)
- gmail.users.drafts.create -> draft_id=def456 (bob@example.com thread)
- gmail.users.drafts.create -> draft_id=ghi789 (carol@example.com thread)

## KB Updates

- blocklist.md: appended 1 new pattern
- tracker.md: marked 2 items resolved, added 1 new follow-up

## Notable Observations

- bob@example.com is from VIP list; auto-engaged per evaluation framework.
"""

SAMPLE_FAIL_LOG = """# Triage Log — 2026-05-15 (Morning)

## Emails Processed (12)

- alice@example.com: classified Active Conversations, response sent
- bob@example.com: classified New Opportunities

## Drafts Created (2)

- gmail.users.drafts.create -> draft_id=abc123
- gmail.users.drafts.create -> draft_id=def456

## Auto-replies sent

- gmail.users.messages.send -> message_id=xyz789 (alice@example.com auto-reply)

## KB Updates
- blocklist.md: appended 1 new pattern
"""


def scan_log(text: str) -> Dict[str, Any]:
    findings: List[Dict[str, Any]] = []
    draft_count = 0

    for line_no, line in enumerate(text.splitlines(), start=1):
        for pattern in SEND_PATTERNS:
            if pattern.search(line):
                findings.append({
                    "line": line_no,
                    "pattern": pattern.pattern,
                    "text": line.strip()[:200],
                })
        for pattern in DRAFT_INDICATORS:
            if pattern.search(line):
                draft_count += 1
                break

    verdict = "FAIL" if findings else "PASS"
    return {
        "verdict": verdict,
        "send_violations": findings,
        "send_violation_count": len(findings),
        "draft_indicator_count": draft_count,
    }


def render_human(result: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"Draft-safety verdict: {result['verdict']}")
    out.append(f"  Send-shape violations: {result['send_violation_count']}")
    out.append(f"  Draft indicators (informational): {result['draft_indicator_count']}")
    out.append("")
    if result["verdict"] == "PASS":
        out.append("[ok] No send-shape tool calls detected. NEVER-SEND discipline held.")
    else:
        out.append("[FAIL] Send-shape tool calls detected. NEVER-SEND discipline broke.")
        out.append("")
        out.append("Violations:")
        for f in result["send_violations"]:
            out.append(f"  L{f['line']:>4}  matched /{f['pattern']}/")
            out.append(f"          → {f['text']}")
        out.append("")
        out.append("ACTION REQUIRED:")
        out.append("  1. Verify whether the email was actually sent (check user's email Sent folder).")
        out.append("  2. If sent: alert user immediately; check recipient/content for severity.")
        out.append("  3. Investigate skill body — find which step invoked the send verb.")
        out.append("  4. Patch skill to use draft verb only; re-test.")
    return "\n".join(out)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--action-log", help="Path to a triage-log/<date>-<label>.md file")
    parser.add_argument("--sample-pass", action="store_true", help="Scan embedded clean log (should PASS)")
    parser.add_argument("--sample-fail", action="store_true", help="Scan embedded violation log (should FAIL)")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if args.sample_pass:
        text = SAMPLE_PASS_LOG
    elif args.sample_fail:
        text = SAMPLE_FAIL_LOG
    elif args.action_log:
        p = Path(args.action_log)
        if not p.exists():
            print(f"error: {args.action_log} not found", file=sys.stderr); return 2
        text = p.read_text(encoding="utf-8")
    else:
        parser.print_help(); return 0

    result = scan_log(text)
    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_human(result))
    return 0 if result["verdict"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
