#!/usr/bin/env python3
"""handoff_template_generator.py — Generate a handoff document scaffold tailored to next-session focus.

Stdlib-only. Outputs a markdown skeleton matching Matt Pocock's handoff structure:
  - Goal of next session
  - State of play
  - Open decisions
  - Skills to use
  - Artifacts (references only — NO duplication of content)

The "next focus" argument tailors which sections get emphasized + which prompts
are included as placeholder hints.

NO LLM CALLS. Stdlib only. Templating + sectional emphasis only.

Usage:
    python handoff_template_generator.py                                   # uses embedded sample
    python handoff_template_generator.py --next-focus "ship PR to dev"
    python handoff_template_generator.py --next-focus "debug auth" --output json
    python handoff_template_generator.py --next-focus "review CI failures" --out /tmp/handoff-XXX.md
"""

import argparse
import json
import os
import sys
import tempfile
from datetime import datetime
from typing import Any, Dict


# Tag focuses to section emphasis
FOCUS_EMPHASIS = [
    ("ship", "deployment_emphasis"),
    ("deploy", "deployment_emphasis"),
    ("pr", "deployment_emphasis"),
    ("review", "review_emphasis"),
    ("audit", "review_emphasis"),
    ("debug", "debug_emphasis"),
    ("fix", "debug_emphasis"),
    ("investigate", "debug_emphasis"),
    ("design", "design_emphasis"),
    ("plan", "design_emphasis"),
    ("scope", "design_emphasis"),
    ("test", "test_emphasis"),
    ("qa", "test_emphasis"),
]


SECTION_PROMPTS = {
    "deployment_emphasis": [
        "What's the exact command to ship? `git push` + `mcp__github__create_pull_request`?",
        "Which checks must be green before merge?",
        "Who needs to approve?",
        "What's the rollback plan if CI catches something?",
    ],
    "review_emphasis": [
        "What's the review checklist for this PR?",
        "Which files are sensitive (security/secrets)?",
        "Where are existing similar patterns?",
        "What past PRs reviewed this code path?",
    ],
    "debug_emphasis": [
        "What's the exact symptom + reproduction steps?",
        "What's been tried already?",
        "Which logs / traces are most informative?",
        "What's the smallest reproducing case?",
    ],
    "design_emphasis": [
        "What's the user-facing outcome the design must achieve?",
        "What's the non-negotiable constraint?",
        "What are the rejected alternatives + why?",
        "What's reversible vs irreversible in this design?",
    ],
    "test_emphasis": [
        "What's the test plan?",
        "Which existing tests cover this?",
        "Where are edge cases hiding?",
        "How is success measured?",
    ],
    "default": [
        "What's the immediate next action?",
        "What's blocking right now?",
        "Where are the relevant files?",
        "What decisions are still open?",
    ],
}


def _detect_emphasis(focus: str) -> str:
    if not focus:
        return "default"
    focus_lower = focus.lower()
    for keyword, emphasis in FOCUS_EMPHASIS:
        if keyword in focus_lower:
            return emphasis
    return "default"


def generate_template(next_focus: str, session_id: str = "") -> str:
    emphasis = _detect_emphasis(next_focus)
    prompts = SECTION_PROMPTS.get(emphasis, SECTION_PROMPTS["default"])
    timestamp = datetime.now().isoformat(timespec="seconds")
    session_label = session_id or "<session_id>"

    lines = []
    lines.append(f"# Handoff — {next_focus or '(general)'}")
    lines.append("")
    lines.append(f"**Generated:** {timestamp}")
    lines.append(f"**From session:** {session_label}")
    lines.append(f"**Next focus:** {next_focus or '(unspecified — fill in)'}")
    lines.append("")
    lines.append("---")
    lines.append("")
    lines.append("## Goal of next session")
    lines.append("")
    lines.append(f"[Describe what the next session must accomplish. Tailored to: {next_focus or 'general'}]")
    lines.append("")
    lines.append("Prompts to answer:")
    for p in prompts:
        lines.append(f"- {p}")
    lines.append("")
    lines.append("## State of play")
    lines.append("")
    lines.append("**Done:**")
    lines.append("- [list what's complete with paths/refs to artifacts]")
    lines.append("")
    lines.append("**In progress:**")
    lines.append("- [list what's mid-flight + current branch/PR if applicable]")
    lines.append("")
    lines.append("**Blocking:**")
    lines.append("- [list blockers + who/what unblocks each]")
    lines.append("")
    lines.append("## Open decisions")
    lines.append("")
    lines.append("- [Decision 1: options + current lean]")
    lines.append("- [Decision 2: options + current lean]")
    lines.append("")
    lines.append("## Skills to use (next session)")
    lines.append("")
    lines.append("- [Skill 1 — when to invoke]")
    lines.append("- [Skill 2 — when to invoke]")
    lines.append("")
    lines.append("## Artifacts (reference only — do NOT duplicate)")
    lines.append("")
    lines.append("- **PRD/Plan:** [path or URL]")
    lines.append("- **ADRs:** [path]")
    lines.append("- **Issues:** [#nnn]")
    lines.append("- **Branch:** [name]")
    lines.append("- **Open PRs:** [#nnn]")
    lines.append("- **Recent commits:** [paths or SHAs]")
    lines.append("- **Validators/tests run:** [results]")
    lines.append("")
    lines.append("---")
    lines.append("")
    lines.append("**Rule:** This document references existing artifacts. If you find yourself duplicating content from a PRD/plan/issue, replace it with a path/URL instead.")
    return "\n".join(lines)


def analyze(next_focus: str, session_id: str = "") -> Dict[str, Any]:
    emphasis = _detect_emphasis(next_focus)
    template = generate_template(next_focus, session_id)
    return {
        "next_focus": next_focus,
        "emphasis_detected": emphasis,
        "session_id": session_id,
        "template_length_chars": len(template),
        "template_length_lines": template.count("\n") + 1,
        "template": template,
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Generate a handoff document template per Matt Pocock's structure.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("--next-focus", default="", help="Description of what the next session will focus on")
    parser.add_argument("--session-id", default="", help="Optional session ID for traceability")
    parser.add_argument("--out", help="Write template to file (default: stdout)")
    parser.add_argument("--mktemp", action="store_true", help="Write to a mktemp-style file (handoff-XXXXXX.md)")
    parser.add_argument("--output", choices=("text", "json"), default="text", help="Output format")
    args = parser.parse_args()

    if not args.next_focus:
        args.next_focus = "(embedded sample: continue Stream B Matt Pocock skills batch)"
        args.session_id = args.session_id or "sample-session-001"

    result = analyze(args.next_focus, args.session_id)

    if args.mktemp:
        fd, path = tempfile.mkstemp(prefix="handoff-", suffix=".md", text=True)
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            f.write(result["template"])
        result["written_to"] = path

    if args.out:
        with open(args.out, "w", encoding="utf-8") as f:
            f.write(result["template"])
        result["written_to"] = args.out

    if args.output == "json":
        print(json.dumps({k: v for k, v in result.items() if k != "template"} | {"template_preview": result["template"][:500]}, indent=2))
    else:
        if "written_to" in result:
            print(f"Wrote handoff template to: {result['written_to']}")
            print(f"  Focus: {result['next_focus']}")
            print(f"  Emphasis: {result['emphasis_detected']}")
            print(f"  Length: {result['template_length_lines']} lines")
        else:
            print(result["template"])
    return 0


if __name__ == "__main__":
    sys.exit(main())
