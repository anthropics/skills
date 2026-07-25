#!/usr/bin/env python3
"""kb_validator.py — Validate the 7-file KB contract at ${WORKSPACE}/Email/.

Stdlib-only. Confirms the inbox-setup skill produced the files inbox-triage
expects to read on every run. Used at end of Section 8 (Confirmation & Handoff)
and any time the user wants to spot-check the KB state.

Checks (per `references/kb_file_contract.md`):

  1. Required core files exist:
       - email-taxonomy.md
       - email-patterns.md
       - blocklist.md
       - tracker.md
  2. triage-log/ exists as a DIRECTORY (not a file)
  3. Conditional files exist iff their triggering section ran:
       - evaluation-framework.md (only if opportunity emails category)
       - rate-card.md (only if user has pricing)
  4. Each required file has an H1 header
  5. email-taxonomy.md has both "## Categories" + "## Report Preferences"
  6. email-patterns.md has "## Voice Calibration Status" (samples collected or not)

Output: PASS / WARN / FAIL per rule + overall verdict.

NO LLM CALLS. Pure filesystem + regex.

Usage:
    python kb_validator.py --workspace /path/to/workspace
    python kb_validator.py --workspace . --expect-evaluation --expect-rate-card
    python kb_validator.py --sample
"""

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional


CORE_REQUIRED = ["email-taxonomy.md", "email-patterns.md", "blocklist.md", "tracker.md"]
CONDITIONAL = ["evaluation-framework.md", "rate-card.md"]
LOG_DIR = "triage-log"


SAMPLE_KB: Dict[str, str] = {
    "email-taxonomy.md": (
        "# Email Taxonomy\n\n## Categories\n\n### New Opportunities\n"
        "- Signals: pitch / proposal / collab\n- Default action: classify + draft\n\n"
        "### Newsletters\n- Signals: unsubscribe / newsletter / digest\n"
        "- Default action: skip\n\n## Report Preferences\n\n"
        "- Delivery format: email-draft-to-self\n- Detail level: 30-second-scan\n"
    ),
    "email-patterns.md": (
        "# Email Patterns\n\n## Voice Register\nCasual\n\n## Hard Rules\n"
        "- Never: emojis in client emails\n- Always: reply within 24h\n\n"
        "## Voice Calibration Status\nSamples collected: 4 emails analyzed.\n"
    ),
    "blocklist.md": (
        "# Blocklist\n\n## Sender / Domain Auto-Skip\n"
        "- recruiter@*: cold outreach — added 2026-05-15\n\n"
        "## Decline Patterns\n- 'looking for backend engineers': cold recruiter\n"
    ),
    "tracker.md": (
        "# Tracker\n\n## Active Follow-Ups\n\n"
        "| Item | Context | Deadline | Status |\n|---|---|---|---|\n"
        "| Q3 contract | renewal due | 2026-06-15 | pending |\n\n## Overdue\n\n"
        "## Resolved (Recent)\n\n## Update Log\n"
    ),
    "evaluation-framework.md": (
        "# Evaluation Framework (Opportunity Emails)\n\n## Gut Filter (First Check)\n"
        "Is the budget realistic for the scope?\n\n## TAKE-IT Signals\n- Clear budget stated\n"
        "- VIP sender\n- Aligned to stated focus\n\n## PASS Signals (Instant Deal-Breakers)\n"
        "- Free / unpaid\n- Equity-only\n- Out-of-scope industry\n"
    ),
}


def check_file(workspace: Path, filename: str) -> Dict[str, Any]:
    p = workspace / "Email" / filename
    return {
        "filename": filename,
        "exists": p.exists() and p.is_file(),
        "path": str(p),
        "size": p.stat().st_size if p.exists() and p.is_file() else 0,
    }


def check_h1(workspace: Path, filename: str) -> Optional[str]:
    p = workspace / "Email" / filename
    if not p.exists() or not p.is_file():
        return None
    try:
        for line in p.read_text(encoding="utf-8").splitlines():
            m = re.match(r"^#\s+(.+?)\s*$", line)
            if m:
                return m.group(1).strip()
        return None
    except OSError:
        return None


def has_section(workspace: Path, filename: str, section_header: str) -> bool:
    p = workspace / "Email" / filename
    if not p.exists() or not p.is_file():
        return False
    try:
        text = p.read_text(encoding="utf-8")
        return bool(re.search(rf"^##\s+{re.escape(section_header)}\s*$", text, re.MULTILINE))
    except OSError:
        return False


def validate(
    workspace: Path,
    expect_evaluation: bool = False,
    expect_rate_card: bool = False,
) -> Dict[str, Any]:
    findings: List[Dict[str, str]] = []

    def add(rule: str, level: str, message: str) -> None:
        findings.append({"rule": rule, "level": level, "message": message})

    email_dir = workspace / "Email"
    if not email_dir.exists():
        add("workspace-email-dir", "FAIL", f"{email_dir} does not exist. Run inbox-setup first.")
        return finalize(findings)
    if not email_dir.is_dir():
        add("workspace-email-dir", "FAIL", f"{email_dir} is not a directory.")
        return finalize(findings)
    add("workspace-email-dir", "PASS", f"{email_dir} exists.")

    # Core required files
    for fn in CORE_REQUIRED:
        info = check_file(workspace, fn)
        if not info["exists"]:
            add(f"core-file:{fn}", "FAIL", f"Required file missing: Email/{fn}")
        elif info["size"] == 0:
            add(f"core-file:{fn}", "FAIL", f"Required file is empty: Email/{fn}")
        else:
            add(f"core-file:{fn}", "PASS", f"Email/{fn} present ({info['size']} bytes).")

    # H1 check on core files that exist
    for fn in CORE_REQUIRED:
        if not (workspace / "Email" / fn).exists():
            continue
        h1 = check_h1(workspace, fn)
        if h1:
            add(f"h1:{fn}", "PASS", f"Email/{fn} H1: '{h1}'")
        else:
            add(f"h1:{fn}", "FAIL", f"Email/{fn} has no H1.")

    # email-taxonomy.md must have both required subsections
    if (workspace / "Email" / "email-taxonomy.md").exists():
        if has_section(workspace, "email-taxonomy.md", "Categories"):
            add("taxonomy-categories", "PASS", "email-taxonomy.md has '## Categories' section.")
        else:
            add("taxonomy-categories", "FAIL", "email-taxonomy.md missing '## Categories' section.")
        if has_section(workspace, "email-taxonomy.md", "Report Preferences"):
            add("taxonomy-report-prefs", "PASS", "email-taxonomy.md has '## Report Preferences' section.")
        else:
            add("taxonomy-report-prefs", "WARN", "email-taxonomy.md missing '## Report Preferences' section (added at end of S7).")

    # email-patterns.md must have Voice Calibration Status
    if (workspace / "Email" / "email-patterns.md").exists():
        if has_section(workspace, "email-patterns.md", "Voice Calibration Status"):
            add("patterns-calibration", "PASS", "email-patterns.md has '## Voice Calibration Status' section.")
        else:
            add("patterns-calibration", "WARN", "email-patterns.md missing '## Voice Calibration Status' section (states whether samples were collected).")

    # Conditional files
    for fn in CONDITIONAL:
        info = check_file(workspace, fn)
        expect = (fn == "evaluation-framework.md" and expect_evaluation) or (fn == "rate-card.md" and expect_rate_card)
        if expect and not info["exists"]:
            add(f"conditional-file:{fn}", "FAIL", f"Expected (per --expect flag) but missing: Email/{fn}")
        elif not expect and info["exists"]:
            add(f"conditional-file:{fn}", "WARN", f"Email/{fn} exists but neither --expect-evaluation nor --expect-rate-card was set (may be stale from earlier setup).")
        elif expect and info["exists"]:
            add(f"conditional-file:{fn}", "PASS", f"Email/{fn} present (expected).")
        else:
            add(f"conditional-file:{fn}", "PASS", f"Email/{fn} correctly absent (not expected).")

    # triage-log/ must be a directory
    triage_log = workspace / "Email" / LOG_DIR
    if not triage_log.exists():
        add("triage-log-dir", "FAIL", f"Email/{LOG_DIR}/ missing. Must be created as empty directory at end of S6.")
    elif not triage_log.is_dir():
        add("triage-log-dir", "FAIL", f"Email/{LOG_DIR} exists but is not a directory.")
    else:
        add("triage-log-dir", "PASS", f"Email/{LOG_DIR}/ exists as directory.")

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


def render_human(result: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"KB contract verdict: {result['verdict']}")
    counts = result["counts"]
    out.append(f"  PASS: {counts['PASS']}  WARN: {counts['WARN']}  FAIL: {counts['FAIL']}")
    out.append("")
    out.append("Findings:")
    for f in result["findings"]:
        marker = {"PASS": "[ok]", "WARN": "[warn]", "FAIL": "[FAIL]"}[f["level"]]
        out.append(f"  {marker} {f['rule']}: {f['message']}")
    return "\n".join(out)


def run_sample() -> Dict[str, Any]:
    import tempfile
    with tempfile.TemporaryDirectory() as td:
        ws = Path(td)
        email_dir = ws / "Email"
        email_dir.mkdir(parents=True)
        for name, content in SAMPLE_KB.items():
            (email_dir / name).write_text(content, encoding="utf-8")
        (email_dir / LOG_DIR).mkdir()
        return validate(ws, expect_evaluation=True, expect_rate_card=False)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--workspace", help="Path to workspace (looks at <workspace>/Email/)")
    parser.add_argument("--expect-evaluation", action="store_true", help="Expect evaluation-framework.md to exist")
    parser.add_argument("--expect-rate-card", action="store_true", help="Expect rate-card.md to exist")
    parser.add_argument("--sample", action="store_true", help="Run on embedded sample KB")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if args.sample:
        result = run_sample()
    elif args.workspace:
        ws = Path(args.workspace)
        if not ws.exists():
            print(f"error: {args.workspace} not found", file=sys.stderr)
            return 2
        result = validate(ws, args.expect_evaluation, args.expect_rate_card)
    else:
        parser.print_help()
        return 0

    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_human(result))
    return 0 if result["verdict"] != "FAIL" else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
