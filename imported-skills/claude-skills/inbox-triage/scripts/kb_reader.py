#!/usr/bin/env python3
"""kb_reader.py — Read + validate the 7-file KB at ${WORKSPACE}/Email/.

Stdlib-only. The triage skill's first step. Loads the 7-file knowledge base
written by inbox-setup, validates required files are present, parses out the
structured data triage needs, and FAILs fast if anything required is missing
or malformed.

Returns:
  - For each file: presence + parsed content
  - For required-core files (taxonomy, patterns, blocklist, tracker): MUST exist or FAIL
  - For optional-core files (evaluation-framework, rate-card): note presence
  - For triage-log/: must be a directory

Mirror of inbox-setup/scripts/kb_validator.py, but read-perspective + parses
the actual content (not just structure validation).

NO LLM CALLS. Pure filesystem + regex.

Usage:
    python kb_reader.py --workspace /path/to/workspace
    python kb_reader.py --workspace . --output json
    python kb_reader.py --sample
"""

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional


REQUIRED_CORE = ["email-taxonomy.md", "email-patterns.md", "blocklist.md", "tracker.md"]
OPTIONAL_CORE = ["evaluation-framework.md", "rate-card.md"]
LOG_DIR = "triage-log"


SAMPLE_KB: Dict[str, str] = {
    "email-taxonomy.md": (
        "# Email Taxonomy\n\n## Categories\n\n### New Opportunities\n"
        "- Signals: pitch / proposal / collab\n- Default action: classify + draft\n\n"
        "### Active Conversations\n- Signals: re: / threading\n- Default action: draft\n\n"
        "### Newsletters\n- Signals: unsubscribe / digest\n- Default action: skip\n\n"
        "## Report Preferences\n\n"
        "- Delivery format: email-draft-to-self\n- Detail level: 30-second-scan\n"
    ),
    "email-patterns.md": (
        "# Email Patterns\n\n## Voice Register\nCasual\n\n## Hard Rules\n"
        "- Never: emojis in client emails\n- Always: reply within 24h\n\n"
        "## Pet Peeves (Forbidden Tokens)\n- 'I hope this email finds you well'\n"
        "- 'circle back'\n\n## Sign-Offs (Voice Fingerprints)\n- '—Alex'\n- 'Best, Alex'\n\n"
        "## Voice Calibration Status\nSamples collected: 4 emails analyzed.\n"
    ),
    "blocklist.md": (
        "# Blocklist\n\n## Sender / Domain Auto-Skip\n"
        "- recruiter@*: cold outreach — added 2026-05-15\n\n"
        "## Decline Patterns\n- 'looking for backend engineers': cold recruiter\n\n"
        "## Recently Removed (User Overrode)\n"
    ),
    "tracker.md": (
        "# Tracker\n\n## Active Follow-Ups\n\n"
        "| Item | Context | Deadline | Status |\n|---|---|---|---|\n"
        "| Q3 contract | renewal due | 2026-06-15 | pending |\n\n## Overdue\n\n"
        "## Resolved (Recent)\n\n## Update Log\n"
    ),
    "evaluation-framework.md": (
        "# Evaluation Framework (Opportunity Emails)\n\n## Gut Filter\n"
        "Is the budget realistic for the scope?\n\n## TAKE-IT Signals\n- Clear budget stated\n"
        "- VIP sender\n\n## PASS Signals\n- Free / unpaid\n- Out-of-scope industry\n\n"
        "## VIP List\n- alice@example.com\n"
    ),
}


def load_file(workspace: Path, filename: str) -> Optional[Dict[str, Any]]:
    p = workspace / "Email" / filename
    if not p.exists() or not p.is_file():
        return None
    try:
        text = p.read_text(encoding="utf-8")
        return {
            "path": str(p),
            "size": p.stat().st_size,
            "text": text,
        }
    except OSError:
        return None


def extract_h1(text: str) -> Optional[str]:
    m = re.search(r"^#\s+(.+?)\s*$", text, re.MULTILINE)
    return m.group(1).strip() if m else None


def extract_section(text: str, header: str) -> Optional[str]:
    """Extract content between '## {header}' and the next '## ' (or EOF)."""
    pattern = rf"^##\s+{re.escape(header)}\s*\n(.*?)(?=^##\s|\Z)"
    m = re.search(pattern, text, re.MULTILINE | re.DOTALL)
    return m.group(1).strip() if m else None


def extract_h3_blocks(text: str, parent_section: str) -> List[Dict[str, str]]:
    """Inside parent_section, extract each `### {name}` block."""
    section_text = extract_section(text, parent_section)
    if not section_text:
        return []
    blocks: List[Dict[str, str]] = []
    pattern = re.compile(r"^###\s+(.+?)\s*\n(.*?)(?=^###\s|\Z)", re.MULTILINE | re.DOTALL)
    for m in pattern.finditer(section_text):
        blocks.append({
            "name": m.group(1).strip(),
            "body": m.group(2).strip(),
        })
    return blocks


def parse_taxonomy(text: str) -> Dict[str, Any]:
    return {
        "h1": extract_h1(text),
        "categories": extract_h3_blocks(text, "Categories"),
        "report_preferences": extract_section(text, "Report Preferences"),
    }


def parse_patterns(text: str) -> Dict[str, Any]:
    return {
        "h1": extract_h1(text),
        "voice_register": extract_section(text, "Voice Register"),
        "hard_rules": extract_section(text, "Hard Rules"),
        "pet_peeves": extract_section(text, "Pet Peeves (Forbidden Tokens)") or extract_section(text, "Pet Peeves"),
        "sign_offs": extract_section(text, "Sign-Offs (Voice Fingerprints)") or extract_section(text, "Sign-Offs"),
        "voice_patterns": extract_section(text, "Voice Patterns (Extracted from Samples)"),
        "calibration_status": extract_section(text, "Voice Calibration Status"),
    }


def parse_blocklist(text: str) -> Dict[str, Any]:
    return {
        "h1": extract_h1(text),
        "auto_skip": extract_section(text, "Sender / Domain Auto-Skip"),
        "decline_patterns": extract_section(text, "Decline Patterns"),
        "recently_removed": extract_section(text, "Recently Removed (User Overrode)"),
    }


def parse_tracker(text: str) -> Dict[str, Any]:
    return {
        "h1": extract_h1(text),
        "active_follow_ups": extract_section(text, "Active Follow-Ups"),
        "overdue": extract_section(text, "Overdue"),
        "resolved_recent": extract_section(text, "Resolved (Recent)"),
        "update_log": extract_section(text, "Update Log"),
    }


def parse_evaluation(text: str) -> Dict[str, Any]:
    return {
        "h1": extract_h1(text),
        "gut_filter": extract_section(text, "Gut Filter (First Check)") or extract_section(text, "Gut Filter"),
        "take_it_signals": extract_section(text, "TAKE-IT Signals"),
        "pass_signals": extract_section(text, "PASS Signals (Instant Deal-Breakers)") or extract_section(text, "PASS Signals"),
        "decision_tree": extract_section(text, "Decision Tree"),
        "vip_list": extract_section(text, "VIP List (Bypass PASS Filters)") or extract_section(text, "VIP List"),
        "negotiation_posture": extract_section(text, "Negotiation Posture"),
    }


def parse_rate_card(text: str) -> Dict[str, Any]:
    return {
        "h1": extract_h1(text),
        "standard_pricing": extract_section(text, "Standard Pricing"),
        "terms": extract_section(text, "Terms"),
        "negotiation_posture": extract_section(text, "Negotiation Posture"),
        "counter_offer_patterns": extract_section(text, "Counter-Offer Patterns"),
    }


def read_kb(workspace: Path) -> Dict[str, Any]:
    issues: List[Dict[str, str]] = []

    def add_issue(level: str, message: str) -> None:
        issues.append({"level": level, "message": message})

    email_dir = workspace / "Email"
    if not email_dir.exists():
        add_issue("FAIL", f"{email_dir} does not exist. Run /cs:inbox-setup first.")
        return {"verdict": "FAIL", "issues": issues, "files": {}}

    files: Dict[str, Any] = {}

    # Required core
    for fn in REQUIRED_CORE:
        loaded = load_file(workspace, fn)
        if loaded is None:
            add_issue("FAIL", f"Required core file missing: Email/{fn}. Run /cs:inbox-setup first.")
            files[fn] = {"present": False}
            continue
        if loaded["size"] == 0:
            add_issue("FAIL", f"Required core file is empty: Email/{fn}.")
            files[fn] = {"present": True, "size": 0}
            continue
        files[fn] = {"present": True, "size": loaded["size"], "path": loaded["path"]}
        text = loaded["text"]
        if fn == "email-taxonomy.md":
            files[fn]["parsed"] = parse_taxonomy(text)
        elif fn == "email-patterns.md":
            files[fn]["parsed"] = parse_patterns(text)
        elif fn == "blocklist.md":
            files[fn]["parsed"] = parse_blocklist(text)
        elif fn == "tracker.md":
            files[fn]["parsed"] = parse_tracker(text)

    # Optional core
    for fn in OPTIONAL_CORE:
        loaded = load_file(workspace, fn)
        if loaded is None:
            files[fn] = {"present": False}
            continue
        files[fn] = {"present": True, "size": loaded["size"], "path": loaded["path"]}
        text = loaded["text"]
        if fn == "evaluation-framework.md":
            files[fn]["parsed"] = parse_evaluation(text)
        elif fn == "rate-card.md":
            files[fn]["parsed"] = parse_rate_card(text)

    # triage-log/ directory
    triage_log = email_dir / LOG_DIR
    if not triage_log.exists():
        add_issue("FAIL", f"Email/{LOG_DIR}/ missing. Run /cs:inbox-setup first.")
        files[LOG_DIR] = {"present": False}
    elif not triage_log.is_dir():
        add_issue("FAIL", f"Email/{LOG_DIR} exists but is not a directory.")
        files[LOG_DIR] = {"present": False, "error": "not a directory"}
    else:
        files[LOG_DIR] = {"present": True, "is_directory": True, "log_count": len(list(triage_log.glob("*.md")))}

    fail_count = sum(1 for i in issues if i["level"] == "FAIL")
    verdict = "FAIL" if fail_count > 0 else "PASS"

    return {"verdict": verdict, "issues": issues, "files": files}


def render_human(result: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"KB read verdict: {result['verdict']}")
    out.append("")
    out.append("Files:")
    for fn, info in result["files"].items():
        if not info.get("present"):
            out.append(f"  [missing] {fn}")
        elif fn == LOG_DIR:
            out.append(f"  [ok]      {fn}/  ({info.get('log_count', 0)} log files)")
        else:
            out.append(f"  [ok]      {fn}  ({info['size']} bytes)")
    if result["issues"]:
        out.append("")
        out.append("Issues:")
        for i in result["issues"]:
            out.append(f"  [{i['level']}] {i['message']}")
    if result["verdict"] == "PASS":
        out.append("")
        out.append("KB ready for triage. Parsed structure available via --output json.")
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
        return read_kb(ws)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--workspace", help="Path to workspace (looks at <workspace>/Email/)")
    parser.add_argument("--sample", action="store_true", help="Read embedded sample KB")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if args.sample:
        result = run_sample()
    elif args.workspace:
        ws = Path(args.workspace)
        if not ws.exists():
            print(f"error: {args.workspace} not found", file=sys.stderr); return 2
        result = read_kb(ws)
    else:
        parser.print_help(); return 0

    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_human(result))
    return 0 if result["verdict"] != "FAIL" else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
