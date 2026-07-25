#!/usr/bin/env python3
"""section_progress_tracker.py — JSON-backed walk state for 8-section setup.

Stdlib-only. Tracks the setup interview state at ~/.inbox_setup_sessions/<session>.json
so the skill can:

  - Know which section is currently active
  - Record each question's answer
  - Mark each section as done with the file(s) it committed
  - Detect drop-off and produce useful partial state
  - Resume later if the user drops off mid-interview

Actions:
  start                 Create a new session
  record_q              Record an answer to a question
  record_section_done   Mark section complete with files committed
  status                Show current session state
  list                  List all sessions
  close                 Mark session ended

Usage:
    python section_progress_tracker.py --action start --session inbox-setup-20260515 --user alice
    python section_progress_tracker.py --action record_q --session ... --section 1 --question 1 --answer "Solo consultant"
    python section_progress_tracker.py --action record_section_done --session ... --section 2 --files "email-taxonomy.md"
    python section_progress_tracker.py --action status --session ...
    python section_progress_tracker.py --action list
    python section_progress_tracker.py --action close --session ...
"""

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional


SESSIONS_DIR = Path.home() / ".inbox_setup_sessions"
TOTAL_SECTIONS = 8


def session_path(name: str) -> Path:
    return SESSIONS_DIR / f"{name}.json"


def load_session(name: str) -> Dict[str, Any]:
    p = session_path(name)
    if not p.exists():
        raise FileNotFoundError(f"Session not found: {name}")
    return json.loads(p.read_text(encoding="utf-8"))


def save_session(name: str, data: Dict[str, Any]) -> None:
    SESSIONS_DIR.mkdir(parents=True, exist_ok=True)
    session_path(name).write_text(json.dumps(data, indent=2), encoding="utf-8")


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def action_start(name: str, user: Optional[str]) -> Dict[str, Any]:
    if session_path(name).exists():
        raise FileExistsError(f"Session already exists: {name}")
    data: Dict[str, Any] = {
        "session": name,
        "user": user or "(anonymous)",
        "started_at": now_iso(),
        "ended_at": None,
        "active_section": 1,
        "sections": {str(i): {"status": "pending", "questions_answered": [], "files_committed": []} for i in range(1, TOTAL_SECTIONS + 1)},
        "total_questions_answered": 0,
        "skip_log": [],
    }
    save_session(name, data)
    return data


def action_record_q(name: str, section: int, question: int, answer: str) -> Dict[str, Any]:
    data = load_session(name)
    key = str(section)
    if key not in data["sections"]:
        raise ValueError(f"Invalid section: {section}")
    sec = data["sections"][key]
    if sec["status"] == "pending":
        sec["status"] = "in_progress"
        sec["started_at"] = now_iso()
    sec["questions_answered"].append({
        "question": question,
        "answer": answer,
        "at": now_iso(),
    })
    data["total_questions_answered"] += 1
    data["active_section"] = section
    save_session(name, data)
    return data


def action_record_section_done(name: str, section: int, files: List[str]) -> Dict[str, Any]:
    data = load_session(name)
    key = str(section)
    if key not in data["sections"]:
        raise ValueError(f"Invalid section: {section}")
    sec = data["sections"][key]
    sec["status"] = "done"
    sec["files_committed"] = files
    sec["ended_at"] = now_iso()
    # Advance active section
    if section < TOTAL_SECTIONS:
        data["active_section"] = section + 1
    save_session(name, data)
    return data


def action_record_skip(name: str, section: int, reason: str) -> Dict[str, Any]:
    data = load_session(name)
    key = str(section)
    sec = data["sections"][key]
    sec["status"] = "skipped"
    sec["skip_reason"] = reason
    sec["ended_at"] = now_iso()
    data["skip_log"].append({"section": section, "reason": reason, "at": now_iso()})
    if section < TOTAL_SECTIONS:
        data["active_section"] = section + 1
    save_session(name, data)
    return data


def action_status(name: str) -> Dict[str, Any]:
    return load_session(name)


def action_close(name: str) -> Dict[str, Any]:
    data = load_session(name)
    if data.get("ended_at") is None:
        data["ended_at"] = now_iso()
        save_session(name, data)
    return data


def action_list() -> List[Dict[str, Any]]:
    SESSIONS_DIR.mkdir(parents=True, exist_ok=True)
    out: List[Dict[str, Any]] = []
    for p in sorted(SESSIONS_DIR.glob("*.json")):
        try:
            data = json.loads(p.read_text(encoding="utf-8"))
            done_sections = sum(1 for s in data["sections"].values() if s["status"] == "done")
            out.append({
                "session": data["session"],
                "user": data["user"],
                "started_at": data["started_at"],
                "ended_at": data["ended_at"],
                "active_section": data["active_section"],
                "done_sections": done_sections,
                "total_questions_answered": data["total_questions_answered"],
            })
        except (OSError, json.JSONDecodeError):
            continue
    return out


def render_status_human(data: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"Session:          {data['session']}")
    out.append(f"User:             {data['user']}")
    out.append(f"Started:          {data['started_at']}")
    out.append(f"Ended:            {data.get('ended_at') or '(active)'}")
    out.append(f"Active section:   {data['active_section']}/{TOTAL_SECTIONS}")
    out.append(f"Total Qs answered:{data['total_questions_answered']}")
    out.append("")
    out.append("Per-section state:")
    for key in sorted(data["sections"].keys(), key=lambda k: int(k)):
        sec = data["sections"][key]
        marker = {"pending": "  ", "in_progress": "↻ ", "done": "✓ ", "skipped": "→ "}.get(sec["status"], "  ")
        files = ", ".join(sec["files_committed"]) if sec["files_committed"] else "—"
        out.append(f"  {marker}S{key}: {sec['status']:<12s} ({len(sec['questions_answered'])} Q answered, files: {files})")
    if data["skip_log"]:
        out.append("")
        out.append("Skip log:")
        for s in data["skip_log"]:
            out.append(f"  S{s['section']}: {s['reason']}")
    return "\n".join(out)


def render_list_human(rows: List[Dict[str, Any]]) -> str:
    if not rows:
        return "(no sessions)"
    out: List[str] = []
    out.append(f"{'session':<40s}  {'user':<15s}  {'active':>6s}  {'done':>4s}  {'Q':>3s}  status")
    out.append("-" * 90)
    for r in rows:
        status = "closed" if r["ended_at"] else "active"
        out.append(
            f"{r['session']:<40s}  {r['user']:<15s}  {r['active_section']:>6d}  {r['done_sections']:>4d}  {r['total_questions_answered']:>3d}  {status}"
        )
    return "\n".join(out)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--action", required=True, choices=["start", "record_q", "record_section_done", "record_skip", "status", "list", "close"])
    parser.add_argument("--session", help="Session name")
    parser.add_argument("--user", help="(start only) user identifier")
    parser.add_argument("--section", type=int, help="Section number 1-8")
    parser.add_argument("--question", type=int, help="(record_q only) question number within section")
    parser.add_argument("--answer", help="(record_q only) answer text")
    parser.add_argument("--files", help="(record_section_done only) comma-separated filenames")
    parser.add_argument("--reason", help="(record_skip only) why section was skipped")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    try:
        if args.action == "start":
            if not args.session:
                print("error: --session required for start", file=sys.stderr); return 2
            result = action_start(args.session, args.user)
        elif args.action == "record_q":
            if not (args.session and args.section and args.question is not None and args.answer is not None):
                print("error: --session, --section, --question, --answer required", file=sys.stderr); return 2
            result = action_record_q(args.session, args.section, args.question, args.answer)
        elif args.action == "record_section_done":
            if not (args.session and args.section and args.files):
                print("error: --session, --section, --files required", file=sys.stderr); return 2
            files = [f.strip() for f in args.files.split(",") if f.strip()]
            result = action_record_section_done(args.session, args.section, files)
        elif args.action == "record_skip":
            if not (args.session and args.section and args.reason):
                print("error: --session, --section, --reason required", file=sys.stderr); return 2
            result = action_record_skip(args.session, args.section, args.reason)
        elif args.action == "status":
            if not args.session:
                print("error: --session required for status", file=sys.stderr); return 2
            result = action_status(args.session)
        elif args.action == "close":
            if not args.session:
                print("error: --session required for close", file=sys.stderr); return 2
            result = action_close(args.session)
        else:
            result = action_list()
    except (FileNotFoundError, FileExistsError, ValueError) as e:
        print(f"error: {e}", file=sys.stderr); return 2

    if args.output == "json":
        print(json.dumps(result, indent=2, default=str))
    else:
        if args.action == "list":
            print(render_list_human(result))
        else:
            print(render_status_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
