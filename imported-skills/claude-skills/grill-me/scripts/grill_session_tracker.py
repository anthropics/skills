#!/usr/bin/env python3
"""grill_session_tracker.py — Track grill-me session state across turns.

Stdlib-only. JSON-backed session storage for the relentless interrogation pattern.
Tracks: questions asked, answers received, recommendations, decisions locked,
remaining branches. Persistence enables resume across sessions.

Storage: ~/.grill_sessions/<session_name>.json

Actions:
  - start <session_name>: initialize new session from plan doc
  - record <session_name> --question-id N --answer "text": record an answer
  - status <session_name>: show progress
  - list: list all sessions
  - close <session_name>: mark complete + summary

NO LLM CALLS. Stdlib only.

Usage:
    python grill_session_tracker.py --action list
    python grill_session_tracker.py --action start --session my-plan --plan path/to/plan.md
    python grill_session_tracker.py --action record --session my-plan --question-id 1 --answer "we chose X"
    python grill_session_tracker.py --action status --session my-plan
    python grill_session_tracker.py --action close --session my-plan
"""

import argparse
import json
import os
import sys
from datetime import datetime
from typing import Any, Dict, List

# Import question generator
_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)
from question_generator import analyze as analyze_plan, SAMPLE_PLAN  # noqa: E402


SESSIONS_DIR = os.path.expanduser("~/.grill_sessions")


def _ensure_dir() -> None:
    os.makedirs(SESSIONS_DIR, exist_ok=True)


def _session_path(name: str) -> str:
    return os.path.join(SESSIONS_DIR, f"{name}.json")


def _load(name: str) -> Dict[str, Any]:
    path = _session_path(name)
    if not os.path.isfile(path):
        return {}
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def _save(name: str, data: Dict[str, Any]) -> None:
    _ensure_dir()
    with open(_session_path(name), "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2)


def start_session(name: str, plan_path: str) -> Dict[str, Any]:
    if plan_path:
        with open(plan_path, "r", encoding="utf-8") as f:
            plan_text = f.read()
    else:
        plan_text = SAMPLE_PLAN
        plan_path = "<embedded sample>"

    plan_analysis = analyze_plan(plan_text)
    session = {
        "name": name,
        "started_at": datetime.now().isoformat(timespec="seconds"),
        "plan_source": plan_path,
        "total_questions": plan_analysis["total_questions"],
        "questions": plan_analysis["questions"],
        "answers": {},  # question_n -> {"answer": str, "recorded_at": iso}
        "status": "active",
    }
    _save(name, session)
    return session


def record_answer(name: str, qid: int, answer: str) -> Dict[str, Any]:
    session = _load(name)
    if not session:
        raise ValueError(f"Session not found: {name}")
    session["answers"][str(qid)] = {
        "answer": answer,
        "recorded_at": datetime.now().isoformat(timespec="seconds"),
    }
    _save(name, session)
    return session


def session_status(name: str) -> Dict[str, Any]:
    session = _load(name)
    if not session:
        return {"error": f"Session not found: {name}"}
    answered = len(session.get("answers", {}))
    total = session.get("total_questions", 0)
    pct = round(100.0 * answered / max(total, 1), 1)
    next_q = None
    for q in session.get("questions", []):
        if str(q["n"]) not in session.get("answers", {}):
            next_q = q
            break
    return {
        "name": session["name"],
        "status": session.get("status", "active"),
        "answered": answered,
        "total": total,
        "percent_complete": pct,
        "next_question": next_q,
        "all_answers": session.get("answers", {}),
    }


def list_sessions() -> List[str]:
    _ensure_dir()
    return sorted(
        os.path.splitext(f)[0]
        for f in os.listdir(SESSIONS_DIR)
        if f.endswith(".json")
    )


def close_session(name: str) -> Dict[str, Any]:
    session = _load(name)
    if not session:
        raise ValueError(f"Session not found: {name}")
    session["status"] = "closed"
    session["closed_at"] = datetime.now().isoformat(timespec="seconds")
    _save(name, session)
    return session


def render_status(r: Dict[str, Any]) -> str:
    if "error" in r:
        return f"ERROR: {r['error']}"
    lines = []
    lines.append("=" * 72)
    lines.append(f"GRILL SESSION: {r['name']}")
    lines.append("=" * 72)
    lines.append(f"Status: {r['status']}  ({r['answered']} / {r['total']} answered, {r['percent_complete']}%)")
    lines.append("")
    if r["next_question"]:
        q = r["next_question"]
        lines.append(f"Next question (Q{q['n']}):")
        lines.append(f"  {q['question']}")
        lines.append(f"  Recommended: {q['recommended']}")
    else:
        lines.append("All questions answered. Run --action close to mark session complete.")
    lines.append("")
    if r["all_answers"]:
        lines.append("Answered:")
        for qid, ans in sorted(r["all_answers"].items(), key=lambda x: int(x[0])):
            lines.append(f"  Q{qid}: {ans['answer'][:100]}")
    return "\n".join(lines)


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Track grill-me session state across turns.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    action_choices = ("start", "record", "status", "list", "close")
    parser.add_argument("--action", default="status", choices=action_choices, help="Session action")
    parser.add_argument("--session", help="Session name")
    parser.add_argument("--plan", default="", help="Path to plan markdown (start action)")
    parser.add_argument("--question-id", type=int, help="Question number to record")
    parser.add_argument("--answer", help="Answer text (record action)")
    parser.add_argument("--output", choices=("text", "json"), default="text", help="Output format")
    return parser


def _print_session_list(sessions: List[str], json_output: bool) -> None:
    if json_output:
        print(json.dumps({"sessions": sessions}, indent=2))
        return
    print("Sessions:")
    items = sessions or ["(none)"]
    for s in items:
        print(f"  - {s}")


def _print_start_summary(session: Dict[str, Any]) -> None:
    print(f"Started session: {session['name']}")
    print(f"  Plan: {session['plan_source']}")
    print(f"  Total questions: {session['total_questions']}")
    questions = session.get("questions") or []
    first = questions[0]["question"] if questions else "(none)"
    print(f"  First question: {first}")


def _action_list(args: argparse.Namespace) -> int:
    _print_session_list(list_sessions(), args.output == "json")
    return 0


def _action_start(args: argparse.Namespace) -> int:
    name = args.session or "sample-session"
    session = start_session(name, args.plan)
    if args.output == "json":
        print(json.dumps(session, indent=2))
    else:
        _print_start_summary(session)
    return 0


def _action_record(args: argparse.Namespace) -> int:
    if not args.session or args.question_id is None or not args.answer:
        print("error: record requires --session, --question-id, --answer", file=sys.stderr)
        return 1
    record_answer(args.session, args.question_id, args.answer)
    result = session_status(args.session)
    output = json.dumps(result, indent=2) if args.output == "json" else render_status(result)
    print(output)
    return 0


def _action_status(args: argparse.Namespace) -> int:
    name = args.session or "sample-session"
    result = session_status(name)
    output = json.dumps(result, indent=2) if args.output == "json" else render_status(result)
    print(output)
    return 0


def _action_close(args: argparse.Namespace) -> int:
    if not args.session:
        print("error: close requires --session", file=sys.stderr)
        return 1
    session = close_session(args.session)
    if args.output == "json":
        print(json.dumps(session, indent=2))
    else:
        print(f"Closed session: {args.session}")
    return 0


ACTION_DISPATCH = {
    "list": _action_list,
    "start": _action_start,
    "record": _action_record,
    "status": _action_status,
    "close": _action_close,
}


def main() -> int:
    args = _build_parser().parse_args()
    handler = ACTION_DISPATCH.get(args.action)
    if handler is None:
        return 0
    return handler(args)


if __name__ == "__main__":
    sys.exit(main())
