#!/usr/bin/env python3
"""
routing_transparency_logger.py — JSON-backed audit log for the research orchestrator.

Records every routing decision, override, and delegation handoff to a
per-session JSON file at ~/.research_sessions/<session>.json. Stdlib only.

Schema:
  {
    "session": "<name>",
    "created_at": "<iso8601>",
    "events": [
      {"at": "<iso8601>", "type": "decision",   "question": "...", "route_to": "...", "confidence": "...", "matched": {...}},
      {"at": "<iso8601>", "type": "override",   "from": "...", "to": "...", "reason": "..."},
      {"at": "<iso8601>", "type": "delegation", "target": "...", "signals": "..."}
    ]
  }

Usage:
  python routing_transparency_logger.py --action record_decision --session demo --question "..." --route-to litreview --confidence "high (2 signals)"
  python routing_transparency_logger.py --action record_override --session demo --from litreview --to fallback --reason "wanted general scope"
  python routing_transparency_logger.py --action record_delegation --session demo --target litreview --signals "pico,meta-analysis"
  python routing_transparency_logger.py --action read --session demo
  python routing_transparency_logger.py --sample
"""

import argparse
import json
import os
import sys
from datetime import datetime, timezone
from pathlib import Path


def _now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _session_path(session: str) -> Path:
    base = Path.home() / ".research_sessions"
    base.mkdir(parents=True, exist_ok=True)
    safe = "".join(c if c.isalnum() or c in ("-", "_") else "_" for c in session)
    return base / f"{safe}.json"


def _load(session: str) -> dict:
    path = _session_path(session)
    if not path.exists():
        return {"session": session, "created_at": _now(), "events": []}
    return json.loads(path.read_text(encoding="utf-8"))


def _save(session: str, data: dict) -> Path:
    path = _session_path(session)
    path.write_text(json.dumps(data, indent=2), encoding="utf-8")
    return path


def record_decision(session: str, question: str, route_to: str, confidence: str,
                    matched: dict | None = None) -> dict:
    data = _load(session)
    event = {
        "at": _now(),
        "type": "decision",
        "question": question,
        "route_to": route_to,
        "confidence": confidence,
        "matched": matched or {},
    }
    data["events"].append(event)
    _save(session, data)
    return event


def record_override(session: str, from_target: str, to_target: str, reason: str) -> dict:
    data = _load(session)
    event = {
        "at": _now(),
        "type": "override",
        "from": from_target,
        "to": to_target,
        "reason": reason,
    }
    data["events"].append(event)
    _save(session, data)
    return event


def record_delegation(session: str, target: str, signals: str) -> dict:
    data = _load(session)
    event = {
        "at": _now(),
        "type": "delegation",
        "target": target,
        "signals": signals,
    }
    data["events"].append(event)
    _save(session, data)
    return event


def read(session: str) -> dict:
    return _load(session)


def render_human(result: dict) -> str:
    if "events" in result:
        lines = [
            f"Session: {result['session']}",
            f"Created: {result['created_at']}",
            f"Events ({len(result['events'])}):",
        ]
        for e in result["events"]:
            t = e.get("type")
            if t == "decision":
                lines.append(f"  [{e['at']}] decision → {e['route_to']} ({e['confidence']})")
            elif t == "override":
                lines.append(f"  [{e['at']}] override {e['from']} → {e['to']} ({e['reason']})")
            elif t == "delegation":
                lines.append(f"  [{e['at']}] delegation → {e['target']} (signals: {e['signals']})")
            else:
                lines.append(f"  [{e['at']}] {t}: {e}")
        return "\n".join(lines)
    return json.dumps(result, indent=2)


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--action",
                   choices=["record_decision", "record_override", "record_delegation", "read"],
                   help="What to do.")
    p.add_argument("--session", help="Session name (used as filename stem).")
    p.add_argument("--question", help="(record_decision) The classified question.")
    p.add_argument("--route-to", dest="route_to", help="(record_decision) Routing target.")
    p.add_argument("--confidence", help="(record_decision) Confidence string.")
    p.add_argument("--matched", help="(record_decision) Matched signals (JSON).")
    p.add_argument("--from", dest="from_target", help="(record_override) Previous target.")
    p.add_argument("--to", dest="to_target", help="(record_override) New target.")
    p.add_argument("--reason", help="(record_override) Why user overrode.")
    p.add_argument("--target", help="(record_delegation) Specialist target.")
    p.add_argument("--signals", help="(record_delegation) Signals that matched.")
    p.add_argument("--output", choices=["human", "json"], default="human")
    p.add_argument("--sample", action="store_true", help="Run a built-in 4-event sample sequence.")
    args = p.parse_args()

    if args.sample:
        session = "sample"
        path = _session_path(session)
        if path.exists():
            path.unlink()
        record_decision(session,
                        "Can you review the literature on PICO for sepsis?",
                        "litreview",
                        "high (2 signals)",
                        {"litreview": ["pico", "literature"]})
        record_delegation(session, "litreview", "pico,literature")
        record_decision(session,
                        "What's the buzz about Anthropic on HN?",
                        "pulse",
                        "high (2 signals)",
                        {"pulse": ["hn", "buzz"]})
        record_override(session, "pulse", "fallback", "wanted general scope")
        result = read(session)
        if args.output == "json":
            print(json.dumps(result, indent=2))
        else:
            print(render_human(result))
        return

    if not args.action:
        p.error("--action is required (unless --sample)")
    if not args.session:
        p.error("--session is required")

    if args.action == "record_decision":
        if not (args.question and args.route_to and args.confidence):
            p.error("record_decision requires --question, --route-to, --confidence")
        matched = json.loads(args.matched) if args.matched else None
        out = record_decision(args.session, args.question, args.route_to, args.confidence, matched)
    elif args.action == "record_override":
        if not (args.from_target and args.to_target and args.reason):
            p.error("record_override requires --from, --to, --reason")
        out = record_override(args.session, args.from_target, args.to_target, args.reason)
    elif args.action == "record_delegation":
        if not (args.target and args.signals):
            p.error("record_delegation requires --target, --signals")
        out = record_delegation(args.session, args.target, args.signals)
    elif args.action == "read":
        out = read(args.session)
    else:
        p.error(f"unknown action {args.action}")

    if args.output == "json":
        print(json.dumps(out, indent=2))
    else:
        print(render_human(out))


if __name__ == "__main__":
    main()
