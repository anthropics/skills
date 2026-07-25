#!/usr/bin/env python3
"""citation_tracker.py — JSON-backed three-count audit log for pulse runs.

Stdlib-only. Maintains the research-pack convention's three counts:

  - queries sent     (every tool call issued)
  - sources received (every item returned across all queries)
  - sources cited    (every URL that made it into the final synthesis)

Session state persists in ~/.pulse_sessions/<session>.json so runs can be
inspected and resumed.

NO LLM CALLS. Pure JSON I/O + counters.

Actions:
  start             Create a new session file
  record_sent       Increment sent count + log the query
  record_received   Increment received count by N
  record_cited      Increment cited count + log the URL
  status            Show current counts + audit summary block
  list              List existing sessions
  close             Finalize the session (set ended_at timestamp)

Usage:
    python citation_tracker.py --action start --session pulse-2026-05-15-claude-code --topic "Claude Code adoption"
    python citation_tracker.py --action record_sent --session pulse-... --query "claude code adoption" --platform reddit
    python citation_tracker.py --action record_received --session pulse-... --count 12 --platform reddit
    python citation_tracker.py --action record_cited --session pulse-... --url "https://reddit.com/..." --platform reddit
    python citation_tracker.py --action status --session pulse-...
    python citation_tracker.py --action list
    python citation_tracker.py --action close --session pulse-...
"""

import argparse
import json
import os
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional


SESSIONS_DIR = Path.home() / ".pulse_sessions"


def session_path(name: str) -> Path:
    return SESSIONS_DIR / f"{name}.json"


def load_session(name: str) -> Dict[str, Any]:
    p = session_path(name)
    if not p.exists():
        raise FileNotFoundError(f"Session not found: {name} (looked at {p})")
    return json.loads(p.read_text(encoding="utf-8"))


def save_session(name: str, data: Dict[str, Any]) -> None:
    SESSIONS_DIR.mkdir(parents=True, exist_ok=True)
    session_path(name).write_text(json.dumps(data, indent=2), encoding="utf-8")


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def action_start(name: str, topic: Optional[str]) -> Dict[str, Any]:
    if session_path(name).exists():
        raise FileExistsError(f"Session already exists: {name}")
    data: Dict[str, Any] = {
        "session": name,
        "topic": topic or "",
        "started_at": now_iso(),
        "ended_at": None,
        "queries_sent": [],
        "sources_received": [],
        "sources_cited": [],
        "counts": {"sent": 0, "received": 0, "cited": 0},
    }
    save_session(name, data)
    return data


def action_record_sent(name: str, query: str, platform: str) -> Dict[str, Any]:
    data = load_session(name)
    data["queries_sent"].append({"query": query, "platform": platform, "at": now_iso()})
    data["counts"]["sent"] += 1
    save_session(name, data)
    return data


def action_record_received(name: str, count: int, platform: str) -> Dict[str, Any]:
    data = load_session(name)
    data["sources_received"].append({"count": count, "platform": platform, "at": now_iso()})
    data["counts"]["received"] += count
    save_session(name, data)
    return data


def action_record_cited(name: str, url: str, platform: str) -> Dict[str, Any]:
    data = load_session(name)
    data["sources_cited"].append({"url": url, "platform": platform, "at": now_iso()})
    data["counts"]["cited"] += 1
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
            out.append({
                "session": data.get("session", p.stem),
                "topic": data.get("topic", ""),
                "started_at": data.get("started_at", ""),
                "ended_at": data.get("ended_at"),
                "counts": data.get("counts", {}),
            })
        except (OSError, json.JSONDecodeError):
            continue
    return out


def render_status_human(data: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"Session:        {data['session']}")
    out.append(f"Topic:          {data.get('topic', '(unset)')}")
    out.append(f"Started:        {data['started_at']}")
    out.append(f"Ended:          {data.get('ended_at') or '(active)'}")
    out.append("")
    out.append("Three-count audit:")
    c = data["counts"]
    out.append(f"  Sent:         {c['sent']}")
    out.append(f"  Received:     {c['received']}")
    out.append(f"  Cited:        {c['cited']}")
    out.append("")
    # Per-platform breakdown
    by_platform_sent: Dict[str, int] = {}
    for q in data["queries_sent"]:
        by_platform_sent[q["platform"]] = by_platform_sent.get(q["platform"], 0) + 1
    if by_platform_sent:
        out.append("Sent by platform:")
        for plat, n in sorted(by_platform_sent.items(), key=lambda kv: -kv[1]):
            out.append(f"  {plat:<10s} {n}")
    out.append("")
    out.append("Audit block (paste in synthesis):")
    parts: List[str] = []
    for plat, n in sorted(by_platform_sent.items(), key=lambda kv: -kv[1]):
        parts.append(f"{plat}: {n}")
    breakdown = " (" + ", ".join(parts) + ")" if parts else ""
    out.append(
        f"  *Audit:* Queries sent: {c['sent']}{breakdown}. "
        f"Sources received: {c['received']}. Sources cited: {c['cited']}. "
        f"Training knowledge: 0 ([Background] excluded from count)."
    )
    return "\n".join(out)


def render_list_human(rows: List[Dict[str, Any]]) -> str:
    if not rows:
        return "(no sessions found)"
    out: List[str] = []
    out.append(f"{'session':<55s}  {'sent':>4s} {'recv':>4s} {'cited':>5s}  status")
    out.append("-" * 88)
    for r in rows:
        c = r["counts"]
        status = "closed" if r.get("ended_at") else "active"
        out.append(
            f"{r['session']:<55s}  {c.get('sent', 0):>4d} {c.get('received', 0):>4d} {c.get('cited', 0):>5d}  {status}"
        )
    return "\n".join(out)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument(
        "--action",
        choices=["start", "record_sent", "record_received", "record_cited", "status", "list", "close"],
        required=True,
    )
    parser.add_argument("--session", help="Session name")
    parser.add_argument("--topic", help="(start only) topic string")
    parser.add_argument("--query", help="(record_sent only) the query text")
    parser.add_argument("--platform", help="(record_* only) platform name: reddit | hn | web | x | other")
    parser.add_argument("--count", type=int, help="(record_received only) number of sources received")
    parser.add_argument("--url", help="(record_cited only) cited URL")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    try:
        if args.action == "start":
            if not args.session:
                print("error: --session required for start", file=sys.stderr)
                return 2
            result = action_start(args.session, args.topic)
        elif args.action == "record_sent":
            if not (args.session and args.query and args.platform):
                print("error: --session, --query, --platform required for record_sent", file=sys.stderr)
                return 2
            result = action_record_sent(args.session, args.query, args.platform)
        elif args.action == "record_received":
            if not (args.session and args.count is not None and args.platform):
                print("error: --session, --count, --platform required for record_received", file=sys.stderr)
                return 2
            result = action_record_received(args.session, args.count, args.platform)
        elif args.action == "record_cited":
            if not (args.session and args.url and args.platform):
                print("error: --session, --url, --platform required for record_cited", file=sys.stderr)
                return 2
            result = action_record_cited(args.session, args.url, args.platform)
        elif args.action == "status":
            if not args.session:
                print("error: --session required for status", file=sys.stderr)
                return 2
            result = action_status(args.session)
        elif args.action == "close":
            if not args.session:
                print("error: --session required for close", file=sys.stderr)
                return 2
            result = action_close(args.session)
        else:  # list
            result = action_list()
    except (FileNotFoundError, FileExistsError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 2

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
