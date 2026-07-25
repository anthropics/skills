#!/usr/bin/env python3
"""citation_tracker.py — Syllabus three-count audit + 1s sequential discipline.

Stdlib-only. Mirrors litreview's citation_tracker (research-pack convention)
adapted for syllabus's per-section search budget.

Tracked counts:
  - searches_total
  - searches_per_section
  - papers_received
  - papers_cited

Per-section detail recorded for DOCX audit log.
Enforces 1s sequential gap.

Usage:
    python citation_tracker.py --action start --session syllabus-bio101-20260515 --course "Intro Biology"
    python citation_tracker.py --action record_search --session ... --section "Cell Biology" --query "..."
    python citation_tracker.py --action record_received --session ... --section "Cell Biology" --count 3
    python citation_tracker.py --action record_cited --session ... --section "Cell Biology" --url "..."
    python citation_tracker.py --action status --session ...
"""

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional


SESSIONS_DIR = Path.home() / ".syllabus_sessions"
MIN_GAP_SECONDS = 1.0


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


def now_ts() -> float:
    return datetime.now(timezone.utc).timestamp()


def action_start(name: str, course: Optional[str], audience: Optional[str], year_range: Optional[str]) -> Dict[str, Any]:
    if session_path(name).exists():
        raise FileExistsError(f"Session already exists: {name}")
    data: Dict[str, Any] = {
        "session": name,
        "course": course or "",
        "audience": audience or "",
        "year_range": year_range or "",
        "consensus_tier": None,
        "started_at": now_iso(),
        "ended_at": None,
        "searches": [],
        "received_log": [],
        "cited": [],
        "counts": {
            "searches_total": 0,
            "papers_received_total": 0,
            "papers_cited_total": 0,
        },
        "by_section": {},
    }
    save_session(name, data)
    return data


def action_record_search(name: str, section: str, query: str, tier: Optional[str]) -> Dict[str, Any]:
    data = load_session(name)
    if data["searches"]:
        last_ts = data["searches"][-1].get("ts", 0)
        gap = now_ts() - last_ts
        if gap < MIN_GAP_SECONDS:
            raise RuntimeError(
                f"Sequential discipline violated: {gap:.2f}s gap (need >= {MIN_GAP_SECONDS}s). "
                f"Wait {MIN_GAP_SECONDS - gap:.2f}s more."
            )
    if tier and not data["consensus_tier"]:
        data["consensus_tier"] = tier
    data["searches"].append({"section": section, "query": query, "tier": tier, "at": now_iso(), "ts": now_ts()})
    data["counts"]["searches_total"] += 1
    if section not in data["by_section"]:
        data["by_section"][section] = {"searches": 0, "received": 0, "cited": 0}
    data["by_section"][section]["searches"] += 1
    save_session(name, data)
    return data


def action_record_received(name: str, section: str, count: int) -> Dict[str, Any]:
    data = load_session(name)
    data["received_log"].append({"section": section, "count": count, "at": now_iso()})
    data["counts"]["papers_received_total"] += count
    if section not in data["by_section"]:
        data["by_section"][section] = {"searches": 0, "received": 0, "cited": 0}
    data["by_section"][section]["received"] += count
    save_session(name, data)
    return data


def action_record_cited(name: str, section: str, url: str, title: Optional[str]) -> Dict[str, Any]:
    data = load_session(name)
    if any(c["url"] == url for c in data["cited"]):
        return data
    data["cited"].append({"section": section, "url": url, "title": title, "at": now_iso()})
    data["counts"]["papers_cited_total"] += 1
    if section not in data["by_section"]:
        data["by_section"][section] = {"searches": 0, "received": 0, "cited": 0}
    data["by_section"][section]["cited"] += 1
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


def render_status_human(data: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"Session:           {data['session']}")
    out.append(f"Course:            {data.get('course', '(unset)')}")
    out.append(f"Audience:          {data.get('audience', '(unset)')}")
    out.append(f"Year range:        {data.get('year_range', '(unset)')}")
    out.append(f"Consensus tier:    {data.get('consensus_tier') or '(not detected)'}")
    out.append(f"Started:           {data['started_at']}")
    out.append(f"Ended:             {data.get('ended_at') or '(active)'}")
    out.append("")
    c = data["counts"]
    out.append(f"Total searches:    {c['searches_total']}")
    out.append(f"Total received:    {c['papers_received_total']}")
    out.append(f"Total cited:       {c['papers_cited_total']}")
    out.append("")
    if data["by_section"]:
        out.append("Per-section breakdown:")
        for section, stats in data["by_section"].items():
            out.append(f"  {section:<40s} {stats['searches']} searches → {stats['received']} received → {stats['cited']} cited")
    out.append("")
    out.append("Audit block (paste in DOCX audit-log section):")
    out.append(
        f"  Total queries: {c['searches_total']}. Papers received: {c['papers_received_total']}. "
        f"Papers cited: {c['papers_cited_total']}. "
        f"Plan tier: {data.get('consensus_tier') or 'undetected'}."
    )
    return "\n".join(out)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--action", required=True, choices=["start", "record_search", "record_received", "record_cited", "status", "list", "close"])
    parser.add_argument("--session")
    parser.add_argument("--course")
    parser.add_argument("--audience")
    parser.add_argument("--year-range")
    parser.add_argument("--section")
    parser.add_argument("--query")
    parser.add_argument("--tier")
    parser.add_argument("--count", type=int)
    parser.add_argument("--url")
    parser.add_argument("--title")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    try:
        if args.action == "start":
            result = action_start(args.session, args.course, args.audience, args.year_range)
        elif args.action == "record_search":
            result = action_record_search(args.session, args.section, args.query, args.tier)
        elif args.action == "record_received":
            result = action_record_received(args.session, args.section, args.count)
        elif args.action == "record_cited":
            result = action_record_cited(args.session, args.section, args.url, args.title)
        elif args.action == "status":
            result = action_status(args.session)
        elif args.action == "close":
            result = action_close(args.session)
        else:
            SESSIONS_DIR.mkdir(parents=True, exist_ok=True)
            result = [{"session": p.stem, "data": json.loads(p.read_text(encoding="utf-8"))} for p in sorted(SESSIONS_DIR.glob("*.json"))]
    except (FileNotFoundError, FileExistsError, RuntimeError) as e:
        print(f"error: {e}", file=sys.stderr); return 2

    if args.output == "json":
        print(json.dumps(result, indent=2, default=str))
    else:
        if args.action == "list":
            print(json.dumps(result, indent=2, default=str))
        else:
            print(render_status_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
