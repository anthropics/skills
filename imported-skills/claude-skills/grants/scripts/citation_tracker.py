#!/usr/bin/env python3
"""citation_tracker.py — JSON-backed three-count audit for grants runs.

Stdlib-only. Mirrors litreview's tracker but extended for grants's
multi-source workflow (Consensus + RePORTER + NOSI fetches).

Tracked counts:
  - consensus_searches    (5 facets sent)
  - consensus_received    (papers shown across facets)
  - consensus_cited       (papers cited in DOCX)
  - reporter_searches     (typically 2: narrow + broad)
  - reporter_projects     (projects returned across both)
  - reporter_cited        (projects cited in DOCX)
  - nosi_fetches          (NOT-* fetches attempted)
  - nosi_succeeded        (fetches that returned content)

Enforces 1s sequential gap on Consensus searches (research-pack convention).
Persists at ~/.grants_sessions/<session>.json.

Usage:
    python citation_tracker.py --action start --session grants-20260515 --topic "sepsis prediction"
    python citation_tracker.py --action record_consensus_search --session ... --facet established --query "..." --tier free
    python citation_tracker.py --action record_consensus_received --session ... --count 10
    python citation_tracker.py --action record_consensus_cited --session ... --url "https://consensus.app/..."
    python citation_tracker.py --action record_reporter_search --session ... --type narrow --query "..." --projects 23
    python citation_tracker.py --action record_reporter_cited --session ... --project-num "R01HL12345"
    python citation_tracker.py --action record_nosi --session ... --nosi "NOT-HL-25-014" --status fetched
    python citation_tracker.py --action status --session ...
    python citation_tracker.py --action close --session ...
"""

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional


SESSIONS_DIR = Path.home() / ".grants_sessions"
MIN_CONSENSUS_GAP_SECONDS = 1.0


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


def action_start(name: str, topic: Optional[str]) -> Dict[str, Any]:
    if session_path(name).exists():
        raise FileExistsError(f"Session already exists: {name}")
    data: Dict[str, Any] = {
        "session": name,
        "topic": topic or "",
        "started_at": now_iso(),
        "ended_at": None,
        "consensus_tier": None,
        "consensus_searches": [],
        "consensus_received_log": [],
        "consensus_cited": [],
        "reporter_searches": [],
        "reporter_cited": [],
        "nosi_fetches": [],
        "counts": {
            "consensus_searches": 0,
            "consensus_received": 0,
            "consensus_cited": 0,
            "reporter_searches": 0,
            "reporter_projects": 0,
            "reporter_cited": 0,
            "nosi_fetches": 0,
            "nosi_succeeded": 0,
        },
    }
    save_session(name, data)
    return data


def action_record_consensus_search(name: str, facet: str, query: str, tier: Optional[str]) -> Dict[str, Any]:
    data = load_session(name)
    if data["consensus_searches"]:
        last_ts = data["consensus_searches"][-1].get("ts", 0)
        gap = now_ts() - last_ts
        if gap < MIN_CONSENSUS_GAP_SECONDS:
            raise RuntimeError(
                f"Consensus sequential discipline violated: {gap:.2f}s gap (need >= {MIN_CONSENSUS_GAP_SECONDS}s). "
                f"Wait {MIN_CONSENSUS_GAP_SECONDS - gap:.2f}s more."
            )
    if tier and not data["consensus_tier"]:
        data["consensus_tier"] = tier
    data["consensus_searches"].append({"facet": facet, "query": query, "tier": tier, "at": now_iso(), "ts": now_ts()})
    data["counts"]["consensus_searches"] += 1
    save_session(name, data)
    return data


def action_record_consensus_received(name: str, count: int) -> Dict[str, Any]:
    data = load_session(name)
    data["consensus_received_log"].append({"count": count, "at": now_iso()})
    data["counts"]["consensus_received"] += count
    save_session(name, data)
    return data


def action_record_consensus_cited(name: str, url: str) -> Dict[str, Any]:
    data = load_session(name)
    if any(p["url"] == url for p in data["consensus_cited"]):
        return data
    data["consensus_cited"].append({"url": url, "at": now_iso()})
    data["counts"]["consensus_cited"] += 1
    save_session(name, data)
    return data


def action_record_reporter_search(name: str, search_type: str, query: str, projects: int) -> Dict[str, Any]:
    data = load_session(name)
    data["reporter_searches"].append({"type": search_type, "query": query, "projects_returned": projects, "at": now_iso()})
    data["counts"]["reporter_searches"] += 1
    data["counts"]["reporter_projects"] += projects
    save_session(name, data)
    return data


def action_record_reporter_cited(name: str, project_num: str) -> Dict[str, Any]:
    data = load_session(name)
    if any(p["project_num"] == project_num for p in data["reporter_cited"]):
        return data
    data["reporter_cited"].append({"project_num": project_num, "at": now_iso()})
    data["counts"]["reporter_cited"] += 1
    save_session(name, data)
    return data


def action_record_nosi(name: str, nosi: str, status: str) -> Dict[str, Any]:
    data = load_session(name)
    data["nosi_fetches"].append({"nosi": nosi, "status": status, "at": now_iso()})
    data["counts"]["nosi_fetches"] += 1
    if status == "fetched" or status == "succeeded":
        data["counts"]["nosi_succeeded"] += 1
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
            d = json.loads(p.read_text(encoding="utf-8"))
            out.append({
                "session": d.get("session", p.stem),
                "topic": d.get("topic", ""),
                "tier": d.get("consensus_tier"),
                "counts": d.get("counts", {}),
                "ended_at": d.get("ended_at"),
            })
        except (OSError, json.JSONDecodeError):
            continue
    return out


def render_status_human(data: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"Session:           {data['session']}")
    out.append(f"Topic:             {data.get('topic', '(unset)')}")
    out.append(f"Consensus tier:    {data.get('consensus_tier') or '(not detected)'}")
    out.append(f"Started:           {data['started_at']}")
    out.append(f"Ended:             {data.get('ended_at') or '(active)'}")
    out.append("")
    c = data["counts"]
    out.append("Counts:")
    out.append(f"  Consensus searches:   {c['consensus_searches']}")
    out.append(f"  Consensus received:   {c['consensus_received']}")
    out.append(f"  Consensus cited:      {c['consensus_cited']}")
    out.append(f"  RePORTER searches:    {c['reporter_searches']}")
    out.append(f"  RePORTER projects:    {c['reporter_projects']}")
    out.append(f"  RePORTER cited:       {c['reporter_cited']}")
    out.append(f"  NOSI fetches:         {c['nosi_fetches']}  ({c['nosi_succeeded']} succeeded)")
    out.append("")
    out.append("Audit block (paste in DOCX Section 9):")
    out.append(
        f"  Three counts — Queries sent: {c['consensus_searches'] + c['reporter_searches']} "
        f"(Consensus {c['consensus_searches']}, RePORTER {c['reporter_searches']}). "
        f"Results received: {c['consensus_received'] + c['reporter_projects']} "
        f"(Consensus {c['consensus_received']} + RePORTER {c['reporter_projects']}). "
        f"Results cited: {c['consensus_cited'] + c['reporter_cited']} "
        f"(Consensus {c['consensus_cited']} + RePORTER {c['reporter_cited']}). "
        f"NOSI fetches: {c['nosi_succeeded']}/{c['nosi_fetches']} succeeded."
    )
    return "\n".join(out)


def render_list_human(rows: List[Dict[str, Any]]) -> str:
    if not rows:
        return "(no sessions)"
    out: List[str] = []
    out.append(f"{'session':<35s} {'tier':<5s} {'C-srch':>6s} {'C-rcvd':>6s} {'C-cit':>5s} {'R-srch':>6s} {'R-prj':>5s} {'R-cit':>5s} {'NOSI':>4s}")
    out.append("-" * 90)
    for r in rows:
        c = r["counts"]
        out.append(
            f"{r['session']:<35s} {(r.get('tier') or '—'):<5s} "
            f"{c.get('consensus_searches', 0):>6d} {c.get('consensus_received', 0):>6d} "
            f"{c.get('consensus_cited', 0):>5d} {c.get('reporter_searches', 0):>6d} "
            f"{c.get('reporter_projects', 0):>5d} {c.get('reporter_cited', 0):>5d} "
            f"{c.get('nosi_succeeded', 0):>4d}"
        )
    return "\n".join(out)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument(
        "--action",
        required=True,
        choices=[
            "start", "record_consensus_search", "record_consensus_received", "record_consensus_cited",
            "record_reporter_search", "record_reporter_cited", "record_nosi",
            "status", "list", "close",
        ],
    )
    parser.add_argument("--session")
    parser.add_argument("--topic")
    parser.add_argument("--facet")
    parser.add_argument("--query")
    parser.add_argument("--tier")
    parser.add_argument("--count", type=int)
    parser.add_argument("--url")
    parser.add_argument("--type", dest="search_type")
    parser.add_argument("--projects", type=int)
    parser.add_argument("--project-num")
    parser.add_argument("--nosi")
    parser.add_argument("--status")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    try:
        if args.action == "start":
            result = action_start(args.session, args.topic)
        elif args.action == "record_consensus_search":
            result = action_record_consensus_search(args.session, args.facet, args.query, args.tier)
        elif args.action == "record_consensus_received":
            result = action_record_consensus_received(args.session, args.count)
        elif args.action == "record_consensus_cited":
            result = action_record_consensus_cited(args.session, args.url)
        elif args.action == "record_reporter_search":
            result = action_record_reporter_search(args.session, args.search_type, args.query, args.projects)
        elif args.action == "record_reporter_cited":
            result = action_record_reporter_cited(args.session, args.project_num)
        elif args.action == "record_nosi":
            result = action_record_nosi(args.session, args.nosi, args.status)
        elif args.action == "status":
            result = action_status(args.session)
        elif args.action == "close":
            result = action_close(args.session)
        else:
            result = action_list()
    except (FileNotFoundError, FileExistsError, RuntimeError) as e:
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
