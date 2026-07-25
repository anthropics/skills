#!/usr/bin/env python3
"""citation_tracker.py — JSON-backed three-count audit for litreview runs.

Stdlib-only. Mirrors pulse's citation_tracker.py (research-pack convention)
but adapted for academic search (free lane: PubMed E-utilities + OpenAlex;
optional enhancement lane: Consensus MCP when connected):

  - searches executed       (queries issued, any lane)
  - unique papers received  (deduplicated across all searches)
  - papers cited             (made it into the DOCX guide)

Enforces sequential discipline by rejecting record_search calls within 1
second of the prior (research-pack 1 q/sec convention across all lanes).

Session state persists in ~/.litreview_sessions/<session>.json.

Actions:
  start             Create a new session
  record_search     Record a search query + enforce 1s gap
  record_papers_received  Record N papers from this search (with dedup intent)
  record_cited      Record a paper URL that made it into the DOCX
  status            Show current counts + audit block
  list              List all sessions
  close             Mark session ended

Usage:
    python citation_tracker.py --action start --session litreview-20260515 --topic "LLM clinical reasoning"
    python citation_tracker.py --action record_search --session ... --query "..." --lane free
    python citation_tracker.py --action record_papers_received --session ... --count 10 --unique 8
    python citation_tracker.py --action record_cited --session ... --url "https://pubmed.ncbi.nlm.nih.gov/<PMID>/"
    python citation_tracker.py --action status --session ...
    python citation_tracker.py --action list
    python citation_tracker.py --action close --session ...
"""

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional


SESSIONS_DIR = Path.home() / ".litreview_sessions"
MIN_SEARCH_GAP_SECONDS = 1.0  # research-pack 1 q/sec convention (all lanes)


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
        "plan_tier": None,
        "searches": [],
        "papers_received_log": [],
        "papers_cited": [],
        "counts": {"searches": 0, "papers_received_unique": 0, "papers_cited": 0},
    }
    save_session(name, data)
    return data


def action_record_search(name: str, query: str, tier: Optional[str]) -> Dict[str, Any]:
    data = load_session(name)
    if data["searches"]:
        last_ts = data["searches"][-1].get("ts", 0)
        gap = now_ts() - last_ts
        if gap < MIN_SEARCH_GAP_SECONDS:
            raise RuntimeError(
                f"Sequential discipline violation: search submitted {gap:.2f}s after prior "
                f"(min gap: {MIN_SEARCH_GAP_SECONDS}s). Wait at least {MIN_SEARCH_GAP_SECONDS - gap:.2f}s more."
            )
    if tier and not data["plan_tier"]:
        data["plan_tier"] = tier
    data["searches"].append({"query": query, "tier": tier, "at": now_iso(), "ts": now_ts()})
    data["counts"]["searches"] += 1
    save_session(name, data)
    return data


def action_record_papers_received(name: str, count: int, unique: Optional[int]) -> Dict[str, Any]:
    data = load_session(name)
    unique_count = unique if unique is not None else count
    data["papers_received_log"].append({"raw_count": count, "unique_after_dedup": unique_count, "at": now_iso()})
    data["counts"]["papers_received_unique"] += unique_count
    save_session(name, data)
    return data


def action_record_cited(name: str, url: str, paper_title: Optional[str]) -> Dict[str, Any]:
    data = load_session(name)
    if any(p["url"] == url for p in data["papers_cited"]):
        return data  # Already cited; idempotent
    data["papers_cited"].append({"url": url, "title": paper_title, "at": now_iso()})
    data["counts"]["papers_cited"] += 1
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
                "started_at": d.get("started_at", ""),
                "ended_at": d.get("ended_at"),
                "plan_tier": d.get("plan_tier"),
                "counts": d.get("counts", {}),
            })
        except (OSError, json.JSONDecodeError):
            continue
    return out


def render_status_human(data: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"Session:           {data['session']}")
    out.append(f"Topic:             {data.get('topic', '(unset)')}")
    out.append(f"Search lane:       {data.get('plan_tier') or 'free'}")
    out.append(f"Started:           {data['started_at']}")
    out.append(f"Ended:             {data.get('ended_at') or '(active)'}")
    out.append("")
    c = data["counts"]
    out.append("Three-count audit:")
    out.append(f"  Searches:        {c['searches']}")
    out.append(f"  Unique papers:   {c['papers_received_unique']}")
    out.append(f"  Cited:           {c['papers_cited']}")
    out.append("")
    out.append("Audit block (paste in DOCX Section 8):")
    out.append(
        f"  Searches executed: {c['searches']}. "
        f"Unique papers received: {c['papers_received_unique']}. "
        f"Papers cited in guide: {c['papers_cited']}. "
        f"Search lane: {data.get('plan_tier') or 'free'}."
    )
    return "\n".join(out)


def render_list_human(rows: List[Dict[str, Any]]) -> str:
    if not rows:
        return "(no sessions)"
    out: List[str] = []
    out.append(f"{'session':<40s}  {'lane':<6s}  {'srch':>4s}  {'uniq':>4s}  {'cited':>5s}  status")
    out.append("-" * 78)
    for r in rows:
        c = r["counts"]
        status = "closed" if r["ended_at"] else "active"
        tier = r.get("plan_tier") or "free"
        out.append(
            f"{r['session']:<40s}  {tier:<6s}  "
            f"{c.get('searches', 0):>4d}  {c.get('papers_received_unique', 0):>4d}  "
            f"{c.get('papers_cited', 0):>5d}  {status}"
        )
    return "\n".join(out)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument(
        "--action",
        required=True,
        choices=["start", "record_search", "record_papers_received", "record_cited", "status", "list", "close"],
    )
    parser.add_argument("--session", help="Session name")
    parser.add_argument("--topic", help="(start only) topic string")
    parser.add_argument("--query", help="(record_search only) search query text (any lane)")
    parser.add_argument("--tier", "--lane", dest="tier", help="(record_search only) search lane: free | free+consensus")
    parser.add_argument("--count", type=int, help="(record_papers_received only) raw paper count")
    parser.add_argument("--unique", type=int, help="(record_papers_received only) unique count after dedup")
    parser.add_argument("--url", help="(record_cited only) source URL of cited paper (PubMed/DOI/OpenAlex/Consensus)")
    parser.add_argument("--title", help="(record_cited only) paper title for the log")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    try:
        if args.action == "start":
            if not args.session:
                print("error: --session required for start", file=sys.stderr); return 2
            result = action_start(args.session, args.topic)
        elif args.action == "record_search":
            if not (args.session and args.query):
                print("error: --session, --query required", file=sys.stderr); return 2
            result = action_record_search(args.session, args.query, args.tier)
        elif args.action == "record_papers_received":
            if not (args.session and args.count is not None):
                print("error: --session, --count required", file=sys.stderr); return 2
            result = action_record_papers_received(args.session, args.count, args.unique)
        elif args.action == "record_cited":
            if not (args.session and args.url):
                print("error: --session, --url required", file=sys.stderr); return 2
            result = action_record_cited(args.session, args.url, args.title)
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
