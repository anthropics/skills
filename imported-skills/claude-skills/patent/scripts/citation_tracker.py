#!/usr/bin/env python3
"""citation_tracker.py — Patent skill three-count audit across multi-source patent search.

Stdlib-only. Mirrors litreview/grants/dossier trackers but adapted for patent's
4-source workflow:

  - Google Patents (workhorse, no auth)
  - Espacenet (global)
  - USPTO PPS (US deep dive)
  - Lens.org (BYOK, citation graph)

Tracked counts:
  - searches_per_source       (broken out by source)
  - patents_received_total
  - patents_cited_total
  - patents_cited_by_source
  - sub_use_case               (recorded at start; drives audit verbatim)
  - lens_byok_used             (boolean — surfaced in audit log)

Enforces 1s sequential discipline across ALL sources combined.

Usage:
    python citation_tracker.py --action start --session patent-MS-novelty-20260515 --invention "..." --sub-use-case novelty
    python citation_tracker.py --action record_search --session ... --source google_patents --query "..."
    python citation_tracker.py --action record_received --session ... --source google_patents --count 10
    python citation_tracker.py --action record_cited --session ... --source google_patents --patent-num "US10000000B2"
    python citation_tracker.py --action record_lens_byok --session ...
    python citation_tracker.py --action status --session ...
    python citation_tracker.py --action close --session ...
"""

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional


SESSIONS_DIR = Path.home() / ".patent_sessions"
MIN_GAP_SECONDS = 1.0
VALID_SOURCES = ["google_patents", "espacenet", "uspto", "lens", "websearch"]
VALID_SUB_USE_CASES = ["novelty", "fto", "landscape", "diligence", "litigation"]


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


def action_start(name: str, invention: Optional[str], sub_use_case: Optional[str]) -> Dict[str, Any]:
    if session_path(name).exists():
        raise FileExistsError(f"Session already exists: {name}")
    if sub_use_case and sub_use_case not in VALID_SUB_USE_CASES:
        raise ValueError(f"Invalid sub-use-case '{sub_use_case}'. Pick from: {VALID_SUB_USE_CASES}")
    data: Dict[str, Any] = {
        "session": name,
        "invention": invention or "",
        "sub_use_case": sub_use_case or "",
        "started_at": now_iso(),
        "ended_at": None,
        "lens_byok_used": False,
        "searches": [],
        "received_log": [],
        "cited": [],
        "counts": {
            "searches_total": 0,
            "searches_by_source": {s: 0 for s in VALID_SOURCES},
            "received_total": 0,
            "received_by_source": {s: 0 for s in VALID_SOURCES},
            "cited_total": 0,
            "cited_by_source": {s: 0 for s in VALID_SOURCES},
        },
    }
    save_session(name, data)
    return data


def action_record_search(name: str, source: str, query: str) -> Dict[str, Any]:
    data = load_session(name)
    if source not in VALID_SOURCES:
        raise ValueError(f"Invalid source '{source}'. Pick from: {VALID_SOURCES}")
    if data["searches"]:
        last_ts = data["searches"][-1].get("ts", 0)
        gap = now_ts() - last_ts
        if gap < MIN_GAP_SECONDS:
            raise RuntimeError(
                f"Sequential discipline violated: {gap:.2f}s gap (need >= {MIN_GAP_SECONDS}s). "
                f"Wait {MIN_GAP_SECONDS - gap:.2f}s more."
            )
    data["searches"].append({"source": source, "query": query, "at": now_iso(), "ts": now_ts()})
    data["counts"]["searches_total"] += 1
    data["counts"]["searches_by_source"][source] += 1
    save_session(name, data)
    return data


def action_record_received(name: str, source: str, count: int) -> Dict[str, Any]:
    data = load_session(name)
    if source not in VALID_SOURCES:
        raise ValueError(f"Invalid source '{source}'")
    data["received_log"].append({"source": source, "count": count, "at": now_iso()})
    data["counts"]["received_total"] += count
    data["counts"]["received_by_source"][source] += count
    save_session(name, data)
    return data


def action_record_cited(name: str, source: str, patent_num: str, title: Optional[str]) -> Dict[str, Any]:
    data = load_session(name)
    if source not in VALID_SOURCES:
        raise ValueError(f"Invalid source '{source}'")
    if any(c["patent_num"] == patent_num for c in data["cited"]):
        return data
    data["cited"].append({"source": source, "patent_num": patent_num, "title": title, "at": now_iso()})
    data["counts"]["cited_total"] += 1
    data["counts"]["cited_by_source"][source] += 1
    save_session(name, data)
    return data


def action_record_lens_byok(name: str) -> Dict[str, Any]:
    data = load_session(name)
    data["lens_byok_used"] = True
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
    out.append(f"Invention:         {data.get('invention', '(unset)')}")
    out.append(f"Sub-use-case:      {data.get('sub_use_case', '(unset)')}")
    out.append(f"Lens.org BYOK:     {'YES' if data.get('lens_byok_used') else 'no (citation graph skipped)'}")
    out.append(f"Started:           {data['started_at']}")
    out.append(f"Ended:             {data.get('ended_at') or '(active)'}")
    out.append("")
    c = data["counts"]
    out.append(f"Total searches:    {c['searches_total']}")
    out.append("By source:")
    for src, n in c["searches_by_source"].items():
        if n > 0:
            out.append(f"  {src:<18s} {n}")
    out.append("")
    out.append(f"Patents received:  {c['received_total']}")
    out.append(f"Patents cited:     {c['cited_total']}")
    out.append("Cited by source:")
    for src, n in c["cited_by_source"].items():
        if n > 0:
            out.append(f"  {src:<18s} {n}")
    out.append("")
    out.append("Audit block (paste in DOCX Section 8):")
    out.append(
        f"  Searches: {c['searches_total']} (Google Patents: {c['searches_by_source'].get('google_patents', 0)}, "
        f"Espacenet: {c['searches_by_source'].get('espacenet', 0)}, "
        f"USPTO: {c['searches_by_source'].get('uspto', 0)}, "
        f"Lens.org: {c['searches_by_source'].get('lens', 0)}). "
        f"Patents received: {c['received_total']}. Patents cited: {c['cited_total']}. "
        f"Lens.org BYOK: {'used' if data.get('lens_byok_used') else 'not provided (citation graph skipped)'}."
    )
    return "\n".join(out)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--action", required=True, choices=["start", "record_search", "record_received", "record_cited", "record_lens_byok", "status", "list", "close"])
    parser.add_argument("--session")
    parser.add_argument("--invention")
    parser.add_argument("--sub-use-case", choices=VALID_SUB_USE_CASES)
    parser.add_argument("--source", choices=VALID_SOURCES)
    parser.add_argument("--query")
    parser.add_argument("--count", type=int)
    parser.add_argument("--patent-num")
    parser.add_argument("--title")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    try:
        if args.action == "start":
            result = action_start(args.session, args.invention, args.sub_use_case)
        elif args.action == "record_search":
            result = action_record_search(args.session, args.source, args.query)
        elif args.action == "record_received":
            result = action_record_received(args.session, args.source, args.count)
        elif args.action == "record_cited":
            result = action_record_cited(args.session, args.source, args.patent_num, args.title)
        elif args.action == "record_lens_byok":
            result = action_record_lens_byok(args.session)
        elif args.action == "status":
            result = action_status(args.session)
        elif args.action == "close":
            result = action_close(args.session)
        else:
            SESSIONS_DIR.mkdir(parents=True, exist_ok=True)
            result = [{"session": p.stem, "data": json.loads(p.read_text(encoding="utf-8"))} for p in sorted(SESSIONS_DIR.glob("*.json"))]
    except (FileNotFoundError, FileExistsError, ValueError, RuntimeError) as e:
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
