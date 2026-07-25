#!/usr/bin/env python3
"""
citation_tracker.py — Local-first citation ledger for AEO.

Tracks when/where your content gets cited by LLMs (ChatGPT, Perplexity,
Claude, Gemini, Mistral). Stores entries in ~/.aeo-data/citations.json
(local, no telemetry). Stdlib only.

Actions:
  add     — log a citation you observed in an LLM response
  list    — list all citations or filter by --url / --llm / --since
  report  — per-URL aggregate: count, LLM coverage, velocity, top queries
  export  — emit CSV for reporting

Usage:
  python3 citation_tracker.py --action add --url https://x.com/post \
      --llm perplexity --query "what is AEO" --date 2026-05-17 --notes "first half of response"
  python3 citation_tracker.py --action list --url https://x.com/post
  python3 citation_tracker.py --action report --url https://x.com/post
  python3 citation_tracker.py --action export --output citations.csv
  python3 citation_tracker.py --sample

Source: distilled from aeo-box citation_tracker.py.
"""

import argparse
import csv
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SUPPORTED_LLMS = ["chatgpt", "perplexity", "claude", "gemini", "mistral", "copilot", "brave", "you", "other"]


def _data_dir() -> Path:
    """Return the local data directory, creating if needed."""
    d = Path.home() / ".aeo-data"
    d.mkdir(parents=True, exist_ok=True)
    return d


def _ledger_path() -> Path:
    return _data_dir() / "citations.json"


def _load_ledger() -> dict:
    path = _ledger_path()
    if not path.exists():
        return {"schema_version": 1, "citations": []}
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as e:
        sys.stderr.write(f"[citation_tracker] WARN: ledger file corrupted ({e}); starting fresh\n")
        return {"schema_version": 1, "citations": []}


def _save_ledger(ledger: dict) -> Path:
    path = _ledger_path()
    path.write_text(json.dumps(ledger, indent=2), encoding="utf-8")
    return path


def add_citation(url: str, llm: str, query: str, date: str | None = None,
                 notes: str = "", position: str = "") -> dict:
    """Add a citation entry. Returns the saved entry."""
    if llm.lower() not in SUPPORTED_LLMS:
        sys.stderr.write(f"[citation_tracker] WARN: unknown LLM '{llm}' (allowed: {SUPPORTED_LLMS})\n")

    entry = {
        "id": _make_id(),
        "url": url,
        "llm": llm.lower(),
        "query": query,
        "date": date or datetime.now(timezone.utc).date().isoformat(),
        "logged_at": datetime.now(timezone.utc).isoformat(),
        "notes": notes,
        "position": position,
    }
    ledger = _load_ledger()
    ledger["citations"].append(entry)
    _save_ledger(ledger)
    return entry


def _make_id() -> str:
    """8-char ID from current timestamp."""
    return datetime.now(timezone.utc).strftime("%Y%m%d-%H%M%S-%f")[:21]


def list_citations(url: str | None = None, llm: str | None = None,
                   since: str | None = None) -> list:
    """List citations matching filters."""
    ledger = _load_ledger()
    cits = ledger["citations"]
    if url:
        cits = [c for c in cits if c["url"] == url]
    if llm:
        cits = [c for c in cits if c["llm"] == llm.lower()]
    if since:
        cits = [c for c in cits if c["date"] >= since]
    return cits


def report(url: str | None = None) -> dict:
    """Generate aggregate report. If URL specified, per-URL stats.
    Otherwise, full-ledger summary."""
    cits = list_citations(url=url) if url else _load_ledger()["citations"]
    if not cits:
        return {
            "url": url,
            "total_citations": 0,
            "llms_covered": [],
            "verdict": "NO_DATA",
        }

    by_llm = {}
    by_query = {}
    by_date = {}
    for c in cits:
        by_llm[c["llm"]] = by_llm.get(c["llm"], 0) + 1
        by_query[c["query"]] = by_query.get(c["query"], 0) + 1
        by_date[c["date"]] = by_date.get(c["date"], 0) + 1

    top_queries = sorted(by_query.items(), key=lambda kv: -kv[1])[:10]
    dates = sorted(by_date.keys())

    # Velocity: citations per day, rolling 30 days
    velocity = 0.0
    if len(dates) >= 2:
        first = datetime.fromisoformat(dates[0])
        last = datetime.fromisoformat(dates[-1])
        days = max((last - first).days, 1)
        velocity = round(len(cits) / days, 2)

    verdict = "STRONG" if len(by_llm) >= 3 and len(cits) >= 10 else \
              "EMERGING" if len(cits) >= 3 else \
              "EARLY"

    return {
        "url": url,
        "total_citations": len(cits),
        "llms_covered": sorted(by_llm.keys()),
        "llm_coverage_count": len(by_llm),
        "citations_per_llm": by_llm,
        "top_queries": top_queries,
        "first_citation_date": dates[0] if dates else None,
        "last_citation_date": dates[-1] if dates else None,
        "velocity_per_day": velocity,
        "verdict": verdict,
        "interpretation": {
            "STRONG":   "Cited by 3+ LLMs with steady volume — content has citation moat",
            "EMERGING": "Cited multiple times but not yet cross-LLM — push for coverage breadth",
            "EARLY":    "Few or no citations — keep optimizing + waiting for LLM training refresh",
            "NO_DATA":  "No citations recorded yet",
        }.get(verdict, ""),
    }


def export_csv(output_path: str) -> int:
    """Export the full citation ledger as CSV. Returns row count."""
    ledger = _load_ledger()
    cits = ledger["citations"]
    fieldnames = ["id", "url", "llm", "query", "date", "logged_at", "notes", "position"]
    with open(output_path, "w", encoding="utf-8", newline="") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        for c in cits:
            w.writerow({k: c.get(k, "") for k in fieldnames})
    return len(cits)


def render_human(action: str, data: Any) -> str:
    """Render results as human-readable text."""
    if action == "add":
        return (f"✅ Logged citation:\n"
                f"   URL: {data['url']}\n"
                f"   LLM: {data['llm']}\n"
                f"   Query: {data['query']}\n"
                f"   Date: {data['date']}\n"
                f"   ID: {data['id']}")

    if action == "list":
        if not data:
            return "(no citations match the filters)"
        lines = [f"Found {len(data)} citation(s):"]
        for c in data:
            lines.append(f"  [{c['date']}] {c['llm']:12s} ← {c['url']}")
            lines.append(f"             query: {c['query']}")
            if c.get("notes"):
                lines.append(f"             notes: {c['notes']}")
        return "\n".join(lines)

    if action == "report":
        if data.get("total_citations", 0) == 0:
            return f"📊 Report ({data.get('url') or 'all'}):\n   No citations recorded yet."
        lines = [
            f"📊 Citation Report — {data.get('url') or 'ALL URLs'}",
            f"",
            f"   Total citations:    {data['total_citations']}",
            f"   LLMs covered:       {data['llm_coverage_count']} ({', '.join(data['llms_covered'])})",
            f"   First citation:     {data['first_citation_date']}",
            f"   Last citation:      {data['last_citation_date']}",
            f"   Velocity:           {data['velocity_per_day']} citations/day",
            f"   Verdict:            {data['verdict']}",
            f"   Interpretation:     {data['interpretation']}",
            "",
            "   Citations per LLM:",
        ]
        for llm, n in sorted(data["citations_per_llm"].items(), key=lambda kv: -kv[1]):
            lines.append(f"     {llm:12s} {n}")
        lines.append("")
        lines.append("   Top queries:")
        for q, n in data["top_queries"]:
            lines.append(f"     ({n:2d}) {q}")
        return "\n".join(lines)

    if action == "export":
        return f"✅ Exported {data} citations to CSV"

    return json.dumps(data, indent=2, default=str)


def _run_sample():
    """Populate sample data + show all actions."""
    sample_path = Path.home() / ".aeo-data" / "citations.sample.json"
    # Use a separate sample file to avoid clobbering real data
    actual_path = _ledger_path()
    backup = None
    if actual_path.exists():
        backup = actual_path.read_text(encoding="utf-8")

    try:
        # Write fresh ledger for the sample
        _save_ledger({"schema_version": 1, "citations": []})
        add_citation("https://example.com/blog/aeo-guide", "perplexity",
                     "what is answer engine optimization", "2026-05-10",
                     notes="cited in first half of response")
        add_citation("https://example.com/blog/aeo-guide", "chatgpt",
                     "how to optimize content for ChatGPT", "2026-05-12")
        add_citation("https://example.com/blog/aeo-guide", "claude",
                     "AEO vs SEO differences", "2026-05-15")
        add_citation("https://example.com/blog/aeo-guide", "perplexity",
                     "best AEO practices 2026", "2026-05-16")
        add_citation("https://example.com/blog/llm-citations", "gemini",
                     "how do LLMs choose citations", "2026-05-14")

        print("=== Sample: add ===")
        print(render_human("add", {"url": "https://example.com/blog/aeo-guide",
                                    "llm": "perplexity",
                                    "query": "what is AEO",
                                    "date": "2026-05-10",
                                    "id": "sample-001"}))
        print("")
        print("=== Sample: list (filtered by URL) ===")
        cits = list_citations(url="https://example.com/blog/aeo-guide")
        print(render_human("list", cits))
        print("")
        print("=== Sample: report ===")
        r = report(url="https://example.com/blog/aeo-guide")
        print(render_human("report", r))
        print("")
        print("=== Sample: export ===")
        n = export_csv(str(Path.home() / ".aeo-data" / "citations.sample.csv"))
        print(render_human("export", n))
        print(f"  → wrote {Path.home() / '.aeo-data' / 'citations.sample.csv'}")
    finally:
        # Restore the user's real ledger
        if backup is not None:
            actual_path.write_text(backup, encoding="utf-8")
        else:
            if actual_path.exists():
                actual_path.unlink()


def main():
    p = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    p.add_argument("--action", choices=["add", "list", "report", "export"],
                   help="What to do")
    p.add_argument("--url", help="Page URL (for add/list/report)")
    p.add_argument("--llm", help="LLM that cited (chatgpt, perplexity, claude, gemini, mistral, ...)")
    p.add_argument("--query", help="The query that triggered the citation (for add)")
    p.add_argument("--date", help="Date the citation was observed (YYYY-MM-DD; defaults to today)")
    p.add_argument("--notes", default="", help="Optional notes (for add)")
    p.add_argument("--position", default="", help="Where in the LLM response the citation appeared (for add)")
    p.add_argument("--since", help="List/report filter: YYYY-MM-DD")
    p.add_argument("--output", help="Path for CSV export (action=export)")
    p.add_argument("--output-format", choices=["human", "json"], default="human")
    p.add_argument("--sample", action="store_true",
                   help="Populate sample data + show all actions (preserves your real ledger)")
    args = p.parse_args()

    if args.sample:
        _run_sample()
        return

    if not args.action:
        p.error("--action is required (or use --sample)")

    if args.action == "add":
        if not (args.url and args.llm and args.query):
            p.error("add requires --url, --llm, --query")
        result = add_citation(args.url, args.llm, args.query, args.date, args.notes, args.position)
    elif args.action == "list":
        result = list_citations(args.url, args.llm, args.since)
    elif args.action == "report":
        result = report(args.url)
    elif args.action == "export":
        if not args.output:
            args.output = str(Path.home() / ".aeo-data" / "citations.csv")
        result = export_csv(args.output)
    else:
        p.error(f"unknown action {args.action}")

    if args.output_format == "json":
        print(json.dumps(result, indent=2, default=str))
    else:
        print(render_human(args.action, result))


if __name__ == "__main__":
    main()
