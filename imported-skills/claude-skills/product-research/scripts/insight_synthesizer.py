#!/usr/bin/env python3
"""insight_synthesizer.py - Cluster coded observations into candidate insights; flag anecdotes.

Stdlib-only. Deterministic. NO LLM calls. NEVER fabricates an insight: it counts evidence,
clusters by tag, ranks by cross-participant recurrence, and flags any candidate supported by
fewer than --min-sources independent participants as an ANECDOTE, not an insight.

Input: a list of observations, each with {participant, tag, note}. The synthesizer groups by
tag, counts distinct participants per tag, and ranks. This is the atomic-research discipline:
an observation is evidence; an insight requires recurrence across independent sources.

Usage:
    python3 insight_synthesizer.py --sample
    python3 insight_synthesizer.py --input observations.json --min-sources 3
    python3 insight_synthesizer.py --input observations.json --output json
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
try:
    import config_loader as _cfg
except ImportError:  # pragma: no cover
    _cfg = None

SAMPLE = {
    "study": "Onboarding discovery (mid-market HR)",
    "observations": [
        {"participant": "P1", "tag": "import-confusion", "note": "Couldn't find CSV import."},
        {"participant": "P2", "tag": "import-confusion", "note": "Expected import on the dashboard."},
        {"participant": "P3", "tag": "import-confusion", "note": "Gave up looking for bulk upload."},
        {"participant": "P1", "tag": "permissions-unclear", "note": "Unsure who could see reports."},
        {"participant": "P4", "tag": "permissions-unclear", "note": "Worried about data visibility."},
        {"participant": "P2", "tag": "wants-slack", "note": "Asked for a Slack integration."},
    ],
}


def synthesize(data: dict, min_sources: int) -> dict:
    obs = data.get("observations", [])
    by_tag_participants = defaultdict(set)
    by_tag_notes = defaultdict(list)
    for o in obs:
        tag = o.get("tag", "untagged")
        part = o.get("participant", "UNKNOWN")
        by_tag_participants[tag].add(part)
        by_tag_notes[tag].append({"participant": part, "note": o.get("note", "")})

    candidates = []
    for tag, parts in by_tag_participants.items():
        n_sources = len(parts)
        is_insight = n_sources >= min_sources
        candidates.append({
            "tag": tag,
            "distinct_participants": n_sources,
            "observation_count": len(by_tag_notes[tag]),
            "classification": "INSIGHT" if is_insight else "ANECDOTE (single/low-source — do not generalize)",
            "evidence": by_tag_notes[tag],
        })
    candidates.sort(key=lambda c: (c["distinct_participants"], c["observation_count"]), reverse=True)

    total_participants = len({o.get("participant") for o in obs})
    return {
        "study": data.get("study", "UNSPECIFIED"),
        "min_sources_for_insight": min_sources,
        "total_participants": total_participants,
        "candidates": candidates,
        "note": "An observation is evidence; an insight requires recurrence across independent participants. "
                "Anecdotes are surfaced, never promoted to insights.",
    }


def _render_human(r: dict) -> str:
    lines = [f"Insight Synthesis: {r['study']}",
             f"  total participants: {r['total_participants']}   insight threshold: >= {r['min_sources_for_insight']} sources", ""]
    for c in r["candidates"]:
        lines.append(f"[{c['classification']}] {c['tag']}  "
                     f"({c['distinct_participants']} participants, {c['observation_count']} observations)")
        for e in c["evidence"]:
            lines.append(f"      {e['participant']}: {e['note']}")
        lines.append("")
    lines.append(f"note: {r['note']}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description="Cluster coded observations into insights; flag anecdotes.")
    p.add_argument("--input", help="Path to JSON with observations[]")
    p.add_argument("--min-sources", type=int, default=None,
                   help="min distinct participants to call it an insight (overrides onboarding)")
    p.add_argument("--output", choices=["human", "json"], default="human")
    p.add_argument("--sample", action="store_true", help="use the embedded sample")
    args = p.parse_args(argv)

    conf = _cfg.load_config() if _cfg else {}
    min_sources = args.min_sources if args.min_sources is not None else int(conf.get("insight_min_sources", 3))
    data = SAMPLE if (args.sample or not args.input) else json.load(open(args.input))
    result = synthesize(data, min_sources)
    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(_render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
