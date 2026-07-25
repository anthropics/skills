#!/usr/bin/env python3
"""segmentation_scorer.py - Score candidate market segments against Kotler's actionability criteria.

Stdlib-only. Deterministic. NO LLM calls.

Each candidate segment is scored 0-100 across the five Kotler criteria for a useful segment:
  1. measurable      can you size and identify it?
  2. substantial     is it large/profitable enough to serve?
  3. accessible      can you reach it through channels?
  4. differentiable   does it respond differently from other segments?
  5. actionable      can you design and execute a program for it?

Segments failing the substantiality or accessibility gates are flagged: a demographic slice
that is unreachable or too small is not a market segment.

Usage:
    python3 segmentation_scorer.py --sample
    python3 segmentation_scorer.py --input segments.json --profile enterprise
    python3 segmentation_scorer.py --input segments.json --output json
"""

from __future__ import annotations

import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
try:
    import config_loader as _cfg
except ImportError:  # pragma: no cover
    _cfg = None

CRITERIA = ["measurable", "substantial", "accessible", "differentiable", "actionable"]
WEIGHTS = {"measurable": 0.15, "substantial": 0.25, "accessible": 0.25,
           "differentiable": 0.20, "actionable": 0.15}
GATE_FLOOR = 40.0  # substantiality + accessibility gate

# Profiles nudge the substantiality expectation (enterprise tolerates smaller, higher-value segments).
PROFILES = {
    "b2b-saas": 1.0,
    "consumer": 1.0,
    "enterprise": 0.85,
    "marketplace": 1.0,
    "hardware": 1.0,
    "services": 0.9,
}

SAMPLE = {
    "segments": [
        {"name": "Mid-market HR teams (51-250 emp)",
         "scores": {"measurable": 85, "substantial": 80, "accessible": 75, "differentiable": 70, "actionable": 80}},
        {"name": "Solopreneurs who 'might' want analytics",
         "scores": {"measurable": 40, "substantial": 30, "accessible": 35, "differentiable": 30, "actionable": 40}},
        {"name": "Enterprise CHROs (1000+ emp)",
         "scores": {"measurable": 90, "substantial": 95, "accessible": 50, "differentiable": 85, "actionable": 70}},
    ],
}


def score_segment(seg: dict, sub_mult: float) -> dict:
    raw = seg.get("scores", {})
    breakdown = {}
    composite = 0.0
    for c in CRITERIA:
        s = float(raw.get(c, 0.0))
        if c == "substantial":
            s = min(100.0, s / sub_mult)  # enterprise: smaller segments still count (divide by <1 raises)
        breakdown[c] = round(s, 1)
        composite += s * WEIGHTS[c]
    flags = []
    if breakdown["substantial"] < GATE_FLOOR:
        flags.append("FAILS SUBSTANTIALITY GATE: too small/unprofitable to be a target segment.")
    if breakdown["accessible"] < GATE_FLOOR:
        flags.append("FAILS ACCESSIBILITY GATE: no viable channel to reach it.")
    verdict = "DROP" if flags else ("TARGET" if composite >= 65 else "WATCH")
    return {
        "name": seg.get("name", "UNNAMED"),
        "composite": round(composite, 1),
        "breakdown": breakdown,
        "flags": flags,
        "verdict": verdict,
    }


def evaluate(data: dict, profile: str) -> dict:
    if profile not in PROFILES:
        raise ValueError(f"Unknown profile '{profile}'. Choose from {list(PROFILES)}.")
    mult = PROFILES[profile]
    scored = sorted((score_segment(s, mult) for s in data.get("segments", [])),
                    key=lambda x: x["composite"], reverse=True)
    return {
        "profile": profile,
        "segments": scored,
        "note": "A demographic or firmographic slice is not a segment unless it is substantial AND accessible.",
    }


def _render_human(r: dict) -> str:
    lines = [f"Segmentation Scoring (profile: {r['profile']})", ""]
    for s in r["segments"]:
        lines.append(f"[{s['verdict']}] {s['name']}  — composite {s['composite']}/100")
        for c, v in s["breakdown"].items():
            lines.append(f"      {c:16s} {v}")
        for f in s["flags"]:
            lines.append(f"      ! {f}")
        lines.append("")
    lines.append(f"note: {r['note']}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description="Score market segments against Kotler's 5 criteria.")
    p.add_argument("--input", help="Path to JSON with segments[]")
    p.add_argument("--profile", default=None, choices=list(PROFILES),
                   help="overrides onboarding default_profile")
    p.add_argument("--output", choices=["human", "json"], default="human")
    p.add_argument("--sample", action="store_true", help="use the embedded sample")
    args = p.parse_args(argv)

    conf = _cfg.load_config() if _cfg else {}
    profile = args.profile or conf.get("default_profile", "b2b-saas")
    data = SAMPLE if (args.sample or not args.input) else json.load(open(args.input))
    try:
        result = evaluate(data, profile)
    except ValueError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2

    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(_render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
