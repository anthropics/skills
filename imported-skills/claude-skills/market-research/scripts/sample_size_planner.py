#!/usr/bin/env python3
"""sample_size_planner.py - Survey sample-size with finite-population correction + per-segment minima.

Stdlib-only. Deterministic. NO LLM calls.

Computes the classic proportion-estimate sample size:
    n0 = z^2 * p * (1-p) / e^2
then applies the finite-population correction (FPC) when a population N is given:
    n  = n0 / (1 + (n0 - 1)/N)
Also computes per-segment minimums and a proportional quota allocation, because a survey
powered overall is NOT powered per reported segment.

Usage:
    python3 sample_size_planner.py --sample
    python3 sample_size_planner.py --population 62000 --confidence 0.95 --moe 0.05 --proportion 0.5
    python3 sample_size_planner.py --input survey.json --output json
"""

from __future__ import annotations

import argparse
import json
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
try:
    import config_loader as _cfg
except ImportError:  # pragma: no cover
    _cfg = None

Z = {0.80: 1.2816, 0.85: 1.4395, 0.90: 1.6449, 0.95: 1.9600, 0.99: 2.5758}

SAMPLE = {
    "population": 62000,
    "confidence": 0.95,
    "margin_of_error": 0.05,
    "expected_proportion": 0.5,
    "segments": [
        {"name": "1-50 employees", "population_share": 0.55},
        {"name": "51-250 employees", "population_share": 0.30},
        {"name": "251-1000 employees", "population_share": 0.15},
    ],
    "segment_moe": 0.08,
}


def _z(conf: float) -> float:
    if conf not in Z:
        raise ValueError(f"confidence must be one of {sorted(Z)}.")
    return Z[conf]


def base_n(conf: float, moe: float, p: float, population: float | None) -> dict:
    if not 0.0 < p < 1.0:
        raise ValueError("expected_proportion must be in (0,1).")
    if not 0.0 < moe < 1.0:
        raise ValueError("margin_of_error must be in (0,1).")
    z = _z(conf)
    n0 = (z ** 2) * p * (1 - p) / (moe ** 2)
    if population and population > 0:
        n = n0 / (1 + (n0 - 1) / population)
        fpc_applied = True
    else:
        n = n0
        fpc_applied = False
    return {
        "confidence": conf,
        "margin_of_error": moe,
        "expected_proportion": p,
        "population": population,
        "n_unadjusted": math.ceil(n0),
        "n_with_fpc": math.ceil(n),
        "fpc_applied": fpc_applied,
        "z": z,
    }


def segment_plan(data: dict, overall: dict) -> dict:
    seg_moe = float(data.get("segment_moe", data.get("margin_of_error", 0.05)))
    conf = float(data.get("confidence", 0.95))
    p = float(data.get("expected_proportion", 0.5))
    z = _z(conf)
    per_seg_min = math.ceil((z ** 2) * p * (1 - p) / (seg_moe ** 2))

    segs = data.get("segments", [])
    total_quota = max(overall["n_with_fpc"], per_seg_min * len(segs)) if segs else overall["n_with_fpc"]
    out_segs = []
    for s in segs:
        share = float(s.get("population_share", 0.0))
        proportional = math.ceil(total_quota * share)
        quota = max(proportional, per_seg_min)
        out_segs.append({
            "name": s.get("name", "UNNAMED"),
            "population_share": share,
            "proportional_quota": proportional,
            "minimum_for_segment_moe": per_seg_min,
            "recommended_quota": quota,
        })
    return {
        "segment_margin_of_error": seg_moe,
        "minimum_per_segment": per_seg_min,
        "recommended_total_with_segment_floors": sum(s["recommended_quota"] for s in out_segs) if out_segs else total_quota,
        "segments": out_segs,
    }


def plan(data: dict) -> dict:
    overall = base_n(
        float(data.get("confidence", 0.95)),
        float(data.get("margin_of_error", 0.05)),
        float(data.get("expected_proportion", 0.5)),
        data.get("population"),
    )
    result = {"overall": overall}
    if data.get("segments"):
        result["segmentation"] = segment_plan(data, overall)
    result["notes"] = [
        "A survey powered overall is NOT powered per reported segment — fund the segment floors.",
        "expected_proportion=0.5 is the conservative (maximum-variance) default.",
        "FPC matters when the sample is a large fraction of the population (small N).",
    ]
    return result


def _render_human(r: dict) -> str:
    o = r["overall"]
    lines = ["Survey Sample-Size Plan", "",
             f"  Confidence: {o['confidence']:.0%}   MoE: {o['margin_of_error']:.0%}   p: {o['expected_proportion']}",
             f"  n (unadjusted):      {o['n_unadjusted']}",
             f"  n (with FPC):        {o['n_with_fpc']}  (population {o['population']}, fpc_applied={o['fpc_applied']})"]
    if "segmentation" in r:
        s = r["segmentation"]
        lines += ["", f"  Per-segment MoE: {s['segment_margin_of_error']:.0%}  => minimum {s['minimum_per_segment']} per segment",
                  f"  Recommended total with segment floors: {s['recommended_total_with_segment_floors']}", ""]
        for seg in s["segments"]:
            lines.append(f"    {seg['name']:24s} share {seg['population_share']:.0%}  "
                         f"proportional {seg['proportional_quota']}  recommended {seg['recommended_quota']}")
    lines += ["", "Notes:"]
    for n in r["notes"]:
        lines.append(f"  - {n}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description="Survey sample size with FPC + per-segment minima.")
    p.add_argument("--input", help="Path to JSON survey spec")
    p.add_argument("--population", type=float, default=None)
    p.add_argument("--confidence", type=float, default=None, help="overrides onboarding default_confidence")
    p.add_argument("--moe", type=float, default=None, help="margin of error (overrides onboarding default_moe)")
    p.add_argument("--proportion", type=float, default=0.5, help="expected proportion")
    p.add_argument("--output", choices=["human", "json"], default="human")
    p.add_argument("--sample", action="store_true", help="use the embedded sample")
    args = p.parse_args(argv)

    conf = _cfg.load_config() if _cfg else {}
    confidence = args.confidence if args.confidence is not None else conf.get("default_confidence", 0.95)
    moe = args.moe if args.moe is not None else conf.get("default_moe", 0.05)

    if args.sample:
        data = SAMPLE
    elif args.input:
        data = json.load(open(args.input))
    else:
        data = {"population": args.population, "confidence": confidence,
                "margin_of_error": moe, "expected_proportion": args.proportion}

    try:
        result = plan(data)
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
