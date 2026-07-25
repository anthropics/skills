#!/usr/bin/env python3
"""saturation_planner.py - Method-based participant/sample guidance with a confidence label.

Stdlib-only. Deterministic. NO LLM calls. NEVER fabricates insight: it gives method-based
sample guidance and an explicit confidence level, surfacing limits.

Models:
  - usability (Nielsen): ~5 users per segment uncovers ~85% of problems at typical p=0.31;
    problems found = 1 - (1 - p)^n.
  - thematic saturation (Guest et al.): ~12 interviews per homogeneous group typically
    reaches saturation; >5 (Faulkner) when stakes/heterogeneity are high.
  - evaluative coverage: detectable-problem coverage for a chosen per-problem detection rate.

Usage:
    python3 saturation_planner.py --sample
    python3 saturation_planner.py --method usability --segments 2 --detection-rate 0.31
    python3 saturation_planner.py --method thematic --segments 3 --output json
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

METHODS = ["usability", "thematic", "evaluative-coverage"]


def usability_plan(segments: int, p: float, target_coverage: float) -> dict:
    # n per segment to reach target coverage: n = ln(1 - target) / ln(1 - p)
    import math
    if not 0.0 < p < 1.0:
        raise ValueError("detection-rate must be in (0,1).")
    n = math.ceil(math.log(1 - target_coverage) / math.log(1 - p))
    coverage_at_5 = 1 - (1 - p) ** 5
    return {
        "method": "usability",
        "per_problem_detection_rate": p,
        "target_coverage": target_coverage,
        "n_per_segment": n,
        "segments": segments,
        "total_participants": n * segments,
        "coverage_at_5_per_segment": round(coverage_at_5, 3),
        "confidence": "MODERATE" if n >= 5 else "LOW (small-n usability finds problems, not rates)",
        "limits": "Usability tests surface problems, not their population prevalence. Do not report percentages.",
    }


def thematic_plan(segments: int, stakes_high: bool) -> dict:
    base = 12  # Guest et al. typical saturation for a homogeneous group
    per_segment = base if not stakes_high else max(base, 15)
    return {
        "method": "thematic",
        "n_per_segment": per_segment,
        "segments": segments,
        "total_participants": per_segment * segments,
        "confidence": "MODERATE-HIGH" if per_segment >= 12 else "LOW",
        "limits": "Saturation is observed, not guaranteed; track new-theme rate and stop when it flattens. "
                  "Faulkner (2003): more than 5 when heterogeneity or stakes are high.",
    }


def evaluative_coverage_plan(segments: int, n_per_segment: int, p: float) -> dict:
    coverage = 1 - (1 - p) ** n_per_segment
    return {
        "method": "evaluative-coverage",
        "per_problem_detection_rate": p,
        "n_per_segment": n_per_segment,
        "segments": segments,
        "expected_problem_coverage": round(coverage, 3),
        "confidence": "MODERATE" if coverage >= 0.8 else "LOW",
        "limits": "Coverage is for the assumed detection rate; rarer problems need more participants.",
    }


def plan(method: str, segments: int, p: float, target: float, stakes_high: bool, n: int) -> dict:
    if method == "usability":
        out = usability_plan(segments, p, target)
    elif method == "thematic":
        out = thematic_plan(segments, stakes_high)
    elif method == "evaluative-coverage":
        out = evaluative_coverage_plan(segments, n, p)
    else:
        raise ValueError(f"method must be one of {METHODS}.")
    out["disclaimer"] = "Method-based guidance with explicit confidence. This is not a power calculation; " \
                        "it never claims an insight the data cannot support."
    return out


def _render_human(r: dict) -> str:
    lines = [f"Saturation / Sample Plan  (method: {r['method']})", ""]
    for k, v in r.items():
        if k in ("method",):
            continue
        lines.append(f"  {k:32s} : {v}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description="Method-based product-research sample guidance with confidence.")
    p.add_argument("--method", choices=METHODS, default=None, help="overrides onboarding default_method")
    p.add_argument("--segments", type=int, default=1)
    p.add_argument("--detection-rate", type=float, default=0.31, help="per-problem detection rate (usability)")
    p.add_argument("--target-coverage", type=float, default=0.85, help="target problem coverage (usability)")
    p.add_argument("--stakes-high", action="store_true", help="raise thematic n for high heterogeneity/stakes")
    p.add_argument("--n-per-segment", type=int, default=8, help="n per segment (evaluative-coverage)")
    p.add_argument("--output", choices=["human", "json"], default="human")
    p.add_argument("--sample", action="store_true", help="use the embedded sample")
    args = p.parse_args(argv)

    conf = _cfg.load_config() if _cfg else {}
    method = args.method or conf.get("default_method", "usability")
    stakes_high = args.stakes_high or bool(conf.get("stakes_high", False))

    if args.sample:
        try:
            result = plan("usability", 2, 0.31, 0.85, False, 8)
        except ValueError as e:
            print(f"error: {e}", file=sys.stderr)
            return 2
    else:
        try:
            result = plan(method, args.segments, args.detection_rate,
                          args.target_coverage, stakes_high, args.n_per_segment)
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
