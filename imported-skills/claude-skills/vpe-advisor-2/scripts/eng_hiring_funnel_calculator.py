#!/usr/bin/env python3
"""eng_hiring_funnel_calculator.py — Eng hiring funnel health + pipeline gap.

Stdlib-only. Takes ATS funnel data and outputs:
  - Conversion rate per stage (Applied -> Sourcer -> Recruiter -> Hiring Mgr -> Tech -> Onsite -> Offer -> Accept)
  - End-to-end conversion rate
  - Time-to-fill (median across closed hires)
  - Pipeline volume gap (what's needed to hit hiring target)
  - Weakest-stage identification + typical fix

Deterministic math.

Input schema (JSON):
{
  "period_label": "Q2 2026",
  "period_days": 90,
  "hiring_target_engineers": 4,
  "funnel_stages": [
    {"stage": "applied", "count": 480},
    {"stage": "sourcer_screen", "count": 145},
    {"stage": "recruiter_screen", "count": 89},
    {"stage": "hiring_manager_screen", "count": 52},
    {"stage": "technical_interview", "count": 40},
    {"stage": "onsite_full_loop", "count": 14},
    {"stage": "offer_extended", "count": 5},
    {"stage": "offer_accepted", "count": 3}
  ],
  "median_time_to_fill_days": 62
}

Usage:
    python eng_hiring_funnel_calculator.py                       # uses embedded sample
    python eng_hiring_funnel_calculator.py path/to/funnel.json
    python eng_hiring_funnel_calculator.py funnel.json --output json
"""

import argparse
import json
import sys
from typing import Any, Dict, List


SAMPLE: Dict[str, Any] = {
    "period_label": "Q2 2026",
    "period_days": 90,
    "hiring_target_engineers": 4,
    "funnel_stages": [
        {"stage": "applied", "count": 480},
        {"stage": "sourcer_screen", "count": 145},
        {"stage": "recruiter_screen", "count": 89},
        {"stage": "hiring_manager_screen", "count": 52},
        {"stage": "technical_interview", "count": 40},
        {"stage": "onsite_full_loop", "count": 14},
        {"stage": "offer_extended", "count": 5},
        {"stage": "offer_accepted", "count": 3},
    ],
    "median_time_to_fill_days": 62,
}


# Healthy conversion benchmarks (B2B SaaS baseline, mid-stage)
HEALTHY_RANGES = {
    "applied_to_sourcer_screen":           (0.30, 0.50),
    "sourcer_screen_to_recruiter_screen":  (0.50, 0.70),
    "recruiter_screen_to_hiring_manager_screen": (0.60, 0.80),
    "hiring_manager_screen_to_technical_interview": (0.70, 0.85),
    "technical_interview_to_onsite_full_loop":      (0.30, 0.50),
    "onsite_full_loop_to_offer_extended":           (0.25, 0.40),
    "offer_extended_to_offer_accepted":             (0.70, 0.90),
}


# Bottleneck typical fixes
STAGE_FIXES = {
    "applied_to_sourcer_screen": [
        "Top of funnel volume / resume quality issue",
        "Diversify sourcing channels (cap inbound at 50%; rest via direct sourcing + referrals)",
        "Tighten job description if too broad; loosen if too specific",
    ],
    "sourcer_screen_to_recruiter_screen": [
        "Sourcer is over-filtering or under-filtering",
        "Calibrate with recruiter weekly; share rejection reasons",
        "Provide sourcer with explicit ICP rubric (must-haves vs nice-to-haves)",
    ],
    "recruiter_screen_to_hiring_manager_screen": [
        "Recruiter and hiring manager disagree on criteria",
        "Hiring manager should attend first 5 recruiter screens to calibrate",
        "Document explicit calibration notes for the role",
    ],
    "hiring_manager_screen_to_technical_interview": [
        "Hiring manager screen too lenient OR technical bar unclear",
        "Define explicit advance-vs-reject criteria for the hiring manager call",
        "Limit hiring manager screen to 30 min; technical bar comes next",
    ],
    "technical_interview_to_onsite_full_loop": [
        "Technical bar too high for the role level",
        "Or: technical interview is filtering for wrong skills (e.g., algorithms when job is integration work)",
        "Calibrate technical interviewers; share rubric; rotate to avoid one strict gatekeeper",
    ],
    "onsite_full_loop_to_offer_extended": [
        "Onsite is over-correlated with first interviewer (anchoring bias)",
        "Use structured rubrics; require independent scoring before debrief",
        "Hire debrief facilitator if no one is owning the calibration",
    ],
    "offer_extended_to_offer_accepted": [
        "Comp is below market — run cs-chro-advisor's comp_benchmarker",
        "Close discipline is weak — VPE / hiring manager should close personally",
        "Offer letter too slow; candidates accept competing offers in the gap",
    ],
}


def conversion_rate(top: float, bottom: float) -> float:
    return bottom / top if top else 0


def level(rate: float, healthy_min: float, healthy_max: float) -> str:
    if rate >= healthy_min and rate <= healthy_max:
        return "Healthy"
    if rate < healthy_min:
        return "LEAKY"
    return "Above benchmark"


def analyze(payload: Dict[str, Any]) -> Dict[str, Any]:
    stages = payload.get("funnel_stages", [])
    stage_counts = {s["stage"]: s["count"] for s in stages}

    # Compute conversion per stage
    transitions = []
    stage_order = [s["stage"] for s in stages]
    for i in range(len(stage_order) - 1):
        top_stage = stage_order[i]
        bottom_stage = stage_order[i + 1]
        top = stage_counts.get(top_stage, 0)
        bottom = stage_counts.get(bottom_stage, 0)
        rate = conversion_rate(top, bottom)
        key = f"{top_stage}_to_{bottom_stage}"
        healthy = HEALTHY_RANGES.get(key, (0.3, 1.0))
        transitions.append({
            "transition": key,
            "from": top_stage,
            "to": bottom_stage,
            "from_count": top,
            "to_count": bottom,
            "rate": round(rate, 3),
            "rate_pct": round(rate * 100, 1),
            "healthy_min_pct": round(healthy[0] * 100, 1),
            "healthy_max_pct": round(healthy[1] * 100, 1),
            "level": level(rate, healthy[0], healthy[1]),
        })

    # End-to-end conversion
    if stage_counts:
        top_count = stages[0]["count"] if stages else 0
        bottom_count = stages[-1]["count"] if stages else 0
        end_to_end = conversion_rate(top_count, bottom_count)
    else:
        end_to_end = 0

    # Pipeline gap
    target = payload.get("hiring_target_engineers", 0)
    if end_to_end > 0:
        required_top = int(target / end_to_end)
    else:
        required_top = None
    current_top = stages[0]["count"] if stages else 0
    pipeline_gap = (required_top - current_top) if required_top is not None else None

    # Weakest stage
    leaky = [t for t in transitions if t["level"] == "LEAKY"]
    if leaky:
        # Pick the one with the largest gap from healthy_min
        weakest = min(leaky, key=lambda t: t["rate"] - t["healthy_min_pct"] / 100)
    else:
        weakest = None

    return {
        "period_label": payload.get("period_label"),
        "hiring_target": target,
        "transitions": transitions,
        "end_to_end_conversion": round(end_to_end, 4),
        "end_to_end_pct": round(end_to_end * 100, 2),
        "current_top_of_funnel": current_top,
        "required_top_of_funnel_for_target": required_top,
        "pipeline_gap": pipeline_gap,
        "median_time_to_fill_days": payload.get("median_time_to_fill_days"),
        "weakest_stage": weakest,
        "weakest_stage_fixes": STAGE_FIXES.get(weakest["transition"], []) if weakest else [],
    }


def render_text(result: Dict[str, Any], source: str) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("ENGINEERING HIRING FUNNEL")
    lines.append(f"Source: {source}")
    lines.append("=" * 72)
    lines.append("")
    lines.append(f"Period: {result['period_label']}  |  Hiring target: {result['hiring_target']} engineers")
    lines.append(f"Median time-to-fill: {result['median_time_to_fill_days']} days")
    lines.append("")
    lines.append("-" * 72)
    lines.append("FUNNEL CONVERSION:")
    lines.append("")
    for t in result["transitions"]:
        marker = "🟢" if t["level"] == "Healthy" else ("🔴" if t["level"] == "LEAKY" else "🔵")
        lines.append(f"  {marker} {t['from']:<28} -> {t['to']:<28}")
        lines.append(f"      {t['from_count']:>4} -> {t['to_count']:>4}  ({t['rate_pct']:>5.1f}%)   [healthy {t['healthy_min_pct']}-{t['healthy_max_pct']}%]  {t['level']}")
        lines.append("")

    lines.append("-" * 72)
    lines.append(f"END-TO-END CONVERSION: {result['end_to_end_pct']}%  (top to accepted)")
    lines.append("")
    lines.append("PIPELINE GAP:")
    lines.append(f"  Current top of funnel: {result['current_top_of_funnel']}")
    lines.append(f"  Required for target ({result['hiring_target']} hires): {result['required_top_of_funnel_for_target']}")
    gap = result["pipeline_gap"]
    if gap is None:
        lines.append("  Pipeline gap: unable to compute (no conversions)")
    elif gap > 0:
        lines.append(f"  Pipeline gap: +{gap} candidates needed at top of funnel  🔴")
    else:
        lines.append(f"  Pipeline gap: 0 (sufficient — overflow {-gap})  🟢")
    lines.append("")
    lines.append("-" * 72)

    if result["weakest_stage"]:
        w = result["weakest_stage"]
        lines.append(f"WEAKEST STAGE: {w['transition']}  ({w['rate_pct']}% vs healthy {w['healthy_min_pct']}+%)")
        lines.append("")
        lines.append("Recommended fixes:")
        for f in result["weakest_stage_fixes"]:
            lines.append(f"  • {f}")
        lines.append("")
    else:
        lines.append("No LEAKY stages detected. Funnel conversions within healthy ranges.")
        lines.append("")

    lines.append("-" * 72)
    lines.append("REMINDER: 'We can't find good engineers' usually means a specific stage is leaking, or")
    lines.append("top-of-funnel volume is too low. Fix the funnel; don't over-recruit before fixing.")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Engineering hiring funnel: conversion + pipeline gap + weakest-stage fixes.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("path", nargs="?", help="Path to funnel JSON (uses embedded sample if omitted)")
    parser.add_argument("--output", choices=("text", "json"), default="text", help="Output format")
    args = parser.parse_args()

    if args.path:
        try:
            with open(args.path, "r", encoding="utf-8") as f:
                payload = json.load(f)
            source = args.path
        except (IOError, OSError) as e:
            print(f"error: could not read {args.path}: {e}", file=sys.stderr)
            return 1
        except json.JSONDecodeError as e:
            print(f"error: invalid JSON in {args.path}: {e}", file=sys.stderr)
            return 1
    else:
        payload = SAMPLE
        source = "<embedded sample: Q2 2026, 4-engineer hiring target>"

    result = analyze(payload)

    if args.output == "json":
        print(json.dumps({"source": source, **result}, indent=2))
    else:
        print(render_text(result, source))

    return 0


if __name__ == "__main__":
    sys.exit(main())
