#!/usr/bin/env python3
"""hiring_sequencer.py — 12-month quarterly hiring plan for ops teams.

Accounts for:
  * Ramp time (productive ~50% for ramp_time_weeks, then 100%)
  * Annual attrition (compounded weekly across the year)
  * Quarter-over-quarter demand growth
  * Hiring constraints (max hires / quarter)
  * Manager-trigger: when span of control crosses 7-8 ICs, schedule manager hire

Stdlib only.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Any


# Industry profiles — typical ramp + attrition
PROFILES: dict[str, dict[str, float]] = {
    "support":    {"ramp_time_weeks": 8.0,  "attrition_rate_annual_pct": 30.0},
    "cx":         {"ramp_time_weeks": 10.0, "attrition_rate_annual_pct": 28.0},
    "bizops":     {"ramp_time_weeks": 12.0, "attrition_rate_annual_pct": 18.0},
    "finance-ops":{"ramp_time_weeks": 14.0, "attrition_rate_annual_pct": 15.0},
    "it-ops":     {"ramp_time_weeks": 10.0, "attrition_rate_annual_pct": 20.0},
}

SPAN_OF_CONTROL_MAX = 7  # ICs per manager threshold (Fournier)


class Quarter(str, Enum):
    Q1 = "Q1"
    Q2 = "Q2"
    Q3 = "Q3"
    Q4 = "Q4"


@dataclass
class HiringInput:
    team_name: str
    current_fte: int
    target_fte_end_of_year: int
    ramp_time_weeks: float
    attrition_rate_annual_pct: float
    growth_assumption_qoq_pct: float
    max_hires_per_quarter: int


@dataclass
class QuarterPlan:
    quarter: Quarter
    ic_hires: int
    manager_hires: int
    expected_attrition: int
    productive_fte_end_of_quarter: float
    headcount_end_of_quarter: int
    span_of_control: float
    notes: list[str] = field(default_factory=list)


@dataclass
class HiringResult:
    team_name: str
    inputs: HiringInput
    quarters: list[QuarterPlan]
    total_ic_hires: int
    total_manager_hires: int
    total_attrition: int
    headline: str
    warnings: list[str] = field(default_factory=list)


def _productivity_factor(weeks_since_hire: float, ramp_weeks: float) -> float:
    """Linear ramp 50% → 100% over ramp_weeks (Larson)."""
    if weeks_since_hire >= ramp_weeks:
        return 1.0
    if weeks_since_hire <= 0:
        return 0.5
    return 0.5 + 0.5 * (weeks_since_hire / ramp_weeks)


def sequence(inp: HiringInput) -> HiringResult:
    # Demand-side ratchet: target adjusted up by QoQ growth (compounded)
    growth_factor_eoy = (1.0 + inp.growth_assumption_qoq_pct / 100.0) ** 4
    adjusted_target = int(math.ceil(inp.target_fte_end_of_year * growth_factor_eoy))

    # Per-quarter attrition probability — split annual rate across 4 quarters
    q_attrition_rate = 1.0 - (1.0 - inp.attrition_rate_annual_pct / 100.0) ** 0.25

    # Total gap to close: target + replacement hires over the year
    expected_total_attrition = int(math.ceil(
        inp.current_fte * (inp.attrition_rate_annual_pct / 100.0)
    ))
    raw_gap = adjusted_target - inp.current_fte + expected_total_attrition
    total_hires_needed = max(0, raw_gap)

    # Distribute hires front-loaded but capped
    quarters: list[QuarterPlan] = []
    headcount = inp.current_fte
    remaining = total_hires_needed
    cumulative_managers = max(1, math.ceil(inp.current_fte / SPAN_OF_CONTROL_MAX))
    cumulative_ic_hires = 0
    cumulative_manager_hires = 0
    cumulative_attrition = 0
    warnings: list[str] = []

    # Pre-emptive front-load: aim higher in early quarters so ramp completes by EOY
    # Allocation weights Q1>Q2>Q3>Q4 since later hires miss ramp window.
    weights = [0.35, 0.30, 0.20, 0.15]

    for i, qname in enumerate(Quarter):
        ideal_q_hires = math.ceil(total_hires_needed * weights[i])
        q_hires = min(ideal_q_hires, inp.max_hires_per_quarter, remaining)
        if q_hires < ideal_q_hires:
            warnings.append(
                f"{qname.value}: wanted {ideal_q_hires} hires but constrained "
                f"to {q_hires} by max_hires_per_quarter."
            )

        # Attrition realized this quarter
        q_attrition = int(round(headcount * q_attrition_rate))
        cumulative_attrition += q_attrition

        # New headcount after hires + attrition
        new_headcount = headcount + q_hires - q_attrition

        # Manager trigger check — if ICs / managers > threshold, add a manager hire
        # (counted within the ic_hires bucket reallocated as manager)
        ic_count_eoq = new_headcount - cumulative_managers
        span = ic_count_eoq / max(cumulative_managers, 1)
        notes: list[str] = []
        manager_hires_this_q = 0
        if span > SPAN_OF_CONTROL_MAX and q_hires > 0:
            manager_hires_this_q = 1
            q_hires -= 1
            cumulative_managers += 1
            notes.append(
                f"Manager trigger fired: span was {span:.1f} ICs/manager > "
                f"{SPAN_OF_CONTROL_MAX}. Reallocated 1 IC hire to manager hire."
            )
            # Recompute span after manager hire
            ic_count_eoq = new_headcount - cumulative_managers
            span = ic_count_eoq / max(cumulative_managers, 1)

        cumulative_ic_hires += q_hires
        cumulative_manager_hires += manager_hires_this_q
        remaining -= (q_hires + manager_hires_this_q)

        # Productive FTE = full-time members + ramp-fraction for in-quarter hires
        # in-quarter hires are halfway through ramp on average at EOQ → ~halfway up the ramp curve
        avg_weeks_for_q_hires = 6.5  # quarter midpoint (13 weeks / 2)
        ramp_fraction = _productivity_factor(avg_weeks_for_q_hires, inp.ramp_time_weeks)
        productive_fte = (headcount - q_attrition) + (q_hires + manager_hires_this_q) * ramp_fraction

        if productive_fte < adjusted_target * 0.85 and i == 3:
            warnings.append(
                f"EOY productive FTE ({productive_fte:.1f}) below 85% of adjusted "
                f"target ({adjusted_target}) — ramp will extend into next year."
            )

        quarters.append(QuarterPlan(
            quarter=qname,
            ic_hires=q_hires,
            manager_hires=manager_hires_this_q,
            expected_attrition=q_attrition,
            productive_fte_end_of_quarter=round(productive_fte, 1),
            headcount_end_of_quarter=new_headcount,
            span_of_control=round(span, 2),
            notes=notes,
        ))

        headcount = new_headcount

    headline = (
        f"Hire {cumulative_ic_hires} ICs + {cumulative_manager_hires} managers "
        f"across 4 quarters. End-of-year nominal headcount: {headcount} "
        f"(adjusted target: {adjusted_target}). Expect ~{cumulative_attrition} "
        f"attrition over the year."
    )

    return HiringResult(
        team_name=inp.team_name,
        inputs=inp,
        quarters=quarters,
        total_ic_hires=cumulative_ic_hires,
        total_manager_hires=cumulative_manager_hires,
        total_attrition=cumulative_attrition,
        headline=headline,
        warnings=warnings,
    )


def to_markdown(r: HiringResult) -> str:
    lines = [
        f"# Hiring Plan — {r.team_name}",
        "",
        f"**Headline:** {r.headline}",
        "",
        "## Assumptions",
        f"- Current FTE: {r.inputs.current_fte}",
        f"- Target EOY FTE (nominal): {r.inputs.target_fte_end_of_year}",
        f"- Ramp time: {r.inputs.ramp_time_weeks} weeks",
        f"- Annual attrition: {r.inputs.attrition_rate_annual_pct}%",
        f"- QoQ growth: {r.inputs.growth_assumption_qoq_pct}%",
        f"- Max hires per quarter: {r.inputs.max_hires_per_quarter}",
        "",
        "## Quarterly Plan",
        "",
        "| Quarter | IC Hires | Manager Hires | Attrition | Headcount EOQ | Productive FTE EOQ | Span of Control |",
        "|---|---|---|---|---|---|---|",
    ]
    for q in r.quarters:
        lines.append(
            f"| {q.quarter.value} | {q.ic_hires} | {q.manager_hires} | "
            f"{q.expected_attrition} | {q.headcount_end_of_quarter} | "
            f"{q.productive_fte_end_of_quarter} | {q.span_of_control} |"
        )
    lines.append("")
    notes_present = any(q.notes for q in r.quarters)
    if notes_present:
        lines.append("## Quarter Notes")
        for q in r.quarters:
            for n in q.notes:
                lines.append(f"- {q.quarter.value}: {n}")
        lines.append("")
    if r.warnings:
        lines.append("## Warnings")
        for w in r.warnings:
            lines.append(f"- {w}")
        lines.append("")
    lines.extend([
        "## Canon",
        "- Camille Fournier, *The Manager's Path* — span of control thresholds.",
        "- Will Larson, *Staff Engineer* — ramp productivity curves.",
        "- Bersin/Deloitte talent benchmarks — attrition + replacement hire ratios.",
    ])
    return "\n".join(lines)


def to_dict(r: HiringResult) -> dict[str, Any]:
    return {
        "team_name": r.team_name,
        "headline": r.headline,
        "totals": {
            "ic_hires": r.total_ic_hires,
            "manager_hires": r.total_manager_hires,
            "attrition": r.total_attrition,
        },
        "quarters": [
            {
                "quarter": q.quarter.value,
                "ic_hires": q.ic_hires,
                "manager_hires": q.manager_hires,
                "expected_attrition": q.expected_attrition,
                "productive_fte_end_of_quarter": q.productive_fte_end_of_quarter,
                "headcount_end_of_quarter": q.headcount_end_of_quarter,
                "span_of_control": q.span_of_control,
                "notes": q.notes,
            }
            for q in r.quarters
        ],
        "warnings": r.warnings,
        "inputs": {
            "current_fte": r.inputs.current_fte,
            "target_fte_end_of_year": r.inputs.target_fte_end_of_year,
            "ramp_time_weeks": r.inputs.ramp_time_weeks,
            "attrition_rate_annual_pct": r.inputs.attrition_rate_annual_pct,
            "growth_assumption_qoq_pct": r.inputs.growth_assumption_qoq_pct,
            "max_hires_per_quarter": r.inputs.max_hires_per_quarter,
        },
    }


SAMPLE_INPUT: dict[str, Any] = {
    "team_name": "Tier-1 Support",
    "current_fte": 15,
    "target_fte_end_of_year": 35,
    "ramp_time_weeks": 8,
    "attrition_rate_annual_pct": 30,
    "growth_assumption_qoq_pct": 8,
    "hiring_constraints": {"max_hires_per_quarter": 8},
}


def parse_input(raw: dict[str, Any], profile: str | None) -> HiringInput:
    prof = PROFILES.get(profile or "", {})
    ramp = raw.get("ramp_time_weeks", prof.get("ramp_time_weeks", 10.0))
    attr = raw.get(
        "attrition_rate_annual_pct",
        prof.get("attrition_rate_annual_pct", 25.0),
    )
    constraints = raw.get("hiring_constraints", {}) or {}
    return HiringInput(
        team_name=raw["team_name"],
        current_fte=int(raw["current_fte"]),
        target_fte_end_of_year=int(raw["target_fte_end_of_year"]),
        ramp_time_weeks=float(ramp),
        attrition_rate_annual_pct=float(attr),
        growth_assumption_qoq_pct=float(raw.get("growth_assumption_qoq_pct", 0.0)),
        max_hires_per_quarter=int(constraints.get("max_hires_per_quarter", 999)),
    )


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(
        description="12-month quarterly hiring sequencer with ramp + attrition.",
    )
    p.add_argument("--input", type=Path, help="Path to JSON input file.")
    p.add_argument(
        "--profile",
        choices=list(PROFILES.keys()),
        default=None,
        help="Industry profile (defaults for ramp + attrition).",
    )
    p.add_argument(
        "--output", choices=["markdown", "json"], default="markdown",
        help="Output format.",
    )
    p.add_argument("--sample", action="store_true",
                   help="Run on built-in sample input.")
    args = p.parse_args(argv)

    if args.sample:
        raw = SAMPLE_INPUT
    elif args.input:
        raw = json.loads(args.input.read_text())
    else:
        p.error("Provide --input or --sample.")
        return 2

    try:
        inp = parse_input(raw, args.profile)
    except (KeyError, ValueError) as e:
        print(f"ERROR parsing input: {e}", file=sys.stderr)
        return 2

    result = sequence(inp)
    if args.output == "json":
        print(json.dumps(to_dict(result), indent=2))
    else:
        print(to_markdown(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
