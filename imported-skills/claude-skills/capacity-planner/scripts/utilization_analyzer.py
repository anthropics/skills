#!/usr/bin/env python3
"""utilization_analyzer.py — per-member + team-level utilization health.

Detects:
  * RED  : sustained >85% utilization (throughput collapse risk, Reinertsen)
  * AMBER: 70-85% (acceptable but watch — Little's Law tightening)
  * GREEN: 40-70% (healthy)
  * BLUE : <40% (under-loaded or wrong skills)

Team verdict:
  HEALTHY    — most green, no reds, low variance
  SQUEEZED   — majority amber, some red
  OVERLOADED — >30% of team red
  UNBALANCED — utilization variance >30 percentage points across team

Stdlib only.
"""
from __future__ import annotations

import argparse
import json
import statistics
import sys
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Any


class Light(str, Enum):
    GREEN = "GREEN"
    AMBER = "AMBER"
    RED = "RED"
    BLUE = "BLUE"


class TeamVerdict(str, Enum):
    HEALTHY = "HEALTHY"
    SQUEEZED = "SQUEEZED"
    OVERLOADED = "OVERLOADED"
    UNBALANCED = "UNBALANCED"


@dataclass
class Member:
    name: str
    role: str
    utilization_pct: float
    handles_count: int
    hours_billable: float
    hours_capacity: float


@dataclass
class MemberAssessment:
    name: str
    role: str
    utilization_pct: float
    light: Light
    notes: list[str] = field(default_factory=list)


@dataclass
class TeamReport:
    verdict: TeamVerdict
    member_assessments: list[MemberAssessment]
    mean_util: float
    median_util: float
    stdev_util: float
    spread_pct_points: float
    counts: dict[str, int]
    headline: str
    recommendations: list[str]


def classify(member: Member) -> MemberAssessment:
    u = member.utilization_pct
    notes: list[str] = []
    if u >= 85:
        light = Light.RED
        notes.append("Throughput collapse risk per queueing theory (>85% sustained).")
    elif u >= 70:
        light = Light.AMBER
        notes.append("Within tolerable band but no surge capacity.")
    elif u >= 40:
        light = Light.GREEN
    else:
        light = Light.BLUE
        notes.append("Under-loaded — verify scope or reassign work.")

    # Cross-check billable vs capacity hours — if claimed utilization
    # disagrees with hours math by >10 points, flag.
    if member.hours_capacity > 0:
        computed = member.hours_billable / member.hours_capacity * 100
        if abs(computed - u) > 10:
            notes.append(
                f"Reported util ({u:.0f}%) disagrees with hours math "
                f"({computed:.0f}%). Reconcile time tracking."
            )

    return MemberAssessment(
        name=member.name,
        role=member.role,
        utilization_pct=u,
        light=light,
        notes=notes,
    )


def assess_team(members: list[Member]) -> TeamReport:
    if not members:
        raise ValueError("No team members in input.")

    assessments = [classify(m) for m in members]
    utils = [m.utilization_pct for m in members]
    mean_u = statistics.fmean(utils)
    median_u = statistics.median(utils)
    stdev_u = statistics.pstdev(utils) if len(utils) > 1 else 0.0
    spread = max(utils) - min(utils)

    counts = {
        "RED": sum(1 for a in assessments if a.light == Light.RED),
        "AMBER": sum(1 for a in assessments if a.light == Light.AMBER),
        "GREEN": sum(1 for a in assessments if a.light == Light.GREEN),
        "BLUE": sum(1 for a in assessments if a.light == Light.BLUE),
    }
    n = len(members)

    # Verdict logic — order matters
    if spread > 30:
        verdict = TeamVerdict.UNBALANCED
        headline = (f"Load spread of {spread:.0f} percentage points across team — "
                    f"some are red while others are blue.")
    elif counts["RED"] / n > 0.30:
        verdict = TeamVerdict.OVERLOADED
        headline = (f"{counts['RED']} of {n} members in RED zone. Throughput "
                    f"collapse risk.")
    elif counts["AMBER"] / n >= 0.50 or counts["RED"] >= 1:
        verdict = TeamVerdict.SQUEEZED
        headline = f"Team running hot — {counts['AMBER']} amber, {counts['RED']} red."
    else:
        verdict = TeamVerdict.HEALTHY
        headline = f"Team utilization healthy: mean {mean_u:.0f}%, spread {spread:.0f}pp."

    recs: list[str] = []
    if verdict == TeamVerdict.UNBALANCED:
        recs.append("Rebalance load — investigate whether reds need different skills, "
                    "specialization, or just more hands at their queue.")
    if verdict == TeamVerdict.OVERLOADED:
        recs.append("Stop adding scope. Hire or shed work BEFORE attempting "
                    "process improvements (Goldratt: subordinate to the constraint).")
    if verdict == TeamVerdict.SQUEEZED:
        recs.append("Plan to hire next quarter. Re-test in 30 days; squeeze tends "
                    "to become overload during seasonal peaks.")
    if counts["BLUE"] > 0:
        recs.append(f"{counts['BLUE']} member(s) under-loaded — check whether "
                    f"work is reaching them or whether scope/skill needs adjustment.")
    if not recs:
        recs.append("Maintain current sizing; revisit at next quarterly planning cycle.")

    return TeamReport(
        verdict=verdict,
        member_assessments=assessments,
        mean_util=round(mean_u, 1),
        median_util=round(median_u, 1),
        stdev_util=round(stdev_u, 1),
        spread_pct_points=round(spread, 1),
        counts=counts,
        headline=headline,
        recommendations=recs,
    )


def to_markdown(r: TeamReport) -> str:
    lines = [
        "# Utilization Analysis",
        "",
        f"**Verdict:** {r.verdict.value}",
        "",
        f"**Headline:** {r.headline}",
        "",
        "## Team Stats",
        f"- Mean utilization: {r.mean_util}%",
        f"- Median utilization: {r.median_util}%",
        f"- Stdev: {r.stdev_util}pp",
        f"- Spread (max - min): {r.spread_pct_points}pp",
        f"- Counts: RED {r.counts['RED']} / AMBER {r.counts['AMBER']} / "
        f"GREEN {r.counts['GREEN']} / BLUE {r.counts['BLUE']}",
        "",
        "## Member Detail",
        "",
        "| Name | Role | Utilization | Light | Notes |",
        "|---|---|---|---|---|",
    ]
    for a in r.member_assessments:
        notes_str = "; ".join(a.notes) if a.notes else "—"
        lines.append(
            f"| {a.name} | {a.role} | {a.utilization_pct:.0f}% | {a.light.value} | {notes_str} |"
        )
    lines.extend(["", "## Recommendations"])
    for rec in r.recommendations:
        lines.append(f"- {rec}")
    lines.extend([
        "",
        "## Canon",
        "- Reinertsen, *Principles of Product Development Flow*, principle 7.",
        "- Little (1961), *A Proof for the Queuing Formula L = λW*.",
        "- Goldratt, *The Goal* — bottleneck subordination.",
    ])
    return "\n".join(lines)


def to_dict(r: TeamReport) -> dict[str, Any]:
    return {
        "verdict": r.verdict.value,
        "headline": r.headline,
        "stats": {
            "mean_util": r.mean_util,
            "median_util": r.median_util,
            "stdev_util": r.stdev_util,
            "spread_pct_points": r.spread_pct_points,
            "counts": r.counts,
        },
        "members": [
            {
                "name": a.name,
                "role": a.role,
                "utilization_pct": a.utilization_pct,
                "light": a.light.value,
                "notes": a.notes,
            }
            for a in r.member_assessments
        ],
        "recommendations": r.recommendations,
    }


SAMPLE_INPUT: dict[str, Any] = {
    "team_members": [
        {"name": "Alice", "role": "T1 Support", "utilization_pct": 92,
         "handles_count": 48, "hours_billable": 7.4, "hours_capacity": 8},
        {"name": "Bob",   "role": "T1 Support", "utilization_pct": 88,
         "handles_count": 42, "hours_billable": 7.0, "hours_capacity": 8},
        {"name": "Carol", "role": "T1 Support", "utilization_pct": 72,
         "handles_count": 36, "hours_billable": 5.8, "hours_capacity": 8},
        {"name": "Dan",   "role": "T2 Support", "utilization_pct": 65,
         "handles_count": 18, "hours_billable": 5.2, "hours_capacity": 8},
        {"name": "Eve",   "role": "T2 Support", "utilization_pct": 35,
         "handles_count": 8,  "hours_billable": 2.8, "hours_capacity": 8},
    ]
}


def parse_members(raw: dict[str, Any]) -> list[Member]:
    out: list[Member] = []
    for m in raw["team_members"]:
        out.append(Member(
            name=m["name"],
            role=m.get("role", "unspecified"),
            utilization_pct=float(m["utilization_pct"]),
            handles_count=int(m.get("handles_count", 0)),
            hours_billable=float(m.get("hours_billable", 0)),
            hours_capacity=float(m.get("hours_capacity", 0)),
        ))
    return out


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(
        description="Per-member + team-level utilization traffic-light analyzer.",
    )
    p.add_argument("--input", type=Path, help="Path to JSON input file.")
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
        members = parse_members(raw)
    except (KeyError, ValueError) as e:
        print(f"ERROR parsing input: {e}", file=sys.stderr)
        return 2

    report = assess_team(members)
    if args.output == "json":
        print(json.dumps(to_dict(report), indent=2))
    else:
        print(to_markdown(report))
    return 0


if __name__ == "__main__":
    sys.exit(main())
