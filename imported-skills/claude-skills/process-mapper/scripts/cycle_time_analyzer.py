#!/usr/bin/env python3
"""cycle_time_analyzer.py

Compute total cycle time (P50, P90), value-add ratio (VA%), wait %, rework %,
and a Little's-Law throughput estimate for a documented business process.

Verdict per Lean canon:
  VA% > 25%         -> HEALTHY
  10% <= VA% <= 25% -> TYPICAL
  VA% < 10%         -> WASTE-HEAVY

Stdlib only.
"""
from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, asdict
from pathlib import Path


# Per-industry verdict bands. Manufacturing benchmarks higher VA% than services.
PROFILES: dict[str, dict[str, float]] = {
    "saas":          {"healthy": 0.25, "typical": 0.10},
    "services":      {"healthy": 0.20, "typical": 0.08},
    "manufacturing": {"healthy": 0.35, "typical": 0.15},
    "healthcare":    {"healthy": 0.20, "typical": 0.08},
}


@dataclass
class CycleTimeReport:
    process_name: str
    profile: str
    stage_count: int
    total_p50_minutes: float
    total_p90_minutes: float
    value_add_minutes_p50: float
    wait_minutes_p50: float
    rework_minutes_p50: float
    value_add_ratio: float
    wait_ratio: float
    rework_ratio: float
    verdict: str
    wip: int
    throughput_per_hour: float | None
    notes: list[str]


def analyze(normalized: dict, profile: str) -> CycleTimeReport:
    prof = PROFILES.get(profile, PROFILES["saas"])
    stages = normalized.get("stages", [])
    name = normalized.get("process_name", "Untitled Process")
    wip = int(normalized.get("wip", 0) or 0)

    total_p50 = sum(s["duration_minutes_p50"] for s in stages)
    total_p90 = sum(s["duration_minutes_p90"] for s in stages)
    va_p50 = sum(s["duration_minutes_p50"] for s in stages if s["type"] == "value-add")
    wait_p50 = sum(s["duration_minutes_p50"] for s in stages if s["type"] == "wait")
    rework_p50 = sum(s["duration_minutes_p50"] for s in stages if s["type"] == "rework")

    denom = total_p50 if total_p50 > 0 else 1.0
    va_ratio = va_p50 / denom
    wait_ratio = wait_p50 / denom
    rework_ratio = rework_p50 / denom

    if va_ratio >= prof["healthy"]:
        verdict = "HEALTHY"
    elif va_ratio >= prof["typical"]:
        verdict = "TYPICAL"
    else:
        verdict = "WASTE-HEAVY"

    # Little's Law: L = lambda * W  =>  lambda = L / W
    # WIP is items currently in process; W (cycle time) is P50.
    # Convert minutes to hours for a per-hour throughput.
    throughput = None
    if wip > 0 and total_p50 > 0:
        cycle_hours = total_p50 / 60.0
        throughput = wip / cycle_hours

    notes: list[str] = []
    if wip <= 0:
        notes.append(
            "WIP not provided; Little's-Law throughput estimate skipped. "
            "Set 'wip' in the input JSON to enable it."
        )
    if total_p50 == 0:
        notes.append("All stage P50 durations are zero; check input data.")
    if rework_ratio > 0.0 and verdict == "HEALTHY":
        notes.append(
            "Process is healthy by VA%, but rework is non-zero. Six-Sigma canon: "
            "any rework signal is worth a poka-yoke check."
        )
    if wait_ratio > 0.5:
        notes.append(
            "More than half the cycle is wait time. Throughput improves more "
            "from queue removal than from speeding up value-add stages."
        )

    return CycleTimeReport(
        process_name=name,
        profile=profile,
        stage_count=len(stages),
        total_p50_minutes=round(total_p50, 2),
        total_p90_minutes=round(total_p90, 2),
        value_add_minutes_p50=round(va_p50, 2),
        wait_minutes_p50=round(wait_p50, 2),
        rework_minutes_p50=round(rework_p50, 2),
        value_add_ratio=round(va_ratio, 4),
        wait_ratio=round(wait_ratio, 4),
        rework_ratio=round(rework_ratio, 4),
        verdict=verdict,
        wip=wip,
        throughput_per_hour=round(throughput, 4) if throughput is not None else None,
        notes=notes,
    )


def render_markdown(report: CycleTimeReport) -> str:
    lines: list[str] = []
    lines.append(f"# Cycle-Time Analysis: {report.process_name}")
    lines.append("")
    lines.append(f"**Profile:** `{report.profile}`  ")
    lines.append(f"**Verdict:** **{report.verdict}**")
    lines.append("")
    lines.append("## Summary")
    lines.append("")
    lines.append("| Metric | Value |")
    lines.append("|--------|-------|")
    lines.append(f"| Stage count | {report.stage_count} |")
    lines.append(f"| Total P50 (minutes) | {report.total_p50_minutes:.1f} |")
    lines.append(f"| Total P90 (minutes) | {report.total_p90_minutes:.1f} |")
    lines.append(
        f"| Value-add minutes (P50) | {report.value_add_minutes_p50:.1f} |"
    )
    lines.append(f"| Wait minutes (P50) | {report.wait_minutes_p50:.1f} |")
    lines.append(f"| Rework minutes (P50) | {report.rework_minutes_p50:.1f} |")
    lines.append(f"| Value-add ratio (VA%) | {report.value_add_ratio*100:.1f}% |")
    lines.append(f"| Wait ratio | {report.wait_ratio*100:.1f}% |")
    lines.append(f"| Rework ratio | {report.rework_ratio*100:.1f}% |")
    lines.append(f"| WIP (items in process) | {report.wip} |")
    if report.throughput_per_hour is not None:
        lines.append(
            f"| Little's-Law throughput | {report.throughput_per_hour:.3f} items/hour |"
        )
    else:
        lines.append("| Little's-Law throughput | _(needs WIP > 0 in input)_ |")
    lines.append("")
    if report.notes:
        lines.append("## Notes")
        lines.append("")
        for n in report.notes:
            lines.append(f"- {n}")
        lines.append("")
    return "\n".join(lines)


def sample_process() -> dict:
    return {
        "process_name": "Procurement Intake (Sample)",
        "wip": 12,
        "stages": [
            {"name": "Submit PO", "owner": "Requestor", "type": "value-add",
             "duration_minutes_p50": 15, "duration_minutes_p90": 30},
            {"name": "Wait for manager", "owner": "Manager", "type": "wait",
             "duration_minutes_p50": 480, "duration_minutes_p90": 1440},
            {"name": "Manager approves", "owner": "Manager", "type": "value-add",
             "duration_minutes_p50": 10, "duration_minutes_p90": 25},
            {"name": "Wait for finance", "owner": "Finance", "type": "wait",
             "duration_minutes_p50": 720, "duration_minutes_p90": 2880},
            {"name": "Finance validates", "owner": "Finance", "type": "value-add",
             "duration_minutes_p50": 20, "duration_minutes_p90": 60},
            {"name": "Rework: missing W-9", "owner": "Requestor", "type": "rework",
             "duration_minutes_p50": 120, "duration_minutes_p90": 360},
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Analyze cycle time, value-add ratio, and throughput of a process."
    )
    parser.add_argument("--input", type=Path, help="Path to process JSON file.")
    parser.add_argument(
        "--profile",
        choices=sorted(PROFILES.keys()),
        default="saas",
        help="Industry profile for verdict band (default: saas).",
    )
    parser.add_argument(
        "--output",
        choices=["markdown", "json"],
        default="markdown",
        help="Output format (default: markdown).",
    )
    parser.add_argument(
        "--sample",
        action="store_true",
        help="Use a built-in sample process and exit.",
    )
    args = parser.parse_args()

    if args.sample:
        raw = sample_process()
    else:
        if not args.input:
            parser.error("--input is required unless --sample is given")
        if not args.input.exists():
            parser.error(f"input file not found: {args.input}")
        with args.input.open("r", encoding="utf-8") as f:
            raw = json.load(f)

    stages = []
    for s in raw.get("stages", []):
        stages.append(
            {
                "name": s.get("name", ""),
                "owner": s.get("owner", ""),
                "type": s.get("type", ""),
                "duration_minutes_p50": float(s.get("duration_minutes_p50", 0)),
                "duration_minutes_p90": float(s.get("duration_minutes_p90", 0)),
            }
        )
    normalized = {
        "process_name": raw.get("process_name", "Untitled Process"),
        "wip": int(raw.get("wip", 0) or 0),
        "stages": stages,
    }

    report = analyze(normalized, args.profile)

    if args.output == "json":
        print(json.dumps(asdict(report), indent=2))
    else:
        print(render_markdown(report))
    return 0


if __name__ == "__main__":
    sys.exit(main())
