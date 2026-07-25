#!/usr/bin/env python3
"""bottleneck_detector.py

Apply three deterministic detection rules to a process JSON and emit a ranked
list of bottlenecks with severity, root-cause hypothesis, and a recommended
action.

Rules (defaults; tuned per industry profile):
  R1. Stage P50 > 2x mean of value-add stages              -> stage bottleneck
  R2. Wait-state share of total cycle > 40%                -> handoff bottleneck
  R3. Rework share of total cycle > 15%                    -> quality bottleneck

Stdlib only.
"""
from __future__ import annotations

import argparse
import json
import statistics
import sys
from dataclasses import dataclass, asdict
from pathlib import Path


# Per-industry threshold calibration. Manufacturing tolerates less wait;
# healthcare and services tolerate more given regulatory / human-in-the-loop steps.
PROFILES: dict[str, dict[str, float]] = {
    "saas": {
        "stage_multiplier": 2.0,
        "wait_share_max": 0.40,
        "rework_share_max": 0.15,
    },
    "services": {
        "stage_multiplier": 2.5,
        "wait_share_max": 0.50,
        "rework_share_max": 0.15,
    },
    "manufacturing": {
        "stage_multiplier": 1.8,
        "wait_share_max": 0.30,
        "rework_share_max": 0.10,
    },
    "healthcare": {
        "stage_multiplier": 2.5,
        "wait_share_max": 0.55,
        "rework_share_max": 0.12,
    },
}


@dataclass
class Finding:
    severity: str            # CRITICAL | HIGH | MEDIUM
    rule: str                # R1 | R2 | R3
    title: str
    detail: str
    hypothesis: str
    action: str
    impact_minutes_p50: float

    def severity_rank(self) -> int:
        return {"CRITICAL": 0, "HIGH": 1, "MEDIUM": 2}.get(self.severity, 3)


def load(path: Path) -> dict:
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def classify_severity(share: float, threshold: float) -> str:
    """Severity based on how far over the threshold the offender is."""
    if share <= threshold:
        return "MEDIUM"
    if share >= threshold * 2:
        return "CRITICAL"
    if share >= threshold * 1.5:
        return "HIGH"
    return "MEDIUM"


def detect(normalized: dict, profile: str) -> list[Finding]:
    prof = PROFILES.get(profile, PROFILES["saas"])
    stages = normalized.get("stages", [])
    findings: list[Finding] = []

    if not stages:
        return findings

    total_p50 = sum(s["duration_minutes_p50"] for s in stages) or 1.0
    wait_p50 = sum(s["duration_minutes_p50"] for s in stages if s["type"] == "wait")
    rework_p50 = sum(s["duration_minutes_p50"] for s in stages if s["type"] == "rework")
    va_durations = [
        s["duration_minutes_p50"] for s in stages if s["type"] == "value-add"
    ]
    va_mean = statistics.mean(va_durations) if va_durations else 0.0

    # R1: per-stage runaway vs value-add mean
    if va_mean > 0:
        threshold_minutes = va_mean * prof["stage_multiplier"]
        for s in stages:
            if s["duration_minutes_p50"] > threshold_minutes:
                ratio = s["duration_minutes_p50"] / va_mean
                if ratio >= prof["stage_multiplier"] * 3:
                    sev = "CRITICAL"
                elif ratio >= prof["stage_multiplier"] * 2:
                    sev = "HIGH"
                else:
                    sev = "MEDIUM"
                hypothesis = (
                    "Stage runs much longer than the typical value-add step; "
                    "common causes: batched approvals, single approver, "
                    "missing self-service, or unclear acceptance criteria."
                )
                action = (
                    "Decompose the stage; check if approval can be parallelized "
                    "or made conditional. If wait-state, apply Kanban WIP limit "
                    "or remove the handoff."
                )
                findings.append(
                    Finding(
                        severity=sev,
                        rule="R1",
                        title=f"Slow stage: {s['name']}",
                        detail=(
                            f"P50 {s['duration_minutes_p50']:.0f} min vs value-add "
                            f"mean {va_mean:.1f} min (ratio {ratio:.1f}x)."
                        ),
                        hypothesis=hypothesis,
                        action=action,
                        impact_minutes_p50=s["duration_minutes_p50"],
                    )
                )

    # R2: wait-state share
    wait_share = wait_p50 / total_p50
    if wait_share > prof["wait_share_max"]:
        sev = classify_severity(wait_share, prof["wait_share_max"])
        findings.append(
            Finding(
                severity=sev,
                rule="R2",
                title="Process is dominated by wait time",
                detail=(
                    f"Wait stages account for {wait_share*100:.0f}% of total P50, "
                    f"vs {prof['wait_share_max']*100:.0f}% profile threshold."
                ),
                hypothesis=(
                    "Handoffs queue work behind a single role or batch. Per "
                    "Theory of Constraints, the system throughput is set by "
                    "whichever queue is longest, not by stage speed."
                ),
                action=(
                    "Identify the longest wait stage; pull it forward, eliminate "
                    "it via self-service, or apply a WIP limit upstream so the "
                    "queue cannot grow."
                ),
                impact_minutes_p50=wait_p50,
            )
        )

    # R3: rework share
    rework_share = rework_p50 / total_p50
    if rework_share > prof["rework_share_max"]:
        sev = classify_severity(rework_share, prof["rework_share_max"])
        findings.append(
            Finding(
                severity=sev,
                rule="R3",
                title="Process has excessive rework",
                detail=(
                    f"Rework accounts for {rework_share*100:.0f}% of total P50, "
                    f"vs {prof['rework_share_max']*100:.0f}% profile threshold."
                ),
                hypothesis=(
                    "Defects escape upstream stages. Six-Sigma canon: rework is "
                    "always an upstream-quality problem, never a downstream one."
                ),
                action=(
                    "Add a poka-yoke (error-proofing) check at the earliest stage "
                    "that can detect the defect; do not add inspection downstream."
                ),
                impact_minutes_p50=rework_p50,
            )
        )

    findings.sort(key=lambda f: (f.severity_rank(), -f.impact_minutes_p50))
    return findings


def render_markdown(normalized: dict, findings: list[Finding], profile: str) -> str:
    name = normalized.get("process_name", "Untitled Process")
    lines: list[str] = []
    lines.append(f"# Bottleneck Detection: {name}")
    lines.append("")
    lines.append(f"**Profile:** `{profile}`  ")
    lines.append(f"**Findings:** {len(findings)}")
    lines.append("")
    if not findings:
        lines.append("_No bottlenecks detected at the configured thresholds._")
        return "\n".join(lines)
    for i, f in enumerate(findings, 1):
        lines.append(f"## {i}. [{f.severity}] {f.title}")
        lines.append("")
        lines.append(f"- **Rule:** `{f.rule}`")
        lines.append(f"- **Detail:** {f.detail}")
        lines.append(f"- **Hypothesis:** {f.hypothesis}")
        lines.append(f"- **Recommended action:** {f.action}")
        lines.append(f"- **Impact (P50 minutes):** {f.impact_minutes_p50:.0f}")
        lines.append("")
    return "\n".join(lines)


def sample_process() -> dict:
    # Reuses procurement-intake shape from process_documenter
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
        description="Detect bottlenecks in a documented business process."
    )
    parser.add_argument("--input", type=Path, help="Path to process JSON file.")
    parser.add_argument(
        "--profile",
        choices=sorted(PROFILES.keys()),
        default="saas",
        help="Industry profile for threshold calibration (default: saas).",
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
        raw = load(args.input)

    # Minimal normalization: tolerate the same fields as process_documenter
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

    findings = detect(normalized, args.profile)

    if args.output == "json":
        print(
            json.dumps(
                {
                    "process_name": normalized["process_name"],
                    "profile": args.profile,
                    "findings": [asdict(f) for f in findings],
                },
                indent=2,
            )
        )
    else:
        print(render_markdown(normalized, findings, args.profile))
    return 0


if __name__ == "__main__":
    sys.exit(main())
