#!/usr/bin/env python3
"""funnel_confidence_scorer.py — per-stage CoV-based confidence bands with treatment recommendation.

Input: JSON with funnel_stages (each with stage_name and conversion_pct_history over 12 quarters).

For each stage, computes:
  - Mean conversion %
  - Standard deviation
  - Coefficient of variation (CoV = StDev / Mean)
  - Confidence band: HIGH (CoV < 10%), MEDIUM (10-25%), LOW (25-50%), VERY LOW (> 50%)
  - Treatment recommendation per stage (commit-grade / soft-floor / extend-data-window / do-not-use)

The CoV discipline catches the case where two stages have the same mean conversion but very
different reliability — the same average masks very different forecast utility.

Deterministic. Stdlib only.

Usage:
    funnel_confidence_scorer.py --input intake.json --output markdown
    funnel_confidence_scorer.py --sample
"""
from __future__ import annotations

import argparse
import json
import statistics
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any


@dataclass
class StageConfidence:
    stage: str
    history: list[float]
    n: int
    mean_pct: float
    stdev_pct: float
    cov_pct: float
    band: str
    treatment: str
    rationale: list[str] = field(default_factory=list)


def classify_band(cov_pct: float) -> str:
    if cov_pct < 10.0:
        return "HIGH"
    if cov_pct < 25.0:
        return "MEDIUM"
    if cov_pct < 50.0:
        return "LOW"
    return "VERY LOW"


def treatment_for_band(band: str, n: int) -> tuple[str, list[str]]:
    rationale: list[str] = []
    if n < 4:
        rationale.append(f"Sample size n={n} is below the 4-quarter minimum for stable CoV estimation.")
        return "extend-data-window", rationale
    if band == "HIGH":
        rationale.append("CoV < 10% — historically stable. Use as commit-grade conversion input.")
        return "commit-grade", rationale
    if band == "MEDIUM":
        rationale.append("CoV 10-25% — usable but flagged. Apply blended last-4Q / last-12Q weighting.")
        return "blended-weighting", rationale
    if band == "LOW":
        rationale.append("CoV 25-50% — high variance. Use as a soft floor only, never as commit input.")
        return "treat-as-soft-floor", rationale
    rationale.append("CoV > 50% — statistical noise. Do not use for forecasting; root-cause the variance first.")
    return "do-not-use", rationale


def score_stage(stage_data: dict[str, Any]) -> StageConfidence:
    stage = str(stage_data.get("stage_name", "?"))
    history = [float(x) for x in (stage_data.get("conversion_pct_history") or []) if x is not None]
    n = len(history)
    if n == 0:
        return StageConfidence(
            stage=stage, history=[], n=0, mean_pct=0.0, stdev_pct=0.0, cov_pct=0.0,
            band="UNKNOWN", treatment="extend-data-window",
            rationale=["No conversion history provided."],
        )
    mean = statistics.mean(history)
    stdev = statistics.pstdev(history) if n > 1 else 0.0
    cov = (stdev / mean * 100.0) if mean > 0 else 0.0
    band = classify_band(cov)
    treatment, rationale = treatment_for_band(band, n)
    if mean > 0:
        rationale.insert(0, f"Mean {mean:.2f}% across {n} quarters; stdev {stdev:.2f}%; CoV {cov:.1f}%.")
    return StageConfidence(
        stage=stage, history=history, n=n, mean_pct=mean, stdev_pct=stdev,
        cov_pct=cov, band=band, treatment=treatment, rationale=rationale,
    )


def score_all(ctx: dict[str, Any]) -> list[StageConfidence]:
    stages = ctx.get("funnel_stages") or []
    return [score_stage(s) for s in stages]


def render_markdown(rows: list[StageConfidence]) -> str:
    L: list[str] = []
    L.append("# Funnel Confidence Scorer")
    L.append("")
    L.append(f"**Stages scored:** {len(rows)}")
    L.append("")
    L.append("## Confidence band summary")
    L.append("")
    L.append("| Stage | n quarters | Mean % | StDev % | CoV % | Band | Treatment |")
    L.append("|---|---:|---:|---:|---:|:---:|---|")
    for r in rows:
        L.append(
            f"| {r.stage} | {r.n} | {r.mean_pct:.2f} | {r.stdev_pct:.2f} | "
            f"{r.cov_pct:.1f} | **{r.band}** | {r.treatment} |"
        )
    L.append("")
    L.append("## Per-stage rationale")
    L.append("")
    for r in rows:
        L.append(f"### {r.stage} — {r.band} ({r.treatment})")
        for line in r.rationale:
            L.append(f"- {line}")
        L.append("")
    L.append("## Confidence-band thresholds (assumption block)")
    L.append("")
    L.append("- **HIGH** — CoV < 10%. Commit-grade conversion input.")
    L.append("- **MEDIUM** — CoV 10-25%. Use blended last-4Q / last-12Q weighting.")
    L.append("- **LOW** — CoV 25-50%. Soft floor only; never a commit input.")
    L.append("- **VERY LOW** — CoV > 50%. Statistical noise; root-cause before using.")
    L.append("- **Min sample size** — 4 quarters for stable CoV; below that → extend-data-window.")
    L.append("")
    L.append("## Next steps")
    L.append("1. For any stage flagged `do-not-use` or `treat-as-soft-floor`, decompose: segment? motion? rep? quarter-of-year seasonality?")
    L.append("2. Feed HIGH and MEDIUM stages directly into `bookings_forecaster.py`. Exclude LOW and VERY LOW from commit.")
    L.append("3. Present the per-stage confidence table on the same slide as the 3-tier forecast number.")
    return "\n".join(L)


def sample_context() -> dict[str, Any]:
    return {
        "funnel_stages": [
            {"stage_name": "discovery_to_demo", "conversion_pct_history": [
                35, 37, 33, 36, 38, 35, 34, 37, 36, 35, 36, 37
            ]},
            {"stage_name": "demo_to_proposal", "conversion_pct_history": [
                55, 52, 58, 56, 54, 57, 53, 55, 58, 54, 56, 55
            ]},
            {"stage_name": "proposal_to_negotiation", "conversion_pct_history": [
                65, 60, 70, 55, 75, 50, 80, 45, 72, 58, 68, 62
            ]},  # high variance
            {"stage_name": "negotiation_to_verbal", "conversion_pct_history": [
                75, 73, 76, 74, 75, 77, 74, 76, 73, 75, 76, 74
            ]},
            {"stage_name": "verbal_to_commit", "conversion_pct_history": [
                85, 60, 90, 40, 95, 30, 88, 55, 92, 35, 87, 50
            ]},  # very high variance
        ],
    }


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--input", type=Path, help="Path to funnel-history JSON.")
    p.add_argument("--output", default="markdown", choices=["markdown", "json"], help="Output format.")
    p.add_argument("--sample", action="store_true", help="Run with built-in sample context.")
    args = p.parse_args(argv)

    if args.sample:
        ctx = sample_context()
    elif args.input:
        ctx = json.loads(args.input.read_text())
    else:
        p.error("Provide --input or --sample.")
        return 2

    rows = score_all(ctx)
    if args.output == "json":
        out = {
            "stages": [
                {
                    "stage": r.stage, "n": r.n, "mean_pct": round(r.mean_pct, 4),
                    "stdev_pct": round(r.stdev_pct, 4), "cov_pct": round(r.cov_pct, 2),
                    "band": r.band, "treatment": r.treatment, "rationale": r.rationale,
                    "history": r.history,
                }
                for r in rows
            ],
            "thresholds": {
                "HIGH": "CoV < 10",
                "MEDIUM": "10 <= CoV < 25",
                "LOW": "25 <= CoV < 50",
                "VERY LOW": "CoV >= 50",
                "min_sample_n": 4,
            },
        }
        print(json.dumps(out, indent=2))
    else:
        print(render_markdown(rows))
    return 0


if __name__ == "__main__":
    sys.exit(main())
