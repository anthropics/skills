#!/usr/bin/env python3
"""cohort_arr_projector.py — per-cohort NRR / GRR projection over horizon with leaky-cohort callout.

Input: JSON with cohorts (each with acquisition_quarter, starting_arr, per-quarter gross_retention
and expansion_arr percentages) plus a projection_horizon_quarters integer.

Output: per-cohort NRR + GRR projection over the horizon, the consolidated NRR/GRR trajectory, and
a leaky-cohort callout for any cohort whose NRR is declining vs the trailing-cohort average.

The cohort-decomposition discipline surfaces leaks 2-3 quarters before they reach the consolidated
number (Campbell / Skok). Reporting NRR without per-cohort breakdown hides the leak.

Deterministic. Stdlib only.

Usage:
    cohort_arr_projector.py --input intake.json --output markdown
    cohort_arr_projector.py --sample
"""
from __future__ import annotations

import argparse
import json
import statistics
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

# Leak threshold: cohort NRR more than N pp below trailing-cohort average → flag
LEAK_THRESHOLD_PP = 5.0


@dataclass
class CohortProjection:
    cohort_id: str
    acquisition_quarter: str
    starting_arr: float
    nrr_by_quarter: list[float] = field(default_factory=list)
    grr_by_quarter: list[float] = field(default_factory=list)
    arr_by_quarter: list[float] = field(default_factory=list)
    leaky: bool = False
    leak_reason: str = ""


@dataclass
class ProjectionResult:
    cohorts: list[CohortProjection]
    consolidated_nrr: list[float]
    consolidated_grr: list[float]
    consolidated_arr: list[float]
    horizon_q: int
    leaky_cohorts: list[str]
    assumptions: dict[str, Any]


def project_cohort(cohort: dict[str, Any], horizon_q: int) -> CohortProjection:
    cohort_id = str(cohort.get("cohort_id", "?"))
    starting_arr = float(cohort.get("starting_arr") or 0)
    acq_q = str(cohort.get("acquisition_quarter", "?"))

    nrr_list: list[float] = []
    grr_list: list[float] = []
    arr_list: list[float] = []
    running_arr = starting_arr

    for q in range(1, horizon_q + 1):
        gr_key = f"gross_retention_pct_q{q}"
        exp_key = f"expansion_arr_pct_q{q}"
        gr = float(cohort.get(gr_key) if cohort.get(gr_key) is not None else _default_grr(q)) / 100.0
        exp = float(cohort.get(exp_key) if cohort.get(exp_key) is not None else _default_exp(q)) / 100.0
        # NRR = GRR + expansion; multiplicative on the original cohort base
        nrr = gr + exp
        cohort_arr = starting_arr * nrr
        nrr_list.append(nrr * 100.0)
        grr_list.append(gr * 100.0)
        arr_list.append(cohort_arr)
        running_arr = cohort_arr

    return CohortProjection(
        cohort_id=cohort_id,
        acquisition_quarter=acq_q,
        starting_arr=starting_arr,
        nrr_by_quarter=nrr_list,
        grr_by_quarter=grr_list,
        arr_by_quarter=arr_list,
    )


def _default_grr(q: int) -> float:
    # Conservative default GRR curve: 92% Q1, decaying ~1pp per quarter
    return max(85.0, 92.0 - (q - 1) * 1.0)


def _default_exp(q: int) -> float:
    # Conservative default expansion: 4% Q1 ramping to ~10% by Q4
    return min(12.0, 4.0 + (q - 1) * 2.0)


def detect_leaky_cohorts(cohorts: list[CohortProjection]) -> None:
    """A cohort is leaky if its mean NRR is LEAK_THRESHOLD_PP below the average of older cohorts."""
    if len(cohorts) < 2:
        return
    # Sort by acquisition_quarter string (lexicographic works for YYYY-Qn format)
    ordered = sorted(cohorts, key=lambda c: c.acquisition_quarter)
    for i, c in enumerate(ordered):
        if i == 0:
            continue
        prior = ordered[:i]
        prior_mean_nrr = statistics.mean(statistics.mean(p.nrr_by_quarter) for p in prior)
        this_mean_nrr = statistics.mean(c.nrr_by_quarter)
        gap = prior_mean_nrr - this_mean_nrr
        if gap >= LEAK_THRESHOLD_PP:
            c.leaky = True
            c.leak_reason = (
                f"Mean NRR {this_mean_nrr:.1f}% is {gap:.1f} pp below trailing-cohort avg "
                f"{prior_mean_nrr:.1f}% (threshold: {LEAK_THRESHOLD_PP} pp)."
            )


def consolidate(cohorts: list[CohortProjection], horizon_q: int) -> tuple[list[float], list[float], list[float]]:
    cons_nrr: list[float] = []
    cons_grr: list[float] = []
    cons_arr: list[float] = []
    for q_idx in range(horizon_q):
        total_starting = sum(c.starting_arr for c in cohorts)
        if total_starting <= 0:
            cons_nrr.append(0.0); cons_grr.append(0.0); cons_arr.append(0.0)
            continue
        # ARR-weighted NRR + GRR
        weighted_nrr = sum(c.starting_arr * c.nrr_by_quarter[q_idx] for c in cohorts) / total_starting
        weighted_grr = sum(c.starting_arr * c.grr_by_quarter[q_idx] for c in cohorts) / total_starting
        total_arr = sum(c.arr_by_quarter[q_idx] for c in cohorts)
        cons_nrr.append(weighted_nrr)
        cons_grr.append(weighted_grr)
        cons_arr.append(total_arr)
    return cons_nrr, cons_grr, cons_arr


def project(ctx: dict[str, Any]) -> ProjectionResult:
    cohorts_in = ctx.get("cohorts") or []
    horizon_q = int(ctx.get("projection_horizon_quarters") or 4)

    projected = [project_cohort(c, horizon_q) for c in cohorts_in]
    detect_leaky_cohorts(projected)
    cons_nrr, cons_grr, cons_arr = consolidate(projected, horizon_q)
    leaky = [c.cohort_id for c in projected if c.leaky]

    assumptions = {
        "projection_horizon_quarters": horizon_q,
        "leak_threshold_pp": LEAK_THRESHOLD_PP,
        "leak_rule": (
            f"Cohort flagged leaky if mean NRR is ≥ {LEAK_THRESHOLD_PP} pp below "
            "the mean of all earlier-acquired cohorts (Campbell/ProfitWell cohort decomposition discipline)."
        ),
        "consolidation_method": "ARR-weighted (starting_arr) across cohorts per quarter",
        "default_grr_curve_when_missing": "92% Q1 decaying ~1pp/quarter, floor 85%",
        "default_expansion_curve_when_missing": "4% Q1 ramping +2pp/quarter, ceiling 12%",
    }

    return ProjectionResult(
        cohorts=projected,
        consolidated_nrr=cons_nrr,
        consolidated_grr=cons_grr,
        consolidated_arr=cons_arr,
        horizon_q=horizon_q,
        leaky_cohorts=leaky,
        assumptions=assumptions,
    )


def render_markdown(r: ProjectionResult) -> str:
    L: list[str] = []
    L.append("# Cohort ARR Projection")
    L.append("")
    L.append(f"**Horizon:** {r.horizon_q} quarters  •  **Cohorts:** {len(r.cohorts)}  •  **Leaky cohorts:** {len(r.leaky_cohorts)}")
    L.append("")
    if r.leaky_cohorts:
        L.append("## Leaky-cohort callout")
        L.append("")
        L.append("> The consolidated NRR can stay flat while a recent cohort is leaking. Surfacing the leak now is 2-3 quarters cheaper than discovering it in the topline. (Campbell / Skok cohort decomposition.)")
        L.append("")
        for c in r.cohorts:
            if c.leaky:
                L.append(f"- ⚠️  **{c.cohort_id}** ({c.acquisition_quarter}): {c.leak_reason}")
        L.append("")
    else:
        L.append("> No leaky cohorts detected at the configured threshold. Continue cohort decomposition every quarter; leaks emerge faster than you think.")
        L.append("")
    L.append("## Per-cohort NRR heatmap (% by projection quarter)")
    L.append("")
    header = "| Cohort | Acq Q | Starting ARR | " + " | ".join(f"Q+{q}" for q in range(1, r.horizon_q + 1)) + " |"
    sep = "|---|---|---:|" + "---:|" * r.horizon_q
    L.append(header)
    L.append(sep)
    for c in sorted(r.cohorts, key=lambda x: x.acquisition_quarter):
        flag = " ⚠️" if c.leaky else ""
        row = f"| {c.cohort_id}{flag} | {c.acquisition_quarter} | ${c.starting_arr:,.0f} | "
        row += " | ".join(f"{n:.1f}%" for n in c.nrr_by_quarter)
        row += " |"
        L.append(row)
    L.append("")
    L.append("## Consolidated NRR / GRR trajectory")
    L.append("")
    L.append("| Quarter | Consolidated NRR | Consolidated GRR | Consolidated ARR |")
    L.append("|---|---:|---:|---:|")
    for q in range(r.horizon_q):
        L.append(f"| Q+{q+1} | {r.consolidated_nrr[q]:.1f}% | {r.consolidated_grr[q]:.1f}% | ${r.consolidated_arr[q]:,.0f} |")
    L.append("")
    L.append("## Assumption block (NON-OPTIONAL — present alongside the cohort heatmap)")
    L.append("")
    for k, v in r.assumptions.items():
        L.append(f"- **{k}:** {v}")
    L.append("")
    L.append("## Next steps")
    L.append("1. If a leaky cohort is flagged, decompose it: which segment / motion / pricing tier dominates that cohort?")
    L.append("2. Cross-check against the bookings forecast — leaky cohort + flat commit number is a hidden mismatch.")
    L.append("3. Present NRR with the cohort heatmap. Consolidated-only is theatre.")
    return "\n".join(L)


def sample_context() -> dict[str, Any]:
    return {
        "cohorts": [
            {
                "cohort_id": "2025-Q1", "acquisition_quarter": "2025-Q1", "starting_arr": 1_200_000,
                "gross_retention_pct_q1": 93, "gross_retention_pct_q2": 91, "gross_retention_pct_q3": 90, "gross_retention_pct_q4": 89,
                "expansion_arr_pct_q1": 5, "expansion_arr_pct_q2": 8, "expansion_arr_pct_q3": 10, "expansion_arr_pct_q4": 11,
            },
            {
                "cohort_id": "2025-Q2", "acquisition_quarter": "2025-Q2", "starting_arr": 1_500_000,
                "gross_retention_pct_q1": 92, "gross_retention_pct_q2": 90, "gross_retention_pct_q3": 89, "gross_retention_pct_q4": 88,
                "expansion_arr_pct_q1": 6, "expansion_arr_pct_q2": 9, "expansion_arr_pct_q3": 11, "expansion_arr_pct_q4": 12,
            },
            {
                "cohort_id": "2025-Q3", "acquisition_quarter": "2025-Q3", "starting_arr": 1_800_000,
                "gross_retention_pct_q1": 94, "gross_retention_pct_q2": 92, "gross_retention_pct_q3": 91, "gross_retention_pct_q4": 90,
                "expansion_arr_pct_q1": 5, "expansion_arr_pct_q2": 8, "expansion_arr_pct_q3": 10, "expansion_arr_pct_q4": 12,
            },
            {
                # LEAKY: recent cohort, low retention, low expansion
                "cohort_id": "2025-Q4", "acquisition_quarter": "2025-Q4", "starting_arr": 2_100_000,
                "gross_retention_pct_q1": 85, "gross_retention_pct_q2": 82, "gross_retention_pct_q3": 80, "gross_retention_pct_q4": 78,
                "expansion_arr_pct_q1": 2, "expansion_arr_pct_q2": 3, "expansion_arr_pct_q3": 4, "expansion_arr_pct_q4": 5,
            },
        ],
        "projection_horizon_quarters": 4,
    }


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--input", type=Path, help="Path to cohort-intake JSON.")
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

    result = project(ctx)
    if args.output == "json":
        out = {
            "horizon_q": result.horizon_q,
            "leaky_cohorts": result.leaky_cohorts,
            "consolidated_nrr": [round(n, 2) for n in result.consolidated_nrr],
            "consolidated_grr": [round(n, 2) for n in result.consolidated_grr],
            "consolidated_arr": [round(n, 2) for n in result.consolidated_arr],
            "assumptions": result.assumptions,
            "cohorts": [
                {
                    "cohort_id": c.cohort_id,
                    "acquisition_quarter": c.acquisition_quarter,
                    "starting_arr": c.starting_arr,
                    "nrr_by_quarter": [round(n, 2) for n in c.nrr_by_quarter],
                    "grr_by_quarter": [round(n, 2) for n in c.grr_by_quarter],
                    "arr_by_quarter": [round(n, 2) for n in c.arr_by_quarter],
                    "leaky": c.leaky,
                    "leak_reason": c.leak_reason,
                }
                for c in result.cohorts
            ],
        }
        print(json.dumps(out, indent=2))
    else:
        print(render_markdown(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
