#!/usr/bin/env python3
"""bookings_forecaster.py — 3-tier bookings forecast (commit / best-case / pipe-only) with explicit assumption block.

Input: JSON describing opportunities (stage, amount, close_date, age_days, last_activity_days),
historical stage-to-stage conversion (last 4Q and last 12Q windows), and target forecast period.

Output: three forecast numbers (commit, best-case, pipe-only) with the conversion rate, data window,
and weighting choice surfaced explicitly in an assumption block. Forecast without disclosed assumptions
is theatre — the assumption block is non-optional.

Deterministic decision logic. No LLM calls. No third-party deps.

Usage:
    bookings_forecaster.py --input intake.json --profile saas --output markdown
    bookings_forecaster.py --sample
"""
from __future__ import annotations

import argparse
import json
import math
import statistics
import sys
from dataclasses import dataclass, field
from datetime import date, datetime
from pathlib import Path
from typing import Any

# Commit-grade stages: opportunities here count toward the commit number
COMMIT_GRADE_STAGES = {"commit", "verbal", "contract_out", "contract-out", "closed_won_pending"}

# Best-case stages: weighted-stage opps that pass the time-to-close probability threshold
BEST_CASE_STAGES = {
    "commit", "verbal", "contract_out", "contract-out", "closed_won_pending",
    "proposal", "negotiation", "demo_completed", "demo-completed",
}

# Industry profile: default stage-conversion priors when historical data is missing per stage
PROFILES: dict[str, dict[str, float]] = {
    "saas": {
        "discovery": 0.35, "demo_completed": 0.55, "proposal": 0.65,
        "negotiation": 0.75, "verbal": 0.85, "commit": 0.92,
    },
    "api": {
        "discovery": 0.45, "demo_completed": 0.60, "proposal": 0.70,
        "negotiation": 0.80, "verbal": 0.88, "commit": 0.94,
    },
    "enterprise-software": {
        "discovery": 0.20, "demo_completed": 0.40, "proposal": 0.55,
        "negotiation": 0.68, "verbal": 0.80, "commit": 0.90,
    },
    "marketplace": {
        "discovery": 0.40, "demo_completed": 0.60, "proposal": 0.68,
        "negotiation": 0.78, "verbal": 0.86, "commit": 0.92,
    },
    "services": {
        "discovery": 0.30, "demo_completed": 0.50, "proposal": 0.62,
        "negotiation": 0.72, "verbal": 0.82, "commit": 0.90,
    },
}

# Weighting: blend last-4Q (recent regime) and last-12Q (long-run prior)
W_LAST_4Q = 0.70
W_LAST_12Q = 0.30

# Stalled-opp rule: opp age > AGE_STALL_MULTIPLIER * median_stage_age → downweighted
AGE_STALL_MULTIPLIER = 2.0
STALL_DOWNWEIGHT = 0.5  # multiplier applied to stalled opps in commit / best-case


@dataclass
class StageConversion:
    stage: str
    rate: float
    window: str  # "blended", "last_4q", "last_12q", or "profile_prior"
    rationale: str = ""


@dataclass
class OppContribution:
    opp_id: str
    stage: str
    amount: float
    conversion: float
    time_to_close_prob: float
    stalled: bool
    contribution_commit: float
    contribution_best_case: float
    contribution_pipe_only: float


@dataclass
class ForecastResult:
    commit: float
    best_case: float
    pipe_only: float
    pipeline_coverage_ratio: float
    pipeline_risk_pct: float  # variance between commit and pipe-only
    assumptions: dict[str, Any]
    stage_conversions: list[StageConversion]
    opp_contributions: list[OppContribution]
    warnings: list[str] = field(default_factory=list)


def parse_date(s: str | None) -> date | None:
    if not s:
        return None
    try:
        return datetime.fromisoformat(str(s)).date()
    except ValueError:
        return None


def blend_conversion(
    stage: str,
    hist: dict[str, Any],
    profile: str,
) -> StageConversion:
    """Return blended conversion rate for a stage with surfaced window."""
    last4 = hist.get("stage_X_to_Y_pct_last_4q") or {}
    last12 = hist.get("stage_X_to_Y_pct_last_12q") or {}

    r4 = last4.get(stage)
    r12 = last12.get(stage)

    if r4 is not None and r12 is not None:
        rate = W_LAST_4Q * float(r4) + W_LAST_12Q * float(r12)
        return StageConversion(
            stage=stage,
            rate=rate,
            window="blended",
            rationale=f"Blended {W_LAST_4Q:.0%} last-4Q ({r4:.2%}) + {W_LAST_12Q:.0%} last-12Q ({r12:.2%}).",
        )
    if r4 is not None:
        return StageConversion(
            stage=stage,
            rate=float(r4),
            window="last_4q",
            rationale=f"Only last-4Q available ({r4:.2%}); no last-12Q data.",
        )
    if r12 is not None:
        return StageConversion(
            stage=stage,
            rate=float(r12),
            window="last_12q",
            rationale=f"Only last-12Q available ({r12:.2%}); no last-4Q data.",
        )
    prior = PROFILES.get(profile, PROFILES["saas"]).get(stage)
    if prior is not None:
        return StageConversion(
            stage=stage,
            rate=prior,
            window="profile_prior",
            rationale=f"No historical data; using '{profile}' profile prior ({prior:.2%}).",
        )
    return StageConversion(
        stage=stage,
        rate=0.20,
        window="fallback",
        rationale="No historical data, no profile prior; using conservative 20% fallback.",
    )


def time_to_close_probability(
    close_date: date | None,
    target_start: date | None,
    target_end: date | None,
    age_days: int,
) -> float:
    """Probability that the opp closes within the target window.

    Heuristic: linear decay from 1.0 (close_date inside window) → 0.3 (close_date 90 days outside)
    plus a stall penalty for high-age opps with no recent activity.
    """
    if close_date is None or target_end is None:
        return 0.50  # unknown close-date → coin flip
    if target_start is not None and target_start <= close_date <= target_end:
        return 1.0
    if close_date < (target_start or close_date):
        return 0.40  # close-date already past → CRM hygiene issue
    days_late = (close_date - target_end).days
    if days_late <= 30:
        return 0.70
    if days_late <= 60:
        return 0.50
    if days_late <= 90:
        return 0.30
    return 0.15


def is_stalled(age_days: int, last_activity_days: int, median_stage_age: int) -> bool:
    if median_stage_age <= 0:
        return last_activity_days > 60
    return age_days > AGE_STALL_MULTIPLIER * median_stage_age and last_activity_days > 45


def compute_forecast(ctx: dict[str, Any], profile: str) -> ForecastResult:
    opps = ctx.get("opportunities") or []
    hist = ctx.get("historical_conversion") or {}
    target = ctx.get("target_period") or {}

    target_start = parse_date(target.get("start_date"))
    target_end = parse_date(target.get("end_date"))

    # Compute median stage age per stage for stall detection
    by_stage_age: dict[str, list[int]] = {}
    for o in opps:
        stage = str(o.get("stage", "")).lower()
        age = int(o.get("age_days") or 0)
        by_stage_age.setdefault(stage, []).append(age)
    median_stage_age = {s: int(statistics.median(ages)) for s, ages in by_stage_age.items() if ages}

    # Resolve conversion per unique stage encountered
    unique_stages = sorted({str(o.get("stage", "")).lower() for o in opps})
    stage_conversions = [blend_conversion(s, hist, profile) for s in unique_stages]
    sc_map = {sc.stage: sc for sc in stage_conversions}

    commit_total = 0.0
    best_case_total = 0.0
    pipe_only_total = 0.0
    contributions: list[OppContribution] = []
    warnings: list[str] = []

    for o in opps:
        opp_id = str(o.get("opp_id") or o.get("id") or "?")
        stage = str(o.get("stage", "")).lower()
        amount = float(o.get("amount") or 0)
        close_date = parse_date(o.get("close_date"))
        age_days = int(o.get("age_days") or 0)
        last_activity_days = int(o.get("last_activity_days") or 0)

        sc = sc_map.get(stage)
        rate = sc.rate if sc else 0.20
        ttc = time_to_close_probability(close_date, target_start, target_end, age_days)
        median_age = median_stage_age.get(stage, 0)
        stalled = is_stalled(age_days, last_activity_days, median_age)
        stall_mult = STALL_DOWNWEIGHT if stalled else 1.0

        # Commit: commit-grade stages only, full rate × ttc × stall
        contrib_commit = 0.0
        if stage in COMMIT_GRADE_STAGES:
            contrib_commit = amount * rate * ttc * stall_mult

        # Best-case: best-case stages, rate × ttc (no stall penalty applied to best-case)
        contrib_best = 0.0
        if stage in BEST_CASE_STAGES:
            contrib_best = amount * rate * ttc

        # Pipe-only: all opps regardless of stage, weighted only by conversion (no ttc, no stall)
        contrib_pipe = amount * rate

        commit_total += contrib_commit
        best_case_total += contrib_best
        pipe_only_total += contrib_pipe

        contributions.append(OppContribution(
            opp_id=opp_id, stage=stage, amount=amount, conversion=rate,
            time_to_close_prob=ttc, stalled=stalled,
            contribution_commit=contrib_commit,
            contribution_best_case=contrib_best,
            contribution_pipe_only=contrib_pipe,
        ))

    # Pipeline coverage ratio = total pipeline $ / commit number
    total_pipeline = sum(float(o.get("amount") or 0) for o in opps)
    coverage = (total_pipeline / commit_total) if commit_total > 0 else 0.0

    if coverage > 0 and coverage < 3.0:
        warnings.append(
            f"Pipeline coverage ratio is {coverage:.2f}x — below the 3.0x SaaS-industry floor. "
            f"Commit is structurally unsupported (Pacific Crest / KeyBanc SaaS Survey)."
        )

    pipeline_risk = 0.0
    if pipe_only_total > 0:
        pipeline_risk = (pipe_only_total - commit_total) / pipe_only_total * 100.0

    if best_case_total > 0 and pipe_only_total > 0:
        bc_pipe_ratio = best_case_total / pipe_only_total
        if bc_pipe_ratio < 0.5:
            warnings.append(
                f"Best-case is {bc_pipe_ratio:.1%} of pipe-only — likely sandbagging "
                f"(McKinsey forecast-bias research)."
            )
        elif bc_pipe_ratio > 0.8:
            warnings.append(
                f"Best-case is {bc_pipe_ratio:.1%} of pipe-only — likely hockey-sticking "
                f"(OpenView SaaS forecasting benchmarks)."
            )

    # ASSUMPTION BLOCK — non-optional
    assumptions = {
        "conversion_window_weighting": f"{W_LAST_4Q:.0%} last-4Q + {W_LAST_12Q:.0%} last-12Q (blended)",
        "industry_profile": profile,
        "commit_grade_stages": sorted(COMMIT_GRADE_STAGES),
        "best_case_stages": sorted(BEST_CASE_STAGES),
        "time_to_close_model": "linear decay; 1.0 inside window, 0.7 within 30 days late, 0.5 within 60, 0.3 within 90, 0.15 thereafter",
        "stall_rule": f"opp age > {AGE_STALL_MULTIPLIER}x median stage age AND last_activity > 45 days → contribution * {STALL_DOWNWEIGHT}",
        "stage_conversions_applied": [
            {"stage": sc.stage, "rate": round(sc.rate, 4), "window": sc.window, "rationale": sc.rationale}
            for sc in stage_conversions
        ],
        "data_window_disclosed": True,
        "weighting_choice_disclosed": True,
    }

    return ForecastResult(
        commit=commit_total,
        best_case=best_case_total,
        pipe_only=pipe_only_total,
        pipeline_coverage_ratio=coverage,
        pipeline_risk_pct=pipeline_risk,
        assumptions=assumptions,
        stage_conversions=stage_conversions,
        opp_contributions=contributions,
        warnings=warnings,
    )


def render_markdown(r: ForecastResult, ctx: dict[str, Any], profile: str) -> str:
    L: list[str] = []
    target = ctx.get("target_period") or {}
    L.append("# Bookings Forecast — 3-Tier")
    L.append("")
    L.append(f"**Profile:** `{profile}`  •  **Target period:** {target.get('start_date', '?')} → {target.get('end_date', '?')}")
    L.append(f"**Opportunities scored:** {len(r.opp_contributions)}")
    L.append("")
    L.append("## Three numbers")
    L.append("")
    L.append(f"| Tier | Amount | Notes |")
    L.append(f"|---|---:|---|")
    L.append(f"| **Commit** | ${r.commit:,.0f} | Commit-grade stages × blended conversion × time-to-close × stall penalty |")
    L.append(f"| **Best-case** | ${r.best_case:,.0f} | Best-case stages × blended conversion × time-to-close |")
    L.append(f"| **Pipe-only** | ${r.pipe_only:,.0f} | All pipeline × blended conversion (no time/stall adjustment) |")
    L.append("")
    L.append(f"**Pipeline-coverage ratio:** {r.pipeline_coverage_ratio:.2f}x (commit-relative)")
    L.append(f"**Pipeline-risk variance:** {r.pipeline_risk_pct:.1f}% (commit-to-pipe gap)")
    L.append("")
    L.append("## Assumption block (NON-OPTIONAL — present this on the board slide)")
    L.append("")
    L.append(f"- **Conversion-window weighting:** {r.assumptions['conversion_window_weighting']}")
    L.append(f"- **Industry profile:** `{r.assumptions['industry_profile']}`")
    L.append(f"- **Commit-grade stages:** {', '.join(r.assumptions['commit_grade_stages'])}")
    L.append(f"- **Best-case stages:** {', '.join(r.assumptions['best_case_stages'])}")
    L.append(f"- **Time-to-close model:** {r.assumptions['time_to_close_model']}")
    L.append(f"- **Stall rule:** {r.assumptions['stall_rule']}")
    L.append("")
    L.append("### Stage conversions applied")
    L.append("")
    L.append("| Stage | Rate | Window | Rationale |")
    L.append("|---|---:|---|---|")
    for sc in r.stage_conversions:
        L.append(f"| {sc.stage} | {sc.rate:.2%} | {sc.window} | {sc.rationale} |")
    L.append("")
    if r.warnings:
        L.append("## Warnings")
        for w in r.warnings:
            L.append(f"- ⚠️  {w}")
        L.append("")
    L.append("## Per-opp contributions (top 10 by commit)")
    L.append("")
    top = sorted(r.opp_contributions, key=lambda c: -c.contribution_commit)[:10]
    L.append("| Opp | Stage | Amount | Conv | TTC | Stalled | Commit $ |")
    L.append("|---|---|---:|---:|---:|:---:|---:|")
    for c in top:
        L.append(
            f"| {c.opp_id} | {c.stage} | ${c.amount:,.0f} | {c.conversion:.0%} | "
            f"{c.time_to_close_prob:.0%} | {'Y' if c.stalled else '-'} | ${c.contribution_commit:,.0f} |"
        )
    L.append("")
    L.append("## Next steps")
    L.append("1. Run `cohort_arr_projector.py` to surface leaky cohorts in NRR.")
    L.append("2. Run `funnel_confidence_scorer.py` to score per-stage reliability (CoV).")
    L.append("3. Present commit + best-case + pipe-only WITH the assumption block. No assumption block = theatre.")
    return "\n".join(L)


def sample_context() -> dict[str, Any]:
    return {
        "opportunities": [
            {"opp_id": "OPP-101", "stage": "commit", "amount": 180000, "close_date": "2026-06-15", "age_days": 45, "last_activity_days": 3},
            {"opp_id": "OPP-102", "stage": "verbal", "amount": 95000, "close_date": "2026-06-22", "age_days": 60, "last_activity_days": 7},
            {"opp_id": "OPP-103", "stage": "verbal", "amount": 220000, "close_date": "2026-08-05", "age_days": 210, "last_activity_days": 55},  # stalled
            {"opp_id": "OPP-104", "stage": "negotiation", "amount": 140000, "close_date": "2026-06-30", "age_days": 90, "last_activity_days": 10},
            {"opp_id": "OPP-105", "stage": "proposal", "amount": 75000, "close_date": "2026-07-15", "age_days": 30, "last_activity_days": 4},
            {"opp_id": "OPP-106", "stage": "proposal", "amount": 250000, "close_date": "2026-09-01", "age_days": 75, "last_activity_days": 12},
            {"opp_id": "OPP-107", "stage": "demo_completed", "amount": 60000, "close_date": "2026-07-30", "age_days": 25, "last_activity_days": 2},
            {"opp_id": "OPP-108", "stage": "discovery", "amount": 110000, "close_date": "2026-08-20", "age_days": 14, "last_activity_days": 5},
            {"opp_id": "OPP-109", "stage": "discovery", "amount": 45000, "close_date": "2026-09-15", "age_days": 8, "last_activity_days": 2},
        ],
        "historical_conversion": {
            "stage_X_to_Y_pct_last_4q": {
                "discovery": 0.32, "demo_completed": 0.52, "proposal": 0.60,
                "negotiation": 0.72, "verbal": 0.84, "commit": 0.91,
            },
            "stage_X_to_Y_pct_last_12q": {
                "discovery": 0.38, "demo_completed": 0.58, "proposal": 0.67,
                "negotiation": 0.76, "verbal": 0.87, "commit": 0.93,
            },
        },
        "target_period": {"start_date": "2026-06-01", "end_date": "2026-06-30"},
    }


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--input", type=Path, help="Path to forecast-intake JSON.")
    p.add_argument(
        "--profile", default="saas", choices=list(PROFILES.keys()),
        help="Industry profile for stage-conversion priors when historical data is missing per stage.",
    )
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

    result = compute_forecast(ctx, args.profile)
    if args.output == "json":
        out = {
            "profile": args.profile,
            "commit": round(result.commit, 2),
            "best_case": round(result.best_case, 2),
            "pipe_only": round(result.pipe_only, 2),
            "pipeline_coverage_ratio": round(result.pipeline_coverage_ratio, 3),
            "pipeline_risk_pct": round(result.pipeline_risk_pct, 2),
            "assumptions": result.assumptions,
            "warnings": result.warnings,
            "opp_contributions": [
                {
                    "opp_id": c.opp_id, "stage": c.stage, "amount": c.amount,
                    "conversion": round(c.conversion, 4),
                    "time_to_close_prob": round(c.time_to_close_prob, 3),
                    "stalled": c.stalled,
                    "commit": round(c.contribution_commit, 2),
                    "best_case": round(c.contribution_best_case, 2),
                    "pipe_only": round(c.contribution_pipe_only, 2),
                }
                for c in result.opp_contributions
            ],
        }
        print(json.dumps(out, indent=2))
    else:
        print(render_markdown(result, ctx, args.profile))
    return 0


if __name__ == "__main__":
    sys.exit(main())
