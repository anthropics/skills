#!/usr/bin/env python3
"""
sla_compliance_tracker.py — Per-vendor SLA compliance tracking.

Takes JSON of SLA records {vendor, sla_metric, target, actual_last_month,
actual_last_quarter, breach_count_12m}. Computes:
  - Compliance % vs target (last month, last quarter)
  - Trend classification (improving / stable / degrading)
  - Credit-claim eligibility flag (per typical SLA credit clauses)

Output: per-vendor compliance scorecard markdown with action items.

Stdlib only. Deterministic. No LLM calls.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Any


class Trend(str, Enum):
    IMPROVING = "improving"
    STABLE = "stable"
    DEGRADING = "degrading"


class ComplianceState(str, Enum):
    MET = "met"
    AT_RISK = "at-risk"
    BREACHED = "breached"


@dataclass
class SLAResult:
    vendor: str
    sla_metric: str
    target: float
    actual_last_month: float
    actual_last_quarter: float
    breach_count_12m: int
    compliance_month_pct: float
    compliance_quarter_pct: float
    state: ComplianceState
    trend: Trend
    credit_claim_eligible: bool
    action_items: list[str]


# A small library of typical SLA credit-claim thresholds.
# breach_count_12m >= 2  OR  actual_last_quarter < target by > 0.5pp  -> eligible.
# This is "SIG-Lite-ish" — operators tune per actual contract.
CREDIT_CLAIM_DELTA_PP = 0.5  # percentage points (or hours) below/above target


# Metrics where lower is better (response time, resolution hours, etc.).
# Anything else (uptime_pct, throughput, etc.) is "higher is better."
_LOWER_IS_BETTER_HINTS = (
    "response",
    "resolution",
    "latency",
    "hours",
    "minutes",
    "mttr",
    "time_to",
)


def _is_lower_better(sla_metric: str) -> bool:
    metric_lc = sla_metric.lower()
    return any(h in metric_lc for h in _LOWER_IS_BETTER_HINTS)


def _compute_compliance_pct(actual: float, target: float, lower_is_better: bool) -> float:
    """Compliance % capped at 100. Direction depends on metric semantics."""
    if target <= 0:
        return 100.0
    if lower_is_better:
        # actual <= target -> 100%. actual = 2*target -> 50%. actual = 4*target -> 25%.
        return round(min(100.0, (target / actual) * 100.0), 2) if actual > 0 else 100.0
    return round(min(100.0, (actual / target) * 100.0), 2)


def _classify_state(
    actual_last_quarter: float, target: float, lower_is_better: bool
) -> ComplianceState:
    if lower_is_better:
        if actual_last_quarter <= target:
            return ComplianceState.MET
        if actual_last_quarter <= target * 1.10:  # within 10% over
            return ComplianceState.AT_RISK
        return ComplianceState.BREACHED
    # higher is better
    if actual_last_quarter >= target:
        return ComplianceState.MET
    if actual_last_quarter >= target - 0.25:
        return ComplianceState.AT_RISK
    return ComplianceState.BREACHED


def _classify_trend(
    actual_last_month: float, actual_last_quarter: float, lower_is_better: bool
) -> Trend:
    delta = actual_last_month - actual_last_quarter
    # For lower-is-better metrics, a negative delta (smaller now) is improving.
    if lower_is_better:
        delta = -delta
    if delta > 0.1:
        return Trend.IMPROVING
    if delta < -0.1:
        return Trend.DEGRADING
    return Trend.STABLE


def _credit_eligible(
    actual_last_quarter: float,
    target: float,
    breach_count_12m: int,
    lower_is_better: bool,
) -> bool:
    if breach_count_12m >= 2:
        return True
    if lower_is_better:
        if actual_last_quarter > (target + CREDIT_CLAIM_DELTA_PP):
            return True
    else:
        if actual_last_quarter < (target - CREDIT_CLAIM_DELTA_PP):
            return True
    return False


def _build_action_items(
    state: ComplianceState,
    trend: Trend,
    credit_eligible: bool,
    breach_count_12m: int,
) -> list[str]:
    items: list[str] = []
    if credit_eligible:
        items.append("Open an SLA credit-claim ticket with the vendor's CSM.")
    if state == ComplianceState.BREACHED:
        items.append("Escalate to vendor exec sponsor. Request root-cause analysis.")
    if state == ComplianceState.AT_RISK and trend == Trend.DEGRADING:
        items.append("Schedule QBR within 30 days. Trend will breach if uncorrected.")
    if breach_count_12m >= 4:
        items.append(
            f"{breach_count_12m} breaches in 12 months — flag vendor as REVIEW in next scorecard."
        )
    if state == ComplianceState.MET and trend == Trend.IMPROVING and breach_count_12m == 0:
        items.append("No action required. Acknowledge in next vendor business review.")
    if not items:
        items.append("Monitor — no immediate action.")
    return items


def evaluate_sla(record: dict[str, Any]) -> SLAResult:
    target = float(record["target"])
    actual_month = float(record["actual_last_month"])
    actual_quarter = float(record["actual_last_quarter"])
    breach_count = int(record.get("breach_count_12m", 0))
    sla_metric = str(record["sla_metric"])
    lower_is_better = _is_lower_better(sla_metric)

    state = _classify_state(actual_quarter, target, lower_is_better)
    trend = _classify_trend(actual_month, actual_quarter, lower_is_better)
    eligible = _credit_eligible(actual_quarter, target, breach_count, lower_is_better)
    return SLAResult(
        vendor=str(record["vendor"]),
        sla_metric=sla_metric,
        target=target,
        actual_last_month=actual_month,
        actual_last_quarter=actual_quarter,
        breach_count_12m=breach_count,
        compliance_month_pct=_compute_compliance_pct(
            actual_month, target, lower_is_better
        ),
        compliance_quarter_pct=_compute_compliance_pct(
            actual_quarter, target, lower_is_better
        ),
        state=state,
        trend=trend,
        credit_claim_eligible=eligible,
        action_items=_build_action_items(state, trend, eligible, breach_count),
    )


# ---------- Markdown rendering ----------


def render_markdown(results: list[SLAResult]) -> str:
    lines: list[str] = []
    lines.append("# SLA Compliance Report")
    lines.append("")

    # Summary
    total = len(results)
    breached = sum(1 for r in results if r.state == ComplianceState.BREACHED)
    at_risk = sum(1 for r in results if r.state == ComplianceState.AT_RISK)
    eligible = [r for r in results if r.credit_claim_eligible]
    lines.append(
        f"**Summary:** {total} SLAs tracked · {breached} breached · {at_risk} at risk · "
        f"{len(eligible)} credit-claim eligible."
    )
    lines.append("")

    # Detail table
    lines.append("## Per-SLA Status")
    lines.append("")
    lines.append(
        "| Vendor | SLA Metric | Target | Last Month | Last Quarter | "
        "Compliance Q | State | Trend | Breaches 12m | Credit Eligible |"
    )
    lines.append(
        "|---|---|---|---|---|---|---|---|---|---|"
    )
    for r in results:
        lines.append(
            f"| {r.vendor} | {r.sla_metric} | {r.target} | {r.actual_last_month} | "
            f"{r.actual_last_quarter} | {r.compliance_quarter_pct}% | "
            f"{r.state.value} | {r.trend.value} | {r.breach_count_12m} | "
            f"{'YES' if r.credit_claim_eligible else 'no'} |"
        )
    lines.append("")

    # Action items
    lines.append("## Action Items")
    lines.append("")
    for r in results:
        lines.append(f"### {r.vendor} — {r.sla_metric}")
        for item in r.action_items:
            lines.append(f"- {item}")
        lines.append("")

    # Credit-claim shortlist
    if eligible:
        lines.append("## Credit-Claim Shortlist")
        lines.append("")
        lines.append("| Vendor | SLA | Target | Last Q | Breaches 12m |")
        lines.append("|---|---|---|---|---|")
        for r in eligible:
            lines.append(
                f"| {r.vendor} | {r.sla_metric} | {r.target} | {r.actual_last_quarter} | "
                f"{r.breach_count_12m} |"
            )
        lines.append("")

    return "\n".join(lines)


# ---------- Sample data ----------

SAMPLE_RECORDS: list[dict[str, Any]] = [
    {
        "vendor": "Okta",
        "sla_metric": "uptime_pct",
        "target": 99.99,
        "actual_last_month": 99.95,
        "actual_last_quarter": 99.91,
        "breach_count_12m": 3,
    },
    {
        "vendor": "Snowflake",
        "sla_metric": "uptime_pct",
        "target": 99.9,
        "actual_last_month": 99.98,
        "actual_last_quarter": 99.97,
        "breach_count_12m": 1,
    },
    {
        "vendor": "LegacyCRM",
        "sla_metric": "support_p90_response_hours",
        "target": 8.0,
        "actual_last_month": 36.0,
        "actual_last_quarter": 38.0,
        "breach_count_12m": 11,
    },
    {
        "vendor": "ChartingTool",
        "sla_metric": "uptime_pct",
        "target": 99.5,
        "actual_last_month": 99.6,
        "actual_last_quarter": 99.5,
        "breach_count_12m": 0,
    },
    {
        "vendor": "BoutiqueQA",
        "sla_metric": "ticket_resolution_hours",
        "target": 24.0,
        "actual_last_month": 30.0,
        "actual_last_quarter": 28.0,
        "breach_count_12m": 6,
    },
]


# ---------- CLI ----------


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Track per-vendor SLA compliance and flag credit-claim eligibility."
    )
    parser.add_argument("--input", type=Path, help="Path to JSON SLA records.")
    parser.add_argument("--output", type=Path, help="Path to write markdown report.")
    parser.add_argument(
        "--sample", action="store_true", help="Run against built-in sample SLA records."
    )
    args = parser.parse_args(argv)

    if not args.sample and not args.input:
        parser.error("provide --input or --sample")

    if args.sample:
        records = SAMPLE_RECORDS
    else:
        try:
            records = json.loads(args.input.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            print(f"error reading {args.input}: {exc}", file=sys.stderr)
            return 2
        if not isinstance(records, list):
            print("input JSON must be a list of SLA record objects", file=sys.stderr)
            return 2

    results = [evaluate_sla(r) for r in records]
    md = render_markdown(results)

    if args.output:
        args.output.write_text(md, encoding="utf-8")
        print(f"wrote {args.output}")
    else:
        print(md)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
