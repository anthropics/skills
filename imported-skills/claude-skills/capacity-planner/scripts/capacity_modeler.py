#!/usr/bin/env python3
"""capacity_modeler.py — Ops capacity sizing via Erlang-C queueing math.

Sizes an ops team (Support / CX / BizOps / Finance ops / IT ops) against
demand and an SLA target. Implements Erlang-C in pure stdlib to compute:

  * Required FTE at 70%, 80%, and 90% utilization
  * Probability of SLA breach at each utilization level
  * Capacity headroom — extra tickets/day before SLA breaks

Industry profiles tune default shrinkage and SLA conventions.

Stdlib only. No LLM calls. Deterministic. Save the JSON sample for shape.
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


# ---------------------------------------------------------------------------
# Industry profiles
# ---------------------------------------------------------------------------
PROFILES: dict[str, dict[str, float]] = {
    # shrinkage = % of paid time NOT available for productive ticket-handling
    # (training, breaks, sync, PTO accrual, ad-hoc interrupts)
    "support": {"shrinkage_pct_default": 30.0, "sla_target_minutes_default": 60.0},
    "cx": {"shrinkage_pct_default": 32.0, "sla_target_minutes_default": 30.0},
    "bizops": {"shrinkage_pct_default": 25.0, "sla_target_minutes_default": 240.0},
    "finance-ops": {"shrinkage_pct_default": 22.0, "sla_target_minutes_default": 480.0},
    "it-ops": {"shrinkage_pct_default": 28.0, "sla_target_minutes_default": 120.0},
}


class RiskBand(str, Enum):
    SAFE = "SAFE"
    WATCH = "WATCH"
    AT_RISK = "AT_RISK"
    CRITICAL = "CRITICAL"


# ---------------------------------------------------------------------------
# Erlang-C — pure stdlib implementation
# ---------------------------------------------------------------------------
def erlang_c_probability(agents: int, traffic_intensity: float) -> float:
    """Erlang-C: probability an arriving call/ticket has to wait.

    agents (N)             : number of servers
    traffic_intensity (a)  : offered load in Erlangs (lambda * AHT)
                              dimensionless; must satisfy a < N for stability.

    Returns P(wait) in [0, 1]. Returns 1.0 if system unstable (a >= N).
    """
    if agents <= 0:
        return 1.0
    if traffic_intensity <= 0:
        return 0.0
    if traffic_intensity >= agents:
        return 1.0

    # Numerator: a^N / N! * N / (N - a)
    # Denominator: sum_{k=0}^{N-1} a^k / k!  +  numerator
    # Computed in log-space to avoid overflow on big numbers.
    a = traffic_intensity
    n = agents
    # log(a^n / n!) = n*log(a) - lgamma(n+1)
    log_a_n_over_nfact = n * math.log(a) - math.lgamma(n + 1)
    numerator_term = math.exp(log_a_n_over_nfact) * (n / (n - a))

    sum_terms = 0.0
    for k in range(n):
        log_term = k * math.log(a) - math.lgamma(k + 1)
        sum_terms += math.exp(log_term)

    denom = sum_terms + numerator_term
    if denom <= 0:
        return 1.0
    return numerator_term / denom


def service_level(agents: int, traffic_intensity: float,
                  aht_seconds: float, sla_target_seconds: float) -> float:
    """P(answered within SLA target) for M/M/c queue.

    SL = 1 - P_wait * exp(-(N - a) * T / AHT)
    """
    pw = erlang_c_probability(agents, traffic_intensity)
    if agents <= traffic_intensity:
        return 0.0
    exponent = -(agents - traffic_intensity) * (sla_target_seconds / aht_seconds)
    # guard against overflow
    if exponent < -700:
        return 1.0 - pw * 0.0
    return 1.0 - pw * math.exp(exponent)


def required_agents_for_utilization(traffic_intensity: float,
                                    target_utilization: float) -> int:
    """Minimum N such that traffic_intensity / N <= target_utilization."""
    if target_utilization <= 0 or target_utilization >= 1:
        raise ValueError("target_utilization must be in (0,1)")
    n = math.ceil(traffic_intensity / target_utilization)
    return max(n, 1)


# ---------------------------------------------------------------------------
# Data model
# ---------------------------------------------------------------------------
@dataclass
class Demand:
    tickets_per_day_p50: float
    tickets_per_day_p90: float
    tickets_per_day_p99: float


@dataclass
class CapacityInput:
    team_name: str
    demand: Demand
    sla_target_minutes: float
    current_fte: float
    avg_handle_time_minutes: float
    shrinkage_pct: float
    working_hours_per_day: float = 8.0


@dataclass
class UtilizationScenario:
    target_utilization: float
    required_fte_raw: int      # before shrinkage
    required_fte_loaded: float  # after shrinkage
    p_sla_breach_p50: float
    p_sla_breach_p90: float
    p_sla_breach_p99: float
    actual_utilization_at_demand: float


@dataclass
class CapacityResult:
    team_name: str
    inputs: CapacityInput
    scenarios: list[UtilizationScenario] = field(default_factory=list)
    headroom_extra_tickets_per_day: float = 0.0
    headroom_pct: float = 0.0
    risk_band: RiskBand = RiskBand.SAFE
    recommendation: str = ""
    notes: list[str] = field(default_factory=list)


# ---------------------------------------------------------------------------
# Modeling
# ---------------------------------------------------------------------------
def model_capacity(inp: CapacityInput) -> CapacityResult:
    aht_sec = inp.avg_handle_time_minutes * 60.0
    sla_sec = inp.sla_target_minutes * 60.0

    seconds_per_day_per_fte = inp.working_hours_per_day * 3600.0
    productive_fraction = max(0.0, 1.0 - inp.shrinkage_pct / 100.0)

    def traffic_for(volume_per_day: float) -> float:
        # Erlang offered load (a) = arrival_rate * AHT, in consistent time units.
        # Per-day arrival rate normalized to per-second:
        arrival_per_sec = volume_per_day / seconds_per_day_per_fte
        return arrival_per_sec * aht_sec

    a_p50 = traffic_for(inp.demand.tickets_per_day_p50)
    a_p90 = traffic_for(inp.demand.tickets_per_day_p90)
    a_p99 = traffic_for(inp.demand.tickets_per_day_p99)

    scenarios: list[UtilizationScenario] = []
    for util in (0.70, 0.80, 0.90):
        # Sizing is done against P90 demand by convention (Cleveland).
        n_raw = required_agents_for_utilization(a_p90, util)
        # Loaded headcount accounts for shrinkage: each "agent slot" needs
        # 1 / productive_fraction headcount to staff it.
        n_loaded = n_raw / productive_fraction if productive_fraction > 0 else float("inf")

        sl_p50 = service_level(n_raw, a_p50, aht_sec, sla_sec)
        sl_p90 = service_level(n_raw, a_p90, aht_sec, sla_sec)
        sl_p99 = service_level(n_raw, a_p99, aht_sec, sla_sec)

        scenarios.append(UtilizationScenario(
            target_utilization=util,
            required_fte_raw=n_raw,
            required_fte_loaded=round(n_loaded, 2),
            p_sla_breach_p50=round(1.0 - sl_p50, 4),
            p_sla_breach_p90=round(1.0 - sl_p90, 4),
            p_sla_breach_p99=round(1.0 - sl_p99, 4),
            actual_utilization_at_demand=round(a_p90 / n_raw, 4) if n_raw > 0 else 1.0,
        ))

    # Headroom: with current_fte (loaded), how many extra tickets/day before
    # P(SLA breach) at P90 crosses 10%?
    current_productive_fte = max(1, int(round(inp.current_fte * productive_fraction)))
    headroom_volume = inp.demand.tickets_per_day_p90
    step = max(1.0, inp.demand.tickets_per_day_p90 * 0.02)
    while headroom_volume < inp.demand.tickets_per_day_p90 * 5:
        a = traffic_for(headroom_volume)
        if a >= current_productive_fte:
            break
        sl = service_level(current_productive_fte, a, aht_sec, sla_sec)
        if (1.0 - sl) > 0.10:
            break
        headroom_volume += step
    headroom_extra = max(0.0, headroom_volume - inp.demand.tickets_per_day_p90)
    headroom_pct = (headroom_extra / inp.demand.tickets_per_day_p90 * 100.0
                    if inp.demand.tickets_per_day_p90 > 0 else 0.0)

    # Risk band — pick from 80%-utilization scenario (canonical sizing point)
    s80 = next(s for s in scenarios if s.target_utilization == 0.80)
    if inp.current_fte >= s80.required_fte_loaded and headroom_pct >= 20:
        band = RiskBand.SAFE
        rec = (f"Sized correctly at {inp.current_fte} FTE for P90 demand at 80% "
               f"utilization. Headroom is healthy ({headroom_pct:.0f}%).")
    elif inp.current_fte >= s80.required_fte_loaded:
        band = RiskBand.WATCH
        rec = (f"Headcount adequate ({inp.current_fte} FTE vs. "
               f"{s80.required_fte_loaded} required) but headroom thin "
               f"({headroom_pct:.0f}%). Re-test in 30 days.")
    elif inp.current_fte >= s80.required_fte_loaded * 0.85:
        band = RiskBand.AT_RISK
        rec = (f"Understaffed for P90 demand: have {inp.current_fte}, need "
               f"{s80.required_fte_loaded} at 80% utilization. Expect SLA "
               f"misses at P90 surges. Hire {math.ceil(s80.required_fte_loaded - inp.current_fte)} FTE.")
    else:
        band = RiskBand.CRITICAL
        rec = (f"Critically understaffed: have {inp.current_fte}, need "
               f"{s80.required_fte_loaded}. Throughput collapse risk per "
               f"queueing theory at sustained >85% utilization. Escalate.")

    notes: list[str] = []
    if s80.actual_utilization_at_demand > 0.85:
        notes.append(
            "WARNING: Sizing point pushes >85% utilization. Reinertsen's "
            "principle 7: throughput collapses non-linearly past 80%."
        )
    if inp.shrinkage_pct < 15:
        notes.append("Shrinkage <15% likely understates non-productive time.")
    if inp.shrinkage_pct > 40:
        notes.append("Shrinkage >40% — verify against actual time-on-task data.")

    return CapacityResult(
        team_name=inp.team_name,
        inputs=inp,
        scenarios=scenarios,
        headroom_extra_tickets_per_day=round(headroom_extra, 1),
        headroom_pct=round(headroom_pct, 1),
        risk_band=band,
        recommendation=rec,
        notes=notes,
    )


# ---------------------------------------------------------------------------
# Rendering
# ---------------------------------------------------------------------------
def to_markdown(result: CapacityResult) -> str:
    inp = result.inputs
    lines = [
        f"# Capacity Model — {result.team_name}",
        "",
        f"**Risk band:** {result.risk_band.value}",
        "",
        f"**Recommendation:** {result.recommendation}",
        "",
        "## Inputs",
        f"- Current FTE: {inp.current_fte}",
        f"- AHT: {inp.avg_handle_time_minutes} min",
        f"- SLA target: {inp.sla_target_minutes} min",
        f"- Shrinkage: {inp.shrinkage_pct}%",
        f"- Working hours / day: {inp.working_hours_per_day}",
        f"- Demand P50 / P90 / P99: {inp.demand.tickets_per_day_p50} / "
        f"{inp.demand.tickets_per_day_p90} / {inp.demand.tickets_per_day_p99} tickets/day",
        "",
        "## Sizing Scenarios (Erlang-C, sized to P90 demand)",
        "",
        "| Target Util | Raw FTE | Loaded FTE (post-shrinkage) | P(SLA breach @ P50) | P(SLA breach @ P90) | P(SLA breach @ P99) |",
        "|---|---|---|---|---|---|",
    ]
    for s in result.scenarios:
        lines.append(
            f"| {int(s.target_utilization*100)}% | {s.required_fte_raw} | "
            f"{s.required_fte_loaded} | {s.p_sla_breach_p50*100:.1f}% | "
            f"{s.p_sla_breach_p90*100:.1f}% | {s.p_sla_breach_p99*100:.1f}% |"
        )
    lines.extend([
        "",
        "## Headroom",
        f"- Extra tickets/day before SLA breaks: {result.headroom_extra_tickets_per_day}",
        f"- Headroom %: {result.headroom_pct:.1f}%",
        "",
    ])
    if result.notes:
        lines.append("## Notes")
        for n in result.notes:
            lines.append(f"- {n}")
        lines.append("")
    lines.append("## Canon")
    lines.append("- Erlang (1909), Little (1961), Cleveland *Call Center Mgmt on Fast Forward*, Reinertsen *Principles of Product Development Flow*.")
    return "\n".join(lines)


def to_dict(result: CapacityResult) -> dict[str, Any]:
    return {
        "team_name": result.team_name,
        "risk_band": result.risk_band.value,
        "recommendation": result.recommendation,
        "headroom_extra_tickets_per_day": result.headroom_extra_tickets_per_day,
        "headroom_pct": result.headroom_pct,
        "scenarios": [
            {
                "target_utilization": s.target_utilization,
                "required_fte_raw": s.required_fte_raw,
                "required_fte_loaded": s.required_fte_loaded,
                "p_sla_breach_p50": s.p_sla_breach_p50,
                "p_sla_breach_p90": s.p_sla_breach_p90,
                "p_sla_breach_p99": s.p_sla_breach_p99,
                "actual_utilization_at_demand": s.actual_utilization_at_demand,
            }
            for s in result.scenarios
        ],
        "notes": result.notes,
        "inputs": {
            "current_fte": result.inputs.current_fte,
            "avg_handle_time_minutes": result.inputs.avg_handle_time_minutes,
            "sla_target_minutes": result.inputs.sla_target_minutes,
            "shrinkage_pct": result.inputs.shrinkage_pct,
            "working_hours_per_day": result.inputs.working_hours_per_day,
            "demand": {
                "tickets_per_day_p50": result.inputs.demand.tickets_per_day_p50,
                "tickets_per_day_p90": result.inputs.demand.tickets_per_day_p90,
                "tickets_per_day_p99": result.inputs.demand.tickets_per_day_p99,
            },
        },
    }


# ---------------------------------------------------------------------------
# Sample + parsing
# ---------------------------------------------------------------------------
SAMPLE_INPUT: dict[str, Any] = {
    "team_name": "Tier-1 Support",
    "demand": {
        "tickets_per_day_p50": 320,
        "tickets_per_day_p90": 480,
        "tickets_per_day_p99": 720,
    },
    "sla_target_minutes": 60,
    "current_fte": 12,
    "avg_handle_time_minutes": 18,
    "shrinkage_pct": 30,
    "working_hours_per_day": 8,
}


def parse_input(raw: dict[str, Any], profile: str | None) -> CapacityInput:
    prof = PROFILES.get(profile or "", {})
    shrinkage = raw.get("shrinkage_pct", prof.get("shrinkage_pct_default", 30.0))
    sla = raw.get("sla_target_minutes",
                  prof.get("sla_target_minutes_default", 60.0))
    d = raw["demand"]
    return CapacityInput(
        team_name=raw["team_name"],
        demand=Demand(
            tickets_per_day_p50=float(d["tickets_per_day_p50"]),
            tickets_per_day_p90=float(d["tickets_per_day_p90"]),
            tickets_per_day_p99=float(d["tickets_per_day_p99"]),
        ),
        sla_target_minutes=float(sla),
        current_fte=float(raw["current_fte"]),
        avg_handle_time_minutes=float(raw["avg_handle_time_minutes"]),
        shrinkage_pct=float(shrinkage),
        working_hours_per_day=float(raw.get("working_hours_per_day", 8.0)),
    )


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(
        description="Erlang-C ops capacity sizer (stdlib only).",
    )
    p.add_argument("--input", type=Path, help="Path to JSON input file.")
    p.add_argument(
        "--profile",
        choices=list(PROFILES.keys()),
        default=None,
        help="Industry profile (defaults for shrinkage + SLA).",
    )
    p.add_argument(
        "--output",
        choices=["markdown", "json"],
        default="markdown",
        help="Output format.",
    )
    p.add_argument(
        "--sample",
        action="store_true",
        help="Run on built-in sample input and print result.",
    )
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

    result = model_capacity(inp)

    if args.output == "json":
        print(json.dumps(to_dict(result), indent=2))
    else:
        print(to_markdown(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
