#!/usr/bin/env python3
"""phase_gate_scorer.py - Score a study plan for feasibility and route a phase-gate verdict.

Stdlib-only. Deterministic. NO LLM calls. ESTIMATE / decision-support only: the verdict
names the human owner(s) who must sign — it never authorizes a study on its own.

Scores a study plan 0-100 across 5 dimensions:
  1. recruitment_feasibility   eligible-population size vs target enrollment + timeline
  2. endpoint_readiness        endpoint validated + instrument in place
  3. statistical_power         is the planned n adequate for the stated effect?
  4. operational_complexity    sites, visits, procedures (inverted: simpler = higher)
  5. budget_fit                planned budget vs profile cost-per-patient benchmark

Verdict:
  - composite >= 80 and no blockers  -> GO
  - composite 65-79                  -> GO-WITH-CONDITIONS
  - composite 50-64 or 1 blocker     -> REDESIGN
  - composite < 50 or 2+ blockers    -> NO-GO

Profiles tune the cost-per-patient benchmark and recruitment difficulty.

Usage:
    python3 phase_gate_scorer.py --sample
    python3 phase_gate_scorer.py --input study.json --profile device --phase 2
    python3 phase_gate_scorer.py --input study.json --output json
"""

from __future__ import annotations

import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
try:
    import config_loader as _cfg
except ImportError:  # pragma: no cover
    _cfg = None

BANNER = "ESTIMATE ONLY — a medical monitor + biostatistician + regulatory owner must sign the gate decision."

WEIGHTS = {
    "recruitment_feasibility": 0.25,
    "endpoint_readiness": 0.20,
    "statistical_power": 0.25,
    "operational_complexity": 0.15,
    "budget_fit": 0.15,
}

# cost_per_patient_usd is the profile benchmark used for budget_fit scoring.
PROFILES = {
    "drug": {"cost_per_patient_usd": 41000, "recruit_difficulty": 1.0},
    "device": {"cost_per_patient_usd": 28000, "recruit_difficulty": 0.9},
    "biologic": {"cost_per_patient_usd": 52000, "recruit_difficulty": 1.1},
    "diagnostic": {"cost_per_patient_usd": 12000, "recruit_difficulty": 0.8},
    "digital-therapeutic": {"cost_per_patient_usd": 6000, "recruit_difficulty": 0.7},
}

OWNERS = {
    "GO": ["Principal Investigator", "Medical Monitor", "Biostatistician"],
    "GO-WITH-CONDITIONS": ["Principal Investigator", "Medical Monitor", "Biostatistician", "Regulatory Owner"],
    "REDESIGN": ["Medical Monitor", "Biostatistician", "Regulatory Owner", "Study Director"],
    "NO-GO": ["Medical Monitor", "Biostatistician", "Regulatory Owner", "Study Director", "R&D Head"],
}

SAMPLE = {
    "study_id": "PSO-2026-P2",
    "phase": 2,
    "eligible_population": 4200,
    "target_enrollment": 240,
    "enrollment_months": 14,
    "sites": 18,
    "endpoint_validated": True,
    "instrument_in_place": True,
    "planned_n": 240,
    "required_n": 260,
    "visits_per_patient": 9,
    "invasive_procedures": 2,
    "planned_budget_usd": 8200000,
}


def _clamp(x, lo=0.0, hi=100.0):
    return max(lo, min(hi, x))


def score_plan(study: dict, profile: dict, phase: int) -> dict:
    blockers: list[str] = []
    breakdown = {}

    # 1. recruitment feasibility: eligible pop must dwarf target; ~25 enroll/site/yr nominal
    elig = float(study.get("eligible_population", 0))
    target = float(study.get("target_enrollment", 1)) or 1
    months = float(study.get("enrollment_months", 12)) or 12
    sites = float(study.get("sites", 1)) or 1
    pool_ratio = elig / target if target else 0
    nominal_capacity = sites * 25.0 * (months / 12.0) / profile["recruit_difficulty"]
    capacity_ratio = nominal_capacity / target if target else 0
    recruit = _clamp(40.0 * min(pool_ratio / 10.0, 1.0) + 60.0 * min(capacity_ratio, 1.0))
    if pool_ratio < 3.0:
        blockers.append("recruitment: eligible pool < 3x target enrollment")
    breakdown["recruitment_feasibility"] = round(recruit, 1)

    # 2. endpoint readiness
    er = 0.0
    er += 60.0 if study.get("endpoint_validated") else 0.0
    er += 40.0 if study.get("instrument_in_place") else 0.0
    if not study.get("endpoint_validated"):
        blockers.append("endpoint: primary endpoint not validated")
    breakdown["endpoint_readiness"] = round(er, 1)

    # 3. statistical power: planned_n vs required_n
    planned_n = float(study.get("planned_n", 0))
    required_n = float(study.get("required_n", 0)) or 1
    ratio = planned_n / required_n if required_n else 0
    power = _clamp(100.0 * min(ratio, 1.0)) if ratio >= 1.0 else _clamp(100.0 * ratio - (1.0 - ratio) * 40.0)
    if ratio < 0.9:
        blockers.append(f"power: planned n ({planned_n:.0f}) < 90% of required n ({required_n:.0f})")
    breakdown["statistical_power"] = round(power, 1)

    # 4. operational complexity (inverted: more visits/procedures = lower score)
    visits = float(study.get("visits_per_patient", 6))
    procs = float(study.get("invasive_procedures", 0))
    complexity = _clamp(100.0 - (visits - 4) * 6.0 - procs * 10.0)
    breakdown["operational_complexity"] = round(complexity, 1)

    # 5. budget fit: planned budget vs benchmark cost-per-patient * target
    benchmark = profile["cost_per_patient_usd"] * target
    planned_budget = float(study.get("planned_budget_usd", 0))
    if planned_budget <= 0:
        budget = 0.0
        blockers.append("budget: no planned budget provided")
    else:
        coverage = planned_budget / benchmark if benchmark else 0
        # 100 if planned >= benchmark, sliding down if under-funded
        budget = _clamp(100.0 * min(coverage, 1.0)) if coverage >= 1.0 else _clamp(coverage * 100.0)
        if coverage < 0.75:
            blockers.append("budget: planned budget < 75% of benchmark cost")
    breakdown["budget_fit"] = round(budget, 1)

    composite = sum(breakdown[d] * w for d, w in WEIGHTS.items())
    verdict = _verdict(composite, blockers)
    return {
        "study_id": study.get("study_id", "UNSPECIFIED"),
        "phase": phase,
        "composite": round(composite, 1),
        "verdict": verdict,
        "named_owners": OWNERS[verdict],
        "breakdown": breakdown,
        "blockers": blockers,
        "benchmark_cost_usd": round(benchmark, 0),
    }


def _verdict(composite: float, blockers: list[str]) -> str:
    n = len(blockers)
    if n >= 2 or composite < 50.0:
        return "NO-GO"
    if n == 1 or composite < 65.0:
        return "REDESIGN"
    if composite < 80.0:
        return "GO-WITH-CONDITIONS"
    return "GO"


def evaluate(study: dict, profile_name: str, phase: int) -> dict:
    if profile_name not in PROFILES:
        raise ValueError(f"Unknown profile '{profile_name}'. Choose from {list(PROFILES)}.")
    return score_plan(study, PROFILES[profile_name], phase)


def _apply_named_owners(roles: list[str], owners: dict) -> list[str]:
    """Replace generic owner roles with 'Role (Name)' when onboarding named them."""
    role_to_key = {
        "Biostatistician": "biostatistician",
        "Medical Monitor": "medical_monitor",
        "Regulatory Owner": "regulatory_owner",
    }
    out = []
    for r in roles:
        name = owners.get(role_to_key.get(r, ""))
        out.append(f"{r} ({name})" if name else r)
    return out


def _render_human(r: dict) -> str:
    lines = [f"!! {BANNER}", "", f"Study: {r['study_id']}  (Phase {r['phase']})",
             f"Composite feasibility: {r['composite']}/100", f"Verdict: {r['verdict']}", ""]
    lines.append("Dimension breakdown:")
    for d, s in r["breakdown"].items():
        lines.append(f"  {d:26s} {s}")
    lines.append("")
    if r["blockers"]:
        lines.append("Blockers (each can force a downgrade):")
        for b in r["blockers"]:
            lines.append(f"  ! {b}")
        lines.append("")
    lines.append(f"Benchmark study cost (this profile): ${r['benchmark_cost_usd']:,.0f}")
    lines.append("Named owners who must sign the gate decision: " + ", ".join(r["named_owners"]))
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description="Score study feasibility and route a phase-gate verdict (ESTIMATE ONLY).")
    p.add_argument("--input", help="Path to JSON study plan")
    p.add_argument("--profile", default=None, choices=list(PROFILES),
                   help="overrides onboarding default_profile")
    p.add_argument("--phase", type=int, default=2, choices=[1, 2, 3, 4])
    p.add_argument("--output", choices=["human", "json"], default="human")
    p.add_argument("--sample", action="store_true", help="use the embedded sample")
    args = p.parse_args(argv)

    conf = _cfg.load_config() if _cfg else {}
    profile = args.profile or conf.get("default_profile", "drug")
    study = SAMPLE if (args.sample or not args.input) else json.load(open(args.input))
    phase = study.get("phase", args.phase) if (args.sample or not args.input) else args.phase
    try:
        result = evaluate(study, profile, phase)
    except ValueError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    result["named_owners"] = _apply_named_owners(result["named_owners"], conf.get("owners") or {})

    if args.output == "json":
        result["_banner"] = BANNER
        print(json.dumps(result, indent=2))
    else:
        print(_render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
