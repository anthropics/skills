#!/usr/bin/env python3
"""
fullstack_decision_engine.py — Deterministic fullstack-stack picker with explicit kill criteria.

Stdlib-only. No LLM calls. Same input -> same output. Loads profile JSON files
from ../profiles/ and matches them against caller-supplied constraints, then
returns a ranked recommendation with named-approver chain, success thresholds,
and the kill criteria the choice trips (if any).

Karpathy discipline:
  - #1 Think Before Coding: forces caller to supply --team-size, --cadence,
    --user-facing, --budget — the four assumptions that decide the stack.
  - #2 Simplicity First: does NOT scaffold anything. Picks the profile.
    Scaffolding is the existing project_scaffolder.py's job.
  - #3 Surgical Changes: prints a digest; never edits files.
  - #4 Goal-Driven Execution: every recommendation prints verifiable success
    thresholds (latency, uptime, LCP).

Matt Pocock discipline:
  - Never auto-approves. Every output names the human(s) who must sign off.
  - If two profiles tie within ~10%, the tool surfaces the tie and the
    tradeoff — does not pick.

Usage:
    python fullstack_decision_engine.py --help
    python fullstack_decision_engine.py --sample
    python fullstack_decision_engine.py \\
        --team-size 6 --team-size-12mo 12 \\
        --cadence daily --user-facing true --budget 5000 \\
        --traffic-p99-rps 50 --data-sensitivity pii-only
    python fullstack_decision_engine.py ... --output json
    python fullstack_decision_engine.py --list-profiles
"""
from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
PROFILES_DIR = SCRIPT_DIR.parent / "profiles"


@dataclass
class Inputs:
    team_size: int
    team_size_12mo: int
    cadence: str
    user_facing: bool
    budget_usd_monthly: int
    traffic_p99_rps: int
    data_sensitivity: str
    read_write_ratio: float

    def kill_criteria_check(self) -> list[str]:
        """Return list of self-inconsistent inputs (Karpathy #1)."""
        kills: list[str] = []
        if self.team_size_12mo < self.team_size:
            kills.append(
                f"team shrinking ({self.team_size} -> {self.team_size_12mo}): "
                "if intentional, plan for handoff/maintenance mode, not new architecture."
            )
        if self.cadence == "quarterly" and self.user_facing:
            kills.append(
                "quarterly cadence on a customer-facing product: fix the deployment "
                "bottleneck before stack work (Forsgren/Humble/Kim, Accelerate 2018)."
            )
        if self.budget_usd_monthly < 200 and self.user_facing and self.traffic_p99_rps > 50:
            kills.append(
                f"budget ceiling ${self.budget_usd_monthly}/mo with {self.traffic_p99_rps} p99 RPS "
                "customer-facing: math does not work; raise budget or reduce scope."
            )
        if self.data_sensitivity in ("phi", "pci") and self.team_size < 4:
            kills.append(
                f"data sensitivity {self.data_sensitivity!r} with team size {self.team_size}: "
                "regulated workloads require named DPO + security owner + DBA review minimum."
            )
        return kills


@dataclass
class Match:
    profile_name: str
    score: float
    matched_constraints: list[str] = field(default_factory=list)
    violated_constraints: list[str] = field(default_factory=list)
    profile_data: dict[str, Any] = field(default_factory=dict)


def load_profiles() -> dict[str, dict[str, Any]]:
    profiles: dict[str, dict[str, Any]] = {}
    if not PROFILES_DIR.exists():
        return profiles
    for p in sorted(PROFILES_DIR.glob("*.json")):
        with p.open() as f:
            data = json.load(f)
        profiles[data.get("profile_name", p.stem)] = data
    return profiles


def score_profile(profile: dict[str, Any], inputs: Inputs) -> Match:
    """Score how well a profile fits the inputs. 0.0–1.0."""
    name = profile.get("profile_name", "unknown")
    constraints = profile.get("constraints", {})
    matched: list[str] = []
    violated: list[str] = []
    w_total = 0.0
    w_matched = 0.0

    def check(label: str, ok: bool, weight: float) -> None:
        nonlocal w_total, w_matched
        w_total += weight
        if ok:
            w_matched += weight
            matched.append(label)
        else:
            violated.append(label)

    if "team_size_max" in constraints:
        check(
            f"team_size <= {constraints['team_size_max']}",
            inputs.team_size <= constraints["team_size_max"],
            weight=2.0,
        )
    if "team_size_min" in constraints:
        check(
            f"team_size >= {constraints['team_size_min']}",
            inputs.team_size >= constraints["team_size_min"],
            weight=2.0,
        )
    if "team_size_year_one_max" in constraints:
        check(
            f"team_size_12mo <= {constraints['team_size_year_one_max']}",
            inputs.team_size_12mo <= constraints["team_size_year_one_max"],
            weight=1.5,
        )
    if "deployment_cadence" in constraints:
        target = constraints["deployment_cadence"]
        # Profile cadences are explicit alternatives joined by "-or-",
        # e.g. "weekly-or-on-demand" → {"weekly", "on-demand"}.
        # Modifier suffixes like "-with-gates" are stripped for matching.
        allowed = {a.split("-with-")[0] for a in target.split("-or-")}
        ok = inputs.cadence in allowed
        check(f"cadence ~ {target}", ok, weight=1.5)
    if "cloud_budget_monthly_usd_ceiling" in constraints:
        check(
            f"budget <= ${constraints['cloud_budget_monthly_usd_ceiling']}/mo",
            inputs.budget_usd_monthly <= constraints["cloud_budget_monthly_usd_ceiling"],
            weight=1.5,
        )
    if "user_facing" in constraints:
        check(
            f"user_facing = {constraints['user_facing']}",
            inputs.user_facing == constraints["user_facing"],
            weight=2.0,
        )
    if "data_sensitivity_tier" in constraints:
        target = constraints["data_sensitivity_tier"]
        ok = inputs.data_sensitivity in target or "or" in target
        check(f"data_sensitivity ~ {target}", ok, weight=1.0)
    if "read_write_ratio_min" in constraints:
        check(
            f"read_write_ratio >= {constraints['read_write_ratio_min']}",
            inputs.read_write_ratio >= constraints["read_write_ratio_min"],
            weight=1.0,
        )

    score = w_matched / w_total if w_total > 0 else 0.0
    return Match(
        profile_name=name,
        score=score,
        matched_constraints=matched,
        violated_constraints=violated,
        profile_data=profile,
    )


def rank(profiles: dict[str, dict[str, Any]], inputs: Inputs) -> list[Match]:
    matches = [score_profile(p, inputs) for p in profiles.values()]
    matches.sort(key=lambda m: m.score, reverse=True)
    return matches


def render_markdown(inputs: Inputs, matches: list[Match], kills: list[str]) -> str:
    lines: list[str] = []
    lines.append("# Fullstack Stack Decision")
    lines.append("")
    lines.append("## Inputs (your assumptions, Karpathy #1)")
    lines.append("")
    for k, v in asdict(inputs).items():
        lines.append(f"- **{k}**: `{v}`")
    lines.append("")
    if kills:
        lines.append("## Kill criteria tripped — STOP and resolve before proceeding")
        lines.append("")
        for k in kills:
            lines.append(f"- {k}")
        lines.append("")
    if not matches:
        lines.append("No profiles loaded. Check ../profiles/ exists.")
        return "\n".join(lines)
    top = matches[0]
    second = matches[1] if len(matches) > 1 else None
    lines.append("## Recommended profile")
    lines.append("")
    lines.append(f"**{top.profile_name}** — fit score {top.score:.0%}")
    lines.append("")
    lines.append(f"_{top.profile_data.get('description', '')}_")
    lines.append("")
    if top.matched_constraints:
        lines.append("**Matched constraints:**")
        for c in top.matched_constraints:
            lines.append(f"- {c}")
        lines.append("")
    if top.violated_constraints:
        lines.append("**Violated constraints (review before locking choice):**")
        for c in top.violated_constraints:
            lines.append(f"- {c}")
        lines.append("")
    if second and abs(top.score - second.score) < 0.15:
        lines.append(
            f"## Close runner-up: {second.profile_name} (fit {second.score:.0%}) — "
            "tie within 15%; surface the tradeoff to the user before locking."
        )
        lines.append("")
    stack = top.profile_data.get("stack_recommendations", {})
    if stack:
        lines.append("## Stack recommendation")
        lines.append("")
        lines.append("```json")
        lines.append(json.dumps(stack, indent=2))
        lines.append("```")
        lines.append("")
    anti = top.profile_data.get("anti_recommendations", {})
    if anti:
        lines.append("## Anti-patterns (DO NOT introduce these on this profile)")
        lines.append("")
        for k, v in anti.items():
            lines.append(f"- **{k}** — {v}")
        lines.append("")
    thresholds = top.profile_data.get("success_thresholds", {})
    if thresholds:
        lines.append("## Verifiable success criteria (Karpathy #4)")
        lines.append("")
        for k, v in thresholds.items():
            lines.append(f"- `{k}` = {v}")
        lines.append("")
    approvers = top.profile_data.get("named_approver_chain", {})
    if approvers:
        lines.append("## Named approvers (this tool NEVER auto-approves)")
        lines.append("")
        for k, v in approvers.items():
            lines.append(f"- **{k}**: {v}")
        lines.append("")
    canon = top.profile_data.get("canon_references", [])
    if canon:
        lines.append("## Canon")
        lines.append("")
        for c in canon:
            lines.append(f"- {c}")
        lines.append("")
    lines.append("---")
    lines.append("")
    lines.append(
        "Next step: walk the 7 forcing questions in `references/forcing_questions.md` "
        "with the user. Do NOT scaffold until every question has an answer."
    )
    return "\n".join(lines)


def render_json(inputs: Inputs, matches: list[Match], kills: list[str]) -> str:
    out = {
        "inputs": asdict(inputs),
        "kill_criteria_tripped": kills,
        "ranked_matches": [
            {
                "profile_name": m.profile_name,
                "score": round(m.score, 4),
                "matched_constraints": m.matched_constraints,
                "violated_constraints": m.violated_constraints,
                "stack_recommendations": m.profile_data.get("stack_recommendations", {}),
                "anti_recommendations": m.profile_data.get("anti_recommendations", {}),
                "success_thresholds": m.profile_data.get("success_thresholds", {}),
                "named_approver_chain": m.profile_data.get("named_approver_chain", {}),
            }
            for m in matches
        ],
    }
    return json.dumps(out, indent=2)


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        description="Deterministic fullstack-stack picker. Matches inputs against profile JSON files; surfaces tradeoffs + kill criteria + named approvers. Never auto-approves.",
        epilog="See ../references/forcing_questions.md for the 7-question grill that must be walked before this tool is run.",
    )
    p.add_argument("--team-size", type=int, help="Engineers today.")
    p.add_argument("--team-size-12mo", type=int, help="Credible engineer count in 12 months.")
    p.add_argument(
        "--cadence",
        choices=["per-pr", "daily", "weekly", "quarterly", "on-demand"],
        help="Target deployment cadence.",
    )
    p.add_argument(
        "--user-facing",
        choices=["true", "false"],
        help="Is the surface customer-facing (true) or internal/marketing (false)?",
    )
    p.add_argument("--budget", type=int, help="Monthly cloud + SaaS budget ceiling (USD).")
    p.add_argument(
        "--traffic-p99-rps",
        type=int,
        default=0,
        help="One-year p99 traffic forecast (requests per second).",
    )
    p.add_argument(
        "--data-sensitivity",
        choices=["public", "internal", "pii-only", "pii", "phi", "pci", "regulated"],
        default="public",
        help="Data sensitivity tier.",
    )
    p.add_argument(
        "--read-write-ratio",
        type=float,
        default=1.0,
        help="Reads per write (>= 100 hints marketing-site profile).",
    )
    p.add_argument("--output", choices=["markdown", "json"], default="markdown")
    p.add_argument("--list-profiles", action="store_true", help="List available profile names + exit.")
    p.add_argument("--sample", action="store_true", help="Run with sample SaaS-startup inputs.")
    return p


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)

    profiles = load_profiles()

    if args.list_profiles:
        if not profiles:
            print("No profiles found in", PROFILES_DIR, file=sys.stderr)
            return 1
        for name, data in profiles.items():
            print(f"{name}: {data.get('description', '')[:120]}")
        return 0

    if args.sample:
        inputs = Inputs(
            team_size=6,
            team_size_12mo=12,
            cadence="daily",
            user_facing=True,
            budget_usd_monthly=5000,
            traffic_p99_rps=45,
            data_sensitivity="pii-only",
            read_write_ratio=4.0,
        )
    else:
        required = [
            ("team_size", args.team_size),
            ("team_size_12mo", args.team_size_12mo),
            ("cadence", args.cadence),
            ("user_facing", args.user_facing),
            ("budget", args.budget),
        ]
        missing = [name for name, val in required if val is None]
        if missing:
            print(
                "Missing required inputs: " + ", ".join(missing),
                file=sys.stderr,
            )
            print(
                "Run with --sample to see a worked example, or --list-profiles to see profile names.",
                file=sys.stderr,
            )
            return 2
        inputs = Inputs(
            team_size=args.team_size,
            team_size_12mo=args.team_size_12mo,
            cadence=args.cadence,
            user_facing=(args.user_facing == "true"),
            budget_usd_monthly=args.budget,
            traffic_p99_rps=args.traffic_p99_rps,
            data_sensitivity=args.data_sensitivity,
            read_write_ratio=args.read_write_ratio,
        )

    kills = inputs.kill_criteria_check()
    matches = rank(profiles, inputs)

    if args.output == "json":
        print(render_json(inputs, matches, kills))
    else:
        print(render_markdown(inputs, matches, kills))
    return 0


if __name__ == "__main__":
    sys.exit(main())
