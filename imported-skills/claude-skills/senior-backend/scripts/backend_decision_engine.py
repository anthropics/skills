#!/usr/bin/env python3
"""
backend_decision_engine.py — Deterministic backend pattern + stack picker.

Stdlib-only. No LLM calls. Matches caller-supplied constraints (team size,
QPS, tenancy, data sensitivity, pattern preference) against profile JSON
files in ../profiles/ and returns a ranked recommendation with SLO floor,
anti-patterns, named approvers, and kill criteria.

Karpathy discipline:
  - #1 Think Before Coding: requires the seven forcing-question answers as
    inputs. Refuses to recommend without read/write ratio + QPS.
  - #4 Goal-Driven Execution: every recommendation prints the SLO floor
    (p50/p95/p99 latency + uptime + RPO/RTO).

Matt Pocock discipline:
  - Never auto-approves. Production schema changes always name the human
    chain (tech-lead + on-call + DBA).

Usage:
    python backend_decision_engine.py --help
    python backend_decision_engine.py --sample
    python backend_decision_engine.py \\
        --team-size 8 --qps-p99 50 --read-write-ratio 20 \\
        --tenancy shared-multi-tenant --data-sensitivity pii \\
        --pattern modular-monolith --language-preference typescript
    python backend_decision_engine.py ... --output json
    python backend_decision_engine.py --list-profiles
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
    qps_p99: int
    read_write_ratio: float
    tenancy: str
    data_sensitivity: str
    pattern_preference: str
    language_preference: str
    has_platform_team: bool
    needs_admin_panel: bool

    def kill_criteria_check(self) -> list[str]:
        kills: list[str] = []
        # Microservices threshold (Newman, MonolithFirst)
        if self.pattern_preference == "microservices" and self.team_size < 30:
            kills.append(
                f"microservices with team size {self.team_size}: Sam Newman's MonolithFirst rule — "
                "extract a service only when (a) team >= 30 AND (b) bounded context proven independent "
                "AND (c) platform team exists. Reduce to modular monolith."
            )
        if self.pattern_preference == "microservices" and not self.has_platform_team:
            kills.append(
                "microservices without a platform team: operational burden falls on product engineers, "
                "halving their velocity. Either fund a platform team or stay modular."
            )
        # Compliance gate
        if self.data_sensitivity in ("phi", "pci") and self.team_size < 4:
            kills.append(
                f"data sensitivity {self.data_sensitivity!r} with team size {self.team_size}: regulated workloads "
                "require named compliance owner + DBA + security review. Escalate to ra-qm-team or cs-ciso-advisor."
            )
        # QPS realism
        if self.qps_p99 > 5000 and self.pattern_preference == "modular-monolith":
            kills.append(
                f"QPS p99 {self.qps_p99} with modular monolith: throughput class typically forces extracted "
                "services for hot paths. Re-examine pattern with the candidate hot path identified."
            )
        if self.qps_p99 < 1 and self.team_size > 5:
            kills.append(
                f"QPS p99 {self.qps_p99} with team size {self.team_size}: traffic forecast is implausibly low — "
                "pull current metrics or this is a tooling problem, not an architecture problem."
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
    name = profile.get("profile_name", "unknown")
    c = profile.get("constraints", {})
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

    if "team_size_min" in c:
        check(f"team_size >= {c['team_size_min']}", inputs.team_size >= c["team_size_min"], weight=2.0)
    if "team_size_max" in c:
        check(f"team_size <= {c['team_size_max']}", inputs.team_size <= c["team_size_max"], weight=2.0)
    if "tenancy" in c:
        target = c["tenancy"]
        ok = inputs.tenancy in target or target in inputs.tenancy
        check(f"tenancy ~ {target}", ok, weight=1.5)
    if "data_sensitivity_tier_max" in c:
        tier_order = {"public": 0, "internal": 1, "pii-only": 2, "pii": 2, "phi": 3, "pci": 3, "regulated": 4}
        ok = tier_order.get(inputs.data_sensitivity, 0) <= tier_order.get(c["data_sensitivity_tier_max"], 4)
        check(f"data_sensitivity <= {c['data_sensitivity_tier_max']}", ok, weight=1.0)
    if "pattern" in c:
        target = c["pattern"]
        ok = inputs.pattern_preference in target or target in inputs.pattern_preference
        check(f"pattern ~ {target}", ok, weight=2.0)
    if "qps_p99_min" in c:
        check(f"qps_p99 >= {c['qps_p99_min']}", inputs.qps_p99 >= c["qps_p99_min"], weight=1.5)
    if "platform_team_exists" in c:
        check(
            f"platform_team_exists = {c['platform_team_exists']}",
            inputs.has_platform_team == c["platform_team_exists"],
            weight=1.5,
        )
    if "admin_panel_needed" in c:
        check(
            f"admin_panel_needed = {c['admin_panel_needed']}",
            inputs.needs_admin_panel == c["admin_panel_needed"],
            weight=1.0,
        )
    # Language preference — match only against fields that explicitly name a language:
    # profile_name, stack.language, stack.runtime. The previous substring search over
    # the entire serialized profile false-matched e.g. "go" against "django"/"mongo".
    if inputs.language_preference:
        lang = inputs.language_preference.lower()
        stack = profile.get("stack", {})
        language_fields = [
            name.lower(),
            str(stack.get("language", "")).lower(),
            str(stack.get("runtime", "")).lower(),
        ]
        # Token-level match: split on '-' and check exact membership so "go" doesn't
        # match "mongo" but still matches "go-or-rust-microservice".
        tokens: set[str] = set()
        for field in language_fields:
            tokens.update(field.replace("_", "-").split("-"))
        if lang in tokens:
            check(f"stack-language matches '{inputs.language_preference}'", True, weight=1.0)

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
    L: list[str] = []
    L.append("# Backend Stack Decision")
    L.append("")
    L.append("## Inputs (your assumptions, Karpathy #1)")
    L.append("")
    for k, v in asdict(inputs).items():
        L.append(f"- **{k}**: `{v}`")
    L.append("")
    if kills:
        L.append("## Kill criteria tripped — STOP and resolve")
        L.append("")
        for k in kills:
            L.append(f"- {k}")
        L.append("")
    if not matches:
        L.append("No profiles found in ../profiles/.")
        return "\n".join(L)
    top = matches[0]
    second = matches[1] if len(matches) > 1 else None
    L.append("## Recommended profile")
    L.append("")
    L.append(f"**{top.profile_name}** — fit score {top.score:.0%}")
    L.append("")
    L.append(f"_{top.profile_data.get('description', '')}_")
    L.append("")
    if top.matched_constraints:
        L.append("**Matched:**")
        for c in top.matched_constraints:
            L.append(f"- {c}")
        L.append("")
    if top.violated_constraints:
        L.append("**Violated (review before locking):**")
        for c in top.violated_constraints:
            L.append(f"- {c}")
        L.append("")
    if second and abs(top.score - second.score) < 0.15:
        L.append(f"## Close runner-up: {second.profile_name} ({second.score:.0%}) — surface the tradeoff.")
        L.append("")
    for stack_key in ("stack", "stack_go", "stack_rust"):
        stack = top.profile_data.get(stack_key)
        if stack:
            L.append(f"## {stack_key}")
            L.append("")
            L.append("```json")
            L.append(json.dumps(stack, indent=2))
            L.append("```")
            L.append("")
    anti = top.profile_data.get("anti_recommendations", {})
    if anti:
        L.append("## Anti-patterns (DO NOT introduce on this profile)")
        L.append("")
        for k, v in anti.items():
            L.append(f"- **{k}** — {v}")
        L.append("")
    thresh = top.profile_data.get("success_thresholds", {})
    if thresh:
        L.append("## Verifiable SLO floor (Karpathy #4)")
        L.append("")
        for k, v in thresh.items():
            L.append(f"- `{k}` = {v}")
        L.append("")
    approvers = top.profile_data.get("named_approver_chain", {})
    if approvers:
        L.append("## Named approvers (this tool NEVER auto-approves)")
        L.append("")
        for k, v in approvers.items():
            L.append(f"- **{k}**: {v}")
        L.append("")
    canon = top.profile_data.get("canon_references", [])
    if canon:
        L.append("## Canon")
        L.append("")
        for c in canon:
            L.append(f"- {c}")
        L.append("")
    L.append("---")
    L.append("")
    L.append("BEFORE locking: fork into `slo-architect` to formalize the SLO, and `api-design-reviewer` to validate the API contract.")
    return "\n".join(L)


def render_json(inputs: Inputs, matches: list[Match], kills: list[str]) -> str:
    return json.dumps(
        {
            "inputs": asdict(inputs),
            "kill_criteria_tripped": kills,
            "ranked_matches": [
                {
                    "profile_name": m.profile_name,
                    "score": round(m.score, 4),
                    "matched_constraints": m.matched_constraints,
                    "violated_constraints": m.violated_constraints,
                    "stack": m.profile_data.get("stack")
                    or m.profile_data.get("stack_go")
                    or m.profile_data.get("stack_rust")
                    or {},
                    "anti_recommendations": m.profile_data.get("anti_recommendations", {}),
                    "success_thresholds": m.profile_data.get("success_thresholds", {}),
                    "named_approver_chain": m.profile_data.get("named_approver_chain", {}),
                }
                for m in matches
            ],
        },
        indent=2,
    )


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        description="Deterministic backend pattern + stack picker. Surfaces tradeoffs + SLO floor + named approvers. Never auto-approves.",
        epilog="See ../references/forcing_questions.md for the 7-question grill.",
    )
    p.add_argument("--team-size", type=int, help="Backend engineers on this service.")
    p.add_argument("--qps-p99", type=int, help="Year-1 p99 QPS forecast.")
    p.add_argument("--read-write-ratio", type=float, help="Reads per write.")
    p.add_argument(
        "--tenancy",
        choices=["single-tenant", "shared-multi-tenant", "isolated-multi-tenant"],
        help="Tenancy model.",
    )
    p.add_argument(
        "--data-sensitivity",
        choices=["public", "internal", "pii-only", "pii", "phi", "pci", "regulated"],
        help="Highest data sensitivity tier in scope.",
    )
    p.add_argument(
        "--pattern",
        choices=["monolith", "modular-monolith", "domain-bounded-services", "microservices", "serverless"],
        help="Preferred pattern.",
    )
    p.add_argument(
        "--language-preference",
        choices=["typescript", "python", "go", "rust", "java", "kotlin", "dotnet"],
        default="typescript",
        help="Preferred backend language.",
    )
    p.add_argument("--platform-team", choices=["true", "false"], default="false", help="Dedicated platform team exists?")
    p.add_argument("--needs-admin-panel", choices=["true", "false"], default="false", help="Admin panel needed (Django shines)?")
    p.add_argument("--output", choices=["markdown", "json"], default="markdown")
    p.add_argument("--list-profiles", action="store_true")
    p.add_argument("--sample", action="store_true")
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
            team_size=8,
            qps_p99=50,
            read_write_ratio=20.0,
            tenancy="shared-multi-tenant",
            data_sensitivity="pii",
            pattern_preference="modular-monolith",
            language_preference="typescript",
            has_platform_team=False,
            needs_admin_panel=False,
        )
    else:
        required = [
            ("team_size", args.team_size),
            ("qps_p99", args.qps_p99),
            ("read_write_ratio", args.read_write_ratio),
            ("tenancy", args.tenancy),
            ("data_sensitivity", args.data_sensitivity),
            ("pattern", args.pattern),
        ]
        missing = [n for n, v in required if v is None]
        if missing:
            print("Missing required inputs: " + ", ".join(missing), file=sys.stderr)
            print("Run with --sample for an example, or --list-profiles.", file=sys.stderr)
            return 2
        inputs = Inputs(
            team_size=args.team_size,
            qps_p99=args.qps_p99,
            read_write_ratio=args.read_write_ratio,
            tenancy=args.tenancy,
            data_sensitivity=args.data_sensitivity,
            pattern_preference=args.pattern,
            language_preference=args.language_preference,
            has_platform_team=(args.platform_team == "true"),
            needs_admin_panel=(args.needs_admin_panel == "true"),
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
