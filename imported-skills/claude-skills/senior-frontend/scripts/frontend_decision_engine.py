#!/usr/bin/env python3
"""
frontend_decision_engine.py — Deterministic frontend framework + rendering picker.

Stdlib-only. No LLM calls. Same input -> same output. Matches caller-supplied
constraints (primary device, LCP target, SEO-dependence, auth-walled, team
size) against profile JSON files in ../profiles/ and returns a ranked
recommendation with bundle budget, anti-patterns, and verifiable success
thresholds.

Karpathy discipline:
  - #1 Think Before Coding: requires --primary-device, --lcp-target-ms,
    --seo-dependent, --auth-walled, --team-size.
  - #4 Goal-Driven Execution: every recommendation prints the bundle and
    Web Vitals thresholds the chosen profile commits to.

Usage:
    python frontend_decision_engine.py --help
    python frontend_decision_engine.py --sample
    python frontend_decision_engine.py \\
        --primary-device mobile-4g --lcp-target-ms 2000 \\
        --seo-dependent true --auth-walled false --team-size 5
    python frontend_decision_engine.py ... --output json
    python frontend_decision_engine.py --list-profiles
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
    primary_device: str
    lcp_target_ms: int
    seo_dependent: bool
    auth_walled: bool
    team_size: int
    read_write_ratio: float
    inp_target_ms: int

    def kill_criteria_check(self) -> list[str]:
        kills: list[str] = []
        if self.seo_dependent and self.auth_walled:
            kills.append(
                "seo-dependent AND auth-walled: split the surface — public marketing "
                "goes static/SSR; auth-walled app goes SPA. Do not pick a single profile for both."
            )
        if self.primary_device == "mobile-4g" and self.lcp_target_ms > 3000:
            kills.append(
                f"mobile-4g primary with LCP target {self.lcp_target_ms}ms: "
                "target is too loose for the device class. Tighten to < 2500ms (Web Vitals 'good')."
            )
        if self.primary_device == "mobile-4g" and self.inp_target_ms > 300:
            kills.append(
                f"mobile-4g primary with INP target {self.inp_target_ms}ms: "
                "target is too loose for the device class. Tighten to < 200ms (Web Vitals 'good')."
            )
        if self.team_size < 1:
            kills.append("team_size < 1 makes no sense.")
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

    if "primary_device" in c:
        devices = c["primary_device"] if isinstance(c["primary_device"], list) else [c["primary_device"]]
        check(f"primary_device in {devices}", inputs.primary_device in devices, weight=2.0)
    if "seo_dependent" in c:
        check(f"seo_dependent = {c['seo_dependent']}", inputs.seo_dependent == c["seo_dependent"], weight=2.0)
    if "auth_walled_only" in c:
        check(f"auth_walled_only = {c['auth_walled_only']}", inputs.auth_walled == c["auth_walled_only"], weight=2.0)
    if "team_size_min" in c:
        check(f"team_size >= {c['team_size_min']}", inputs.team_size >= c["team_size_min"], weight=1.0)
    if "team_size_max" in c:
        check(f"team_size <= {c['team_size_max']}", inputs.team_size <= c["team_size_max"], weight=1.0)
    if "read_write_ratio_min" in c:
        check(f"read_write_ratio >= {c['read_write_ratio_min']}", inputs.read_write_ratio >= c["read_write_ratio_min"], weight=1.0)
    thresholds = profile.get("success_thresholds", {})
    if "lcp_ms_mobile_4g_p75" in thresholds:
        check(
            f"lcp_target supports {thresholds['lcp_ms_mobile_4g_p75']}ms p75",
            inputs.lcp_target_ms >= thresholds["lcp_ms_mobile_4g_p75"],
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
    L: list[str] = []
    L.append("# Frontend Stack Decision")
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
    stack = top.profile_data.get("stack", {})
    if stack:
        L.append("## Stack")
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
        L.append("## Verifiable success criteria (Karpathy #4)")
        L.append("")
        for k, v in thresh.items():
            L.append(f"- `{k}` = {v}")
        L.append("")
    gates = top.profile_data.get("ci_gates", [])
    if gates:
        L.append("## CI gates (required)")
        L.append("")
        for g in gates:
            L.append(f"- {g}")
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
    L.append("Walk `references/forcing_questions.md` BEFORE scaffolding. Do not pick this profile silently.")
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
                    "stack": m.profile_data.get("stack", {}),
                    "anti_recommendations": m.profile_data.get("anti_recommendations", {}),
                    "success_thresholds": m.profile_data.get("success_thresholds", {}),
                    "ci_gates": m.profile_data.get("ci_gates", []),
                }
                for m in matches
            ],
        },
        indent=2,
    )


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        description="Deterministic frontend framework + rendering picker. Surfaces tradeoffs + bundle budget + anti-patterns. Never auto-approves.",
        epilog="See ../references/forcing_questions.md for the 7-question grill.",
    )
    p.add_argument(
        "--primary-device",
        choices=["mobile-4g", "desktop-fiber", "low-end-android", "corporate-network"],
        help="Primary device + network condition.",
    )
    p.add_argument("--lcp-target-ms", type=int, help="LCP target in milliseconds (p75 on primary device).")
    p.add_argument("--inp-target-ms", type=int, default=200, help="INP target in milliseconds (default 200).")
    p.add_argument("--seo-dependent", choices=["true", "false"], help="Is the surface SEO-dependent?")
    p.add_argument("--auth-walled", choices=["true", "false"], help="Is the surface fully auth-walled?")
    p.add_argument("--team-size", type=int, help="Frontend engineers on this surface.")
    p.add_argument("--read-write-ratio", type=float, default=1.0, help="Reads per write (>= 100 hints static).")
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
            primary_device="mobile-4g",
            lcp_target_ms=2000,
            seo_dependent=True,
            auth_walled=False,
            team_size=5,
            read_write_ratio=4.0,
            inp_target_ms=150,
        )
    else:
        required = [
            ("primary_device", args.primary_device),
            ("lcp_target_ms", args.lcp_target_ms),
            ("seo_dependent", args.seo_dependent),
            ("auth_walled", args.auth_walled),
            ("team_size", args.team_size),
        ]
        missing = [n for n, v in required if v is None]
        if missing:
            print("Missing required inputs: " + ", ".join(missing), file=sys.stderr)
            print("Run with --sample for an example, or --list-profiles.", file=sys.stderr)
            return 2
        inputs = Inputs(
            primary_device=args.primary_device,
            lcp_target_ms=args.lcp_target_ms,
            seo_dependent=(args.seo_dependent == "true"),
            auth_walled=(args.auth_walled == "true"),
            team_size=args.team_size,
            read_write_ratio=args.read_write_ratio,
            inp_target_ms=args.inp_target_ms,
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
