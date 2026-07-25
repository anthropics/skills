#!/usr/bin/env python3
"""joint_gtm_planner.py - Generate a 90-day joint GTM plan for a signed partner.

Stdlib-only. Deterministic. Validates that the sales_motion is compatible with the
partner_tier — refuses to plan channel-led GTM for a REFERRAL tier, refuses to plan
white-label for any tier other than OEM.

Output: 90-day plan with:
  - Pre-launch milestones (days -30 to 0): training, certification, materials, target accounts
  - Launch motion (days 0 to 30): MDF allocation, first deals, joint pursuit
  - Mid-quarter checkpoint (day 45): named checkpoint criteria
  - 90-day success criteria: pipeline-sourced floor, deals-closed floor, learnings doc

Industry profiles tune:
  - target account count by tier
  - MDF spend defaults by tier
  - pipeline-sourced floor by tier (multiple of deal_avg_size)

Usage:
    python joint_gtm_planner.py --sample
    python joint_gtm_planner.py --input gtm.json --profile saas
    python joint_gtm_planner.py --input gtm.json --output json
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, field, asdict
from typing import Any


SAMPLE_GTM = {
    "partner_name": "Northstar Consulting",
    "partner_tier": "SI_CONSULTING",
    "target_segments": ["mid-market financial services EMEA", "regulated SaaS LATAM"],
    "joint_value_proposition": (
        "We bring the platform; Northstar brings 8 certified consultants who deliver "
        "the regulated-vertical implementation in 60 days vs the 180 days customers "
        "would spend doing it themselves."
    ),
    "sales_motion": "co_sell",
    "commitment_horizon_months": 12,
    "deal_avg_size_usd": 90000,
}


VALID_TIERS = ("REFERRAL", "RESELLER", "OEM", "SI_CONSULTING", "STRATEGIC")
VALID_MOTIONS = ("pure_referral", "co_sell", "channel_led", "white_label")


# Hard compatibility matrix: which motions are allowed at which tier.
TIER_MOTION_MATRIX: dict[str, set[str]] = {
    "REFERRAL":      {"pure_referral"},
    "RESELLER":      {"pure_referral", "co_sell", "channel_led"},
    "OEM":           {"co_sell", "channel_led", "white_label"},
    "SI_CONSULTING": {"pure_referral", "co_sell"},
    "STRATEGIC":     {"co_sell", "channel_led"},
}


PROFILES: dict[str, dict[str, Any]] = {
    "saas": {
        "target_accounts": {"REFERRAL": 5, "RESELLER": 15, "OEM": 10, "SI_CONSULTING": 12, "STRATEGIC": 20},
        "mdf_default": {"REFERRAL": 0, "RESELLER": 15000, "OEM": 40000, "SI_CONSULTING": 20000, "STRATEGIC": 75000},
        "pipeline_floor_multiple": {"REFERRAL": 3, "RESELLER": 8, "OEM": 6, "SI_CONSULTING": 6, "STRATEGIC": 12},
        "deals_closed_floor": {"REFERRAL": 1, "RESELLER": 3, "OEM": 2, "SI_CONSULTING": 2, "STRATEGIC": 4},
    },
    "api": {
        "target_accounts": {"REFERRAL": 8, "RESELLER": 20, "OEM": 8, "SI_CONSULTING": 10, "STRATEGIC": 15},
        "mdf_default": {"REFERRAL": 0, "RESELLER": 10000, "OEM": 30000, "SI_CONSULTING": 15000, "STRATEGIC": 60000},
        "pipeline_floor_multiple": {"REFERRAL": 4, "RESELLER": 10, "OEM": 8, "SI_CONSULTING": 6, "STRATEGIC": 15},
        "deals_closed_floor": {"REFERRAL": 1, "RESELLER": 4, "OEM": 2, "SI_CONSULTING": 2, "STRATEGIC": 5},
    },
    "enterprise-software": {
        "target_accounts": {"REFERRAL": 3, "RESELLER": 8, "OEM": 6, "SI_CONSULTING": 10, "STRATEGIC": 15},
        "mdf_default": {"REFERRAL": 0, "RESELLER": 30000, "OEM": 75000, "SI_CONSULTING": 40000, "STRATEGIC": 150000},
        "pipeline_floor_multiple": {"REFERRAL": 2, "RESELLER": 5, "OEM": 4, "SI_CONSULTING": 5, "STRATEGIC": 8},
        "deals_closed_floor": {"REFERRAL": 1, "RESELLER": 2, "OEM": 1, "SI_CONSULTING": 2, "STRATEGIC": 3},
    },
    "marketplace": {
        "target_accounts": {"REFERRAL": 10, "RESELLER": 25, "OEM": 12, "SI_CONSULTING": 15, "STRATEGIC": 25},
        "mdf_default": {"REFERRAL": 0, "RESELLER": 10000, "OEM": 25000, "SI_CONSULTING": 15000, "STRATEGIC": 50000},
        "pipeline_floor_multiple": {"REFERRAL": 5, "RESELLER": 12, "OEM": 8, "SI_CONSULTING": 8, "STRATEGIC": 18},
        "deals_closed_floor": {"REFERRAL": 2, "RESELLER": 5, "OEM": 3, "SI_CONSULTING": 3, "STRATEGIC": 6},
    },
    "hardware": {
        "target_accounts": {"REFERRAL": 5, "RESELLER": 10, "OEM": 8, "SI_CONSULTING": 8, "STRATEGIC": 12},
        "mdf_default": {"REFERRAL": 0, "RESELLER": 25000, "OEM": 100000, "SI_CONSULTING": 30000, "STRATEGIC": 200000},
        "pipeline_floor_multiple": {"REFERRAL": 2, "RESELLER": 6, "OEM": 5, "SI_CONSULTING": 4, "STRATEGIC": 10},
        "deals_closed_floor": {"REFERRAL": 1, "RESELLER": 2, "OEM": 1, "SI_CONSULTING": 2, "STRATEGIC": 3},
    },
}


@dataclass
class Milestone:
    day: int
    name: str
    owner: str
    deliverable: str


@dataclass
class GtmPlan:
    partner_name: str
    profile: str
    partner_tier: str
    sales_motion: str
    target_segments: list[str]
    joint_value_proposition: str
    pre_launch: list[Milestone] = field(default_factory=list)
    launch: list[Milestone] = field(default_factory=list)
    mid_quarter_checkpoint: list[str] = field(default_factory=list)
    success_criteria_90d: list[str] = field(default_factory=list)
    mdf_allocation_usd: float = 0.0
    target_account_count: int = 0
    pipeline_floor_usd: float = 0.0
    deals_closed_floor: int = 0
    validation_errors: list[str] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)


def _validate(gtm: dict) -> list[str]:
    errs: list[str] = []
    tier = (gtm.get("partner_tier") or "").upper()
    motion = (gtm.get("sales_motion") or "").lower()
    if tier not in VALID_TIERS:
        errs.append(f"partner_tier '{tier}' not in {VALID_TIERS}")
        return errs
    if motion not in VALID_MOTIONS:
        errs.append(f"sales_motion '{motion}' not in {VALID_MOTIONS}")
        return errs
    if motion not in TIER_MOTION_MATRIX[tier]:
        errs.append(
            f"sales_motion '{motion}' is not compatible with tier '{tier}'. "
            f"Allowed motions for {tier}: {sorted(TIER_MOTION_MATRIX[tier])}. "
            f"If you need '{motion}', re-tier the partner via partner_tier_classifier.py first."
        )
    if not gtm.get("joint_value_proposition"):
        errs.append("joint_value_proposition is required (one sentence with end-customer)")
    if not gtm.get("target_segments"):
        errs.append("target_segments is required (named segments, not 'everyone')")
    return errs


def _pre_launch_milestones(tier: str, motion: str) -> list[Milestone]:
    base = [
        Milestone(-30, "Mutual NDA + Partner Agreement signed",
                  "BD lead + Legal both sides", "Signed PDFs"),
        Milestone(-25, "Joint kickoff call: name exec sponsors",
                  "BD lead + Partner GM", "Sponsor pair documented"),
        Milestone(-20, "Target Account List (TAL) jointly built",
                  "Sales Director + Partner Sales lead",
                  "Named-account list with conflict resolution per-account"),
        Milestone(-15, "Partner sales training (week 1 of 2)",
                  "Sales Enablement", "Training attendance log"),
        Milestone(-10, "Partner sales training (week 2 of 2) + certification",
                  "Sales Enablement + Partner reps",
                  "Named certified reps per partner"),
    ]
    if tier in ("OEM", "STRATEGIC"):
        base.append(Milestone(
            -7, "Integration QA + support runbook signoff",
            "Engineering + Support both sides",
            "Joint Tier-1/Tier-2 support runbook"))
    if motion == "white_label":
        base.append(Milestone(
            -5, "Brand-use guide + co-branded asset pack approved",
            "Marketing + Legal", "Asset pack + brand-use rules"))
    if motion in ("co_sell", "channel_led"):
        base.append(Milestone(
            -3, "Rules of Engagement signed (channel conflict)",
            "Sales Director + Partner Sales lead",
            "Signed ROE with named-account map"))
    base.append(Milestone(
        0, "Joint launch announcement + first pursuit kickoff",
        "Marketing + Sales both sides",
        "Press / blog / customer-facing materials"))
    return base


def _launch_milestones(tier: str, motion: str) -> list[Milestone]:
    base = [
        Milestone(7, "First joint pursuit named (single account)",
                  "Sales Director + Partner Sales lead",
                  "Account brief + close plan"),
        Milestone(15, "5 joint pursuits in flight",
                  "Sales Director + Partner Sales lead",
                  "Pipeline-sourced report"),
        Milestone(30, "First closed-won OR clear blocker isolation",
                  "Sales Director + Partner Sales lead",
                  "Win/Loss writeup"),
    ]
    if motion == "channel_led":
        base.append(Milestone(
            20, "Partner-led demo without our SE present (validation)",
            "Partner Sales lead", "Recording + scorecard"))
    if tier == "OEM":
        base.append(Milestone(
            25, "First end-customer Tier-2 support ticket through joint runbook",
            "Support both sides", "Ticket resolution timeline"))
    return base


def _mid_quarter_checkpoint(tier: str, motion: str, pipeline_floor: float) -> list[str]:
    return [
        f"Day 45: pipeline sourced ≥ 50% of 90-day floor (${pipeline_floor * 0.5:,.0f})",
        f"Day 45: at least 1 closed-won OR named blocker with owner + remediation date",
        f"Day 45: certified rep count maintained at signed-agreement level",
        f"Day 45: ROE working — no channel-conflict escalations OR all resolved at named-human level",
        f"Day 45: kill-criteria trigger review — if any, escalate to partnership committee NOW",
    ]


def _success_criteria(tier: str, motion: str, pipeline_floor: float, deals_floor: int) -> list[str]:
    base = [
        f"Pipeline-sourced through partner ≥ ${pipeline_floor:,.0f} (validated by both sides)",
        f"Deals closed-won through partner ≥ {deals_floor}",
        f"Joint win/loss doc covering all material deals (closed-won AND closed-lost)",
        f"Certified rep count ≥ partner-agreement level",
        f"Channel-conflict log: zero unresolved escalations",
    ]
    if tier == "OEM":
        base.append("End-customer NPS via the OEM at or above corporate floor")
        base.append("Support SLA breach rate ≤ 5% of tickets")
    if tier == "STRATEGIC":
        base.append("Exec sponsor pair active (both sides — verify before quarter close)")
        base.append("Executive QBR completed with signed-off next-quarter pipeline floor")
    if motion == "channel_led":
        base.append("≥ 50% of closed-won were partner-led (not just partner-influenced)")
    if motion == "white_label":
        base.append("Embedded volume hit minimum threshold; no brand-bleed incidents")
    base.append("Decision: continue / re-tier / unwind, with named human accountable")
    return base


def plan_gtm(gtm: dict, profile_name: str = "saas") -> GtmPlan:
    if profile_name not in PROFILES:
        raise ValueError(f"Unknown profile '{profile_name}'. Choose from {list(PROFILES)}.")
    profile = PROFILES[profile_name]

    errs = _validate(gtm)
    plan = GtmPlan(
        partner_name=str(gtm.get("partner_name", "UNSPECIFIED")),
        profile=profile_name,
        partner_tier=(gtm.get("partner_tier") or "").upper(),
        sales_motion=(gtm.get("sales_motion") or "").lower(),
        target_segments=list(gtm.get("target_segments", []) or []),
        joint_value_proposition=str(gtm.get("joint_value_proposition", "")),
        validation_errors=errs,
    )
    if errs:
        return plan

    tier = plan.partner_tier
    motion = plan.sales_motion
    deal_avg = float(gtm.get("deal_avg_size_usd", 0.0))

    plan.target_account_count = profile["target_accounts"].get(tier, 0)
    plan.mdf_allocation_usd = float(profile["mdf_default"].get(tier, 0))
    pipe_multiple = profile["pipeline_floor_multiple"].get(tier, 0)
    plan.pipeline_floor_usd = deal_avg * pipe_multiple
    plan.deals_closed_floor = profile["deals_closed_floor"].get(tier, 0)

    plan.pre_launch = _pre_launch_milestones(tier, motion)
    plan.launch = _launch_milestones(tier, motion)
    plan.mid_quarter_checkpoint = _mid_quarter_checkpoint(tier, motion, plan.pipeline_floor_usd)
    plan.success_criteria_90d = _success_criteria(
        tier, motion, plan.pipeline_floor_usd, plan.deals_closed_floor
    )

    horizon = int(gtm.get("commitment_horizon_months", 12) or 12)
    if horizon < 12:
        plan.warnings.append(
            f"commitment_horizon_months={horizon} < 12: partner programs rarely produce "
            "signal in less than a full sales cycle. Consider extending or downgrading tier."
        )
    if tier == "STRATEGIC" and horizon < 24:
        plan.warnings.append(
            "STRATEGIC tier with sub-24-month horizon is structurally inconsistent; "
            "either commit multi-year or re-tier."
        )
    if deal_avg <= 0:
        plan.warnings.append(
            "deal_avg_size_usd not provided or 0 — pipeline floor cannot be computed. "
            "Re-run with a real number from your closed-won data."
        )

    return plan


def _render_human(p: GtmPlan) -> str:
    lines = []
    lines.append(f"Joint GTM Plan: {p.partner_name}")
    lines.append(f"Profile: {p.profile} ; Tier: {p.partner_tier} ; Motion: {p.sales_motion}")
    if p.validation_errors:
        lines.append("")
        lines.append("VALIDATION ERRORS (plan not generated):")
        for e in p.validation_errors:
            lines.append(f"  ! {e}")
        return "\n".join(lines)
    lines.append("")
    lines.append(f"Target segments: {'; '.join(p.target_segments)}")
    lines.append(f"Joint value prop: {p.joint_value_proposition}")
    lines.append("")
    lines.append(f"MDF allocation: ${p.mdf_allocation_usd:,.0f}")
    lines.append(f"Target accounts: {p.target_account_count}")
    lines.append(f"90-day pipeline floor: ${p.pipeline_floor_usd:,.0f}")
    lines.append(f"90-day closed-won floor: {p.deals_closed_floor}")
    lines.append("")
    lines.append("Pre-launch milestones (day -30 to 0):")
    for m in p.pre_launch:
        lines.append(f"  Day {m.day:+4d}  {m.name}")
        lines.append(f"            owner: {m.owner}")
        lines.append(f"            deliverable: {m.deliverable}")
    lines.append("")
    lines.append("Launch milestones (day 0 to 30):")
    for m in p.launch:
        lines.append(f"  Day {m.day:+4d}  {m.name}")
        lines.append(f"            owner: {m.owner}")
        lines.append(f"            deliverable: {m.deliverable}")
    lines.append("")
    lines.append("Mid-quarter checkpoint (day 45):")
    for c in p.mid_quarter_checkpoint:
        lines.append(f"  - {c}")
    lines.append("")
    lines.append("90-day success criteria:")
    for s in p.success_criteria_90d:
        lines.append(f"  - {s}")
    if p.warnings:
        lines.append("")
        lines.append("Warnings:")
        for w in p.warnings:
            lines.append(f"  ! {w}")
    return "\n".join(lines)


def _to_jsonable(p: GtmPlan) -> dict:
    return asdict(p)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Generate a 90-day joint GTM plan for a signed partner.",
    )
    parser.add_argument("--input", help="Path to JSON GTM context")
    parser.add_argument("--profile", default="saas", choices=list(PROFILES))
    parser.add_argument("--output", default="human", choices=["human", "json", "markdown"])
    parser.add_argument("--sample", action="store_true", help="Use embedded sample GTM context")
    args = parser.parse_args(argv)

    if args.sample or not args.input:
        gtm = SAMPLE_GTM
    else:
        with open(args.input) as f:
            gtm = json.load(f)

    plan = plan_gtm(gtm, args.profile)
    if args.output == "json":
        print(json.dumps(_to_jsonable(plan), indent=2))
    else:
        if args.output == "markdown":
            print("# Joint GTM Plan\n")
        print(_render_human(plan))
    return 0 if not plan.validation_errors else 0
    # Note: validation errors print to stdout; exit 0 so pipelines can capture them.


if __name__ == "__main__":
    sys.exit(main())
