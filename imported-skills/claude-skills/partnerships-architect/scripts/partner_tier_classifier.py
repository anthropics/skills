#!/usr/bin/env python3
"""partner_tier_classifier.py - Classify a prospective partner into 1 of 5 tiers.

Stdlib-only. Deterministic logic with hard floors per tier. NEVER auto-signs anything;
output is a tier verdict + rationale + kill criteria, routed to a human committee.

The 5 tiers:
  REFERRAL          - informal intro, no joint commitment, small finder's fee
  RESELLER          - transactional resale with margin, basic certification
  OEM               - white-label / embedded, integration + support commitment
  SI_CONSULTING     - services attach, customer-owned-by-partner
  STRATEGIC         - multi-year, co-investment, dedicated resources both sides

Tier floors (hard requirements — failing a floor caps the tier):
  REFERRAL          - none (default fallback)
  RESELLER          - end_customer_relationships_pct >= 40 AND sales_team_size >= 3
  OEM               - end_customer_relationships_pct >= 60 AND certification_completion AND
                       commitments.dedicated_resources >= 2
  SI_CONSULTING     - end_customer_relationships_pct >= 50 AND sales_team_size >= 5 AND
                       partner_type in {si_consultant}
  STRATEGIC         - named_accounts_sourced_count >= 5 AND multi-year-commit (>=24mo
                       horizon implied by commitments) AND dedicated_resources >= 3 AND
                       joint_marketing_spend >= 50000

Industry profiles (`--profile`) tune the thresholds:
  saas               - default; the floors above
  api                - bias toward technology/OEM; relax sales_team for OEM
  enterprise-software - higher SI bar (8 sales reps)
  marketplace        - higher referral acceptance, lower reseller bar
  hardware           - higher OEM bar (dedicated_resources 4)

Usage:
    python partner_tier_classifier.py --sample
    python partner_tier_classifier.py --input partner.json --profile saas
    python partner_tier_classifier.py --input partner.json --output json
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, field, asdict
from typing import Any


SAMPLE_PARTNER = {
    "partner_name": "Northstar Consulting",
    "partner_type": "si_consultant",
    "independent_demand_evidence": {
        "named_accounts_sourced_count": 7,
        "end_customer_relationships_pct": 65,
        "sales_team_size": 8,
    },
    "strategic_value": {
        "geo_coverage": "EMEA + LATAM",
        "product_complement": "implementation services for our platform",
        "brand_lift": "mid",
        "channel_economics_advantage": "lower CAC in regulated verticals",
    },
    "commitments": {
        "joint_marketing_spend": 75000,
        "dedicated_resources": 4,
        "certification_completion": True,
        "sales_targets": "12 deals in 12 months",
    },
}


VALID_PARTNER_TYPES = (
    "referral", "reseller", "oem", "si_consultant", "technology", "strategic_alliance",
)


PROFILES: dict[str, dict[str, Any]] = {
    "saas": {
        "reseller_floor_ecr": 40,
        "reseller_floor_sales_team": 3,
        "oem_floor_ecr": 60,
        "oem_floor_dedicated": 2,
        "si_floor_ecr": 50,
        "si_floor_sales_team": 5,
        "strategic_floor_sourced": 5,
        "strategic_floor_dedicated": 3,
        "strategic_floor_mdf": 50000,
    },
    "api": {
        "reseller_floor_ecr": 35,
        "reseller_floor_sales_team": 2,
        "oem_floor_ecr": 50,
        "oem_floor_dedicated": 2,
        "si_floor_ecr": 50,
        "si_floor_sales_team": 5,
        "strategic_floor_sourced": 4,
        "strategic_floor_dedicated": 3,
        "strategic_floor_mdf": 40000,
    },
    "enterprise-software": {
        "reseller_floor_ecr": 50,
        "reseller_floor_sales_team": 5,
        "oem_floor_ecr": 65,
        "oem_floor_dedicated": 3,
        "si_floor_ecr": 55,
        "si_floor_sales_team": 8,
        "strategic_floor_sourced": 6,
        "strategic_floor_dedicated": 4,
        "strategic_floor_mdf": 75000,
    },
    "marketplace": {
        "reseller_floor_ecr": 30,
        "reseller_floor_sales_team": 2,
        "oem_floor_ecr": 50,
        "oem_floor_dedicated": 2,
        "si_floor_ecr": 45,
        "si_floor_sales_team": 4,
        "strategic_floor_sourced": 4,
        "strategic_floor_dedicated": 2,
        "strategic_floor_mdf": 30000,
    },
    "hardware": {
        "reseller_floor_ecr": 45,
        "reseller_floor_sales_team": 4,
        "oem_floor_ecr": 70,
        "oem_floor_dedicated": 4,
        "si_floor_ecr": 55,
        "si_floor_sales_team": 6,
        "strategic_floor_sourced": 6,
        "strategic_floor_dedicated": 4,
        "strategic_floor_mdf": 100000,
    },
}


# Kill criteria templates per tier — these are placed into the partnership contract
# so the unwind is mechanical, not a 2-year legal fight.
KILL_CRITERIA: dict[str, list[str]] = {
    "REFERRAL": [
        "No qualified intros in 2 consecutive quarters -> auto-sunset, no notice",
        "Any misrepresentation of relationship as 'partner' externally -> immediate termination",
    ],
    "RESELLER": [
        "Less than 25% of agreed annual sales target hit in any quarter -> 90-day cure",
        "Two consecutive quarters under cure -> tier demotion to REFERRAL or termination",
        "Certification lapses for >60 days -> resale rights suspended",
    ],
    "OEM": [
        "End-customer NPS via the OEM falls below corporate floor -> joint remediation plan",
        "Less than 50% of agreed embedded volume in 2 consecutive quarters -> cure or unwind",
        "Support response SLA breach >5% per quarter -> co-funded customer-success review",
    ],
    "SI_CONSULTING": [
        "Less than 60% of agreed certified resources maintained -> 60-day cure",
        "Customer-attributed delivery failures above named threshold -> joint root-cause + remediation",
        "Loss of practice lead (named person) -> 90-day re-qualification of tier",
    ],
    "STRATEGIC": [
        "Less than 70% of named pipeline floor in 2 consecutive quarters -> joint exec review",
        "Failure of the named exec sponsor on either side -> 90-day re-validation of alliance",
        "Material change of control on either side -> automatic 6-month evaluation period",
        "Loss of integration / technical interop for >30 days -> alliance pause",
    ],
}


@dataclass
class TierScore:
    tier: str
    raw_score: float
    floors_passed: bool
    floors_failed: list[str]
    rationale: str


@dataclass
class ClassificationVerdict:
    partner_name: str
    profile: str
    tier_assigned: str
    composite_rationale: str
    floors_failed_for_higher_tiers: list[str] = field(default_factory=list)
    tier_scores: list[TierScore] = field(default_factory=list)
    kill_criteria: list[str] = field(default_factory=list)
    next_steps: list[str] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)


def _clamp(x: float, lo: float = 0.0, hi: float = 100.0) -> float:
    return max(lo, min(hi, x))


def _check_reseller_floors(partner: dict, profile: dict) -> tuple[bool, list[str]]:
    ide = partner.get("independent_demand_evidence", {}) or {}
    ecr = float(ide.get("end_customer_relationships_pct", 0))
    sts = int(ide.get("sales_team_size", 0))
    fails: list[str] = []
    if ecr < profile["reseller_floor_ecr"]:
        fails.append(
            f"RESELLER floor: end_customer_relationships_pct {ecr:.0f}% < "
            f"{profile['reseller_floor_ecr']}%"
        )
    if sts < profile["reseller_floor_sales_team"]:
        fails.append(
            f"RESELLER floor: sales_team_size {sts} < "
            f"{profile['reseller_floor_sales_team']}"
        )
    return (len(fails) == 0, fails)


def _check_oem_floors(partner: dict, profile: dict) -> tuple[bool, list[str]]:
    ide = partner.get("independent_demand_evidence", {}) or {}
    com = partner.get("commitments", {}) or {}
    ecr = float(ide.get("end_customer_relationships_pct", 0))
    dr = int(com.get("dedicated_resources", 0))
    cert = bool(com.get("certification_completion", False))
    fails: list[str] = []
    if ecr < profile["oem_floor_ecr"]:
        fails.append(
            f"OEM floor: end_customer_relationships_pct {ecr:.0f}% < "
            f"{profile['oem_floor_ecr']}%"
        )
    if dr < profile["oem_floor_dedicated"]:
        fails.append(
            f"OEM floor: dedicated_resources {dr} < {profile['oem_floor_dedicated']}"
        )
    if not cert:
        fails.append("OEM floor: certification_completion is False")
    return (len(fails) == 0, fails)


def _check_si_floors(partner: dict, profile: dict) -> tuple[bool, list[str]]:
    ide = partner.get("independent_demand_evidence", {}) or {}
    ecr = float(ide.get("end_customer_relationships_pct", 0))
    sts = int(ide.get("sales_team_size", 0))
    ptype = (partner.get("partner_type") or "").lower()
    fails: list[str] = []
    if ecr < profile["si_floor_ecr"]:
        fails.append(
            f"SI_CONSULTING floor: end_customer_relationships_pct {ecr:.0f}% < "
            f"{profile['si_floor_ecr']}%"
        )
    if sts < profile["si_floor_sales_team"]:
        fails.append(
            f"SI_CONSULTING floor: sales_team_size {sts} < "
            f"{profile['si_floor_sales_team']}"
        )
    if ptype != "si_consultant":
        fails.append(
            f"SI_CONSULTING floor: partner_type is '{ptype}', expected 'si_consultant'"
        )
    return (len(fails) == 0, fails)


def _check_strategic_floors(partner: dict, profile: dict) -> tuple[bool, list[str]]:
    ide = partner.get("independent_demand_evidence", {}) or {}
    com = partner.get("commitments", {}) or {}
    sourced = int(ide.get("named_accounts_sourced_count", 0))
    dr = int(com.get("dedicated_resources", 0))
    mdf = float(com.get("joint_marketing_spend", 0))
    targets = (com.get("sales_targets") or "").lower()
    fails: list[str] = []
    if sourced < profile["strategic_floor_sourced"]:
        fails.append(
            f"STRATEGIC floor: named_accounts_sourced_count {sourced} < "
            f"{profile['strategic_floor_sourced']}"
        )
    if dr < profile["strategic_floor_dedicated"]:
        fails.append(
            f"STRATEGIC floor: dedicated_resources {dr} < "
            f"{profile['strategic_floor_dedicated']}"
        )
    if mdf < profile["strategic_floor_mdf"]:
        fails.append(
            f"STRATEGIC floor: joint_marketing_spend {mdf:.0f} < "
            f"{profile['strategic_floor_mdf']}"
        )
    # Multi-year heuristic: sales_targets mentions "12 months" or longer; or commitment
    # text references multi-year / 24 / 36 months.
    multi_year_signal = any(
        s in targets for s in ("12 months", "24 months", "36 months", "multi-year", "multi year")
    )
    if not multi_year_signal:
        fails.append(
            "STRATEGIC floor: no multi-year commitment signal in sales_targets text"
        )
    return (len(fails) == 0, fails)


def _strategic_raw_score(partner: dict, profile: dict) -> float:
    ide = partner.get("independent_demand_evidence", {}) or {}
    com = partner.get("commitments", {}) or {}
    sv = partner.get("strategic_value", {}) or {}
    score = 0.0
    # Sourced accounts: 0..40 points (cap at 10 sourced)
    score += min(40.0, ide.get("named_accounts_sourced_count", 0) * 4.0)
    # Dedicated resources: 0..20 points (cap at 5)
    score += min(20.0, com.get("dedicated_resources", 0) * 4.0)
    # MDF: 0..20 points (cap at 100k)
    score += min(20.0, com.get("joint_marketing_spend", 0) / 5000.0)
    # Strategic value flags: 5 points each
    for key in ("geo_coverage", "product_complement", "brand_lift", "channel_economics_advantage"):
        if sv.get(key):
            score += 5.0
    return _clamp(score)


def _oem_raw_score(partner: dict, profile: dict) -> float:
    ide = partner.get("independent_demand_evidence", {}) or {}
    com = partner.get("commitments", {}) or {}
    score = 0.0
    score += min(40.0, ide.get("end_customer_relationships_pct", 0) * 0.6)
    score += min(20.0, com.get("dedicated_resources", 0) * 5.0)
    score += 20.0 if com.get("certification_completion") else 0.0
    score += min(20.0, ide.get("named_accounts_sourced_count", 0) * 3.0)
    return _clamp(score)


def _si_raw_score(partner: dict, profile: dict) -> float:
    ide = partner.get("independent_demand_evidence", {}) or {}
    com = partner.get("commitments", {}) or {}
    score = 0.0
    score += min(35.0, ide.get("end_customer_relationships_pct", 0) * 0.5)
    score += min(25.0, ide.get("sales_team_size", 0) * 3.0)
    score += 15.0 if com.get("certification_completion") else 0.0
    score += min(25.0, com.get("dedicated_resources", 0) * 5.0)
    return _clamp(score)


def _reseller_raw_score(partner: dict, profile: dict) -> float:
    ide = partner.get("independent_demand_evidence", {}) or {}
    score = 0.0
    score += min(50.0, ide.get("end_customer_relationships_pct", 0) * 0.8)
    score += min(40.0, ide.get("sales_team_size", 0) * 5.0)
    score += min(10.0, ide.get("named_accounts_sourced_count", 0) * 2.0)
    return _clamp(score)


def _referral_raw_score(partner: dict, profile: dict) -> float:
    # Referral always passes; raw score is just "do they have any evidence of intent"
    ide = partner.get("independent_demand_evidence", {}) or {}
    score = 30.0  # baseline for showing up
    score += min(40.0, ide.get("named_accounts_sourced_count", 0) * 6.0)
    score += min(30.0, ide.get("end_customer_relationships_pct", 0) * 0.3)
    return _clamp(score)


def classify(partner: dict, profile_name: str = "saas") -> ClassificationVerdict:
    if profile_name not in PROFILES:
        raise ValueError(f"Unknown profile '{profile_name}'. Choose from {list(PROFILES)}.")
    profile = PROFILES[profile_name]

    ptype = (partner.get("partner_type") or "").lower()
    warnings: list[str] = []
    if ptype not in VALID_PARTNER_TYPES:
        warnings.append(
            f"partner_type '{ptype}' is not one of {VALID_PARTNER_TYPES}; "
            "classification continues but verify input"
        )

    # Compute raw scores for each tier
    s_strategic = _strategic_raw_score(partner, profile)
    s_oem = _oem_raw_score(partner, profile)
    s_si = _si_raw_score(partner, profile)
    s_reseller = _reseller_raw_score(partner, profile)
    s_referral = _referral_raw_score(partner, profile)

    # Floor checks
    p_reseller, f_reseller = _check_reseller_floors(partner, profile)
    p_oem, f_oem = _check_oem_floors(partner, profile)
    p_si, f_si = _check_si_floors(partner, profile)
    p_strategic, f_strategic = _check_strategic_floors(partner, profile)

    scores = [
        TierScore("STRATEGIC", s_strategic, p_strategic, f_strategic,
                  f"raw={s_strategic:.1f}/100 ; floors={'PASS' if p_strategic else 'FAIL'}"),
        TierScore("OEM", s_oem, p_oem, f_oem,
                  f"raw={s_oem:.1f}/100 ; floors={'PASS' if p_oem else 'FAIL'}"),
        TierScore("SI_CONSULTING", s_si, p_si, f_si,
                  f"raw={s_si:.1f}/100 ; floors={'PASS' if p_si else 'FAIL'}"),
        TierScore("RESELLER", s_reseller, p_reseller, f_reseller,
                  f"raw={s_reseller:.1f}/100 ; floors={'PASS' if p_reseller else 'FAIL'}"),
        TierScore("REFERRAL", s_referral, True, [],
                  f"raw={s_referral:.1f}/100 ; floors=PASS (default)"),
    ]

    # Assign highest tier that PASSES floors AND has raw_score >= 60.
    assigned = "REFERRAL"
    rationale = "Default fallback tier (no higher floors passed)"
    floors_blocking: list[str] = []
    tier_order = ["STRATEGIC", "OEM", "SI_CONSULTING", "RESELLER", "REFERRAL"]
    for tier_name in tier_order:
        ts = next(t for t in scores if t.tier == tier_name)
        if ts.floors_passed and (tier_name == "REFERRAL" or ts.raw_score >= 60.0):
            assigned = tier_name
            rationale = (
                f"Assigned {tier_name}: raw score {ts.raw_score:.1f}/100, all floors passed."
            )
            break
        if not ts.floors_passed:
            floors_blocking.extend(ts.floors_failed)
        elif ts.raw_score < 60.0:
            floors_blocking.append(
                f"{tier_name}: raw score {ts.raw_score:.1f}/100 below 60 minimum"
            )

    # Next steps depend on tier
    next_steps_map = {
        "REFERRAL": [
            "Document the referral arrangement (one-page MOU, no exclusivity)",
            "Define finder's fee % (typical 5-10% of first-year ARR)",
            "Set 2-quarter review with auto-sunset trigger",
        ],
        "RESELLER": [
            "Run scripts/joint_gtm_planner.py with sales_motion='co_sell' or 'channel_led'",
            "Run scripts/revshare_modeler.py to size resale margin (typical 20-35%)",
            "Draft certification curriculum and timeline",
            "Lock kill criteria in contract before signing",
        ],
        "OEM": [
            "Run scripts/joint_gtm_planner.py with sales_motion='white_label'",
            "Run scripts/revshare_modeler.py with deeper revshare band (typical 40-55%)",
            "Validate support model — who answers Tier-2 calls?",
            "Lock IP / integration / brand-use terms in contract",
            "Lock kill criteria including support SLA in contract",
        ],
        "SI_CONSULTING": [
            "Run scripts/joint_gtm_planner.py with sales_motion='co_sell'",
            "Run scripts/revshare_modeler.py (typical 15-25% on product, 0% on services)",
            "Define certified-practice-lead role and named individual",
            "Lock kill criteria around certification headcount",
        ],
        "STRATEGIC": [
            "Verify with `c-level-advisor/ma-playbook` whether this should be acquisition not partnership",
            "Run scripts/joint_gtm_planner.py with sales_motion='channel_led' or 'co_sell'",
            "Run scripts/revshare_modeler.py with strategic-tier band",
            "Negotiate executive-sponsor pairing (named individual each side)",
            "Lock kill criteria including exec-sponsor-departure trigger",
        ],
    }

    return ClassificationVerdict(
        partner_name=str(partner.get("partner_name", "UNSPECIFIED")),
        profile=profile_name,
        tier_assigned=assigned,
        composite_rationale=rationale,
        floors_failed_for_higher_tiers=floors_blocking,
        tier_scores=scores,
        kill_criteria=KILL_CRITERIA.get(assigned, []),
        next_steps=next_steps_map.get(assigned, []),
        warnings=warnings,
    )


def _render_human(v: ClassificationVerdict) -> str:
    lines = []
    lines.append(f"Partner Classification: {v.partner_name}")
    lines.append(f"Profile: {v.profile}")
    lines.append(f"Tier Assigned: {v.tier_assigned}")
    lines.append("")
    lines.append(v.composite_rationale)
    lines.append("")
    lines.append("Tier scoring detail (high to low):")
    for ts in v.tier_scores:
        floor_status = "PASS" if ts.floors_passed else "FAIL"
        lines.append(f"  - {ts.tier:14s} raw={ts.raw_score:5.1f}/100 floors={floor_status}")
        if ts.floors_failed:
            for f in ts.floors_failed:
                lines.append(f"      x {f}")
    lines.append("")
    if v.floors_failed_for_higher_tiers:
        lines.append("Why not a higher tier:")
        for f in v.floors_failed_for_higher_tiers:
            lines.append(f"  - {f}")
        lines.append("")
    lines.append("Kill criteria (put these in the contract):")
    for k in v.kill_criteria:
        lines.append(f"  - {k}")
    lines.append("")
    lines.append("Next steps:")
    for n in v.next_steps:
        lines.append(f"  - {n}")
    if v.warnings:
        lines.append("")
        lines.append("Warnings:")
        for w in v.warnings:
            lines.append(f"  ! {w}")
    return "\n".join(lines)


def _to_jsonable(v: ClassificationVerdict) -> dict:
    return asdict(v)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Classify a prospective partner into REFERRAL / RESELLER / OEM / SI_CONSULTING / STRATEGIC tier.",
    )
    parser.add_argument("--input", help="Path to JSON partner intake")
    parser.add_argument("--profile", default="saas", choices=list(PROFILES))
    parser.add_argument("--output", default="human", choices=["human", "json", "markdown"])
    parser.add_argument("--sample", action="store_true", help="Use embedded sample partner")
    args = parser.parse_args(argv)

    if args.sample or not args.input:
        partner = SAMPLE_PARTNER
    else:
        with open(args.input) as f:
            partner = json.load(f)

    verdict = classify(partner, args.profile)
    if args.output == "json":
        print(json.dumps(_to_jsonable(verdict), indent=2))
    else:
        # human and markdown share the same body; markdown adds a header
        if args.output == "markdown":
            print(f"# Partner Tier Classification\n")
        print(_render_human(verdict))
    return 0


if __name__ == "__main__":
    sys.exit(main())
