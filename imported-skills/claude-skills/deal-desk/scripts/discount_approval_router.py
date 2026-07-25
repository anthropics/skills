#!/usr/bin/env python3
"""discount_approval_router.py - Route a discount request to the right human(s).

Stdlib-only. Outputs the NAMED APPROVER CHAIN, the hop where this deal lands,
and an estimated approval-cycle in business days. The skill never says "approved" —
only "routes to <person>".

Default policy bands (industry-customary, can be overridden in input JSON):
   0% -  15%   AE-approved
  15% -  25%   Sales Manager
  25% -  35%   Director of Sales
  35% -  50%   VP Sales
  50% +        CFO / CRO

Deal-size and tier modifiers nudge the chain (e.g. enterprise deal > $500K ARR
ALWAYS requires VP review even at 10% discount; SMB deal < $25K ARR may stop
one hop earlier for speed).

Usage:
    python discount_approval_router.py --sample
    python discount_approval_router.py --input deal.json --profile saas
    python discount_approval_router.py --input deal.json --output json
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, asdict, field
from typing import Any


SAMPLE_INPUT = {
    "deal_id": "ACME-2026-Q2-117",
    "discount_pct": 32.0,
    "deal_size_arr": 240000,
    "customer_tier": "enterprise",
    "policy_thresholds": None,  # use defaults
}


DEFAULT_BANDS = [
    {"max_pct": 15.0, "approver": "AE",                 "days": 0},
    {"max_pct": 25.0, "approver": "Sales Manager",      "days": 1},
    {"max_pct": 35.0, "approver": "Director of Sales",  "days": 2},
    {"max_pct": 50.0, "approver": "VP Sales",           "days": 3},
    {"max_pct": 100.1, "approver": "CFO + CRO",         "days": 5},
]


PROFILES: dict[str, dict[str, Any]] = {
    "saas": {
        "bands": DEFAULT_BANDS,
        "enterprise_floor_approver": "VP Sales",
        "enterprise_floor_arr": 500000,
        "smb_fast_lane_arr": 25000,
    },
    "enterprise-software": {
        # Larger ACVs absorb deeper discounts; bands shift up
        "bands": [
            {"max_pct": 20.0, "approver": "AE",                 "days": 0},
            {"max_pct": 30.0, "approver": "Sales Manager",      "days": 1},
            {"max_pct": 40.0, "approver": "Director of Sales",  "days": 2},
            {"max_pct": 55.0, "approver": "VP Sales",           "days": 4},
            {"max_pct": 100.1, "approver": "CFO + CRO",         "days": 7},
        ],
        "enterprise_floor_approver": "VP Sales",
        "enterprise_floor_arr": 1000000,
        "smb_fast_lane_arr": 50000,
    },
    "services": {
        # Margin-thin: even small discounts go up the chain fast
        "bands": [
            {"max_pct": 5.0,  "approver": "AE",                 "days": 0},
            {"max_pct": 12.0, "approver": "Sales Manager",      "days": 1},
            {"max_pct": 20.0, "approver": "Director of Sales",  "days": 2},
            {"max_pct": 30.0, "approver": "VP Services",        "days": 3},
            {"max_pct": 100.1, "approver": "CFO + COO",         "days": 5},
        ],
        "enterprise_floor_approver": "VP Services",
        "enterprise_floor_arr": 250000,
        "smb_fast_lane_arr": 10000,
    },
    "marketplace": {
        # Take-rate is the lever; explicit discounts are rare and tightly capped
        "bands": [
            {"max_pct": 3.0,  "approver": "AE",                 "days": 0},
            {"max_pct": 8.0,  "approver": "Sales Manager",      "days": 1},
            {"max_pct": 15.0, "approver": "Director of Sales",  "days": 2},
            {"max_pct": 25.0, "approver": "VP Sales",           "days": 3},
            {"max_pct": 100.1, "approver": "CFO + CRO",         "days": 7},
        ],
        "enterprise_floor_approver": "VP Sales",
        "enterprise_floor_arr": 500000,
        "smb_fast_lane_arr": 15000,
    },
}


@dataclass
class RoutingResult:
    deal_id: str
    profile: str
    discount_pct: float
    deal_size_arr: float
    customer_tier: str
    landing_approver: str
    approver_chain: list[str] = field(default_factory=list)
    estimated_cycle_days: int = 0
    modifiers_applied: list[str] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)


def _bands_for(deal: dict, profile: dict) -> list[dict]:
    """Allow caller to override via deal.policy_thresholds; else use profile."""
    custom = deal.get("policy_thresholds")
    if custom:
        # Expect list of {max_pct, approver, days} dicts; light validation
        out = []
        for b in custom:
            out.append({
                "max_pct": float(b["max_pct"]),
                "approver": str(b["approver"]),
                "days": int(b.get("days", 2)),
            })
        return sorted(out, key=lambda x: x["max_pct"])
    return profile["bands"]


def route_discount(deal: dict, profile_name: str = "saas") -> RoutingResult:
    if profile_name not in PROFILES:
        raise ValueError(f"Unknown profile '{profile_name}'. Choose from {list(PROFILES)}.")
    profile = PROFILES[profile_name]
    bands = _bands_for(deal, profile)

    pct = float(deal.get("discount_pct", 0.0))
    arr = float(deal.get("deal_size_arr", 0.0))
    tier = (deal.get("customer_tier") or "mid").lower()

    # Find the landing band
    landing = bands[-1]
    for b in bands:
        if pct <= b["max_pct"]:
            landing = b
            break

    chain: list[str] = []
    days = 0
    for b in bands:
        chain.append(b["approver"])
        days += b["days"]
        if b is landing:
            break

    modifiers: list[str] = []

    # Enterprise floor: large ARR forces VP-level review even on small discounts
    if tier == "enterprise" and arr >= profile["enterprise_floor_arr"]:
        floor = profile["enterprise_floor_approver"]
        if floor not in chain:
            # Insert before any role above it; simplest is append + dedupe
            chain.append(floor)
            modifiers.append(
                f"enterprise floor: ARR ${arr:,.0f} >= ${profile['enterprise_floor_arr']:,} "
                f"forces {floor} review"
            )
            days += 2

    # SMB fast-lane: small deals can stop one hop early IF discount <= second-band cap
    if (
        tier == "smb"
        and arr <= profile["smb_fast_lane_arr"]
        and len(chain) > 2
        and pct <= bands[1]["max_pct"]
    ):
        dropped = chain.pop()
        modifiers.append(
            f"SMB fast-lane: ARR ${arr:,.0f} <= ${profile['smb_fast_lane_arr']:,} "
            f"drops {dropped} from chain"
        )
        days = max(0, days - 1)

    # Dedup chain while preserving order
    seen: set[str] = set()
    ordered = []
    for a in chain:
        if a not in seen:
            ordered.append(a)
            seen.add(a)
    chain = ordered

    notes = [
        "This is a routing recommendation. The skill does NOT approve.",
        f"Discount {pct:.1f}% landed in the '{landing['approver']}' band "
        f"(<= {landing['max_pct']:.1f}%).",
    ]
    if pct > 50.0:
        notes.append("Discount > 50%: CFO/CRO MUST sign and Finance should re-run unit economics.")

    return RoutingResult(
        deal_id=str(deal.get("deal_id", "UNSPECIFIED")),
        profile=profile_name,
        discount_pct=pct,
        deal_size_arr=arr,
        customer_tier=tier,
        landing_approver=landing["approver"],
        approver_chain=chain,
        estimated_cycle_days=days,
        modifiers_applied=modifiers,
        notes=notes,
    )


def _render_human(r: RoutingResult) -> str:
    lines = []
    lines.append(f"Discount Routing: {r.deal_id}")
    lines.append(f"Profile: {r.profile}")
    lines.append(f"Discount: {r.discount_pct:.1f}%   ARR: ${r.deal_size_arr:,.0f}   Tier: {r.customer_tier}")
    lines.append("")
    lines.append("Approver chain (hops in order):")
    for i, a in enumerate(r.approver_chain, start=1):
        marker = "  <-- discount lands here" if a == r.landing_approver else ""
        lines.append(f"  {i}. {a}{marker}")
    lines.append("")
    lines.append(f"Estimated approval cycle: {r.estimated_cycle_days} business day(s)")
    if r.modifiers_applied:
        lines.append("")
        lines.append("Modifiers applied:")
        for m in r.modifiers_applied:
            lines.append(f"  * {m}")
    lines.append("")
    for n in r.notes:
        lines.append(f"note: {n}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Route a discount request to the right named approver(s).",
    )
    parser.add_argument("--input", help="Path to JSON request")
    parser.add_argument("--profile", default="saas", choices=list(PROFILES))
    parser.add_argument("--output", default="human", choices=["human", "json"])
    parser.add_argument("--sample", action="store_true")
    args = parser.parse_args(argv)

    if args.sample or not args.input:
        deal = SAMPLE_INPUT
    else:
        with open(args.input) as f:
            deal = json.load(f)

    result = route_discount(deal, args.profile)
    if args.output == "json":
        print(json.dumps(asdict(result), indent=2))
    else:
        print(_render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
