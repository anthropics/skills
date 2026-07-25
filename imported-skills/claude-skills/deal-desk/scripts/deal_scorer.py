#!/usr/bin/env python3
"""deal_scorer.py - Score an inbound deal across 5 dimensions and route the verdict.

Stdlib-only. NEVER auto-approves. Output is always a numeric breakdown plus a verdict
(APPROVE / REVIEW / ESCALATE / DECLINE) and a NAMED HUMAN APPROVER chain.

The 5 dimensions (each 0-100, weighted into a composite):
  1. margin        - post-discount margin (fixed-COGS) vs target + margin-$ destroyed
  2. risk          - payment terms + redline count + customer tier
  3. strategic     - logo / reference / expansion / renewal value
  4. commercial    - is the discount within the profile policy band
  5. term shape    - multi-year + payment-up-front vs short, NET-60+ tail

Routing rule (intentionally conservative):
  - composite >= 80 and no CRITICAL signals -> APPROVE  (still names the approver)
  - composite 65-79                          -> REVIEW   (Deal Desk + Sales Director)
  - composite 50-64 or 1 CRITICAL            -> ESCALATE (VP Sales + CFO)
  - composite < 50 or 2+ CRITICAL            -> DECLINE  (CRO + CFO must sign off any override)

Usage:
    python deal_scorer.py --sample
    python deal_scorer.py --input deal.json --profile saas
    python deal_scorer.py --input deal.json --output json
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, field, asdict
from typing import Any


SAMPLE_DEAL = {
    "deal_id": "ACME-2026-Q2-117",
    "customer_name": "Acme Corp",
    "arr": 240000,
    "term_months": 24,
    "discount_pct": 28.0,
    "payment_terms_days": 60,
    "list_price": 333333,
    "gross_margin_pct": 78.0,
    "customer_tier": "enterprise",
    "strategic_value": {
        "logo": True,
        "reference": False,
        "expansion": True,
        "renewal": False,
    },
    "term_redlines": [
        "uncapped indemnity",
        "MFN pricing",
    ],
}


# Industry profiles tune the target margin floor, acceptable discount band,
# and payment-terms tolerance.
PROFILES: dict[str, dict[str, Any]] = {
    "saas": {
        "target_gross_margin": 75.0,
        "discount_band_pct": 25.0,
        "max_payment_terms_days": 30,
        "preferred_term_months": 24,
    },
    "enterprise-software": {
        "target_gross_margin": 70.0,
        "discount_band_pct": 35.0,
        "max_payment_terms_days": 45,
        "preferred_term_months": 36,
    },
    "services": {
        "target_gross_margin": 45.0,
        "discount_band_pct": 15.0,
        "max_payment_terms_days": 30,
        "preferred_term_months": 12,
    },
    "marketplace": {
        "target_gross_margin": 30.0,
        "discount_band_pct": 10.0,
        "max_payment_terms_days": 14,
        "preferred_term_months": 12,
    },
}


# Routing chain by composite + signals. The skill NEVER says "approved" by itself;
# it names the human(s) who must sign.
APPROVER_CHAIN = {
    "APPROVE":  ["AE", "Deal Desk Analyst", "Sales Director"],
    "REVIEW":   ["AE", "Deal Desk Analyst", "Sales Director", "VP Sales"],
    "ESCALATE": ["AE", "Deal Desk Analyst", "Sales Director", "VP Sales", "CFO", "CRO"],
    "DECLINE":  ["AE", "Deal Desk Analyst", "VP Sales", "CFO", "CRO", "General Counsel"],
}


@dataclass
class DimensionScore:
    name: str
    score: float
    weight: float
    rationale: str


@dataclass
class DealScorecard:
    deal_id: str
    profile: str
    composite_score: float
    verdict: str
    approver_chain: list[str]
    dimensions: list[DimensionScore] = field(default_factory=list)
    critical_signals: list[str] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)


def _clamp(x: float, lo: float = 0.0, hi: float = 100.0) -> float:
    return max(lo, min(hi, x))


def score_margin(deal: dict, profile: dict) -> DimensionScore:
    """Effective margin after discount, compared to profile target.

    Math (fixed-COGS model — COGS does not shrink when you discount the price):
        Price P, gross margin G%  ->  COGS = (1 - G/100) * P, fixed.
        Discounted price = (1 - D/100) * P.
        Post-discount margin %:
            net_margin_pct = (G - D) / (100 - D) * 100
        Share of margin DOLLARS destroyed by the discount:
            margin_dollars_destroyed_pct = D / G * 100
        i.e. a 30% discount on an 80%-margin product leaves a 71.4% margin
        percentage but destroys 37.5% of the margin dollars — every discounted
        dollar comes straight out of margin, because the cost side is fixed.

    Score = min(position score, destruction score):
        - position: 100 if net_margin_pct >= target, sliding to 0 at
          (target - 30 pts)
        - destruction: 100 at 0% of margin dollars destroyed, sliding to 0 at
          50% destroyed (2 pts of score per 1% of margin dollars given up)
    The min() means a high starting margin cannot hide discount damage.
    """
    g = float(deal.get("gross_margin_pct", 0.0))
    d = float(deal.get("discount_pct", 0.0))
    target = profile["target_gross_margin"]

    if g <= 0.0 or d >= 100.0:
        rationale = (
            f"Gross margin {g:.1f}% with {d:.1f}% discount -> no margin left "
            f"(vs profile target {target:.1f}%)"
        )
        return DimensionScore("margin", 0.0, 0.30, rationale)

    net_margin = (g - d) / (100.0 - d) * 100.0
    margin_dollars_destroyed = (d / g) * 100.0

    delta = net_margin - target
    position_score = _clamp(100.0 + (delta / 30.0) * 100.0)
    destruction_score = _clamp(100.0 - 2.0 * margin_dollars_destroyed)
    score = min(position_score, destruction_score)

    rationale = (
        f"Gross margin {g:.1f}% with {d:.1f}% discount -> net margin {net_margin:.1f}% "
        f"vs profile target {target:.1f}% (delta {delta:+.1f} pts); "
        f"{margin_dollars_destroyed:.1f}% of margin dollars destroyed (fixed-COGS)"
    )
    return DimensionScore("margin", round(score, 1), 0.30, rationale)


def score_risk(deal: dict, profile: dict) -> DimensionScore:
    """Risk = payment terms shape + redline count + customer-tier offset."""
    payment_days = int(deal.get("payment_terms_days", 30))
    redlines = deal.get("term_redlines", []) or []
    tier = (deal.get("customer_tier") or "smb").lower()

    # Base score 100, deduct per risk factor.
    score = 100.0
    payment_max = profile["max_payment_terms_days"]
    if payment_days > payment_max:
        over = payment_days - payment_max
        score -= min(40.0, over * 0.8)  # NET-90 vs NET-30 = 48 days over = -38.4

    score -= min(40.0, len(redlines) * 12.0)  # each redline = -12

    # SMB tier on long terms is riskier than enterprise on same terms
    if tier == "smb" and payment_days > 30:
        score -= 10.0
    elif tier == "enterprise" and payment_days <= 45:
        score += 5.0  # enterprise tolerance bump

    score = _clamp(score)
    rationale = (
        f"NET-{payment_days} terms (profile max {payment_max}), "
        f"{len(redlines)} redline(s), tier={tier}"
    )
    return DimensionScore("risk", round(score, 1), 0.20, rationale)


def score_strategic(deal: dict, profile: dict) -> DimensionScore:
    """Strategic value from logo, reference, expansion, renewal flags."""
    sv = deal.get("strategic_value", {}) or {}
    weights = {"logo": 25, "reference": 20, "expansion": 30, "renewal": 25}
    earned = sum(w for k, w in weights.items() if sv.get(k))
    rationale = "Flags: " + ", ".join(k for k in weights if sv.get(k)) if earned else "No strategic flags set"
    return DimensionScore("strategic", float(earned), 0.15, rationale)


def score_commercial(deal: dict, profile: dict) -> DimensionScore:
    """Is the discount within the profile's policy band?"""
    d = float(deal.get("discount_pct", 0.0))
    band = profile["discount_band_pct"]
    if d <= band:
        # Within band, score linearly from 100 (no discount) to 80 (band edge)
        score = 100.0 - (d / band) * 20.0
        rationale = f"Discount {d:.1f}% within policy band <= {band:.1f}%"
    else:
        over = d - band
        # Drop 6 points per percentage over band, floor 0
        score = max(0.0, 80.0 - over * 6.0)
        rationale = f"Discount {d:.1f}% EXCEEDS policy band {band:.1f}% by {over:.1f} pts"
    return DimensionScore("commercial", round(score, 1), 0.20, rationale)


def score_term_shape(deal: dict, profile: dict) -> DimensionScore:
    """Term length vs preferred + payment up front."""
    term_months = int(deal.get("term_months", 12))
    preferred = profile["preferred_term_months"]
    payment_days = int(deal.get("payment_terms_days", 30))

    # Length component: 100 if >= preferred, sliding to 40 at half-preferred, floor 30
    if term_months >= preferred:
        length = 100.0
    elif term_months <= preferred / 2:
        length = 30.0
    else:
        length = 30.0 + ((term_months - preferred / 2) / (preferred / 2)) * 70.0

    # Payment component: NET-30 or shorter = 100, NET-60 = 70, NET-90+ = 40
    if payment_days <= 30:
        pay = 100.0
    elif payment_days <= 60:
        pay = 70.0
    elif payment_days <= 90:
        pay = 40.0
    else:
        pay = 20.0

    score = 0.6 * length + 0.4 * pay
    rationale = (
        f"{term_months}-mo term (preferred {preferred}), NET-{payment_days} payment "
        f"-> length={length:.0f}, payment={pay:.0f}"
    )
    return DimensionScore("term_shape", round(score, 1), 0.15, rationale)


def _detect_critical_signals(deal: dict, dims: list[DimensionScore]) -> list[str]:
    sigs: list[str] = []
    redlines = [r.lower() for r in deal.get("term_redlines", []) or []]
    critical_terms = (
        "uncapped indemnity",
        "uncapped liability",
        "mfn",
        "most-favored-nation",
        "perpetual license-back",
        "exclusivity",
    )
    for r in redlines:
        if any(ct in r for ct in critical_terms):
            sigs.append(f"critical redline: {r}")
    # margin dimension below 30 is a critical economic signal on any profile
    # (net margin deep below target, or >35% of margin dollars destroyed)
    for d in dims:
        if d.name == "margin" and d.score < 30.0:
            sigs.append(
                "margin critically impaired (deep below target or >35% of "
                "margin dollars destroyed)"
            )
        if d.name == "commercial" and d.score < 30.0:
            sigs.append("discount far outside policy band")
    return sigs


def _verdict(composite: float, criticals: list[str]) -> str:
    n_crit = len(criticals)
    if n_crit >= 2 or composite < 50.0:
        return "DECLINE"
    if n_crit == 1 or composite < 65.0:
        return "ESCALATE"
    if composite < 80.0:
        return "REVIEW"
    return "APPROVE"


def score_deal(deal: dict, profile_name: str = "saas") -> DealScorecard:
    if profile_name not in PROFILES:
        raise ValueError(f"Unknown profile '{profile_name}'. Choose from {list(PROFILES)}.")
    profile = PROFILES[profile_name]

    dims = [
        score_margin(deal, profile),
        score_risk(deal, profile),
        score_strategic(deal, profile),
        score_commercial(deal, profile),
        score_term_shape(deal, profile),
    ]
    composite = sum(d.score * d.weight for d in dims)
    criticals = _detect_critical_signals(deal, dims)
    verdict = _verdict(composite, criticals)

    notes = [
        "This skill does NOT auto-approve. The approver chain below is who must sign.",
        f"Composite is weighted: margin 30, risk 20, strategic 15, commercial 20, term 15.",
    ]
    if criticals:
        notes.append(f"{len(criticals)} critical signal(s) detected; cannot APPROVE.")

    return DealScorecard(
        deal_id=str(deal.get("deal_id", "UNSPECIFIED")),
        profile=profile_name,
        composite_score=round(composite, 1),
        verdict=verdict,
        approver_chain=APPROVER_CHAIN[verdict],
        dimensions=dims,
        critical_signals=criticals,
        notes=notes,
    )


def _render_human(card: DealScorecard) -> str:
    lines = []
    lines.append(f"Deal Scorecard: {card.deal_id}")
    lines.append(f"Profile: {card.profile}")
    lines.append(f"Composite Score: {card.composite_score}/100")
    lines.append(f"Verdict: {card.verdict}")
    lines.append("")
    lines.append("Dimension breakdown:")
    for d in card.dimensions:
        lines.append(f"  - {d.name:10s} {d.score:5.1f}  (weight {d.weight:.2f})")
        lines.append(f"      {d.rationale}")
    lines.append("")
    if card.critical_signals:
        lines.append("Critical signals:")
        for s in card.critical_signals:
            lines.append(f"  ! {s}")
        lines.append("")
    lines.append("Approver chain (named humans who must sign):")
    lines.append("  " + " -> ".join(card.approver_chain))
    lines.append("")
    for n in card.notes:
        lines.append(f"note: {n}")
    return "\n".join(lines)


def _to_jsonable(card: DealScorecard) -> dict:
    d = asdict(card)
    return d


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Score a deal across 5 dimensions and route to a named approver.",
    )
    parser.add_argument("--input", help="Path to JSON deal context")
    parser.add_argument("--profile", default="saas", choices=list(PROFILES))
    parser.add_argument("--output", default="human", choices=["human", "json"])
    parser.add_argument("--sample", action="store_true", help="Use embedded sample deal")
    args = parser.parse_args(argv)

    if args.sample or not args.input:
        deal = SAMPLE_DEAL
    else:
        with open(args.input) as f:
            deal = json.load(f)

    card = score_deal(deal, args.profile)
    if args.output == "json":
        print(json.dumps(_to_jsonable(card), indent=2))
    else:
        print(_render_human(card))
    return 0


if __name__ == "__main__":
    sys.exit(main())
