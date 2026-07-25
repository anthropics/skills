#!/usr/bin/env python3
"""revshare_modeler.py - Model revshare economics: direct vs via partner.

Stdlib-only. Deterministic. Computes:
  1. Margin per deal direct vs via partner (with named cost-to-serve inputs)
  2. Recommended revshare % band by tier + partner contribution depth
     (sourced > influenced > delivered)
  3. Break-even partner ROI — how many partner-sourced deals to cover MDF + program cost
  4. Long-term economics: at projected scale, when does partner economics beat direct?

Revshare bands by tier (industry-typical, can be tuned by --profile):
  REFERRAL          : 5-10%   on first-year ARR (one-time finder's fee)
  RESELLER          : 20-35%  on net ARR (recurring while customer active)
  OEM               : 40-55%  on net ARR (revshare reflects partner-owned support)
  SI_CONSULTING     : 15-25%  on first-year ARR (services attach independent)
  STRATEGIC         : 25-40%  on net ARR with floor + co-investment

Contribution depth modifies the band:
  sourced (partner-introduced, partner-owned relationship)   -> top half of band
  influenced (partner accelerated, but rep ran the play)     -> bottom half of band
  delivered (partner did the implementation only)            -> services-side comp,
                                                                NOT product revshare
                                                                (refuses to apply
                                                                 product band)

NEVER auto-commits a revshare %. Output is a band + assumptions + break-even, routed
to a human commercial committee.

Usage:
    python revshare_modeler.py --sample
    python revshare_modeler.py --input revshare.json
    python revshare_modeler.py --input revshare.json --output json
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, field, asdict
from typing import Any


SAMPLE_REVSHARE = {
    "partner_name": "Northstar Consulting",
    "partner_tier": "SI_CONSULTING",
    "deal_avg_size_usd": 90000,
    "partner_contribution": "sourced",
    "our_cost_to_serve_direct_usd": 18000,
    "our_cost_to_serve_via_partner_usd": 9000,
    "mdf_annual_usd": 20000,
    "program_overhead_annual_usd": 60000,
    "ttm_arr_projection_usd": 800000,
    "deal_count_projection": 9,
    "project_years": 3,
}


VALID_TIERS = ("REFERRAL", "RESELLER", "OEM", "SI_CONSULTING", "STRATEGIC")
VALID_CONTRIBUTIONS = ("sourced", "influenced", "delivered")


# Industry-typical revshare bands. Lower bound = floor; upper bound = ceiling.
# Tuned by `--profile`.
TIER_BANDS: dict[str, tuple[float, float]] = {
    "REFERRAL":      (5.0, 10.0),
    "RESELLER":      (20.0, 35.0),
    "OEM":           (40.0, 55.0),
    "SI_CONSULTING": (15.0, 25.0),
    "STRATEGIC":     (25.0, 40.0),
}


@dataclass
class RevshareModel:
    partner_name: str
    partner_tier: str
    partner_contribution: str
    deal_avg_size_usd: float
    direct_margin_usd: float
    direct_margin_pct: float
    via_partner_margin_usd_at_low: float
    via_partner_margin_pct_at_low: float
    via_partner_margin_usd_at_high: float
    via_partner_margin_pct_at_high: float
    recommended_revshare_low_pct: float
    recommended_revshare_high_pct: float
    breakeven_partner_sourced_deals: int
    annual_program_cost_usd: float
    ttm_arr_projection_usd: float
    ttm_revshare_payout_low_usd: float
    ttm_revshare_payout_high_usd: float
    ttm_net_to_us_low_usd: float
    ttm_net_to_us_high_usd: float
    crossover_year: int
    direct_economics_3yr_npv_usd: float
    partner_economics_3yr_npv_low_usd: float
    partner_economics_3yr_npv_high_usd: float
    assumptions: list[str] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)
    validation_errors: list[str] = field(default_factory=list)


def _validate(rev: dict) -> list[str]:
    errs: list[str] = []
    tier = (rev.get("partner_tier") or "").upper()
    contrib = (rev.get("partner_contribution") or "").lower()
    if tier not in VALID_TIERS:
        errs.append(f"partner_tier '{tier}' not in {VALID_TIERS}")
    if contrib not in VALID_CONTRIBUTIONS:
        errs.append(f"partner_contribution '{contrib}' not in {VALID_CONTRIBUTIONS}")
    if contrib == "delivered" and tier in ("REFERRAL", "RESELLER", "OEM", "STRATEGIC"):
        errs.append(
            "partner_contribution='delivered' is services attach only — do not pay product "
            "revshare. Pay services-side comp (typical fixed services fee or hourly rate). "
            "Re-classify contribution or move to SI_CONSULTING tier with explicit services band."
        )
    if float(rev.get("deal_avg_size_usd", 0)) <= 0:
        errs.append("deal_avg_size_usd must be > 0")
    return errs


def _contribution_band_shift(band: tuple[float, float], contribution: str) -> tuple[float, float]:
    """Modify band based on contribution depth.
    sourced     -> top half  (mid..high)
    influenced  -> bottom half (low..mid)
    delivered   -> applied only at SI_CONSULTING; for SI, this is the floor band.
    """
    low, high = band
    mid = (low + high) / 2.0
    if contribution == "sourced":
        return (mid, high)
    if contribution == "influenced":
        return (low, mid)
    # delivered (only reaches here for SI_CONSULTING per validation)
    return (low, mid)


def model(rev: dict) -> RevshareModel:
    errs = _validate(rev)
    if errs:
        # Return a stub model with validation errors; nothing else computed.
        return RevshareModel(
            partner_name=str(rev.get("partner_name", "UNSPECIFIED")),
            partner_tier=(rev.get("partner_tier") or "").upper(),
            partner_contribution=(rev.get("partner_contribution") or "").lower(),
            deal_avg_size_usd=float(rev.get("deal_avg_size_usd", 0.0)),
            direct_margin_usd=0.0, direct_margin_pct=0.0,
            via_partner_margin_usd_at_low=0.0, via_partner_margin_pct_at_low=0.0,
            via_partner_margin_usd_at_high=0.0, via_partner_margin_pct_at_high=0.0,
            recommended_revshare_low_pct=0.0, recommended_revshare_high_pct=0.0,
            breakeven_partner_sourced_deals=0,
            annual_program_cost_usd=0.0,
            ttm_arr_projection_usd=0.0,
            ttm_revshare_payout_low_usd=0.0, ttm_revshare_payout_high_usd=0.0,
            ttm_net_to_us_low_usd=0.0, ttm_net_to_us_high_usd=0.0,
            crossover_year=0,
            direct_economics_3yr_npv_usd=0.0,
            partner_economics_3yr_npv_low_usd=0.0,
            partner_economics_3yr_npv_high_usd=0.0,
            validation_errors=errs,
        )

    tier = (rev["partner_tier"] or "").upper()
    contrib = (rev["partner_contribution"] or "").lower()
    deal_avg = float(rev.get("deal_avg_size_usd", 0.0))
    cts_direct = float(rev.get("our_cost_to_serve_direct_usd", 0.0))
    cts_partner = float(rev.get("our_cost_to_serve_via_partner_usd", 0.0))
    mdf = float(rev.get("mdf_annual_usd", 0.0))
    overhead = float(rev.get("program_overhead_annual_usd", 0.0))
    ttm_arr = float(rev.get("ttm_arr_projection_usd", 0.0))
    deal_count = int(rev.get("deal_count_projection", 0) or 0)
    years = int(rev.get("project_years", 3) or 3)

    band = TIER_BANDS[tier]
    band_low, band_high = _contribution_band_shift(band, contrib)

    # Per-deal margin direct (no revshare; full cost-to-serve)
    direct_margin = deal_avg - cts_direct
    direct_margin_pct = (direct_margin / deal_avg * 100.0) if deal_avg else 0.0

    # Per-deal margin via partner: deal - (revshare%) * deal - cts_partner
    via_low_payout = deal_avg * (band_low / 100.0)
    via_high_payout = deal_avg * (band_high / 100.0)
    via_low_margin = deal_avg - via_low_payout - cts_partner
    via_high_margin = deal_avg - via_high_payout - cts_partner
    via_low_pct = (via_low_margin / deal_avg * 100.0) if deal_avg else 0.0
    via_high_pct = (via_high_margin / deal_avg * 100.0) if deal_avg else 0.0

    annual_program_cost = mdf + overhead

    # Break-even partner-sourced deals: program cost / (direct_margin - via_partner_margin_at_HIGH)
    # The cheaper our margin via partner, the more partner-sourced deals required.
    # If via_partner margin > direct margin (rare but possible for high-CTS direct sales), break-even is 0.
    delta_per_deal = direct_margin - via_high_margin
    if delta_per_deal <= 0:
        breakeven = 0
    else:
        breakeven = int(annual_program_cost / delta_per_deal) + 1

    # TTM economics: ttm_arr * revshare%
    ttm_payout_low = ttm_arr * (band_low / 100.0)
    ttm_payout_high = ttm_arr * (band_high / 100.0)
    ttm_net_low = ttm_arr - ttm_payout_high - (deal_count * cts_partner) - annual_program_cost
    ttm_net_high = ttm_arr - ttm_payout_low - (deal_count * cts_partner) - annual_program_cost
    # Direct equivalent at same ARR: ttm_arr - deal_count * cts_direct
    ttm_net_direct = ttm_arr - (deal_count * cts_direct)

    # Crossover year: at what year does partner economics beat direct?
    # Heuristic: if cts_direct - cts_partner > revshare_payout / deal_avg, never
    # need partner growth; if not, year when (deals_partner * marginal_savings) >
    # (annual_program_cost) — simple linear projection over `years`.
    crossover = 0
    if cts_direct > cts_partner and deal_count > 0:
        marginal_savings_per_deal = (cts_direct - cts_partner) - via_low_payout
        if marginal_savings_per_deal > 0:
            # cumulative savings needed to cover all program cost across `years`
            cumulative_program_cost = annual_program_cost * years
            cumulative_savings_per_year = marginal_savings_per_deal * deal_count
            if cumulative_savings_per_year > 0:
                yrs = cumulative_program_cost / cumulative_savings_per_year
                crossover = max(1, int(yrs) + (1 if yrs % 1 else 0))
        else:
            crossover = 0  # marginal economics never positive at low band
    else:
        crossover = 0

    # 3-year NPV at flat discount (we don't discount — keeping math obvious + auditable):
    direct_3yr_npv = ttm_net_direct * years
    partner_3yr_npv_low = ttm_net_low * years
    partner_3yr_npv_high = ttm_net_high * years

    assumptions = [
        f"Tier band ({tier}): {band[0]:.0f}-{band[1]:.0f}% — contribution '{contrib}' "
        f"shifts band to {band_low:.0f}-{band_high:.0f}%.",
        "Cost-to-serve via partner assumes partner owns first-line support; we own "
        "Tier-2+. Validate this matches the contract.",
        "Revshare is paid on net ARR (post-discount), not gross list price.",
        "TTM projection assumes deal_count_projection × deal_avg_size_usd ≈ ttm_arr_projection_usd. "
        "If these are inconsistent, fix the input.",
        "No churn modeled. Partner-sourced cohorts often have +/- 10pt NRR delta vs. direct — "
        "revisit with `c-level-advisor/cco-advisor` for retention-decomposition impact.",
        f"NPV computed flat across {years} years (no discount rate). Apply your WACC manually "
        "if the partnership is balance-sheet material.",
    ]

    warnings: list[str] = []
    if via_high_margin < 0:
        warnings.append(
            f"At top of band ({band_high:.0f}% revshare + ${cts_partner:,.0f} CTS), per-deal "
            "margin is NEGATIVE. Either lower the band, lower cost-to-serve, or do not sign "
            "at this tier."
        )
    if direct_margin > via_low_margin and contrib == "influenced":
        warnings.append(
            "Direct-sale margin > via-partner margin at INFLUENCED contribution. The partner "
            "is being paid for deals that would have closed anyway. Tighten attribution rules."
        )
    if ttm_arr > 0 and breakeven > deal_count:
        warnings.append(
            f"Break-even requires {breakeven} partner-sourced deals/year; projection only "
            f"shows {deal_count}. Program is economically UNPROFITABLE at projection scale. "
            "Re-scope MDF, re-tier, or unwind."
        )
    if contrib == "delivered" and tier == "SI_CONSULTING":
        warnings.append(
            "Delivered-only contribution: pay services-side compensation (fixed fee or hourly) "
            "rather than product revshare. Apply only the floor band as a ceiling."
        )
    if tier == "STRATEGIC" and annual_program_cost < 50000:
        warnings.append(
            f"STRATEGIC tier with program cost ${annual_program_cost:,.0f}/yr is structurally "
            "under-resourced. Strategic alliances require co-investment evidence."
        )

    return RevshareModel(
        partner_name=str(rev.get("partner_name", "UNSPECIFIED")),
        partner_tier=tier,
        partner_contribution=contrib,
        deal_avg_size_usd=deal_avg,
        direct_margin_usd=round(direct_margin, 2),
        direct_margin_pct=round(direct_margin_pct, 1),
        via_partner_margin_usd_at_low=round(via_low_margin, 2),
        via_partner_margin_pct_at_low=round(via_low_pct, 1),
        via_partner_margin_usd_at_high=round(via_high_margin, 2),
        via_partner_margin_pct_at_high=round(via_high_pct, 1),
        recommended_revshare_low_pct=round(band_low, 1),
        recommended_revshare_high_pct=round(band_high, 1),
        breakeven_partner_sourced_deals=breakeven,
        annual_program_cost_usd=round(annual_program_cost, 2),
        ttm_arr_projection_usd=round(ttm_arr, 2),
        ttm_revshare_payout_low_usd=round(ttm_payout_low, 2),
        ttm_revshare_payout_high_usd=round(ttm_payout_high, 2),
        ttm_net_to_us_low_usd=round(ttm_net_low, 2),
        ttm_net_to_us_high_usd=round(ttm_net_high, 2),
        crossover_year=crossover,
        direct_economics_3yr_npv_usd=round(direct_3yr_npv, 2),
        partner_economics_3yr_npv_low_usd=round(partner_3yr_npv_low, 2),
        partner_economics_3yr_npv_high_usd=round(partner_3yr_npv_high, 2),
        assumptions=assumptions,
        warnings=warnings,
    )


def _render_human(m: RevshareModel) -> str:
    lines = []
    lines.append(f"Revshare Model: {m.partner_name}")
    lines.append(f"Tier: {m.partner_tier} ; Contribution: {m.partner_contribution}")
    if m.validation_errors:
        lines.append("")
        lines.append("VALIDATION ERRORS (model not computed):")
        for e in m.validation_errors:
            lines.append(f"  ! {e}")
        return "\n".join(lines)
    lines.append("")
    lines.append("Recommended revshare band:")
    lines.append(
        f"  {m.recommended_revshare_low_pct:.0f}% to {m.recommended_revshare_high_pct:.0f}% "
        f"of net ARR (tier + contribution adjusted)"
    )
    lines.append("")
    lines.append("Per-deal economics:")
    lines.append(
        f"  Direct sale:       ${m.deal_avg_size_usd:>10,.0f} ARR  -  margin "
        f"${m.direct_margin_usd:>10,.0f} ({m.direct_margin_pct:.1f}%)"
    )
    lines.append(
        f"  Via partner (low):  ${m.deal_avg_size_usd:>10,.0f} ARR  -  margin "
        f"${m.via_partner_margin_usd_at_low:>10,.0f} ({m.via_partner_margin_pct_at_low:.1f}%)"
    )
    lines.append(
        f"  Via partner (high): ${m.deal_avg_size_usd:>10,.0f} ARR  -  margin "
        f"${m.via_partner_margin_usd_at_high:>10,.0f} ({m.via_partner_margin_pct_at_high:.1f}%)"
    )
    lines.append("")
    lines.append("Break-even program math:")
    lines.append(f"  Annual program cost (MDF + overhead): ${m.annual_program_cost_usd:,.0f}")
    lines.append(
        f"  Break-even partner-sourced deals/year (at top-of-band): "
        f"{m.breakeven_partner_sourced_deals}"
    )
    lines.append("")
    lines.append("Projected TTM economics:")
    lines.append(f"  TTM ARR through partner:           ${m.ttm_arr_projection_usd:,.0f}")
    lines.append(
        f"  Revshare payout (low..high):        "
        f"${m.ttm_revshare_payout_low_usd:,.0f} .. ${m.ttm_revshare_payout_high_usd:,.0f}"
    )
    lines.append(
        f"  Net to us (low band..high band):    "
        f"${m.ttm_net_to_us_high_usd:,.0f} .. ${m.ttm_net_to_us_low_usd:,.0f}"
    )
    lines.append("")
    lines.append("Long-term comparison (flat, no discount):")
    lines.append(f"  Direct 3-yr NPV:                    ${m.direct_economics_3yr_npv_usd:,.0f}")
    lines.append(
        f"  Partner 3-yr NPV (low..high band):  "
        f"${m.partner_economics_3yr_npv_low_usd:,.0f} .. "
        f"${m.partner_economics_3yr_npv_high_usd:,.0f}"
    )
    if m.crossover_year:
        lines.append(f"  Crossover year (partner > direct): year {m.crossover_year}")
    else:
        lines.append("  Crossover year: not reached within projection window")
    lines.append("")
    lines.append("Assumptions:")
    for a in m.assumptions:
        lines.append(f"  - {a}")
    if m.warnings:
        lines.append("")
        lines.append("Warnings:")
        for w in m.warnings:
            lines.append(f"  ! {w}")
    return "\n".join(lines)


def _to_jsonable(m: RevshareModel) -> dict:
    return asdict(m)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Model revshare economics: direct vs via partner.",
    )
    parser.add_argument("--input", help="Path to JSON revshare context")
    parser.add_argument("--output", default="human", choices=["human", "json", "markdown"])
    parser.add_argument("--sample", action="store_true", help="Use embedded sample revshare")
    args = parser.parse_args(argv)

    if args.sample or not args.input:
        rev = SAMPLE_REVSHARE
    else:
        with open(args.input) as f:
            rev = json.load(f)

    m = model(rev)
    if args.output == "json":
        print(json.dumps(_to_jsonable(m), indent=2))
    else:
        if args.output == "markdown":
            print("# Revshare Model\n")
        print(_render_human(m))
    return 0


if __name__ == "__main__":
    sys.exit(main())
