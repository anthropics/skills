#!/usr/bin/env python3
"""discount_matrix_builder.py - Design a data-backed discount matrix.

Stdlib-only. Builds a 4-dimensional discount matrix indexed by:
  (ARR band) x (term length) x (payment terms days) x (strategic value tier)

Each cell carries:
  - approved_discount_band (min%, max%) — backed by current win-rate and NRR
    distribution observed at that cell in the input `current_deals[]` corpus
  - approver_tier (AE / Manager / Director / VP / CFO)
  - margin_floor_pct — derived from target_constraints.min_margin_pct minus
    a per-cell allowance proportional to strategic value
  - data_backing — n_deals, win_rate, nrr_12mo observed; flagged THIN if n<5
  - exception_required — TRUE when target max% exceeds matrix max%

Industry profiles tune the band widths and approver thresholds:
  saas, enterprise-software, api, marketplace, services

Usage:
    python discount_matrix_builder.py --sample
    python discount_matrix_builder.py --input policy_intake.json --profile saas
    python discount_matrix_builder.py --input policy_intake.json --output json
"""

from __future__ import annotations

import argparse
import json
import sys
from typing import Any


# ------------------------------ Sample input ------------------------------ #

SAMPLE_INPUT: dict[str, Any] = {
    "industry": "saas",
    "current_deals": [
        {"arr": 18000,  "discount_pct": 8,  "term_months": 12, "payment_terms_days": 30, "strategic_value": "standard",  "win_lost": "win",  "nrr_12mo": 1.08},
        {"arr": 22000,  "discount_pct": 12, "term_months": 12, "payment_terms_days": 30, "strategic_value": "standard",  "win_lost": "win",  "nrr_12mo": 1.05},
        {"arr": 28000,  "discount_pct": 18, "term_months": 12, "payment_terms_days": 45, "strategic_value": "standard",  "win_lost": "lost", "nrr_12mo": 0.0},
        {"arr": 75000,  "discount_pct": 14, "term_months": 24, "payment_terms_days": 30, "strategic_value": "standard",  "win_lost": "win",  "nrr_12mo": 1.12},
        {"arr": 95000,  "discount_pct": 22, "term_months": 24, "payment_terms_days": 30, "strategic_value": "logo",      "win_lost": "win",  "nrr_12mo": 1.18},
        {"arr": 130000, "discount_pct": 28, "term_months": 24, "payment_terms_days": 45, "strategic_value": "logo",      "win_lost": "win",  "nrr_12mo": 1.10},
        {"arr": 260000, "discount_pct": 26, "term_months": 36, "payment_terms_days": 30, "strategic_value": "expansion", "win_lost": "win",  "nrr_12mo": 1.22},
        {"arr": 410000, "discount_pct": 30, "term_months": 36, "payment_terms_days": 30, "strategic_value": "expansion", "win_lost": "win",  "nrr_12mo": 1.25},
        {"arr": 540000, "discount_pct": 38, "term_months": 36, "payment_terms_days": 60, "strategic_value": "logo",      "win_lost": "lost", "nrr_12mo": 0.0},
        {"arr": 720000, "discount_pct": 32, "term_months": 36, "payment_terms_days": 30, "strategic_value": "expansion", "win_lost": "win",  "nrr_12mo": 1.20},
    ],
    "target_constraints": {
        "min_margin_pct": 70.0,
        "max_discount_pct_without_exception": 35.0,
        "target_nrr": 1.15,
    },
}


# ------------------------------ Dimensions ------------------------------ #

ARR_BANDS = [
    ("smb",        0,       25_000),
    ("mid",        25_000,  100_000),
    ("enterprise", 100_000, 500_000),
    ("strategic",  500_000, 10_000_000_000),
]

TERM_BANDS = [
    ("annual",      0,  12),
    ("two_year",    13, 24),
    ("multi_year",  25, 120),
]

PAYMENT_BANDS = [
    ("net30_prepay", 0,  30),
    ("net45",        31, 45),
    ("net60_plus",   46, 365),
]

STRATEGIC_TIERS = ["standard", "logo", "expansion", "lighthouse"]


PROFILES: dict[str, dict[str, Any]] = {
    "saas": {
        # max_discount per (arr_band, term_band, payment_band, strat_tier)
        # baseline maxima; tuned by strategic tier and term shape
        "base_max_pct": {"smb": 15, "mid": 22, "enterprise": 30, "strategic": 38},
        "term_bonus":   {"annual": 0, "two_year": 3, "multi_year": 6},
        "payment_penalty": {"net30_prepay": 0, "net45": -2, "net60_plus": -5},
        "strategic_bonus": {"standard": 0, "logo": 4, "expansion": 6, "lighthouse": 10},
        "approver_thresholds": [(15, "AE"), (25, "Sales Manager"), (35, "Director"), (50, "VP Sales"), (100.1, "CFO + CRO")],
    },
    "enterprise-software": {
        "base_max_pct": {"smb": 20, "mid": 28, "enterprise": 38, "strategic": 48},
        "term_bonus":   {"annual": 0, "two_year": 4, "multi_year": 8},
        "payment_penalty": {"net30_prepay": 0, "net45": -2, "net60_plus": -6},
        "strategic_bonus": {"standard": 0, "logo": 5, "expansion": 8, "lighthouse": 12},
        "approver_thresholds": [(20, "AE"), (30, "Sales Manager"), (40, "Director"), (55, "VP Sales"), (100.1, "CFO + CRO")],
    },
    "api": {
        "base_max_pct": {"smb": 10, "mid": 18, "enterprise": 25, "strategic": 32},
        "term_bonus":   {"annual": 0, "two_year": 2, "multi_year": 5},
        "payment_penalty": {"net30_prepay": 0, "net45": -2, "net60_plus": -4},
        "strategic_bonus": {"standard": 0, "logo": 3, "expansion": 5, "lighthouse": 8},
        "approver_thresholds": [(10, "AE"), (18, "Sales Manager"), (25, "Director"), (35, "VP Sales"), (100.1, "CFO + CRO")],
    },
    "marketplace": {
        "base_max_pct": {"smb": 8, "mid": 12, "enterprise": 18, "strategic": 25},
        "term_bonus":   {"annual": 0, "two_year": 2, "multi_year": 4},
        "payment_penalty": {"net30_prepay": 0, "net45": -1, "net60_plus": -3},
        "strategic_bonus": {"standard": 0, "logo": 2, "expansion": 4, "lighthouse": 6},
        "approver_thresholds": [(8, "AE"), (15, "Sales Manager"), (22, "Director"), (30, "VP"), (100.1, "CFO + CRO")],
    },
    "services": {
        # margin-thin; tight bands and fast escalation
        "base_max_pct": {"smb": 5, "mid": 10, "enterprise": 15, "strategic": 22},
        "term_bonus":   {"annual": 0, "two_year": 2, "multi_year": 3},
        "payment_penalty": {"net30_prepay": 0, "net45": -1, "net60_plus": -3},
        "strategic_bonus": {"standard": 0, "logo": 2, "expansion": 3, "lighthouse": 5},
        "approver_thresholds": [(5, "AE"), (12, "Sales Manager"), (20, "Director"), (30, "VP Services"), (100.1, "CFO + COO")],
    },
}


# ------------------------------ Logic ------------------------------ #

def _band(value: float, bands: list[tuple]) -> str:
    for name, lo, hi in bands:
        if lo <= value <= hi:
            return name
    return bands[-1][0]


def _approver_for(max_pct: float, thresholds: list[tuple[float, str]]) -> str:
    for cutoff, name in thresholds:
        if max_pct <= cutoff:
            return name
    return thresholds[-1][1]


def _classify_deal(deal: dict[str, Any]) -> tuple[str, str, str, str]:
    return (
        _band(deal["arr"], ARR_BANDS),
        _band(deal["term_months"], TERM_BANDS),
        _band(deal["payment_terms_days"], PAYMENT_BANDS),
        deal.get("strategic_value", "standard"),
    )


def build_matrix(payload: dict[str, Any], profile_name: str) -> dict[str, Any]:
    profile = PROFILES.get(profile_name, PROFILES["saas"])
    deals = payload.get("current_deals", [])
    constraints = payload.get("target_constraints", {})
    min_margin = float(constraints.get("min_margin_pct", 70.0))
    max_without_exception = float(constraints.get("max_discount_pct_without_exception", 35.0))
    target_nrr = float(constraints.get("target_nrr", 1.10))

    # Bucket observed deals by cell.
    buckets: dict[tuple, list[dict]] = {}
    for d in deals:
        key = _classify_deal(d)
        buckets.setdefault(key, []).append(d)

    cells: list[dict[str, Any]] = []
    for arr_band, _, _ in ARR_BANDS:
        for term_band, _, _ in TERM_BANDS:
            for pay_band, _, _ in PAYMENT_BANDS:
                for strat_tier in STRATEGIC_TIERS:
                    key = (arr_band, term_band, pay_band, strat_tier)
                    base = profile["base_max_pct"][arr_band]
                    bonus_term = profile["term_bonus"][term_band]
                    pen_pay = profile["payment_penalty"][pay_band]
                    bonus_strat = profile["strategic_bonus"][strat_tier]
                    cell_max = max(0.0, base + bonus_term + pen_pay + bonus_strat)
                    cell_min = max(0.0, cell_max * 0.5)  # min discount in this band

                    # Observed data backing
                    obs = buckets.get(key, [])
                    n = len(obs)
                    wins = sum(1 for d in obs if d.get("win_lost") == "win")
                    win_rate = (wins / n) if n else None
                    nrr_vals = [d.get("nrr_12mo", 0.0) for d in obs if d.get("win_lost") == "win"]
                    nrr_obs = (sum(nrr_vals) / len(nrr_vals)) if nrr_vals else None

                    # Margin floor: every 1% discount typically costs ~(1/gm)% of margin.
                    # Cap the cell at the constraint-driven max as well.
                    capped_max = min(cell_max, max_without_exception + bonus_strat)  # strategic gets a touch more
                    exception_required = capped_max > max_without_exception

                    # Margin floor: subtract a strategic-value allowance.
                    margin_floor = max(min_margin - bonus_strat, 50.0)

                    approver = _approver_for(capped_max, profile["approver_thresholds"])

                    cells.append({
                        "arr_band": arr_band,
                        "term_band": term_band,
                        "payment_band": pay_band,
                        "strategic_tier": strat_tier,
                        "approved_discount_min_pct": round(cell_min, 1),
                        "approved_discount_max_pct": round(capped_max, 1),
                        "approver_tier": approver,
                        "margin_floor_pct": round(margin_floor, 1),
                        "exception_required_above_pct": round(max_without_exception, 1),
                        "data_backing": {
                            "n_observed_deals": n,
                            "win_rate": round(win_rate, 3) if win_rate is not None else None,
                            "nrr_12mo_observed": round(nrr_obs, 3) if nrr_obs is not None else None,
                            "thin_data_flag": n < 5,
                        },
                        "meets_target_nrr": (nrr_obs is not None and nrr_obs >= target_nrr),
                        "exception_required": exception_required,
                    })

    return {
        "profile": profile_name,
        "constraints": {
            "min_margin_pct": min_margin,
            "max_discount_pct_without_exception": max_without_exception,
            "target_nrr": target_nrr,
        },
        "n_cells": len(cells),
        "n_observed_deals": len(deals),
        "cells": cells,
    }


# ------------------------------ Rendering ------------------------------ #

def render_markdown(matrix: dict[str, Any]) -> str:
    out: list[str] = []
    out.append(f"# Discount Matrix — profile: `{matrix['profile']}`")
    out.append("")
    out.append("## Constraints")
    for k, v in matrix["constraints"].items():
        out.append(f"- **{k}**: {v}")
    out.append("")
    out.append(f"## Cells ({matrix['n_cells']}) — backed by {matrix['n_observed_deals']} observed deals")
    out.append("")
    out.append("| ARR | Term | Payment | Strategic | Discount band | Approver | Margin floor | n | Win rate | NRR | Exception? |")
    out.append("|---|---|---|---|---|---|---|---|---|---|---|")
    for c in matrix["cells"]:
        db = c["data_backing"]
        wr = f"{db['win_rate']:.0%}" if db["win_rate"] is not None else "—"
        nrr = f"{db['nrr_12mo_observed']:.2f}" if db["nrr_12mo_observed"] is not None else "—"
        thin = " (THIN)" if db["thin_data_flag"] else ""
        exc = "YES" if c["exception_required"] else "no"
        out.append(
            f"| {c['arr_band']} | {c['term_band']} | {c['payment_band']} | {c['strategic_tier']} | "
            f"{c['approved_discount_min_pct']}-{c['approved_discount_max_pct']}% | "
            f"{c['approver_tier']} | {c['margin_floor_pct']}% | "
            f"{db['n_observed_deals']}{thin} | {wr} | {nrr} | {exc} |"
        )
    out.append("")
    out.append("## Notes")
    out.append("- THIN data flag means n<5 observed deals in this cell — treat the band as directional, not data-backed.")
    out.append("- Strategic tiers carry a margin-floor allowance proportional to their bonus; lighthouse cells absorb the deepest discounts.")
    out.append("- Cells flagged `Exception? YES` exceed the policy's max-without-exception threshold and must route through `exception_router.py`.")
    return "\n".join(out)


# ------------------------------ CLI ------------------------------ #

def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description="Design a data-backed discount matrix.")
    ap.add_argument("--input", help="Path to policy intake JSON.")
    ap.add_argument("--profile", default="saas",
                    choices=list(PROFILES.keys()),
                    help="Industry profile (default: saas).")
    ap.add_argument("--output", default="markdown", choices=["markdown", "json"],
                    help="Output format (default: markdown).")
    ap.add_argument("--sample", action="store_true", help="Run with the built-in sample payload.")
    args = ap.parse_args(argv)

    if args.sample:
        payload = SAMPLE_INPUT
        profile = args.profile or payload.get("industry", "saas")
    elif args.input:
        try:
            with open(args.input, "r", encoding="utf-8") as f:
                payload = json.load(f)
        except Exception as e:
            print(f"ERROR: could not read {args.input}: {e}", file=sys.stderr)
            return 1
        profile = args.profile or payload.get("industry", "saas")
    else:
        ap.print_help()
        return 0

    matrix = build_matrix(payload, profile)

    if args.output == "json":
        print(json.dumps(matrix, indent=2))
    else:
        print(render_markdown(matrix))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
