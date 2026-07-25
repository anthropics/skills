#!/usr/bin/env python3
"""channel_roi_analyzer.py

Computes per-channel ROI under three lenses:
  - Cash ROI (year-1 returns / cash invested)
  - LTV ROI (returns * LTV multiplier / investment)
  - Marginal ROI (next dollar of investment, diminishing-returns curve)

Emits a verdict per channel: DOUBLE-DOWN / MAINTAIN / DEFUND / EXIT, plus
the diminishing-returns inflection point.

Stdlib-only. Deterministic.

Usage:
    python channel_roi_analyzer.py --sample
    python channel_roi_analyzer.py --input roi.json --profile saas --output markdown
"""
from __future__ import annotations

import argparse
import json
import math
import sys
from typing import Any

# ---- Industry profiles: LTV multiplier benchmark, marginal-decay shape ----
# LTV multiplier = expected LTV / year-1 ARR (post-retention + expansion). Profile
# values are conservative midpoints from public benchmarks.
# marginal_decay_alpha = exponent k in marginal_roi = avg_roi * exp(-k * scale_idx)
# higher k = faster diminishing returns.
PROFILES = {
    "saas": {"ltv_multiplier": 3.5, "marginal_decay_alpha": 0.35, "cash_roi_target": 1.0},
    "api": {"ltv_multiplier": 4.5, "marginal_decay_alpha": 0.30, "cash_roi_target": 0.8},
    "enterprise-software": {
        "ltv_multiplier": 5.0,
        "marginal_decay_alpha": 0.25,
        "cash_roi_target": 0.6,
    },
    "marketplace": {
        "ltv_multiplier": 2.5,
        "marginal_decay_alpha": 0.45,
        "cash_roi_target": 1.2,
    },
    "hardware": {
        "ltv_multiplier": 1.8,
        "marginal_decay_alpha": 0.50,
        "cash_roi_target": 1.5,
    },
}


def _num(v: Any, default: float = 0.0) -> float:
    try:
        return float(v)
    except (TypeError, ValueError):
        return default


def compute_channel_roi(channel: dict, profile_cfg: dict) -> dict:
    name = channel.get("channel", "unnamed")
    inv = channel.get("investment_ttm", {}) or {}
    ret = channel.get("returns_ttm", {}) or {}

    invested = sum(
        _num(inv.get(k))
        for k in ("programs", "headcount_cost", "partner_program_cost", "mdf", "tooling", "training")
    )
    new_arr = _num(ret.get("new_arr"))
    exp_arr = _num(ret.get("expansion_arr"))
    retained_arr = _num(ret.get("retained_arr_attributable"))
    returns_y1 = new_arr + exp_arr + retained_arr

    if invested <= 0:
        return {"channel": name, "error": "investment_ttm sum must be > 0"}

    # Cash ROI (year-1)
    cash_roi = returns_y1 / invested

    # LTV ROI — apply profile multiplier to recurring portion (new + expansion). Retained
    # is already recurring so we don't double-count.
    ltv_returns = (new_arr + exp_arr) * profile_cfg["ltv_multiplier"] + retained_arr
    ltv_roi = ltv_returns / invested

    # Marginal ROI — diminishing returns. Model: marginal = avg * exp(-alpha * scale_idx)
    # where scale_idx is log10(invested / 100k) clamped >= 0. Inflection = scale at which
    # marginal_roi drops to 1.0 (a dollar in returns a dollar — no profit).
    alpha = profile_cfg["marginal_decay_alpha"]
    scale_idx = max(0.0, math.log10(max(invested, 1.0) / 100_000.0))
    marginal_roi = cash_roi * math.exp(-alpha * scale_idx)

    # Inflection: solve cash_roi * exp(-alpha * x) = 1.0 -> x = ln(cash_roi)/alpha
    if cash_roi > 1.0:
        inflection_scale = math.log(cash_roi) / alpha
        inflection_invested = 100_000.0 * (10 ** inflection_scale)
    else:
        inflection_invested = invested  # already past the inflection

    # Verdict logic — deterministic
    target = profile_cfg["cash_roi_target"]
    if cash_roi >= target * 1.5 and ltv_roi >= 3.0 and marginal_roi >= 1.0:
        verdict = "DOUBLE-DOWN"
        rationale = (
            "Cash ROI > 1.5x target, LTV ROI ≥ 3.0x, marginal ROI > 1.0 — "
            "next dollar still earns positive return. Invest more."
        )
    elif cash_roi >= target and ltv_roi >= 2.0:
        verdict = "MAINTAIN"
        rationale = (
            "Cash ROI meets target and LTV ROI ≥ 2.0x. Hold current investment; "
            "monitor marginal ROI before increasing."
        )
    elif cash_roi >= target * 0.5 or ltv_roi >= 1.5:
        verdict = "DEFUND"
        rationale = (
            "Sub-target cash ROI. LTV ROI may be supportive but not enough to justify "
            "current spend. Cut investment 30-50% and reassess in 2 quarters."
        )
    else:
        verdict = "EXIT"
        rationale = (
            "Both cash ROI and LTV ROI below floor. Channel is value-destroying at "
            "current load. Exit or restructure the program."
        )

    return {
        "channel": name,
        "invested_ttm": round(invested, 2),
        "returns_y1": round(returns_y1, 2),
        "cash_roi": round(cash_roi, 3),
        "ltv_roi": round(ltv_roi, 3),
        "marginal_roi": round(marginal_roi, 3),
        "inflection_invested": round(inflection_invested, 2),
        "verdict": verdict,
        "rationale": rationale,
        "profile_target_cash_roi": target,
    }


def render_markdown(results: list, profile: str) -> str:
    lines = [
        f"# Channel ROI Analysis — profile: `{profile}`",
        "",
        "## Per-channel verdicts",
        "| Channel | Invested | Returns Y1 | Cash ROI | LTV ROI | Marginal ROI | Inflection | Verdict |",
        "|---|---:|---:|---:|---:|---:|---:|---|",
    ]
    for r in results:
        if "error" in r:
            lines.append(f"| {r['channel']} | — | — | — | — | — | — | ERROR: {r['error']} |")
            continue
        lines.append(
            f"| {r['channel']} | ${r['invested_ttm']:,.0f} | ${r['returns_y1']:,.0f} | "
            f"{r['cash_roi']:.2f}x | {r['ltv_roi']:.2f}x | {r['marginal_roi']:.2f}x | "
            f"${r['inflection_invested']:,.0f} | **{r['verdict']}** |"
        )
    lines += ["", "## Verdict rationale"]
    for r in results:
        if "error" in r:
            continue
        lines += [f"### {r['channel']} — {r['verdict']}", r["rationale"], ""]

    lines += [
        "## Definitions",
        "- **Cash ROI** = year-1 returns / cash invested. Profile target shown above.",
        "- **LTV ROI** = (new+expansion ARR × LTV multiplier + retained ARR) / invested.",
        "- **Marginal ROI** = ROI on the next dollar of investment, modeled via "
        "`avg_roi × exp(-alpha × log10(invested / $100k))`. Profile-tuned alpha.",
        "- **Inflection** = invested-$ level at which marginal ROI hits 1.0 (break-even on "
        "the next dollar). Beyond this point, additional spend destroys value.",
    ]
    return "\n".join(lines)


SAMPLE = {
    "profile": "saas",
    "channels": [
        {
            "channel": "direct",
            "investment_ttm": {
                "programs": 200_000,
                "headcount_cost": 1_600_000,
                "partner_program_cost": 0,
                "mdf": 0,
                "tooling": 80_000,
                "training": 60_000,
            },
            "returns_ttm": {
                "new_arr": 3_800_000,
                "expansion_arr": 900_000,
                "retained_arr_attributable": 2_400_000,
            },
        },
        {
            "channel": "partner-led",
            "investment_ttm": {
                "programs": 150_000,
                "headcount_cost": 360_000,
                "partner_program_cost": 280_000,
                "mdf": 120_000,
                "tooling": 30_000,
                "training": 80_000,
            },
            "returns_ttm": {
                "new_arr": 1_400_000,
                "expansion_arr": 200_000,
                "retained_arr_attributable": 900_000,
            },
        },
        {
            "channel": "marketplace",
            "investment_ttm": {
                "programs": 60_000,
                "headcount_cost": 120_000,
                "partner_program_cost": 0,
                "mdf": 0,
                "tooling": 40_000,
                "training": 0,
            },
            "returns_ttm": {
                "new_arr": 200_000,
                "expansion_arr": 40_000,
                "retained_arr_attributable": 80_000,
            },
        },
    ],
}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--input", help="Path to JSON input file")
    ap.add_argument("--output", choices=["json", "markdown"], default="markdown")
    ap.add_argument(
        "--profile",
        choices=list(PROFILES.keys()),
        default="saas",
        help="Industry profile (tunes LTV multiplier + marginal-decay alpha)",
    )
    ap.add_argument("--sample", action="store_true")
    args = ap.parse_args()

    if args.sample:
        payload = SAMPLE
    elif args.input:
        with open(args.input) as f:
            payload = json.load(f)
    else:
        ap.print_help()
        return 0

    profile = payload.get("profile", args.profile)
    if profile not in PROFILES:
        print(f"Unknown profile: {profile}", file=sys.stderr)
        return 2
    profile_cfg = PROFILES[profile]

    channels = payload.get("channels", [])
    if not channels and "channel" in payload:
        channels = [payload]

    results = [compute_channel_roi(c, profile_cfg) for c in channels]
    if args.output == "json":
        print(json.dumps({"profile": profile, "results": results}, indent=2))
    else:
        print(render_markdown(results, profile))
    return 0


if __name__ == "__main__":
    sys.exit(main())
