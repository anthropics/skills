#!/usr/bin/env python3
"""channel_mix_optimizer.py

Computes per-channel effective LTV, payback period, and efficiency ratio
(LTV/CAC), then recommends a channel mix that maximizes effective ARR
subject to constraints (min direct %, max partner concentration %).

Includes a sensitivity table: what happens if direct CAC rises 20%, partner
discount widens 5 points, or retention drops 3 points?

Stdlib-only. Deterministic. No external solver — uses a discrete grid search
over feasible mixes, which is sufficient for 2-6 channel problems.

Usage:
    python channel_mix_optimizer.py --sample
    python channel_mix_optimizer.py --input mix.json --profile saas --output markdown
"""
from __future__ import annotations

import argparse
import json
import sys
from typing import Any

# Industry profiles tune assumed gross-margin-to-monthly conversion and
# benchmark payback targets (months).
PROFILES = {
    "saas": {"payback_target_months": 12, "ltv_cac_floor": 3.0},
    "api": {"payback_target_months": 9, "ltv_cac_floor": 4.0},
    "enterprise-software": {"payback_target_months": 18, "ltv_cac_floor": 3.0},
    "marketplace": {"payback_target_months": 6, "ltv_cac_floor": 2.5},
    "hardware": {"payback_target_months": 24, "ltv_cac_floor": 2.0},
}


def _num(v: Any, default: float = 0.0) -> float:
    try:
        return float(v)
    except (TypeError, ValueError):
        return default


def compute_channel_metrics(ch: dict, profile_cfg: dict) -> dict:
    name = ch.get("name", "unnamed")
    deal_count = _num(ch.get("deal_count_ttm"))
    arr_ttm = _num(ch.get("arr_ttm"))
    avg_deal = _num(ch.get("avg_deal_size"))
    gm_pct = _num(ch.get("gross_margin_pct"), 70.0)
    cac = _num(ch.get("cac"))
    cycle_days = _num(ch.get("sales_cycle_days"), 60)
    retention = _num(ch.get("retention_rate"), 0.85)
    expansion = _num(ch.get("expansion_rate"), 1.05)
    partner_discount = _num(ch.get("partner_discount_pct"), 0)

    if avg_deal <= 0 or cac <= 0:
        return {"name": name, "error": "avg_deal_size and cac must both be > 0"}

    # Effective margin after partner discount
    effective_margin_pct = gm_pct * (1.0 - partner_discount / 100.0)

    # Effective LTV — geometric-series approximation:
    # LTV = avg_deal * (effective_margin/100) * expansion / (1 - retention)
    # If retention >= 1.0, cap denominator at 0.05 to avoid blowup (means
    # "indefinite retention" — we don't reward unrealistically).
    denom = max(1.0 - retention, 0.05)
    effective_ltv = avg_deal * (effective_margin_pct / 100.0) * expansion / denom

    # Payback period: months to recoup CAC at monthly gross margin
    monthly_gross_margin = (avg_deal / 12.0) * (effective_margin_pct / 100.0)
    payback_months = cac / monthly_gross_margin if monthly_gross_margin > 0 else float("inf")

    # Efficiency ratio
    ltv_cac = effective_ltv / cac if cac > 0 else 0.0

    return {
        "name": name,
        "deal_count_ttm": deal_count,
        "arr_ttm": arr_ttm,
        "avg_deal_size": avg_deal,
        "gross_margin_pct": gm_pct,
        "effective_margin_pct": round(effective_margin_pct, 2),
        "cac": cac,
        "sales_cycle_days": cycle_days,
        "retention_rate": retention,
        "expansion_rate": expansion,
        "partner_discount_pct": partner_discount,
        "effective_ltv": round(effective_ltv, 2),
        "payback_months": round(payback_months, 2),
        "ltv_cac": round(ltv_cac, 2),
        "meets_payback_target": payback_months <= profile_cfg["payback_target_months"],
        "meets_ltv_cac_floor": ltv_cac >= profile_cfg["ltv_cac_floor"],
    }


def _is_partner_channel(name: str) -> bool:
    n = name.lower()
    return any(tag in n for tag in ("partner", "reseller", "channel", "oem", "marketplace"))


def _is_direct_channel(name: str) -> bool:
    return "direct" in name.lower() or "inside" in name.lower() or "outbound" in name.lower()


def optimize_mix(metrics: list, constraints: dict) -> dict:
    """Discrete grid search over channel-mix percentages (5% increments)."""
    n = len(metrics)
    if n == 0:
        return {"error": "no channels provided"}

    min_direct = _num(constraints.get("min_direct_pct"), 0)
    max_partner_conc = _num(constraints.get("max_partner_concentration_pct"), 100)

    # Score = effective_ltv / cac (use LTV/CAC as the per-$-CAC efficiency).
    # We allocate a normalized 100 "investment units" across channels and maximize
    # sum(units_i * ltv_cac_i) subject to constraints.
    best_score = -1.0
    best_mix = None

    step = 5
    # generate compositions of 100 over n channels in 5% steps
    def gen(remaining: int, slots: int):
        if slots == 1:
            yield (remaining,)
            return
        for v in range(0, remaining + 1, step):
            for tail in gen(remaining - v, slots - 1):
                yield (v,) + tail

    for mix in gen(100, n):
        # constraint checks
        direct_share = sum(mix[i] for i, m in enumerate(metrics) if _is_direct_channel(m["name"]))
        partner_share_max = max(
            (mix[i] for i, m in enumerate(metrics) if _is_partner_channel(m["name"])),
            default=0,
        )
        if direct_share < min_direct:
            continue
        if partner_share_max > max_partner_conc:
            continue
        score = sum(mix[i] * metrics[i].get("ltv_cac", 0) for i in range(n))
        if score > best_score:
            best_score = score
            best_mix = mix

    if best_mix is None:
        return {"error": "no feasible mix under given constraints"}
    return {
        "best_mix_pct": {metrics[i]["name"]: best_mix[i] for i in range(n)},
        "score": round(best_score, 2),
    }


def sensitivity_scenarios(channels: list, profile_cfg: dict, constraints: dict) -> list:
    """Re-run optimization under perturbed inputs."""
    scenarios = []

    def perturb(perturbation_fn, label: str):
        perturbed = []
        for c in channels:
            cc = dict(c)
            perturbation_fn(cc)
            perturbed.append(cc)
        ms = [compute_channel_metrics(c, profile_cfg) for c in perturbed]
        ms = [m for m in ms if "error" not in m]
        opt = optimize_mix(ms, constraints)
        scenarios.append({"scenario": label, "mix": opt.get("best_mix_pct"), "note": opt.get("error")})

    def bump_direct_cac(c):
        if _is_direct_channel(c.get("name", "")):
            c["cac"] = _num(c.get("cac")) * 1.20

    def widen_partner_discount(c):
        if _is_partner_channel(c.get("name", "")):
            c["partner_discount_pct"] = _num(c.get("partner_discount_pct")) + 5

    def drop_retention(c):
        c["retention_rate"] = max(0.0, _num(c.get("retention_rate"), 0.85) - 0.03)

    perturb(bump_direct_cac, "Direct CAC +20%")
    perturb(widen_partner_discount, "Partner discount +5pts")
    perturb(drop_retention, "All retention -3pts")
    return scenarios


def render_markdown(report: dict, profile: str) -> str:
    lines = [
        f"# Channel Mix Optimization — profile: `{profile}`",
        "",
        "## Per-channel economics",
        "| Channel | Avg deal | Eff margin | CAC | Payback (mo) | LTV | LTV/CAC | Meets bar? |",
        "|---|---:|---:|---:|---:|---:|---:|---|",
    ]
    for m in report["metrics"]:
        if "error" in m:
            lines.append(f"| {m['name']} | — | — | — | — | — | — | ERROR: {m['error']} |")
            continue
        bar = (
            "PASS"
            if m["meets_payback_target"] and m["meets_ltv_cac_floor"]
            else ("PARTIAL" if m["meets_payback_target"] or m["meets_ltv_cac_floor"] else "FAIL")
        )
        lines.append(
            f"| {m['name']} | ${m['avg_deal_size']:,.0f} | {m['effective_margin_pct']:.1f}% | "
            f"${m['cac']:,.0f} | {m['payback_months']:.1f} | ${m['effective_ltv']:,.0f} | "
            f"{m['ltv_cac']:.2f}x | {bar} |"
        )
    lines.append("")

    if "best_mix" in report and report["best_mix"].get("best_mix_pct"):
        lines += ["## Recommended mix (subject to constraints)", "| Channel | Recommended share |", "|---|---:|"]
        for k, v in report["best_mix"]["best_mix_pct"].items():
            lines.append(f"| {k} | {v}% |")
        lines.append("")
    elif "best_mix" in report and report["best_mix"].get("error"):
        lines += [f"## Mix optimization", f"**{report['best_mix']['error']}**", ""]

    if report.get("sensitivity"):
        lines += ["## Sensitivity scenarios", "| Scenario | Recommended mix |", "|---|---|"]
        for s in report["sensitivity"]:
            if s.get("mix"):
                mix_str = ", ".join(f"{k}: {v}%" for k, v in s["mix"].items())
                lines.append(f"| {s['scenario']} | {mix_str} |")
            else:
                lines.append(f"| {s['scenario']} | {s.get('note') or 'no feasible mix'} |")
        lines.append("")

    lines += [
        "## Notes",
        f"- Profile `{profile}` payback target: "
        f"{PROFILES[profile]['payback_target_months']} months; LTV/CAC floor: "
        f"{PROFILES[profile]['ltv_cac_floor']:.1f}x.",
        "- Optimizer maximizes effective-ARR-weighted LTV/CAC across channels, in 5% steps.",
        "- Constraint floors / ceilings are HARD constraints — infeasible mixes are reported as errors.",
    ]
    return "\n".join(lines)


SAMPLE = {
    "profile": "saas",
    "channels": [
        {
            "name": "direct",
            "deal_count_ttm": 120,
            "arr_ttm": 6_000_000,
            "avg_deal_size": 50_000,
            "gross_margin_pct": 75,
            "cac": 18_000,
            "sales_cycle_days": 75,
            "retention_rate": 0.92,
            "expansion_rate": 1.18,
            "partner_discount_pct": 0,
        },
        {
            "name": "partner-led",
            "deal_count_ttm": 80,
            "arr_ttm": 4_000_000,
            "avg_deal_size": 50_000,
            "gross_margin_pct": 75,
            "cac": 10_000,
            "sales_cycle_days": 90,
            "retention_rate": 0.86,
            "expansion_rate": 1.08,
            "partner_discount_pct": 20,
        },
        {
            "name": "marketplace",
            "deal_count_ttm": 200,
            "arr_ttm": 1_000_000,
            "avg_deal_size": 5_000,
            "gross_margin_pct": 70,
            "cac": 1_500,
            "sales_cycle_days": 14,
            "retention_rate": 0.78,
            "expansion_rate": 1.02,
            "partner_discount_pct": 15,
        },
    ],
    "constraints": {"min_direct_pct": 30, "max_partner_concentration_pct": 50},
}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--input")
    ap.add_argument("--output", choices=["json", "markdown"], default="markdown")
    ap.add_argument(
        "--profile",
        choices=list(PROFILES.keys()),
        default="saas",
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
    constraints = payload.get("constraints", {}) or {}

    metrics = [compute_channel_metrics(c, profile_cfg) for c in channels]
    valid_metrics = [m for m in metrics if "error" not in m]
    best = optimize_mix(valid_metrics, constraints)
    sens = sensitivity_scenarios(channels, profile_cfg, constraints) if channels else []

    report = {"profile": profile, "metrics": metrics, "best_mix": best, "sensitivity": sens}

    if args.output == "json":
        print(json.dumps(report, indent=2))
    else:
        print(render_markdown(report, profile))
    return 0


if __name__ == "__main__":
    sys.exit(main())
