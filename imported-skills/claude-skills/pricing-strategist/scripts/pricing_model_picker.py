#!/usr/bin/env python3
"""pricing_model_picker.py — rank pricing models by fit-score for a given customer context.

Input: JSON describing customer context (industry, deal size, customer count, value drivers,
adoption curve, consumption pattern, competitor pricing models).

Output: ranked list of 5 pricing models (subscription seat-based, usage-based, value-based,
freemium, hybrid) with fit-score 0-100 and trade-offs.

Deterministic decision logic. No LLM calls. No third-party deps.

Usage:
    pricing_model_picker.py --input brief.json --profile saas --output markdown
    pricing_model_picker.py --sample
"""
from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

MODELS = [
    "subscription_seat_based",
    "usage_based",
    "value_based",
    "freemium",
    "hybrid",
]

# Industry profile tuning — base biases (additive, capped at ±15)
PROFILES: dict[str, dict[str, int]] = {
    "saas": {
        "subscription_seat_based": 10,
        "usage_based": 0,
        "value_based": 0,
        "freemium": 5,
        "hybrid": 5,
    },
    "api": {
        "subscription_seat_based": -10,
        "usage_based": 15,
        "value_based": 0,
        "freemium": 5,
        "hybrid": 5,
    },
    "ai-tools": {
        "subscription_seat_based": -5,
        "usage_based": 10,
        "value_based": 5,
        "freemium": 5,
        "hybrid": 10,
    },
    "enterprise-software": {
        "subscription_seat_based": 5,
        "usage_based": -5,
        "value_based": 10,
        "freemium": -10,
        "hybrid": 5,
    },
    "marketplace": {
        "subscription_seat_based": -10,
        "usage_based": 10,
        "value_based": 10,
        "freemium": 5,
        "hybrid": 5,
    },
}


@dataclass
class ModelScore:
    model: str
    score: int
    rationale: list[str] = field(default_factory=list)
    tradeoffs: list[str] = field(default_factory=list)


def clamp(n: int, lo: int = 0, hi: int = 100) -> int:
    return max(lo, min(hi, n))


def score_models(ctx: dict[str, Any], profile: str) -> list[ModelScore]:
    """Deterministic per-model scoring. Each model starts at 50 and is adjusted by signals."""
    cp = (ctx.get("consumption_pattern") or {})
    deal_size = float(ctx.get("deal_size_avg") or 0)
    customer_count = int(ctx.get("customer_count") or 0)
    value_drivers = ctx.get("value_drivers") or []
    adoption = (ctx.get("adoption_curve") or "").lower()
    competitor_models = ctx.get("competitor_pricing_models") or []

    seat_signal = float(cp.get("seat-based") or 0)
    usage_signal = float(cp.get("usage-based") or 0)
    value_signal = float(cp.get("value-based") or 0)
    hybrid_signal = float(cp.get("hybrid") or 0)

    scores = {m: ModelScore(model=m, score=50) for m in MODELS}

    # --- Subscription seat-based ---
    s = scores["subscription_seat_based"]
    if seat_signal >= 0.6:
        s.score += 20
        s.rationale.append(f"Strong seat-based consumption signal ({seat_signal:.2f}).")
    elif seat_signal >= 0.3:
        s.score += 8
        s.rationale.append(f"Moderate seat-based signal ({seat_signal:.2f}).")
    if usage_signal > 0.5 and seat_signal < 0.4:
        s.score -= 15
        s.tradeoffs.append("Usage variance is high; seat licensing leaves money on the table.")
    if deal_size > 0 and deal_size < 5000:
        s.score += 5
        s.rationale.append("SMB-friendly deal size — predictable seat math.")
    if "subscription" in " ".join(competitor_models).lower():
        s.score += 5
        s.rationale.append("Competitors already train the market on subscription.")
    s.tradeoffs.append("Predictable revenue, but customers feel friction when adding seats.")

    # --- Usage-based ---
    s = scores["usage_based"]
    if usage_signal >= 0.6:
        s.score += 25
        s.rationale.append(f"Strong usage-variance signal ({usage_signal:.2f}) — power-law users.")
    elif usage_signal >= 0.3:
        s.score += 10
        s.rationale.append(f"Moderate usage signal ({usage_signal:.2f}).")
    if seat_signal > 0.6 and usage_signal < 0.3:
        s.score -= 15
        s.tradeoffs.append("Usage is flat per seat; usage-based adds billing complexity for no upside.")
    if "api" in (ctx.get("industry") or "").lower() or profile == "api":
        s.score += 8
        s.rationale.append("API/infra products align naturally with usage metering.")
    if "usage" in " ".join(competitor_models).lower() or "consumption" in " ".join(competitor_models).lower():
        s.score += 5
        s.rationale.append("Competitive usage pricing trains the market.")
    s.tradeoffs.append("Aligned to value but introduces revenue unpredictability and bill-shock risk.")

    # --- Value-based ---
    s = scores["value_based"]
    measurable = any(
        kw in " ".join(value_drivers).lower()
        for kw in ["revenue", "cost saved", "time saved", "conversion", "fraud prevented", "downtime"]
    )
    if value_signal >= 0.6 and measurable:
        s.score += 25
        s.rationale.append("Customer value is measurable AND signaled as primary.")
    elif value_signal >= 0.4 and measurable:
        s.score += 15
        s.rationale.append("Value signal moderate, measurement plausible.")
    elif value_signal >= 0.4 and not measurable:
        s.score -= 10
        s.tradeoffs.append("Value signal present but no measurable driver — collapses to bad usage pricing.")
    if deal_size >= 50000:
        s.score += 10
        s.rationale.append("Enterprise deal size justifies bespoke value-pricing motion.")
    if customer_count > 0 and customer_count < 50:
        s.score += 5
        s.rationale.append("Small customer count supports per-customer value calibration.")
    if customer_count > 500:
        s.score -= 10
        s.tradeoffs.append("High customer count — value-based does not scale operationally.")
    s.tradeoffs.append("Highest yield model but requires instrumented ROI proof per customer.")

    # --- Freemium ---
    s = scores["freemium"]
    if adoption in ("viral", "bottom-up", "plg", "product-led"):
        s.score += 20
        s.rationale.append(f"Adoption curve '{adoption}' aligns with PLG/freemium funnel.")
    if customer_count > 1000:
        s.score += 10
        s.rationale.append("Large addressable user base supports freemium economics.")
    if deal_size > 25000:
        s.score -= 15
        s.tradeoffs.append("Enterprise ACV — freemium acquisition cost rarely amortizes.")
    if adoption in ("top-down", "enterprise"):
        s.score -= 15
        s.tradeoffs.append("Top-down sale — freemium dilutes positioning without unlocking pipeline.")
    s.tradeoffs.append("Powerful acquisition channel but free-tier cost-to-serve must be a small fraction of paid LTV.")

    # --- Hybrid (platform + usage, or seat + overage) ---
    s = scores["hybrid"]
    if hybrid_signal >= 0.5:
        s.score += 20
        s.rationale.append(f"Hybrid signal explicit ({hybrid_signal:.2f}).")
    if seat_signal >= 0.4 and usage_signal >= 0.4:
        s.score += 15
        s.rationale.append("Both seat AND usage drivers present — natural hybrid candidate.")
    if len(value_drivers) >= 3:
        s.score += 5
        s.rationale.append("Multiple value drivers — single model leaves segments under-served.")
    if deal_size < 1000:
        s.score -= 10
        s.tradeoffs.append("Small deal size — hybrid complexity is not worth the friction.")
    s.tradeoffs.append("Captures more value across segments but increases pricing-page complexity and CS overhead.")

    # Profile bias
    bias = PROFILES.get(profile, {})
    for m, b in bias.items():
        if m in scores:
            scores[m].score += b
            if b != 0:
                scores[m].rationale.append(f"Industry profile '{profile}' adjustment: {b:+d}.")

    # Clamp
    for s in scores.values():
        s.score = clamp(s.score)

    return sorted(scores.values(), key=lambda x: -x.score)


def render_markdown(ranked: list[ModelScore], ctx: dict[str, Any], profile: str) -> str:
    lines: list[str] = []
    lines.append("# Pricing Model Recommendation")
    lines.append("")
    lines.append(f"**Profile:** `{profile}`  •  **Industry:** {ctx.get('industry', 'unspecified')}")
    lines.append(f"**Deal size avg:** {ctx.get('deal_size_avg', 'n/a')}  •  **Customers:** {ctx.get('customer_count', 'n/a')}")
    lines.append("")
    lines.append("> This skill recommends a **model and trade-offs**, not a final price. The human owns the decision.")
    lines.append("")
    lines.append("## Ranked models")
    lines.append("")
    for i, s in enumerate(ranked, 1):
        marker = " *(top recommendation)*" if i == 1 else ""
        lines.append(f"### {i}. {s.model.replace('_', ' ').title()} — fit-score **{s.score}/100**{marker}")
        if s.rationale:
            lines.append("**Why it fits:**")
            for r in s.rationale:
                lines.append(f"- {r}")
        if s.tradeoffs:
            lines.append("**Trade-offs:**")
            for t in s.tradeoffs:
                lines.append(f"- {t}")
        lines.append("")
    lines.append("## Next steps")
    lines.append("1. Validate WTP for the top model with `wtp_analyzer.py` (≥ 30 respondents).")
    lines.append("2. Design tiers with `packaging_designer.py`.")
    lines.append("3. Pressure-test in pricing committee — this output is one input.")
    return "\n".join(lines)


def sample_context() -> dict[str, Any]:
    return {
        "industry": "B2B SaaS — sales intelligence",
        "deal_size_avg": 18000,
        "customer_count": 220,
        "value_drivers": ["revenue lift from better leads", "time saved in research", "conversion uplift"],
        "adoption_curve": "bottom-up",
        "consumption_pattern": {
            "seat-based": 0.45,
            "usage-based": 0.55,
            "value-based": 0.40,
            "hybrid": 0.50,
        },
        "competitor_pricing_models": ["subscription seat-based", "hybrid seat + usage overage"],
    }


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--input", type=Path, help="Path to customer-context JSON.")
    p.add_argument(
        "--profile",
        default="saas",
        choices=list(PROFILES.keys()),
        help="Industry profile for default tuning.",
    )
    p.add_argument("--output", default="markdown", choices=["markdown", "json"], help="Output format.")
    p.add_argument("--sample", action="store_true", help="Run with built-in sample context.")
    args = p.parse_args(argv)

    if args.sample:
        ctx = sample_context()
    elif args.input:
        ctx = json.loads(args.input.read_text())
    else:
        p.error("Provide --input or --sample.")
        return 2

    ranked = score_models(ctx, args.profile)
    if args.output == "json":
        out = {
            "profile": args.profile,
            "context": ctx,
            "ranked": [
                {"model": s.model, "score": s.score, "rationale": s.rationale, "tradeoffs": s.tradeoffs}
                for s in ranked
            ],
        }
        print(json.dumps(out, indent=2))
    else:
        print(render_markdown(ranked, ctx, args.profile))
    return 0


if __name__ == "__main__":
    sys.exit(main())
