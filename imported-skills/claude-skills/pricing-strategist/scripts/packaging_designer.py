#!/usr/bin/env python3
"""packaging_designer.py — Good/Better/Best tier designer with anti-pattern detection.

Input: JSON with feature list (importance + cost-to-serve), customer segments, and
current pricing. Output: 3-tier packaging assignment with anti-pattern flags.

Deterministic logic — features are bucketed into tiers by importance × segment-fit.
No LLM calls.

Usage:
    packaging_designer.py --input features.json --profile saas --output markdown
    packaging_designer.py --sample
"""
from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

PROFILES = {
    "saas": {"good_pct": 0.50, "better_pct": 0.30, "best_pct": 0.20, "price_ratio_good_to_better": 2.5, "price_ratio_better_to_best": 2.0},
    "api": {"good_pct": 0.40, "better_pct": 0.30, "best_pct": 0.30, "price_ratio_good_to_better": 3.0, "price_ratio_better_to_best": 2.5},
    "enterprise": {"good_pct": 0.30, "better_pct": 0.35, "best_pct": 0.35, "price_ratio_good_to_better": 2.0, "price_ratio_better_to_best": 2.5},
    "prosumer": {"good_pct": 0.60, "better_pct": 0.25, "best_pct": 0.15, "price_ratio_good_to_better": 3.0, "price_ratio_better_to_best": 2.0},
}


@dataclass
class Feature:
    name: str
    importance: float       # 0..1, how much customers value it
    cost_to_serve: float    # relative cost units
    segment_fit: dict[str, float] = field(default_factory=dict)  # segment → fit 0..1

    @classmethod
    def from_dict(cls, d: dict[str, Any]) -> "Feature":
        return cls(
            name=d["name"],
            importance=float(d.get("importance", 0.5)),
            cost_to_serve=float(d.get("cost_to_serve", 1.0)),
            segment_fit=d.get("segment_fit", {}),
        )


@dataclass
class Tier:
    name: str
    features: list[Feature] = field(default_factory=list)
    price: float = 0.0


def assign_tiers(features: list[Feature], segments: list[str], profile: str) -> dict[str, Tier]:
    """Assign each feature to Good / Better / Best based on importance and segment fit.

    Rule: high importance across all segments → Good (base).
          mid importance OR segment-skewed to mid → Better.
          low importance OR enterprise-skewed OR high cost-to-serve → Best.
    """
    good = Tier("Good")
    better = Tier("Better")
    best = Tier("Best")

    # Identify enterprise-leaning segments (last in declared order is convention)
    enterprise_seg = segments[-1] if segments else None

    for f in features:
        avg_fit = sum(f.segment_fit.values()) / len(f.segment_fit) if f.segment_fit else 0.5
        enterprise_fit = f.segment_fit.get(enterprise_seg, avg_fit) if enterprise_seg else avg_fit

        # High importance + broad fit → Good
        if f.importance >= 0.75 and avg_fit >= 0.6 and f.cost_to_serve <= 2.0:
            good.features.append(f)
        # Enterprise-skewed OR high cost → Best
        elif enterprise_fit >= 0.7 and avg_fit < 0.6:
            best.features.append(f)
        elif f.cost_to_serve >= 3.0:
            best.features.append(f)
        elif f.importance <= 0.4:
            best.features.append(f)
        # Everything else → Better
        else:
            better.features.append(f)

    return {"good": good, "better": better, "best": best}


def price_tiers(tiers: dict[str, Tier], current_pricing: dict[str, float], profile: str) -> None:
    """Anchor pricing to current_pricing if provided; else use profile ratios from a base of 100."""
    cfg = PROFILES[profile]
    if current_pricing.get("good"):
        tiers["good"].price = float(current_pricing["good"])
    else:
        tiers["good"].price = 100.0
    if current_pricing.get("better"):
        tiers["better"].price = float(current_pricing["better"])
    else:
        tiers["better"].price = tiers["good"].price * cfg["price_ratio_good_to_better"]
    if current_pricing.get("best"):
        tiers["best"].price = float(current_pricing["best"])
    else:
        tiers["best"].price = tiers["better"].price * cfg["price_ratio_better_to_best"]


def detect_anti_patterns(tiers: dict[str, Tier]) -> list[str]:
    """Return list of human-readable anti-pattern flags."""
    flags: list[str] = []
    good, better, best = tiers["good"], tiers["better"], tiers["best"]

    # 1. Empty tier
    for t in (good, better, best):
        if not t.features:
            flags.append(f"Empty tier: '{t.name}' has no features — collapse or re-balance.")

    # 2. Feature in all tiers (no differentiation)
    good_names = {f.name for f in good.features}
    better_names = {f.name for f in better.features}
    best_names = {f.name for f in best.features}
    all_three = good_names & better_names & best_names
    if all_three:
        flags.append(f"No differentiation: features appear in all 3 tiers — {sorted(all_three)}.")

    # 3. Feature dump in Best (>2x the count of Better with <1.5x the price)
    if better.features and best.features and better.price > 0 and best.price > 0:
        feature_ratio = len(best.features) / max(1, len(better.features))
        price_ratio = best.price / better.price
        if feature_ratio > 2.0 and price_ratio < 1.5:
            flags.append(
                f"Feature dump in Best: {len(best.features)} features vs Better's {len(better.features)} "
                f"({feature_ratio:.1f}x) for only {price_ratio:.1f}x the price — customers will buy Better and never upgrade."
            )

    # 4. Best tier > 2x Better price with < 1.5x value (proxy: feature count weighted by importance)
    def value(t: Tier) -> float:
        return sum(f.importance for f in t.features)
    if better.price > 0 and best.price > 0 and value(better) > 0:
        price_jump = best.price / better.price
        value_jump = value(best) / value(better)
        if price_jump > 2.0 and value_jump < 1.5:
            flags.append(
                f"Best tier price-to-value mismatch: {price_jump:.1f}x price for only {value_jump:.1f}x value — "
                "Best becomes a decoy that no one upgrades to."
            )

    # 5. No clear upgrade trigger from Good → Better
    if good.features and better.features:
        good_imp = sum(f.importance for f in good.features) / len(good.features)
        better_imp = sum(f.importance for f in better.features) / len(better.features)
        if better_imp < good_imp - 0.1:
            flags.append(
                "No clear upgrade trigger Good → Better: Better-tier features have lower avg importance than Good. "
                "Why would a Good customer ever upgrade?"
            )

    # 6. Bronze tier as loss leader (cost-to-serve > effective price share)
    if good.features and good.price > 0:
        good_cost = sum(f.cost_to_serve for f in good.features)
        if good_cost > good.price * 0.8:
            flags.append(
                f"Good tier near loss-leader: cost-to-serve ({good_cost:.1f}) > 80% of price ({good.price:.2f}). "
                "Either raise the price floor or strip a feature down to Better."
            )

    # 7. Best tier "Enterprise — call us" with no anchor
    if best.price == 0 and best.features:
        flags.append(
            "Best/Enterprise tier has no published anchor price. 'Call us' without a starting number "
            "loses prospects to competitors who publish ranges."
        )

    return flags


def render_markdown(tiers: dict[str, Tier], flags: list[str], profile: str, segments: list[str]) -> str:
    lines: list[str] = []
    lines.append("# Packaging Recommendation: Good / Better / Best")
    lines.append("")
    lines.append(f"**Profile:** `{profile}`  •  **Segments:** {', '.join(segments) if segments else 'unspecified'}")
    lines.append("")
    for key in ("good", "better", "best"):
        t = tiers[key]
        lines.append(f"## {t.name} — ${t.price:,.2f}")
        if t.features:
            for f in t.features:
                lines.append(f"- **{f.name}** (importance={f.importance:.2f}, cost-to-serve={f.cost_to_serve:.1f})")
        else:
            lines.append("- *(no features assigned)*")
        lines.append("")
    if flags:
        lines.append("## Anti-pattern flags")
        for f in flags:
            lines.append(f"- {f}")
    else:
        lines.append("## Anti-pattern flags")
        lines.append("- None detected.")
    lines.append("")
    lines.append("## Notes")
    lines.append("- Prices are a **starting frame**, not the final number. Validate with Van Westendorp PSM.")
    lines.append("- Re-run after every meaningful feature addition; tier balance drifts as the product grows.")
    return "\n".join(lines)


def sample_input() -> dict[str, Any]:
    return {
        "segments": ["SMB", "Mid-market", "Enterprise"],
        "current_pricing": {"good": 49, "better": 149, "best": 499},
        "features": [
            {"name": "Core dashboard", "importance": 0.95, "cost_to_serve": 0.5, "segment_fit": {"SMB": 1.0, "Mid-market": 1.0, "Enterprise": 1.0}},
            {"name": "Basic reporting", "importance": 0.85, "cost_to_serve": 0.8, "segment_fit": {"SMB": 0.9, "Mid-market": 0.9, "Enterprise": 0.8}},
            {"name": "API access", "importance": 0.6, "cost_to_serve": 1.5, "segment_fit": {"SMB": 0.3, "Mid-market": 0.7, "Enterprise": 0.9}},
            {"name": "Advanced analytics", "importance": 0.65, "cost_to_serve": 2.0, "segment_fit": {"SMB": 0.2, "Mid-market": 0.8, "Enterprise": 0.9}},
            {"name": "Custom workflows", "importance": 0.55, "cost_to_serve": 2.5, "segment_fit": {"SMB": 0.1, "Mid-market": 0.5, "Enterprise": 0.9}},
            {"name": "SSO / SAML", "importance": 0.4, "cost_to_serve": 1.0, "segment_fit": {"SMB": 0.05, "Mid-market": 0.4, "Enterprise": 1.0}},
            {"name": "SLA + dedicated CSM", "importance": 0.3, "cost_to_serve": 5.0, "segment_fit": {"SMB": 0.0, "Mid-market": 0.2, "Enterprise": 1.0}},
            {"name": "On-prem deployment", "importance": 0.2, "cost_to_serve": 4.0, "segment_fit": {"SMB": 0.0, "Mid-market": 0.1, "Enterprise": 0.9}},
            {"name": "Audit logs", "importance": 0.5, "cost_to_serve": 0.8, "segment_fit": {"SMB": 0.1, "Mid-market": 0.5, "Enterprise": 0.95}},
        ],
    }


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--input", type=Path, help="Path to features JSON.")
    p.add_argument("--profile", default="saas", choices=list(PROFILES.keys()), help="Industry profile.")
    p.add_argument("--output", default="markdown", choices=["markdown", "json"], help="Output format.")
    p.add_argument("--sample", action="store_true", help="Run with built-in sample data.")
    args = p.parse_args(argv)

    if args.sample:
        data = sample_input()
    elif args.input:
        data = json.loads(args.input.read_text())
    else:
        p.error("Provide --input or --sample.")
        return 2

    segments = data.get("segments", [])
    current_pricing = data.get("current_pricing", {})
    features = [Feature.from_dict(f) for f in data.get("features", [])]

    tiers = assign_tiers(features, segments, args.profile)
    price_tiers(tiers, current_pricing, args.profile)
    flags = detect_anti_patterns(tiers)

    if args.output == "json":
        out = {
            "profile": args.profile,
            "segments": segments,
            "tiers": {
                k: {
                    "name": t.name,
                    "price": t.price,
                    "features": [{"name": f.name, "importance": f.importance, "cost_to_serve": f.cost_to_serve} for f in t.features],
                }
                for k, t in tiers.items()
            },
            "anti_pattern_flags": flags,
        }
        print(json.dumps(out, indent=2))
    else:
        print(render_markdown(tiers, flags, args.profile, segments))
    return 0


if __name__ == "__main__":
    sys.exit(main())
