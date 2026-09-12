#!/usr/bin/env python3
"""
score_investment.py

A structured scoring calculator for the stock-analysis skill.
Run this to compute a composite score and position sizing recommendation
based on the seven analytical dimensions.

Usage:
  python score_investment.py
  (interactive prompt)

Or import and call score() directly with a dict of scores.
"""

from dataclasses import dataclass
from typing import Optional


VOLATILITY_CLASSES = {
    "smooth_compounder": {"label": "Smooth compounder", "max_pct": 10.0, "example": "Visa, MSFT, Costco"},
    "quality_growth":    {"label": "Quality growth",    "max_pct": 8.0,  "example": "GOOGL, AAPL"},
    "volatile_growth":   {"label": "Volatile growth",   "max_pct": 5.0,  "example": "High-beta emerging leaders"},
    "cyclical":          {"label": "Cyclical",           "max_pct": 4.0,  "example": "FCX, CVX, JPM"},
    "turnaround":        {"label": "Turnaround",         "max_pct": 2.5,  "example": "Pre-profitability, thesis-change"},
    "speculative":       {"label": "Speculative",        "max_pct": 1.0,  "example": "Pre-revenue, binary outcome"},
}


@dataclass
class ScoreInput:
    ticker: str
    business_quality: float      # 1–10
    moat_durability: float        # 1–10
    financial_strength: float    # 1–10
    management_quality: float    # 1–10
    valuation_attractiveness: float  # 1–10
    thesis_clarity: float         # 1–10
    risk_reward_asymmetry: float  # 1–10
    volatility_class: str         # key from VOLATILITY_CLASSES
    current_position_pct: float   # e.g. 2.0 for 2%
    notes: Optional[str] = None


def compute_composite(s: ScoreInput) -> float:
    scores = [
        s.business_quality,
        s.moat_durability,
        s.financial_strength,
        s.management_quality,
        s.valuation_attractiveness,
        s.thesis_clarity,
        s.risk_reward_asymmetry,
    ]
    return round(sum(scores) / len(scores), 2)


def minimum_score(s: ScoreInput) -> tuple[str, float]:
    dims = {
        "Business quality": s.business_quality,
        "Moat durability": s.moat_durability,
        "Financial strength": s.financial_strength,
        "Management quality": s.management_quality,
        "Valuation attractiveness": s.valuation_attractiveness,
        "Thesis clarity": s.thesis_clarity,
        "Risk/reward asymmetry": s.risk_reward_asymmetry,
    }
    min_dim = min(dims, key=dims.get)
    return min_dim, dims[min_dim]


def target_position(s: ScoreInput) -> dict:
    composite = compute_composite(s)
    vc = VOLATILITY_CLASSES.get(s.volatility_class, VOLATILITY_CLASSES["volatile_growth"])
    max_pct = vc["max_pct"]

    # Composite → fraction of max
    if composite >= 8.0:
        fraction = 0.925
    elif composite >= 7.0:
        fraction = 0.725
    elif composite >= 6.0:
        fraction = 0.45
    elif composite >= 5.0:
        fraction = 0.225
    else:
        fraction = 0.1

    raw_target = round(max_pct * fraction, 2)

    # Minimum-score overrides (caps)
    min_dim, min_score_val = minimum_score(s)
    cap = None
    if s.thesis_clarity < 5:
        raw_target = min(raw_target, 1.5)
        cap = f"Thesis Clarity < 5 → capped at 1.5%"
    if s.financial_strength < 4:
        raw_target = min(raw_target, 2.0)
        cap = f"Financial Strength < 4 → capped at 2.0%"
    if s.risk_reward_asymmetry < 4:
        raw_target = min(raw_target, 2.0)
        cap = f"Risk/Reward < 4 → capped at 2.0%"
    if min_score_val <= 2:
        raw_target = min(raw_target, 1.0)
        cap = f"{min_dim} ≤ 2 → exploratory only, capped at 1.0%"

    target = round(raw_target, 2)

    # Action signal
    if target > s.current_position_pct * 1.25:
        action = "ADD — target is materially above current position"
    elif target < s.current_position_pct * 0.75:
        action = "TRIM — target is materially below current position"
    elif composite < 5.0:
        action = "REASSESS — composite below 5.0, consider exit"
    else:
        action = "HOLD — current position near target"

    return {
        "composite": composite,
        "max_pct": max_pct,
        "target_pct": target,
        "action": action,
        "cap_applied": cap,
    }


def conviction_label(composite: float, min_score_val: float) -> str:
    effective = min(composite, min_score_val * 1.2)  # weight minimum score
    if effective >= 7.5:
        return "High conviction"
    elif effective >= 6.0:
        return "Medium conviction"
    elif effective >= 4.5:
        return "Low conviction"
    else:
        return "Exploratory"


def format_report(s: ScoreInput) -> str:
    composite = compute_composite(s)
    tp = target_position(s)
    min_dim, min_val = minimum_score(s)
    conviction = conviction_label(composite, min_val)
    vc = VOLATILITY_CLASSES.get(s.volatility_class, VOLATILITY_CLASSES["volatile_growth"])

    lines = [
        f"{'='*60}",
        f"  STOCK ANALYSIS SCORE — {s.ticker.upper()}",
        f"{'='*60}",
        "",
        f"  {'Dimension':<30} {'Score':>6}",
        f"  {'-'*38}",
        f"  {'Business quality':<30} {s.business_quality:>6.1f}/10",
        f"  {'Moat durability':<30} {s.moat_durability:>6.1f}/10",
        f"  {'Financial strength':<30} {s.financial_strength:>6.1f}/10",
        f"  {'Management quality':<30} {s.management_quality:>6.1f}/10",
        f"  {'Valuation attractiveness':<30} {s.valuation_attractiveness:>6.1f}/10",
        f"  {'Thesis clarity':<30} {s.thesis_clarity:>6.1f}/10",
        f"  {'Risk/reward asymmetry':<30} {s.risk_reward_asymmetry:>6.1f}/10",
        f"  {'-'*38}",
        f"  {'COMPOSITE':<30} {composite:>6.2f}/10",
        "",
        f"  Minimum dimension: {min_dim} ({min_val}/10)",
        f"  Conviction level:  {conviction}",
        "",
        f"{'='*60}",
        f"  POSITION SIZING",
        f"{'='*60}",
        "",
        f"  Volatility class:  {vc['label']} (max {vc['max_pct']}%)",
        f"  Current position:  {s.current_position_pct}%",
        f"  Target position:   {tp['target_pct']}%",
        f"  Action signal:     {tp['action']}",
    ]

    if tp["cap_applied"]:
        lines.append(f"  Cap applied:       {tp['cap_applied']}")

    if s.notes:
        lines += ["", f"  Notes: {s.notes}"]

    lines += [
        "",
        f"{'='*60}",
        "  REMINDER: Write your sell triggers before acting.",
        f"{'='*60}",
    ]

    return "\n".join(lines)


def interactive():
    print("\nStock Analysis Scorer — Interactive Mode")
    print("Enter scores 1–10 for each dimension.\n")

    ticker = input("Ticker symbol: ").strip().upper()

    def get_score(prompt):
        while True:
            try:
                val = float(input(f"  {prompt} (1–10): "))
                if 1 <= val <= 10:
                    return val
                print("  Please enter a value between 1 and 10.")
            except ValueError:
                print("  Invalid input.")

    bq  = get_score("Business quality")
    md  = get_score("Moat durability")
    fs  = get_score("Financial strength")
    mq  = get_score("Management quality")
    va  = get_score("Valuation attractiveness")
    tc  = get_score("Thesis clarity")
    rr  = get_score("Risk/reward asymmetry")

    print("\nVolatility classes:")
    keys = list(VOLATILITY_CLASSES.keys())
    for i, k in enumerate(keys):
        vc = VOLATILITY_CLASSES[k]
        print(f"  {i+1}. {vc['label']} — max {vc['max_pct']}% ({vc['example']})")
    while True:
        try:
            vc_idx = int(input("Choose class (1–6): ")) - 1
            if 0 <= vc_idx < len(keys):
                vc_key = keys[vc_idx]
                break
        except ValueError:
            pass
        print("  Invalid selection.")

    while True:
        try:
            current_pct = float(input("Current position size (% of portfolio, e.g. 2.0): "))
            break
        except ValueError:
            print("  Invalid input.")

    notes = input("Optional notes (press Enter to skip): ").strip() or None

    s = ScoreInput(
        ticker=ticker,
        business_quality=bq,
        moat_durability=md,
        financial_strength=fs,
        management_quality=mq,
        valuation_attractiveness=va,
        thesis_clarity=tc,
        risk_reward_asymmetry=rr,
        volatility_class=vc_key,
        current_position_pct=current_pct,
        notes=notes,
    )

    print()
    print(format_report(s))


def score(scores_dict: dict) -> dict:
    """
    Programmatic interface. Pass a dict with keys matching ScoreInput fields.
    Returns a dict with composite, target_pct, action, conviction.
    """
    s = ScoreInput(**scores_dict)
    composite = compute_composite(s)
    tp = target_position(s)
    min_dim, min_val = minimum_score(s)
    conviction = conviction_label(composite, min_val)

    return {
        "composite": composite,
        "target_pct": tp["target_pct"],
        "action": tp["action"],
        "conviction": conviction,
        "cap_applied": tp["cap_applied"],
        "report": format_report(s),
    }


if __name__ == "__main__":
    interactive()
