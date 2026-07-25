#!/usr/bin/env python3
"""
Growth Model Simulator
----------------------
Projects MRR growth across different growth models (PLG, sales-led, community-led,
hybrid) and shows the impact of channel mix changes on growth trajectory.

Usage:
    python growth_model_simulator.py

Inputs (edit INPUTS section):
    - Starting MRR and churn rate
    - Current channel mix (% of new MRR from each source)
    - Conversion rates per model
    - Growth rate assumptions per channel

Outputs:
    - 12-month MRR projection by growth model
    - Channel mix impact analysis (what happens if you shift mix)
    - Break-even months for each model
    - Side-by-side comparison table
"""

from __future__ import annotations
import math
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple


# ---------------------------------------------------------------------------
# Data models
# ---------------------------------------------------------------------------

@dataclass
class ChannelSource:
    name: str
    pct_of_new_mrr: float      # Current share of new MRR (0.0–1.0)
    monthly_growth_rate: float  # How fast this channel grows month-over-month
    cac: float                  # CAC in dollars
    payback_months: float       # Months to recover CAC


@dataclass
class GrowthModel:
    name: str
    description: str
    channel_mix: Dict[str, float]  # channel name → % of new MRR
    new_mrr_monthly_base: float    # Starting new MRR/month from this model
    monthly_acceleration: float    # Acceleration factor (compounding)
    avg_ltv_cac: float             # Expected LTV:CAC at scale
    months_to_steady_state: int    # Months before model hits its natural growth rate
    notes: List[str] = field(default_factory=list)


@dataclass
class MonthSnapshot:
    month: int
    mrr: float
    new_mrr: float
    churned_mrr: float
    expansion_mrr: float
    net_new_mrr: float
    cumulative_cac_spend: float


@dataclass
class ModelProjection:
    model: GrowthModel
    snapshots: List[MonthSnapshot]
    break_even_month: Optional[int]  # Month when cumulative revenue > cumulative CAC


# ---------------------------------------------------------------------------
# INPUTS — edit these
# ---------------------------------------------------------------------------

STARTING_MRR = 85_000         # Current MRR ($)
MONTHLY_CHURN_RATE = 0.012    # Monthly churn rate (1.2% = ~14% annual)
EXPANSION_RATE = 0.008        # Monthly expansion MRR as % of existing MRR
GROSS_MARGIN = 0.75
SIMULATION_MONTHS = 18

# Channel sources (used to model mix shift scenarios)
CHANNELS: List[ChannelSource] = [
    ChannelSource("Organic/SEO",      pct_of_new_mrr=0.28, monthly_growth_rate=0.04, cac=1_800,  payback_months=9),
    ChannelSource("PLG Self-Serve",   pct_of_new_mrr=0.15, monthly_growth_rate=0.08, cac=900,   payback_months=5),
    ChannelSource("Outbound SDR",     pct_of_new_mrr=0.25, monthly_growth_rate=0.02, cac=5_100,  payback_months=21),
    ChannelSource("Paid Search",      pct_of_new_mrr=0.15, monthly_growth_rate=0.01, cac=6_200,  payback_months=26),
    ChannelSource("Events/Field",     pct_of_new_mrr=0.08, monthly_growth_rate=0.01, cac=9_800,  payback_months=41),
    ChannelSource("Partner/Channel",  pct_of_new_mrr=0.09, monthly_growth_rate=0.05, cac=3_400,  payback_months=14),
]

# Growth models to simulate
GROWTH_MODELS: List[GrowthModel] = [
    GrowthModel(
        name="Current Mix",
        description="Baseline — maintain current channel allocation",
        channel_mix={"Organic/SEO": 0.28, "PLG Self-Serve": 0.15, "Outbound SDR": 0.25,
                     "Paid Search": 0.15, "Events/Field": 0.08, "Partner/Channel": 0.09},
        new_mrr_monthly_base=12_000,
        monthly_acceleration=0.025,
        avg_ltv_cac=3.2,
        months_to_steady_state=3,
        notes=["Baseline. No changes to channel mix."],
    ),
    GrowthModel(
        name="PLG-First",
        description="Shift budget toward PLG self-serve and organic; reduce paid and outbound",
        channel_mix={"Organic/SEO": 0.35, "PLG Self-Serve": 0.35, "Outbound SDR": 0.10,
                     "Paid Search": 0.08, "Events/Field": 0.04, "Partner/Channel": 0.08},
        new_mrr_monthly_base=9_500,   # Slower start — PLG takes time to activate
        monthly_acceleration=0.048,   # But compounds faster
        avg_ltv_cac=5.8,
        months_to_steady_state=6,     # PLG loops take time to build
        notes=[
            "Lower new MRR in months 1-6 while PLG loops activate.",
            "Acceleration compounds strongly after month 6.",
            "Requires product investment in activation/onboarding.",
            "Best fit if time-to-value < 30 min and viral coefficient > 0.3.",
        ],
    ),
    GrowthModel(
        name="Sales-Led Scale",
        description="Double down on outbound SDR and field; optimize for enterprise ACV",
        channel_mix={"Organic/SEO": 0.20, "PLG Self-Serve": 0.05, "Outbound SDR": 0.40,
                     "Paid Search": 0.15, "Events/Field": 0.15, "Partner/Channel": 0.05},
        new_mrr_monthly_base=15_000,  # Higher new MRR from enterprise ACV
        monthly_acceleration=0.018,   # Linear growth — headcount-constrained
        avg_ltv_cac=2.8,
        months_to_steady_state=2,
        notes=[
            "Fastest short-term new MRR if ACV > $30K.",
            "Growth is linear — adds headcount to add pipeline.",
            "CAC and payback worsen as SDR market tightens.",
            "Requires sales capacity increase to sustain.",
        ],
    ),
    GrowthModel(
        name="Community-Led",
        description="Invest in community and content; reduce paid; long-term brand play",
        channel_mix={"Organic/SEO": 0.45, "PLG Self-Serve": 0.15, "Outbound SDR": 0.15,
                     "Paid Search": 0.05, "Events/Field": 0.10, "Partner/Channel": 0.10},
        new_mrr_monthly_base=7_000,   # Slowest start
        monthly_acceleration=0.038,
        avg_ltv_cac=4.5,
        months_to_steady_state=9,     # Community takes longest to activate
        notes=[
            "Lowest new MRR in months 1-9.",
            "Community trust drives lower CAC and higher retention at scale.",
            "Best for categories where buyers seek peer validation.",
            "Requires dedicated community manager from day one.",
        ],
    ),
    GrowthModel(
        name="Hybrid PLS",
        description="PLG self-serve for SMB + sales-assisted for enterprise (Product-Led Sales)",
        channel_mix={"Organic/SEO": 0.30, "PLG Self-Serve": 0.28, "Outbound SDR": 0.22,
                     "Paid Search": 0.08, "Events/Field": 0.06, "Partner/Channel": 0.06},
        new_mrr_monthly_base=11_000,
        monthly_acceleration=0.035,
        avg_ltv_cac=4.1,
        months_to_steady_state=4,
        notes=[
            "PLG handles SMB; sales closes enterprise with PQL signals.",
            "Requires clear PQL definition and SDR/PLG handoff process.",
            "Best if you have a product with both bottom-up and top-down adoption.",
        ],
    ),
]


# ---------------------------------------------------------------------------
# Simulation engine
# ---------------------------------------------------------------------------

def simulate_model(model: GrowthModel, months: int) -> ModelProjection:
    snapshots: List[MonthSnapshot] = []
    mrr = STARTING_MRR
    cumulative_cac = 0.0
    cumulative_revenue = 0.0
    break_even_month = None

    for m in range(1, months + 1):
        # Ramp up — new_mrr accelerates each month
        if m <= model.months_to_steady_state:
            # Ramp phase: linear ramp from 60% to 100% of base
            ramp_factor = 0.6 + 0.4 * (m / model.months_to_steady_state)
        else:
            # Steady state: compound acceleration
            months_past_ramp = m - model.months_to_steady_state
            ramp_factor = 1.0 + model.monthly_acceleration * months_past_ramp

        new_mrr = model.new_mrr_monthly_base * ramp_factor
        churned_mrr = mrr * MONTHLY_CHURN_RATE
        expansion_mrr = mrr * EXPANSION_RATE
        net_new_mrr = new_mrr - churned_mrr + expansion_mrr
        mrr = mrr + net_new_mrr

        # CAC spend approximation: new_mrr / (avg_deal_mrr) * blended_cac
        # Use weighted CAC from channel mix
        weighted_cac = _weighted_cac(model.channel_mix)
        avg_deal_mrr = 1_500  # Assumption: $1,500 average deal MRR
        deals_this_month = new_mrr / avg_deal_mrr
        cac_spend = deals_this_month * weighted_cac
        cumulative_cac += cac_spend
        cumulative_revenue += mrr * GROSS_MARGIN

        if break_even_month is None and cumulative_revenue >= cumulative_cac:
            break_even_month = m

        snapshots.append(MonthSnapshot(
            month=m,
            mrr=mrr,
            new_mrr=new_mrr,
            churned_mrr=churned_mrr,
            expansion_mrr=expansion_mrr,
            net_new_mrr=net_new_mrr,
            cumulative_cac_spend=cumulative_cac,
        ))

    return ModelProjection(
        model=model,
        snapshots=snapshots,
        break_even_month=break_even_month,
    )


def _weighted_cac(channel_mix: Dict[str, float]) -> float:
    channel_cac = {ch.name: ch.cac for ch in CHANNELS}
    total = sum(
        channel_mix.get(name, 0) * cac
        for name, cac in channel_cac.items()
    )
    weight_sum = sum(channel_mix.values())
    return total / weight_sum if weight_sum > 0 else 5_000


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------

def fmt_mrr(n: float) -> str:
    if n >= 1_000_000:
        return f"${n/1_000_000:.3f}M"
    return f"${n/1_000:.1f}K"


def fmt_currency(n: float) -> str:
    if n >= 1_000_000:
        return f"${n/1_000_000:.2f}M"
    if n >= 1_000:
        return f"${n/1_000:.1f}K"
    return f"${n:.0f}"


def print_header(title: str) -> None:
    width = 78
    print("\n" + "=" * width)
    print(f"  {title}")
    print("=" * width)


def print_channel_overview() -> None:
    print_header("Current Channel Mix")
    print(f"  Starting MRR: {fmt_mrr(STARTING_MRR)}  |  Monthly churn: {MONTHLY_CHURN_RATE:.1%}  |  Expansion: {EXPANSION_RATE:.1%}/mo")
    print()
    print(f"  {'Channel':<22} {'% MRR':>7} {'CAC':>8} {'Payback':>9} {'Growth/mo':>10}")
    print("  " + "-" * 60)
    for ch in sorted(CHANNELS, key=lambda c: c.pct_of_new_mrr, reverse=True):
        print(
            f"  {ch.name:<22} {ch.pct_of_new_mrr:>6.0%} "
            f"{fmt_currency(ch.cac):>8} {ch.payback_months:>7.0f}mo "
            f"{ch.monthly_growth_rate:>9.1%}"
        )


def print_model_detail(proj: ModelProjection) -> None:
    model = proj.model
    print_header(f"Model: {model.name}")
    print(f"  {model.description}")
    if model.notes:
        print()
        for note in model.notes:
            print(f"  • {note}")
    print()

    # Print monthly snapshot (every 3 months + final)
    milestones = set(range(3, SIMULATION_MONTHS + 1, 3)) | {SIMULATION_MONTHS}
    print(f"  {'Month':<7} {'MRR':>10} {'New MRR':>9} {'Churned':>9} {'Expand':>8} {'Net New':>9}")
    print("  " + "-" * 56)
    for snap in proj.snapshots:
        if snap.month in milestones:
            print(
                f"  {snap.month:<7} {fmt_mrr(snap.mrr):>10} "
                f"{fmt_mrr(snap.new_mrr):>9} {fmt_mrr(snap.churned_mrr):>9} "
                f"{fmt_mrr(snap.expansion_mrr):>8} {fmt_mrr(snap.net_new_mrr):>9}"
            )

    final = proj.snapshots[-1]
    growth_x = final.mrr / STARTING_MRR
    arr_final = final.mrr * 12
    weighted_cac = _weighted_cac(model.channel_mix)
    be = f"Month {proj.break_even_month}" if proj.break_even_month else f"> {SIMULATION_MONTHS}mo"

    print()
    print(f"  Final MRR ({SIMULATION_MONTHS}mo):    {fmt_mrr(final.mrr)}")
    print(f"  Final ARR:             {fmt_currency(arr_final)}")
    print(f"  Growth multiple:       {growth_x:.1f}x from starting MRR")
    print(f"  Weighted blended CAC:  {fmt_currency(weighted_cac)}")
    print(f"  Expected LTV:CAC:      {model.avg_ltv_cac:.1f}x")
    print(f"  Months to steady state:{model.months_to_steady_state}")
    print(f"  CAC break-even:        {be}")


def print_comparison_table(projections: List[ModelProjection]) -> None:
    print_header(f"Growth Model Comparison — Month {SIMULATION_MONTHS} Outcomes")
    header = (
        f"  {'Model':<20} {'MRR (final)':>12} {'ARR (final)':>12} "
        f"{'Growth':>7} {'LTV:CAC':>8} {'Break-even':>11}"
    )
    print(header)
    print("  " + "-" * 74)
    for proj in sorted(projections, key=lambda p: p.snapshots[-1].mrr, reverse=True):
        final = proj.snapshots[-1]
        growth_x = final.mrr / STARTING_MRR
        arr_final = final.mrr * 12
        be = f"Mo {proj.break_even_month}" if proj.break_even_month else f">{SIMULATION_MONTHS}mo"
        print(
            f"  {proj.model.name:<20} {fmt_mrr(final.mrr):>12} "
            f"{fmt_currency(arr_final):>12} {growth_x:>6.1f}x "
            f"{proj.model.avg_ltv_cac:>7.1f}x {be:>11}"
        )


def print_channel_mix_impact(projections: List[ModelProjection]) -> None:
    print_header("Channel Mix Impact Analysis")
    print("  How shifting channel mix changes growth trajectory:\n")
    baseline = next((p for p in projections if p.model.name == "Current Mix"), None)
    if not baseline:
        return
    baseline_final_mrr = baseline.snapshots[-1].mrr

    for proj in projections:
        if proj.model.name == "Current Mix":
            continue
        final_mrr = proj.snapshots[-1].mrr
        delta = final_mrr - baseline_final_mrr
        delta_pct = (delta / baseline_final_mrr) * 100
        arrow = "↑" if delta > 0 else "↓"
        m6_mrr = proj.snapshots[5].mrr if len(proj.snapshots) >= 6 else 0
        m6_baseline = baseline.snapshots[5].mrr if len(baseline.snapshots) >= 6 else 0
        m6_delta = m6_mrr - m6_baseline
        m6_pct = (m6_delta / m6_baseline) * 100 if m6_baseline else 0
        m6_arrow = "↑" if m6_delta > 0 else "↓"

        print(f"  {proj.model.name}:")
        print(f"    Month 6:  {m6_arrow} {abs(m6_pct):.1f}%  vs. current  ({fmt_mrr(m6_delta)} {'more' if m6_delta > 0 else 'less'} MRR)")
        print(f"    Month {SIMULATION_MONTHS}: {arrow} {abs(delta_pct):.1f}%  vs. current  ({fmt_mrr(delta)} {'more' if delta > 0 else 'less'} MRR)")
        if proj.model.months_to_steady_state > 4:
            print(f"    ⚠ Model takes {proj.model.months_to_steady_state} months to reach steady state — short-term dip expected.")
        print()


def print_decision_guide(projections: List[ModelProjection]) -> None:
    print_header("Decision Guide")
    print("  Choose your growth model based on your constraints:\n")
    guides = [
        ("ACV < $5K and fast time-to-value",         "PLG-First"),
        ("ACV > $25K and complex buying process",     "Sales-Led Scale"),
        ("Strong practitioner community exists",      "Community-Led"),
        ("Both SMB self-serve and enterprise buyers", "Hybrid PLS"),
        ("Uncertain — keep optionality",              "Current Mix"),
    ]
    for condition, model_name in guides:
        proj = next((p for p in projections if p.model.name == model_name), None)
        if proj:
            final_mrr = proj.snapshots[-1].mrr
            print(f"  If: {condition}")
            print(f"  → Use {model_name} → {fmt_mrr(final_mrr)} MRR at month {SIMULATION_MONTHS}")
            print()

    print("  Key question before switching models:")
    print("    'Do we have 12-18 months of runway to prove the new model")
    print("     while the current model continues in parallel?'")
    print("    If no → optimize current model. Don't switch.")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> None:
    print_channel_overview()

    projections = [simulate_model(model, SIMULATION_MONTHS) for model in GROWTH_MODELS]

    for proj in projections:
        print_model_detail(proj)

    print_comparison_table(projections)
    print_channel_mix_impact(projections)
    print_decision_guide(projections)

    print("\n" + "=" * 78)
    print("  Notes:")
    print(f"    Starting MRR:   {fmt_mrr(STARTING_MRR)}")
    print(f"    Simulation:     {SIMULATION_MONTHS} months")
    print(f"    Churn:          {MONTHLY_CHURN_RATE:.1%}/mo ({MONTHLY_CHURN_RATE*12:.0%} annualized)")
    print(f"    Expansion:      {EXPANSION_RATE:.1%}/mo of existing MRR")
    print(f"    Gross margin:   {GROSS_MARGIN:.0%}")
    print("    Acceleration rates are estimates — validate against your actuals.")
    print("=" * 78 + "\n")


if __name__ == "__main__":
    main()
