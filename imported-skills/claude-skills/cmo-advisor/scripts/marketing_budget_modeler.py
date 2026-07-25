#!/usr/bin/env python3
"""
Marketing Budget Modeler
------------------------
Allocates marketing budget across channels based on CAC efficiency and
target MQL volume. Models conservative / moderate / aggressive scenarios.

Usage:
    python marketing_budget_modeler.py

Inputs (edit INPUTS section below or extend with argparse):
    - Annual revenue target (new ARR)
    - Average selling price (ASP)
    - Conversion rates by funnel stage
    - Historical CAC per channel
    - Channel capacity constraints (max MQLs the channel can realistically produce)

Outputs:
    - Required MQL volume by channel
    - Budget allocation per channel per scenario
    - LTV:CAC and payback period per channel
    - Summary table across scenarios
"""

from __future__ import annotations
import math
from dataclasses import dataclass, field
from typing import Dict, List, Tuple


# ---------------------------------------------------------------------------
# Data models
# ---------------------------------------------------------------------------

@dataclass
class Channel:
    name: str
    cac: float              # Customer acquisition cost ($)
    max_mqls_per_month: int # Realistic capacity ceiling (MQLs/month)
    mql_to_close_rate: float  # Combined MQL → closed-won rate (0.0–1.0)
    payback_months: float   # Based on ARPU × gross margin
    ltv: float              # Lifetime value ($)
    trend: str = "stable"   # "improving" | "stable" | "declining"


@dataclass
class FunnelRates:
    mql_to_sal: float     # MQL → Sales Accepted Lead
    sal_to_sql: float     # SAL → Sales Qualified Lead
    sql_to_opp: float     # SQL → Opportunity
    opp_to_close: float   # Opportunity → Closed-Won

    @property
    def mql_to_close(self) -> float:
        return self.mql_to_sal * self.sal_to_sql * self.sql_to_opp * self.opp_to_close


@dataclass
class ScenarioResult:
    name: str
    total_budget: float
    channel_budgets: Dict[str, float]
    channel_mqls: Dict[str, int]
    projected_customers: int
    projected_arr: float
    blended_cac: float
    notes: List[str] = field(default_factory=list)


# ---------------------------------------------------------------------------
# INPUTS — edit these
# ---------------------------------------------------------------------------

TARGET_NEW_ARR = 3_000_000      # New ARR to generate this year ($)
ASP_ANNUAL = 18_000             # Average annual contract value ($)
GROSS_MARGIN = 0.75             # Product gross margin (%)
ARPU_MONTHLY = ASP_ANNUAL / 12  # Monthly revenue per account

FUNNEL = FunnelRates(
    mql_to_sal=0.65,
    sal_to_sql=0.45,
    sql_to_opp=0.75,
    opp_to_close=0.27,
)

# LTV = ARPU_monthly × gross_margin / monthly_churn_rate
MONTHLY_CHURN = 0.012   # ~14% annual churn
LTV = (ARPU_MONTHLY * GROSS_MARGIN) / MONTHLY_CHURN

CHANNELS: List[Channel] = [
    Channel(
        name="Organic SEO",
        cac=1_800,
        max_mqls_per_month=80,
        mql_to_close_rate=FUNNEL.mql_to_close,
        payback_months=(1_800 / (ARPU_MONTHLY * GROSS_MARGIN)),
        ltv=LTV,
        trend="improving",
    ),
    Channel(
        name="Paid Search",
        cac=6_200,
        max_mqls_per_month=60,
        mql_to_close_rate=FUNNEL.mql_to_close,
        payback_months=(6_200 / (ARPU_MONTHLY * GROSS_MARGIN)),
        ltv=LTV,
        trend="stable",
    ),
    Channel(
        name="Paid Social (LinkedIn)",
        cac=8_500,
        max_mqls_per_month=35,
        mql_to_close_rate=FUNNEL.mql_to_close,
        payback_months=(8_500 / (ARPU_MONTHLY * GROSS_MARGIN)),
        ltv=LTV,
        trend="declining",
    ),
    Channel(
        name="Outbound SDR",
        cac=5_100,
        max_mqls_per_month=50,
        mql_to_close_rate=FUNNEL.mql_to_close,
        payback_months=(5_100 / (ARPU_MONTHLY * GROSS_MARGIN)),
        ltv=LTV,
        trend="stable",
    ),
    Channel(
        name="Events / Field",
        cac=9_800,
        max_mqls_per_month=25,
        mql_to_close_rate=FUNNEL.mql_to_close,
        payback_months=(9_800 / (ARPU_MONTHLY * GROSS_MARGIN)),
        ltv=LTV,
        trend="stable",
    ),
    Channel(
        name="Partner / Channel",
        cac=3_400,
        max_mqls_per_month=30,
        mql_to_close_rate=FUNNEL.mql_to_close,
        payback_months=(3_400 / (ARPU_MONTHLY * GROSS_MARGIN)),
        ltv=LTV,
        trend="improving",
    ),
    Channel(
        name="Content / Inbound",
        cac=2_600,
        max_mqls_per_month=45,
        mql_to_close_rate=FUNNEL.mql_to_close,
        payback_months=(2_600 / (ARPU_MONTHLY * GROSS_MARGIN)),
        ltv=LTV,
        trend="improving",
    ),
]


# ---------------------------------------------------------------------------
# Core calculations
# ---------------------------------------------------------------------------

def customers_needed(target_arr: float, asp: float) -> int:
    return math.ceil(target_arr / asp)


def mqls_needed_total(customers: int, mql_to_close: float) -> int:
    return math.ceil(customers / mql_to_close)


def ltv_to_cac(ltv: float, cac: float) -> float:
    return ltv / cac if cac > 0 else 0.0


def score_channel(ch: Channel) -> float:
    """
    Score a channel for budget priority.
    Higher = more efficient. Used to rank allocation order.
    Factors: LTV:CAC ratio, trend multiplier, capacity.
    """
    ratio = ltv_to_cac(ch.ltv, ch.cac)
    trend_mult = {"improving": 1.2, "stable": 1.0, "declining": 0.7}.get(ch.trend, 1.0)
    return ratio * trend_mult


def allocate_mqls(
    channels: List[Channel],
    total_mqls_needed: int,
    budget_multiplier: float = 1.0,
) -> Tuple[Dict[str, int], Dict[str, float]]:
    """
    Allocate MQL targets across channels in priority order (best LTV:CAC first).
    budget_multiplier: 0.7 = conservative, 1.0 = moderate, 1.3 = aggressive.
    Returns (channel → MQLs, channel → budget).
    """
    ranked = sorted(channels, key=score_channel, reverse=True)
    remaining = total_mqls_needed
    channel_mqls: Dict[str, int] = {}
    channel_budget: Dict[str, float] = {}

    for ch in ranked:
        if remaining <= 0:
            channel_mqls[ch.name] = 0
            channel_budget[ch.name] = 0.0
            continue
        # Apply capacity ceiling scaled by multiplier (aggressive = push capacity)
        capacity = int(ch.max_mqls_per_month * 12 * budget_multiplier)
        allocated = min(remaining, capacity)
        channel_mqls[ch.name] = allocated
        channel_budget[ch.name] = allocated * ch.cac
        remaining -= allocated

    return channel_mqls, channel_budget


def build_scenario(
    name: str,
    channels: List[Channel],
    total_mqls: int,
    multiplier: float,
    notes: List[str],
) -> ScenarioResult:
    channel_mqls, channel_budget = allocate_mqls(channels, total_mqls, multiplier)

    total_budget = sum(channel_budget.values())
    total_mqls_allocated = sum(channel_mqls.values())
    projected_customers = math.floor(total_mqls_allocated * FUNNEL.mql_to_close)
    projected_arr = projected_customers * ASP_ANNUAL

    # Blended CAC = total budget / customers acquired
    blended_cac = total_budget / projected_customers if projected_customers > 0 else 0.0

    return ScenarioResult(
        name=name,
        total_budget=total_budget,
        channel_budgets=channel_budget,
        channel_mqls=channel_mqls,
        projected_customers=projected_customers,
        projected_arr=projected_arr,
        blended_cac=blended_cac,
        notes=notes,
    )


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------

def fmt_currency(n: float) -> str:
    if n >= 1_000_000:
        return f"${n/1_000_000:.2f}M"
    if n >= 1_000:
        return f"${n/1_000:.1f}K"
    return f"${n:.0f}"


def fmt_ratio(n: float) -> str:
    return f"{n:.1f}x"


def print_header(title: str) -> None:
    width = 72
    print("\n" + "=" * width)
    print(f"  {title}")
    print("=" * width)


def print_channel_table(channels: List[Channel]) -> None:
    print_header("Channel Analysis — Current State")
    header = f"{'Channel':<25} {'CAC':>8} {'Payback':>9} {'LTV:CAC':>8} {'Cap/mo':>7} {'Trend':>10}"
    print(header)
    print("-" * 72)
    for ch in sorted(channels, key=score_channel, reverse=True):
        ratio = ltv_to_cac(ch.ltv, ch.cac)
        flag = ""
        if ratio < 1:
            flag = " ⚠ LOSS"
        elif ratio >= 6:
            flag = " ★ STRONG"
        elif ratio >= 3:
            flag = " ✓"
        print(
            f"{ch.name:<25} {fmt_currency(ch.cac):>8} "
            f"{ch.payback_months:>7.1f}mo {fmt_ratio(ratio):>8} "
            f"{ch.max_mqls_per_month:>7} {ch.trend:>10}{flag}"
        )


def print_funnel_summary(customers: int, mqls: int) -> None:
    print_header("Funnel Requirements")
    print(f"  Target new ARR:          {fmt_currency(TARGET_NEW_ARR)}")
    print(f"  Average selling price:   {fmt_currency(ASP_ANNUAL)}")
    print(f"  New customers needed:    {customers}")
    print(f"  Funnel MQL→Close rate:   {FUNNEL.mql_to_close:.1%}")
    print(f"  Total MQLs needed:       {mqls}")
    print(f"\n  Funnel stage rates:")
    print(f"    MQL → SAL:             {FUNNEL.mql_to_sal:.0%}")
    print(f"    SAL → SQL:             {FUNNEL.mql_to_sal * FUNNEL.sal_to_sql:.0%}")
    print(f"    SQL → Opportunity:     {FUNNEL.mql_to_sal * FUNNEL.sal_to_sql * FUNNEL.sql_to_opp:.0%}")
    print(f"    Opportunity → Close:   {FUNNEL.mql_to_close:.0%}")
    print(f"\n  LTV (estimated):         {fmt_currency(LTV)}")
    print(f"  Monthly churn:           {MONTHLY_CHURN:.1%}  ({MONTHLY_CHURN*12:.0%} annualized)")


def print_scenario(result: ScenarioResult, channels: List[Channel]) -> None:
    print_header(f"Scenario: {result.name}")
    print(f"  Total marketing budget:  {fmt_currency(result.total_budget)}")
    print(f"  Projected customers:     {result.projected_customers}")
    print(f"  Projected new ARR:       {fmt_currency(result.projected_arr)}")
    print(f"  Blended CAC:             {fmt_currency(result.blended_cac)}")
    blended_ltv_cac = LTV / result.blended_cac if result.blended_cac > 0 else 0
    blended_payback = result.blended_cac / (ARPU_MONTHLY * GROSS_MARGIN)
    print(f"  Blended LTV:CAC:         {fmt_ratio(blended_ltv_cac)}", end="")
    if blended_ltv_cac < 1:
        print("  ⚠ BELOW BREAK-EVEN")
    elif blended_ltv_cac < 3:
        print("  △ MARGINAL")
    elif blended_ltv_cac >= 3:
        print("  ✓ HEALTHY")
    else:
        print()
    print(f"  Blended payback:         {blended_payback:.1f} months")
    if result.notes:
        print(f"\n  Notes:")
        for note in result.notes:
            print(f"    • {note}")

    print(f"\n  {'Channel':<25} {'MQLs':>6} {'Budget':>10} {'% of Budget':>12} {'LTV:CAC':>8}")
    print("  " + "-" * 65)
    for ch in sorted(channels, key=score_channel, reverse=True):
        mqls = result.channel_mqls.get(ch.name, 0)
        budget = result.channel_budgets.get(ch.name, 0.0)
        pct = (budget / result.total_budget * 100) if result.total_budget > 0 else 0
        ratio = ltv_to_cac(ch.ltv, ch.cac)
        print(
            f"  {ch.name:<25} {mqls:>6} {fmt_currency(budget):>10} "
            f"{pct:>11.1f}% {fmt_ratio(ratio):>8}"
        )


def print_scenario_comparison(scenarios: List[ScenarioResult]) -> None:
    print_header("Scenario Comparison")
    header = f"{'Scenario':<18} {'Budget':>10} {'Customers':>10} {'ARR':>10} {'Blended CAC':>12} {'LTV:CAC':>8} {'Payback':>9}"
    print(header)
    print("-" * 82)
    for s in scenarios:
        blended_ltv_cac = LTV / s.blended_cac if s.blended_cac > 0 else 0
        blended_payback = s.blended_cac / (ARPU_MONTHLY * GROSS_MARGIN)
        print(
            f"{s.name:<18} {fmt_currency(s.total_budget):>10} "
            f"{s.projected_customers:>10} {fmt_currency(s.projected_arr):>10} "
            f"{fmt_currency(s.blended_cac):>12} {fmt_ratio(blended_ltv_cac):>8} "
            f"{blended_payback:>7.1f}mo"
        )


def print_recommendations(channels: List[Channel]) -> None:
    print_header("Channel Recommendations")
    scale = [ch for ch in channels if score_channel(ch) >= 1.5 and ch.trend in ("improving", "stable")]
    hold = [ch for ch in channels if 0.8 <= score_channel(ch) < 1.5 or (ch.trend == "stable" and ltv_to_cac(ch.ltv, ch.cac) >= 3)]
    cut = [ch for ch in channels if ltv_to_cac(ch.ltv, ch.cac) < 2 or ch.trend == "declining"]
    # Deduplicate
    hold = [ch for ch in hold if ch not in scale]
    cut = [ch for ch in cut if ch not in scale and ch not in hold]

    if scale:
        print("  SCALE (strong LTV:CAC, improving or stable trend):")
        for ch in scale:
            print(f"    + {ch.name}  [LTV:CAC {fmt_ratio(ltv_to_cac(ch.ltv, ch.cac))}, payback {ch.payback_months:.0f}mo]")
    if hold:
        print("  HOLD (monitor — adequate but not outstanding):")
        for ch in hold:
            print(f"    = {ch.name}  [LTV:CAC {fmt_ratio(ltv_to_cac(ch.ltv, ch.cac))}, trend: {ch.trend}]")
    if cut:
        print("  CUT or REDUCE (poor LTV:CAC or declining):")
        for ch in cut:
            print(f"    - {ch.name}  [LTV:CAC {fmt_ratio(ltv_to_cac(ch.ltv, ch.cac))}, trend: {ch.trend}]")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> None:
    customers = customers_needed(TARGET_NEW_ARR, ASP_ANNUAL)
    total_mqls = mqls_needed_total(customers, FUNNEL.mql_to_close)

    print_channel_table(CHANNELS)
    print_funnel_summary(customers, total_mqls)

    scenarios = [
        build_scenario(
            name="Conservative",
            channels=CHANNELS,
            total_mqls=total_mqls,
            multiplier=0.7,
            notes=[
                "Prioritizes lowest CAC channels only.",
                "May not reach MQL target — expect ~70% of goal.",
                "Best for capital-constrained orgs or short runway.",
            ],
        ),
        build_scenario(
            name="Moderate",
            channels=CHANNELS,
            total_mqls=total_mqls,
            multiplier=1.0,
            notes=[
                "Balanced allocation — efficiency-first but full MQL target.",
                "Recommended baseline. Revisit Q2 based on actuals.",
            ],
        ),
        build_scenario(
            name="Aggressive",
            channels=CHANNELS,
            total_mqls=total_mqls,
            multiplier=1.4,
            notes=[
                "Pushes all channels toward capacity ceiling.",
                "Higher spend on lower-efficiency channels to hit volume.",
                "Requires > 18-month runway to justify payback period.",
            ],
        ),
    ]

    for scenario in scenarios:
        print_scenario(scenario, CHANNELS)

    print_scenario_comparison(scenarios)
    print_recommendations(CHANNELS)

    print("\n" + "=" * 72)
    print("  Key questions before finalizing budget:")
    print("    1. What is the payback period the CFO/board will accept?")
    print("    2. Is CAC for declining-trend channels actually recoverable?")
    print("    3. Does the moderate scenario require sales headcount increase?")
    print("    4. Which channels have capacity to absorb 20% more spend?")
    print("=" * 72 + "\n")


if __name__ == "__main__":
    main()
