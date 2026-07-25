#!/usr/bin/env python3
"""
Unit Economics Analyzer
========================
Per-cohort LTV, per-channel CAC, payback periods, and LTV:CAC ratios.
Never blended averages — those hide what's actually happening.

Usage:
    python unit_economics_analyzer.py
    python unit_economics_analyzer.py --csv

Stdlib only. No dependencies.
"""

import argparse
import csv
import io
import sys
from dataclasses import dataclass, field
from typing import Optional


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass
class CohortData:
    """
    Revenue data for a group of customers acquired in the same period.
    Revenue is tracked monthly: revenue[0] = month 1, revenue[1] = month 2, etc.
    """
    label: str                      # e.g. "Q1 2024"
    acquisition_period: str         # human-readable label
    customers_acquired: int
    total_cac_spend: float          # total S&M spend to acquire this cohort
    monthly_revenue: list[float]    # revenue per month from this cohort
    gross_margin_pct: float = 0.70  # blended gross margin for this cohort


@dataclass
class ChannelData:
    """Acquisition cost and customer data for a single channel."""
    channel: str
    spend: float
    customers_acquired: int
    avg_arpa: float                 # average revenue per account (monthly)
    gross_margin_pct: float = 0.70
    avg_monthly_churn: float = 0.02 # monthly churn rate for customers from this channel


@dataclass
class UnitEconomicsResult:
    """Computed unit economics for a cohort or channel."""
    label: str
    customers: int
    cac: float
    arpa: float                 # average revenue per account per month
    gross_margin_pct: float
    monthly_churn: float
    ltv: float
    ltv_cac_ratio: float
    payback_months: float
    # Cohort-specific
    m1_revenue: Optional[float] = None
    m6_revenue: Optional[float] = None
    m12_revenue: Optional[float] = None
    m24_revenue: Optional[float] = None
    m12_ltv: Optional[float] = None   # realized LTV through month 12
    retention_m6: Optional[float] = None    # % of M1 revenue retained at M6
    retention_m12: Optional[float] = None


# ---------------------------------------------------------------------------
# Calculators
# ---------------------------------------------------------------------------

def calc_ltv(arpa: float, gross_margin_pct: float, monthly_churn: float) -> float:
    """
    LTV = (ARPA × Gross Margin) / Monthly Churn Rate
    Assumes constant churn (simplified; cohort method is more accurate).
    """
    if monthly_churn <= 0:
        return float("inf")
    return (arpa * gross_margin_pct) / monthly_churn


def calc_payback(cac: float, arpa: float, gross_margin_pct: float) -> float:
    """
    CAC Payback (months) = CAC / (ARPA × Gross Margin)
    """
    denominator = arpa * gross_margin_pct
    if denominator <= 0:
        return float("inf")
    return cac / denominator


def analyze_cohort(cohort: CohortData) -> UnitEconomicsResult:
    """Compute full unit economics for a cohort."""
    n = cohort.customers_acquired
    if n == 0:
        raise ValueError(f"Cohort {cohort.label}: customers_acquired cannot be 0")

    cac = cohort.total_cac_spend / n

    # ARPA from month 1 revenue
    m1_rev = cohort.monthly_revenue[0] if cohort.monthly_revenue else 0
    arpa = m1_rev / n if n > 0 else 0

    # Observed monthly churn from cohort data
    # Use revenue decline from M1 to M12 to estimate churn
    months_available = len(cohort.monthly_revenue)
    if months_available >= 12:
        m12_rev = cohort.monthly_revenue[11]
        # Revenue retention over 12 months: (M12/M1)^(1/11) per month on average
        # Implied monthly retention rate
        if m1_rev > 0 and m12_rev > 0:
            monthly_retention = (m12_rev / m1_rev) ** (1 / 11)
            monthly_churn = 1 - monthly_retention
        else:
            monthly_churn = 0.02  # default
    elif months_available >= 6:
        m6_rev = cohort.monthly_revenue[5]
        if m1_rev > 0 and m6_rev > 0:
            monthly_retention = (m6_rev / m1_rev) ** (1 / 5)
            monthly_churn = 1 - monthly_retention
        else:
            monthly_churn = 0.02
    else:
        monthly_churn = 0.02  # default if < 6 months data

    # Clamp to reasonable range
    monthly_churn = max(0.001, min(monthly_churn, 0.30))

    ltv = calc_ltv(arpa, cohort.gross_margin_pct, monthly_churn)
    payback = calc_payback(cac, arpa, cohort.gross_margin_pct)
    ltv_cac = ltv / cac if cac > 0 else float("inf")

    # Snapshot revenues
    def rev_at(month_idx: int) -> Optional[float]:
        if months_available > month_idx:
            return cohort.monthly_revenue[month_idx]
        return None

    m6 = rev_at(5)
    m12 = rev_at(11)
    m24 = rev_at(23)

    # Realized LTV through observed months (actual gross profit)
    m12_ltv = sum(cohort.monthly_revenue[:12]) * cohort.gross_margin_pct if months_available >= 12 else None

    # Retention rates
    ret_m6 = (m6 / m1_rev) if (m6 is not None and m1_rev > 0) else None
    ret_m12 = (m12 / m1_rev) if (m12 is not None and m1_rev > 0) else None

    return UnitEconomicsResult(
        label=cohort.label,
        customers=n,
        cac=cac,
        arpa=arpa,
        gross_margin_pct=cohort.gross_margin_pct,
        monthly_churn=monthly_churn,
        ltv=ltv,
        ltv_cac_ratio=ltv_cac,
        payback_months=payback,
        m1_revenue=m1_rev,
        m6_revenue=m6,
        m12_revenue=m12,
        m24_revenue=m24,
        m12_ltv=m12_ltv,
        retention_m6=ret_m6,
        retention_m12=ret_m12,
    )


def analyze_channel(ch: ChannelData) -> UnitEconomicsResult:
    """Compute unit economics for an acquisition channel."""
    if ch.customers_acquired == 0:
        raise ValueError(f"Channel {ch.channel}: customers_acquired cannot be 0")

    cac = ch.spend / ch.customers_acquired
    ltv = calc_ltv(ch.avg_arpa, ch.gross_margin_pct, ch.avg_monthly_churn)
    payback = calc_payback(cac, ch.avg_arpa, ch.gross_margin_pct)
    ltv_cac = ltv / cac if cac > 0 else float("inf")

    return UnitEconomicsResult(
        label=ch.channel,
        customers=ch.customers_acquired,
        cac=cac,
        arpa=ch.avg_arpa,
        gross_margin_pct=ch.gross_margin_pct,
        monthly_churn=ch.avg_monthly_churn,
        ltv=ltv,
        ltv_cac_ratio=ltv_cac,
        payback_months=payback,
    )


# ---------------------------------------------------------------------------
# Blended metrics (for comparison)
# ---------------------------------------------------------------------------

def blended_cac(channels: list[ChannelData]) -> float:
    total_spend = sum(c.spend for c in channels)
    total_customers = sum(c.customers_acquired for c in channels)
    return total_spend / total_customers if total_customers > 0 else 0


def blended_ltv(channels: list[ChannelData]) -> float:
    """Weighted average LTV by customers acquired."""
    total_customers = sum(c.customers_acquired for c in channels)
    if total_customers == 0:
        return 0
    weighted = sum(
        calc_ltv(c.avg_arpa, c.gross_margin_pct, c.avg_monthly_churn) * c.customers_acquired
        for c in channels
    )
    return weighted / total_customers


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------

def fmt(value: float, prefix: str = "$", decimals: int = 0) -> str:
    if value == float("inf"):
        return "∞"
    if abs(value) >= 1_000_000:
        return f"{prefix}{value/1_000_000:.2f}M"
    if abs(value) >= 1_000:
        return f"{prefix}{value/1_000:.1f}K"
    return f"{prefix}{value:.{decimals}f}"


def pct(value: Optional[float]) -> str:
    if value is None:
        return "n/a"
    return f"{value*100:.1f}%"


def rating(ltv_cac: float, payback: float) -> str:
    if ltv_cac == float("inf"):
        return "∞"
    if ltv_cac >= 5 and payback <= 12:
        return "🟢 Excellent"
    if ltv_cac >= 3 and payback <= 18:
        return "🟡 Good"
    if ltv_cac >= 2 and payback <= 24:
        return "🟠 Marginal"
    return "🔴 Poor"


def print_cohort_analysis(results: list[UnitEconomicsResult]) -> None:
    print("\n" + "="*80)
    print("  COHORT ANALYSIS")
    print("="*80)
    print(f"  {'Cohort':<12} {'Cust':>5} {'CAC':>8} {'ARPA/mo':>9} {'Churn/mo':>10} "
          f"{'LTV':>10} {'LTV:CAC':>8} {'Payback':>9} {'Ret@M12':>8}")
    print("  " + "-"*88)
    for r in results:
        payback_str = f"{r.payback_months:.1f}mo" if r.payback_months != float("inf") else "∞"
        ltv_str = fmt(r.ltv) if r.ltv != float("inf") else "∞"
        ltv_cac_str = f"{r.ltv_cac_ratio:.1f}x" if r.ltv_cac_ratio != float("inf") else "∞"
        print(
            f"  {r.label:<12} {r.customers:>5} {fmt(r.cac):>8} {fmt(r.arpa):>9} "
            f"{pct(r.monthly_churn):>10} {ltv_str:>10} {ltv_cac_str:>8} "
            f"{payback_str:>9} {pct(r.retention_m12):>8}"
        )

    # Trend analysis
    print("\n  Cohort Trend (is the business getting better or worse?):")
    if len(results) >= 3:
        ltv_cac_values = [r.ltv_cac_ratio for r in results if r.ltv_cac_ratio != float("inf")]
        cac_values = [r.cac for r in results]
        churn_values = [r.monthly_churn for r in results]

        if len(ltv_cac_values) >= 2:
            ltv_cac_trend = "↑ Improving" if ltv_cac_values[-1] > ltv_cac_values[0] else "↓ Deteriorating"
        else:
            ltv_cac_trend = "n/a"

        cac_trend = "↓ Decreasing (good)" if cac_values[-1] < cac_values[0] else "↑ Increasing"
        churn_trend = "↓ Improving" if churn_values[-1] < churn_values[0] else "↑ Worsening"

        print(f"    LTV:CAC:    {ltv_cac_trend}")
        print(f"    CAC:        {cac_trend}")
        print(f"    Churn rate: {churn_trend}")


def print_channel_analysis(results: list[UnitEconomicsResult], channels: list[ChannelData]) -> None:
    print("\n" + "="*80)
    print("  CHANNEL ANALYSIS (Per-Channel vs Blended)")
    print("="*80)
    print(f"  {'Channel':<22} {'Spend':>9} {'Cust':>5} {'CAC':>8} {'LTV':>10} {'LTV:CAC':>8} {'Payback':>9} {'Rating'}")
    print("  " + "-"*90)
    for r, ch in zip(results, channels):
        payback_str = f"{r.payback_months:.1f}mo" if r.payback_months != float("inf") else "∞"
        ltv_str = fmt(r.ltv) if r.ltv != float("inf") else "∞"
        ltv_cac_str = f"{r.ltv_cac_ratio:.1f}x" if r.ltv_cac_ratio != float("inf") else "∞"
        print(
            f"  {r.label:<22} {fmt(ch.spend):>9} {r.customers:>5} {fmt(r.cac):>8} "
            f"{ltv_str:>10} {ltv_cac_str:>8} {payback_str:>9}  {rating(r.ltv_cac_ratio, r.payback_months)}"
        )

    # Blended comparison
    b_cac = blended_cac(channels)
    b_ltv = blended_ltv(channels)
    b_ltv_cac = b_ltv / b_cac if b_cac > 0 else 0
    total_spend = sum(c.spend for c in channels)
    total_customers = sum(c.customers_acquired for c in channels)
    avg_payback = sum(
        calc_payback(b_cac, c.avg_arpa, c.gross_margin_pct) * c.customers_acquired
        for c in channels
    ) / total_customers

    print("  " + "-"*90)
    print(
        f"  {'BLENDED (dangerous)':<22} {fmt(total_spend):>9} {total_customers:>5} "
        f"{fmt(b_cac):>8} {fmt(b_ltv):>10} {b_ltv_cac:.1f}x{'':<7} "
        f"{avg_payback:.1f}mo{'':<4}  {rating(b_ltv_cac, avg_payback)}"
    )
    print("\n  ⚠️  Blended numbers hide channel-level problems. Manage channels individually.")

    # Budget reallocation
    print("\n  Recommended Budget Reallocation:")
    sorted_results = sorted(zip(results, channels), key=lambda x: x[0].ltv_cac_ratio, reverse=True)
    for r, ch in sorted_results:
        if r.ltv_cac_ratio >= 3:
            action = "✅ Scale"
        elif r.ltv_cac_ratio >= 2:
            action = "🔄 Optimize"
        else:
            action = "❌ Cut / pause"
        print(f"    {ch.channel:<22} LTV:CAC = {r.ltv_cac_ratio:.1f}x  → {action}")


def export_csv_results(cohort_results: list[UnitEconomicsResult], channel_results: list[UnitEconomicsResult]) -> str:
    buf = io.StringIO()
    writer = csv.writer(buf)
    writer.writerow(["Type", "Label", "Customers", "CAC", "ARPA_Monthly", "Gross_Margin_Pct",
                     "Monthly_Churn", "LTV", "LTV_CAC_Ratio", "Payback_Months",
                     "Retention_M6", "Retention_M12"])
    for r in cohort_results:
        writer.writerow(["cohort", r.label, r.customers, round(r.cac, 2), round(r.arpa, 2),
                         r.gross_margin_pct, round(r.monthly_churn, 4),
                         round(r.ltv, 2) if r.ltv != float("inf") else "inf",
                         round(r.ltv_cac_ratio, 2) if r.ltv_cac_ratio != float("inf") else "inf",
                         round(r.payback_months, 2) if r.payback_months != float("inf") else "inf",
                         round(r.retention_m6, 3) if r.retention_m6 else "",
                         round(r.retention_m12, 3) if r.retention_m12 else ""])
    for r in channel_results:
        writer.writerow(["channel", r.label, r.customers, round(r.cac, 2), round(r.arpa, 2),
                         r.gross_margin_pct, round(r.monthly_churn, 4),
                         round(r.ltv, 2) if r.ltv != float("inf") else "inf",
                         round(r.ltv_cac_ratio, 2) if r.ltv_cac_ratio != float("inf") else "inf",
                         round(r.payback_months, 2) if r.payback_months != float("inf") else "inf",
                         "", ""])
    return buf.getvalue()


# ---------------------------------------------------------------------------
# Sample data
# ---------------------------------------------------------------------------

def make_sample_cohorts() -> list[CohortData]:
    """
    Series A SaaS company, 8 quarters of cohort data.
    Shows a business improving on all dimensions over time.
    """
    return [
        CohortData(
            label="Q1 2023", acquisition_period="Jan-Mar 2023",
            customers_acquired=12, total_cac_spend=54_000,
            gross_margin_pct=0.68,
            monthly_revenue=[
                10_200, 9_600, 9_100, 8_700, 8_300, 8_000,  # M1-M6
                7_800, 7_600, 7_400, 7_200, 7_000, 6_800,   # M7-M12
                6_700, 6_600, 6_500, 6_400, 6_300, 6_200,   # M13-M18
                6_100, 6_000, 5_900, 5_800, 5_700, 5_600,   # M19-M24
            ],
        ),
        CohortData(
            label="Q2 2023", acquisition_period="Apr-Jun 2023",
            customers_acquired=15, total_cac_spend=60_000,
            gross_margin_pct=0.69,
            monthly_revenue=[
                13_500, 12_900, 12_500, 12_100, 11_800, 11_500,
                11_300, 11_100, 10_900, 10_700, 10_500, 10_300,
                10_200, 10_100, 10_000, 9_900, 9_800, 9_700,
            ],
        ),
        CohortData(
            label="Q3 2023", acquisition_period="Jul-Sep 2023",
            customers_acquired=18, total_cac_spend=63_000,
            gross_margin_pct=0.70,
            monthly_revenue=[
                16_200, 15_800, 15_400, 15_100, 14_800, 14_600,
                14_400, 14_200, 14_000, 13_900, 13_800, 13_700,
                13_600, 13_500, 13_400, 13_300,
            ],
        ),
        CohortData(
            label="Q4 2023", acquisition_period="Oct-Dec 2023",
            customers_acquired=22, total_cac_spend=70_400,
            gross_margin_pct=0.71,
            monthly_revenue=[
                20_900, 20_500, 20_200, 19_900, 19_700, 19_500,
                19_300, 19_100, 19_000, 18_900, 18_800, 18_700,
            ],
        ),
        CohortData(
            label="Q1 2024", acquisition_period="Jan-Mar 2024",
            customers_acquired=28, total_cac_spend=81_200,
            gross_margin_pct=0.72,
            monthly_revenue=[
                27_200, 26_900, 26_600, 26_400, 26_200, 26_000,
                25_800, 25_700, 25_600, 25_500,
            ],
        ),
        CohortData(
            label="Q2 2024", acquisition_period="Apr-Jun 2024",
            customers_acquired=34, total_cac_spend=91_800,
            gross_margin_pct=0.72,
            monthly_revenue=[
                33_300, 33_000, 32_800, 32_600, 32_400, 32_200,
            ],
        ),
        CohortData(
            label="Q3 2024", acquisition_period="Jul-Sep 2024",
            customers_acquired=40, total_cac_spend=100_000,
            gross_margin_pct=0.73,
            monthly_revenue=[
                39_600, 39_400, 39_200,
            ],
        ),
        CohortData(
            label="Q4 2024", acquisition_period="Oct-Dec 2024",
            customers_acquired=47, total_cac_spend=112_800,
            gross_margin_pct=0.73,
            monthly_revenue=[
                47_000,
            ],
        ),
    ]


def make_sample_channels() -> list[ChannelData]:
    """
    Q4 2024 channel breakdown. Blended looks fine; per-channel reveals problems.
    """
    return [
        ChannelData("Organic / SEO",     spend=9_500,  customers_acquired=14, avg_arpa=950,  gross_margin_pct=0.73, avg_monthly_churn=0.015),
        ChannelData("Paid Search (SEM)",  spend=48_000, customers_acquired=18, avg_arpa=980,  gross_margin_pct=0.73, avg_monthly_churn=0.020),
        ChannelData("Paid Social",        spend=32_000, customers_acquired=8,  avg_arpa=900,  gross_margin_pct=0.72, avg_monthly_churn=0.025),
        ChannelData("Content / Inbound",  spend=11_000, customers_acquired=6,  avg_arpa=1100, gross_margin_pct=0.74, avg_monthly_churn=0.012),
        ChannelData("Outbound SDR",       spend=22_000, customers_acquired=4,  avg_arpa=1200, gross_margin_pct=0.73, avg_monthly_churn=0.022),
        ChannelData("Events / Webinars",  spend=18_500, customers_acquired=3,  avg_arpa=1050, gross_margin_pct=0.72, avg_monthly_churn=0.028),
        ChannelData("Partner / Referral", spend=7_800,  customers_acquired=7,  avg_arpa=1000, gross_margin_pct=0.73, avg_monthly_churn=0.013),
    ]


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(description="Unit Economics Analyzer")
    parser.add_argument("--csv", action="store_true", help="Export results as CSV to stdout")
    args = parser.parse_args()

    cohorts = make_sample_cohorts()
    channels = make_sample_channels()

    print("\n" + "="*80)
    print("  UNIT ECONOMICS ANALYZER")
    print("  Sample Company: Series A SaaS | Q4 2024 Snapshot")
    print("  Gross Margin: ~72% | Monthly Churn: derived from cohort data")
    print("="*80)

    cohort_results = [analyze_cohort(c) for c in cohorts]
    channel_results = [analyze_channel(c) for c in channels]

    print_cohort_analysis(cohort_results)
    print_channel_analysis(channel_results, channels)

    # Health summary
    print("\n" + "="*80)
    print("  HEALTH SUMMARY")
    print("="*80)
    latest = cohort_results[-1]
    prev = cohort_results[-4] if len(cohort_results) >= 4 else cohort_results[0]

    print(f"\n  Latest Cohort ({latest.label}):")
    print(f"    CAC:          {fmt(latest.cac)}")
    ltv_str = fmt(latest.ltv) if latest.ltv != float("inf") else "∞"
    ltv_cac_str = f"{latest.ltv_cac_ratio:.1f}x" if latest.ltv_cac_ratio != float("inf") else "∞"
    payback_str = f"{latest.payback_months:.1f} months" if latest.payback_months != float("inf") else "∞"
    print(f"    LTV:          {ltv_str}")
    print(f"    LTV:CAC:      {ltv_cac_str}  (target: > 3x)")
    print(f"    CAC Payback:  {payback_str}  (target: < 18mo)")
    print(f"    Rating:       {rating(latest.ltv_cac_ratio, latest.payback_months)}")

    # Trend vs 4 quarters ago
    print(f"\n  Trend vs {prev.label}:")
    cac_delta = (latest.cac - prev.cac) / prev.cac * 100
    ltv_delta_str = "n/a"
    if latest.ltv != float("inf") and prev.ltv != float("inf"):
        ltv_delta = (latest.ltv - prev.ltv) / prev.ltv * 100
        ltv_delta_str = f"{ltv_delta:+.1f}%"
    cac_str = "↓ Better" if cac_delta < 0 else "↑ Worse"
    print(f"    CAC:    {cac_delta:+.1f}%  ({cac_str})")
    print(f"    LTV:    {ltv_delta_str}")

    print("\n  Benchmark Reference:")
    print("    LTV:CAC > 5x  → Scale aggressively")
    print("    LTV:CAC 3-5x  → Healthy; grow at current pace")
    print("    LTV:CAC 2-3x  → Marginal; optimize before scaling")
    print("    LTV:CAC < 2x  → Acquiring unprofitably; stop and fix")
    print("    Payback < 12mo → Outstanding capital efficiency")
    print("    Payback 12-18mo → Good for B2B SaaS")
    print("    Payback > 24mo → Requires long-dated capital to scale")

    if args.csv:
        print("\n\n--- CSV EXPORT ---\n")
        sys.stdout.write(export_csv_results(cohort_results, channel_results))


if __name__ == "__main__":
    main()
