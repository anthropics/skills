#!/usr/bin/env python3
"""
Burn Rate & Runway Calculator
==============================
Models startup runway across base/bull/bear scenarios, incorporating
a hiring plan and revenue trajectory. Outputs months of runway,
cash-out dates, and decision trigger points.

Usage:
    python burn_rate_calculator.py
    python burn_rate_calculator.py --csv  # export to CSV

Stdlib only. No dependencies.
"""

import argparse
import csv
import io
import sys
from dataclasses import dataclass, field
from datetime import date, timedelta
from typing import Optional


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass
class HiringEntry:
    """A planned hire."""
    month: int          # months from model start (1-indexed)
    role: str
    department: str     # "sales", "engineering", "cs", "ga"
    annual_salary: float
    benefits_pct: float = 0.22  # benefits as % of salary
    recruiting_cost: float = 0.0  # one-time recruiting fee


@dataclass
class RevenueEntry:
    """Monthly revenue data point (historical or projected)."""
    month: int
    mrr: float          # monthly recurring revenue
    one_time: float = 0.0


@dataclass
class ModelConfig:
    """Master configuration for a runway scenario."""
    name: str
    starting_cash: float
    starting_mrr: float
    starting_headcount: int
    avg_loaded_salary: float        # average fully-loaded salary per current employee
    base_non_headcount_opex: float  # monthly non-headcount costs (infra, tools, etc.)
    gross_margin_pct: float         # 0.0–1.0
    mrr_growth_rate: float          # monthly MoM growth rate, 0.0–1.0
    hiring_plan: list[HiringEntry] = field(default_factory=list)
    model_months: int = 24
    start_date: Optional[date] = None


@dataclass
class MonthResult:
    """Single month output."""
    month: int
    label: str              # e.g. "Month 1 (Apr 2025)"
    mrr: float
    gross_profit: float
    headcount: int
    headcount_cost: float   # total loaded headcount cost this month
    other_opex: float
    gross_burn: float
    net_burn: float
    cash_start: float
    cash_end: float
    runway_months: float    # projected runway from this month
    cumulative_new_arr: float   # for burn multiple


# ---------------------------------------------------------------------------
# Core calculator
# ---------------------------------------------------------------------------

class RunwayCalculator:

    def __init__(self, config: ModelConfig):
        self.cfg = config

    def run(self) -> list[MonthResult]:
        cfg = self.cfg
        results = []

        # Build headcount schedule: month -> list of new hires starting that month
        hire_by_month: dict[int, list[HiringEntry]] = {}
        for h in cfg.hiring_plan:
            hire_by_month.setdefault(h.month, []).append(h)

        # Track existing employees
        active_employees: list[dict] = []
        for _ in range(cfg.starting_headcount):
            active_employees.append({
                "monthly_loaded": cfg.avg_loaded_salary / 12 * 1.0,
                "start_month": 0,
            })

        cash = cfg.starting_cash
        mrr = cfg.starting_mrr
        cumulative_new_arr = 0.0
        starting_mrr = cfg.starting_mrr

        for m in range(1, cfg.model_months + 1):
            # Process new hires this month
            one_time_recruiting = 0.0
            if m in hire_by_month:
                for hire in hire_by_month[m]:
                    monthly_loaded = (
                        hire.annual_salary * (1 + hire.benefits_pct) / 12
                    )
                    active_employees.append({
                        "monthly_loaded": monthly_loaded,
                        "start_month": m,
                    })
                    one_time_recruiting += hire.recruiting_cost

            # Revenue this month
            mrr = mrr * (1 + cfg.mrr_growth_rate)
            gross_profit = mrr * cfg.gross_margin_pct

            # Headcount cost
            headcount_cost = sum(e["monthly_loaded"] for e in active_employees)
            headcount_cost += one_time_recruiting

            # Other opex (infra, SaaS tools, office, etc.)
            other_opex = cfg.base_non_headcount_opex

            # Burn
            gross_burn = headcount_cost + other_opex
            net_burn = gross_burn - gross_profit

            # Cash
            cash_start = cash
            cash = cash - net_burn
            cash_end = cash

            # Projected runway from this month (using current net burn rate)
            runway = cash_end / net_burn if net_burn > 0 else float("inf")

            # Cumulative new ARR (for burn multiple calc)
            new_mrr_added = mrr - starting_mrr if m == 1 else mrr - results[-1].mrr
            cumulative_new_arr += new_mrr_added * 12

            # Label
            if cfg.start_date:
                month_date = date(
                    cfg.start_date.year,
                    cfg.start_date.month,
                    1,
                ) + timedelta(days=32 * (m - 1))
                month_date = month_date.replace(day=1)
                label = f"Month {m:02d} ({month_date.strftime('%b %Y')})"
            else:
                label = f"Month {m:02d}"

            results.append(MonthResult(
                month=m,
                label=label,
                mrr=mrr,
                gross_profit=gross_profit,
                headcount=len(active_employees),
                headcount_cost=headcount_cost,
                other_opex=other_opex,
                gross_burn=gross_burn,
                net_burn=net_burn,
                cash_start=cash_start,
                cash_end=cash_end,
                runway_months=runway,
                cumulative_new_arr=cumulative_new_arr,
            ))

            # Stop if cash runs out
            if cash_end <= 0:
                break

        return results

    def cash_out_date(self, results: list[MonthResult]) -> Optional[str]:
        """Return the label of the month cash runs out, or None if model survives."""
        for r in results:
            if r.cash_end <= 0:
                return r.label
        return None

    def burn_multiple(self, results: list[MonthResult]) -> float:
        """Burn multiple = total net burn / total net new ARR over model period."""
        total_net_burn = sum(r.net_burn for r in results if r.net_burn > 0)
        first_mrr = results[0].mrr / (1 + self.cfg.mrr_growth_rate)  # starting mrr
        total_new_arr = (results[-1].mrr - first_mrr) * 12
        if total_new_arr <= 0:
            return float("inf")
        return total_net_burn / total_new_arr


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------

def fmt_k(value: float) -> str:
    """Format as $Xk or $X.XM."""
    if abs(value) >= 1_000_000:
        return f"${value/1_000_000:.2f}M"
    if abs(value) >= 1_000:
        return f"${value/1_000:.0f}K"
    return f"${value:.0f}"


def print_summary(name: str, results: list[MonthResult], calc: RunwayCalculator) -> None:
    cash_out = calc.cash_out_date(results)
    bm = calc.burn_multiple(results)
    last = results[-1]
    first = results[0]

    print(f"\n{'='*60}")
    print(f"  SCENARIO: {name}")
    print(f"{'='*60}")
    print(f"  Months modeled:    {len(results)}")
    print(f"  Cash out:          {cash_out or 'Does not run out in model period'}")
    print(f"  Ending cash:       {fmt_k(last.cash_end)}")
    print(f"  Final runway:      {last.runway_months:.1f} months")
    print(f"  Starting MRR:      {fmt_k(first.mrr)}")
    print(f"  Ending MRR:        {fmt_k(last.mrr)}")
    print(f"  Ending headcount:  {last.headcount}")
    print(f"  Burn multiple:     {bm:.2f}x")
    print(f"  Avg net burn:      {fmt_k(sum(r.net_burn for r in results)/len(results))}/mo")

    # Decision triggers
    print(f"\n  Decision Triggers:")
    triggers = {9: "⚠️  START FUNDRAISE", 6: "🔴 COST REDUCTION PLAN", 4: "🚨 EXECUTE CUTS / BRIDGE"}
    shown = set()
    for r in results:
        for threshold, label in triggers.items():
            if r.runway_months <= threshold and threshold not in shown:
                print(f"    {r.label}: {label} (runway = {r.runway_months:.1f} mo)")
                shown.add(threshold)


def print_monthly_table(results: list[MonthResult], max_rows: int = 24) -> None:
    header = f"{'Month':<22} {'MRR':>10} {'Hdct':>6} {'Net Burn':>12} {'Cash':>12} {'Runway':>8}"
    print(f"\n{header}")
    print("-" * len(header))
    for r in results[:max_rows]:
        runway_str = f"{r.runway_months:.1f}mo" if r.runway_months != float("inf") else "∞"
        print(
            f"{r.label:<22} "
            f"{fmt_k(r.mrr):>10} "
            f"{r.headcount:>6} "
            f"{fmt_k(r.net_burn):>12} "
            f"{fmt_k(r.cash_end):>12} "
            f"{runway_str:>8}"
        )


def export_csv(scenarios: list[tuple[str, list[MonthResult]]]) -> str:
    buf = io.StringIO()
    writer = csv.writer(buf)
    writer.writerow([
        "Scenario", "Month", "Label", "MRR", "Gross Profit", "Headcount",
        "Headcount Cost", "Other Opex", "Gross Burn", "Net Burn",
        "Cash Start", "Cash End", "Runway Months"
    ])
    for name, results in scenarios:
        for r in results:
            writer.writerow([
                name, r.month, r.label,
                round(r.mrr, 2), round(r.gross_profit, 2), r.headcount,
                round(r.headcount_cost, 2), round(r.other_opex, 2),
                round(r.gross_burn, 2), round(r.net_burn, 2),
                round(r.cash_start, 2), round(r.cash_end, 2),
                round(r.runway_months, 2),
            ])
    return buf.getvalue()


# ---------------------------------------------------------------------------
# Sample data
# ---------------------------------------------------------------------------

def make_sample_configs() -> list[ModelConfig]:
    """
    Sample company: Series A SaaS startup
      - $3M cash on hand (post Series A)
      - $125K MRR (~$1.5M ARR)
      - 18 employees, $150K avg salary
      - $80K/mo non-headcount opex (infra, tools, office)
      - 72% gross margin
    """
    common_kwargs = dict(
        starting_cash=3_000_000,
        starting_mrr=125_000,
        starting_headcount=18,
        avg_loaded_salary=150_000,
        base_non_headcount_opex=80_000,
        gross_margin_pct=0.72,
        model_months=24,
        start_date=date(2025, 1, 1),
    )

    # Base: 10% MoM growth, moderate hiring
    base_hiring = [
        HiringEntry(month=2,  role="AE #1",         department="sales",       annual_salary=120_000, recruiting_cost=18_000),
        HiringEntry(month=3,  role="Senior SWE #1",  department="engineering", annual_salary=160_000, recruiting_cost=24_000),
        HiringEntry(month=5,  role="SDR #1",         department="sales",       annual_salary=80_000,  recruiting_cost=12_000),
        HiringEntry(month=6,  role="CSM #1",         department="cs",          annual_salary=90_000,  recruiting_cost=13_500),
        HiringEntry(month=8,  role="AE #2",          department="sales",       annual_salary=120_000, recruiting_cost=18_000),
        HiringEntry(month=9,  role="Senior SWE #2",  department="engineering", annual_salary=165_000, recruiting_cost=24_750),
        HiringEntry(month=12, role="Controller",     department="ga",          annual_salary=130_000, recruiting_cost=19_500),
        HiringEntry(month=14, role="AE #3",          department="sales",       annual_salary=125_000, recruiting_cost=18_750),
        HiringEntry(month=15, role="ML Engineer",    department="engineering", annual_salary=175_000, recruiting_cost=26_250),
        HiringEntry(month=18, role="AE #4",          department="sales",       annual_salary=125_000, recruiting_cost=18_750),
    ]

    # Bull: 15% MoM growth, full hiring plan
    bull_hiring = base_hiring + [
        HiringEntry(month=4,  role="Marketing Manager", department="sales",       annual_salary=110_000, recruiting_cost=16_500),
        HiringEntry(month=7,  role="Senior SWE #3",     department="engineering", annual_salary=165_000, recruiting_cost=24_750),
        HiringEntry(month=10, role="AE #5",              department="sales",       annual_salary=125_000, recruiting_cost=18_750),
        HiringEntry(month=13, role="DevOps Engineer",    department="engineering", annual_salary=150_000, recruiting_cost=22_500),
        HiringEntry(month=16, role="AE #6",              department="sales",       annual_salary=125_000, recruiting_cost=18_750),
    ]

    # Bear: 5% MoM growth, hiring freeze after month 3
    bear_hiring = [
        HiringEntry(month=2, role="AE #1",        department="sales",       annual_salary=120_000, recruiting_cost=18_000),
        HiringEntry(month=3, role="Senior SWE #1", department="engineering", annual_salary=160_000, recruiting_cost=24_000),
    ]

    return [
        ModelConfig(name="BULL  (15% MoM, full hiring)",       mrr_growth_rate=0.15, hiring_plan=bull_hiring,  **common_kwargs),
        ModelConfig(name="BASE  (10% MoM, planned hiring)",     mrr_growth_rate=0.10, hiring_plan=base_hiring,  **common_kwargs),
        ModelConfig(name="BEAR  ( 5% MoM, hiring freeze M3+)", mrr_growth_rate=0.05, hiring_plan=bear_hiring,  **common_kwargs),
        ModelConfig(name="DISTRESS (0% growth, freeze now)",    mrr_growth_rate=0.00, hiring_plan=[],           **common_kwargs),
    ]


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(description="Startup Burn Rate & Runway Calculator")
    parser.add_argument("--csv", action="store_true", help="Export full monthly data as CSV to stdout")
    parser.add_argument("--scenario", choices=["bull", "base", "bear", "distress", "all"], default="all")
    args = parser.parse_args()

    configs = make_sample_configs()
    if args.scenario != "all":
        configs = [c for c in configs if args.scenario.upper() in c.name.upper()]

    all_results: list[tuple[str, list[MonthResult]]] = []

    print("\n" + "="*60)
    print("  BURN RATE & RUNWAY CALCULATOR")
    print("  Sample Company: Series A SaaS Startup")
    print("  Starting cash: $3M | Starting MRR: $125K | 18 employees")
    print("="*60)

    for cfg in configs:
        calc = RunwayCalculator(cfg)
        results = calc.run()
        all_results.append((cfg.name, results))
        print_summary(cfg.name, results, calc)
        print_monthly_table(results)

    # Comparison summary
    print("\n" + "="*60)
    print("  SCENARIO COMPARISON")
    print("="*60)
    print(f"  {'Scenario':<40} {'Runway':>8} {'Cash Out':<30} {'Burn Mult':>10}")
    print("  " + "-"*88)
    for cfg, (name, results) in zip(configs, all_results):
        calc = RunwayCalculator(cfg)
        cash_out = calc.cash_out_date(results) or "Survives model period"
        bm = calc.burn_multiple(results)
        final_runway = results[-1].runway_months
        runway_str = f"{final_runway:.1f}mo" if final_runway != float("inf") else "∞"
        bm_str = f"{bm:.2f}x" if bm != float("inf") else "∞"
        print(f"  {name:<40} {runway_str:>8} {cash_out:<30} {bm_str:>10}")

    print("\n  Decision Trigger Reference:")
    print("    9 months runway → Start fundraise process")
    print("    6 months runway → Begin cost reduction planning")
    print("    4 months runway → Execute cuts; explore bridge financing")
    print("    3 months runway → Emergency plan only")

    if args.csv:
        print("\n\n--- CSV EXPORT ---\n")
        sys.stdout.write(export_csv(all_results))


if __name__ == "__main__":
    main()
