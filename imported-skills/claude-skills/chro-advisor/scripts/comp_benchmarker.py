#!/usr/bin/env python3
"""
Compensation Benchmarker
========================
Salary benchmarking and total comp modeling for startup teams.
Analyzes pay equity, compa-ratios, and total comp vs. market.

Usage:
    python comp_benchmarker.py                       # Run with built-in sample data
    python comp_benchmarker.py --config roster.json  # Load from JSON
    python comp_benchmarker.py --help

Output: Band compliance report, compa-ratio distribution, pay equity flags,
        equity value analysis, and total comp vs. market.
"""

import argparse
import json
import csv
import io
import sys
from dataclasses import dataclass, field, asdict
from typing import Optional
from datetime import date
import math


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass
class BandDefinition:
    """Salary band for a role level."""
    level: str          # L1, L2, L3, L4, M1, M2, M3, VP
    function: str       # Engineering, Sales, Product, G&A, Marketing, CS
    band_min: int       # Annual USD
    band_mid: int       # P50 anchor
    band_max: int       # Band ceiling
    market_p25: int     # Market 25th percentile
    market_p50: int     # Market median (should align with band_mid for P50 strategy)
    market_p75: int     # Market 75th percentile
    location_zone: str  # Tier1 (SF/NYC), Tier2 (Austin/Denver), Tier3 (Remote/other), EU


@dataclass
class Employee:
    """One employee record."""
    id: str
    name: str
    role: str
    level: str
    function: str
    location_zone: str
    base_salary: int
    bonus_target_pct: float   # % of base
    equity_shares: int        # Total unvested options/RSUs
    equity_strike: float      # Strike price (0 for RSUs)
    equity_current_409a: float  # Current 409A share price
    equity_vest_years_remaining: float  # How many years of vesting remain
    benefits_annual: int      # Employer-paid benefits cost
    gender: str               # M/F/NB/Undisclosed (for equity audit)
    ethnicity: str            # For equity audit — can be "Undisclosed"
    tenure_years: float
    performance_rating: int   # 1–5
    last_raise_months_ago: int
    last_equity_refresh_months_ago: Optional[int] = None


@dataclass
class CompRoster:
    company: str
    as_of_date: str             # ISO date
    funding_stage: str          # Seed, Series A, Series B, etc.
    comp_philosophy_target: str # P50, P65, P75 — your target percentile
    preferred_stock_price: float  # Last round price (for offer modeling)
    employees: list[Employee] = field(default_factory=list)
    bands: list[BandDefinition] = field(default_factory=list)


# ---------------------------------------------------------------------------
# Band lookup
# ---------------------------------------------------------------------------

def find_band(roster: CompRoster, level: str, function: str, zone: str) -> Optional[BandDefinition]:
    """Find best-matching band. Falls back to any matching level+function if zone not found."""
    matches = [b for b in roster.bands if b.level == level and b.function == function and b.location_zone == zone]
    if matches:
        return matches[0]
    # Fallback: same level+function, any zone
    matches = [b for b in roster.bands if b.level == level and b.function == function]
    if matches:
        return matches[0]
    # Fallback: same level, any function
    matches = [b for b in roster.bands if b.level == level]
    if matches:
        return matches[0]
    return None


# ---------------------------------------------------------------------------
# Compensation analysis
# ---------------------------------------------------------------------------

def compa_ratio(salary: int, band_mid: int) -> float:
    return salary / band_mid if band_mid > 0 else 0.0


def band_position(salary: int, band_min: int, band_max: int) -> float:
    """Position in band: 0.0 = at min, 1.0 = at max."""
    if band_max == band_min:
        return 0.5
    return (salary - band_min) / (band_max - band_min)


def annualized_equity_value(emp: Employee) -> int:
    """Current 409A value of unvested equity, annualized."""
    if emp.equity_vest_years_remaining <= 0:
        return 0
    if emp.equity_current_409a > emp.equity_strike:
        intrinsic = (emp.equity_current_409a - emp.equity_strike) * emp.equity_shares
    else:
        # Options underwater — still show at current FMV for RSUs or future value for options
        intrinsic = emp.equity_current_409a * emp.equity_shares if emp.equity_strike == 0 else 0
    return int(intrinsic / emp.equity_vest_years_remaining)


def total_comp(emp: Employee) -> int:
    bonus = int(emp.base_salary * emp.bonus_target_pct)
    equity = annualized_equity_value(emp)
    return emp.base_salary + bonus + equity + emp.benefits_annual


def analyze_employee(emp: Employee, roster: CompRoster) -> dict:
    band = find_band(roster, emp.level, emp.function, emp.location_zone)
    result = {
        "id": emp.id,
        "name": emp.name,
        "role": emp.role,
        "level": emp.level,
        "function": emp.function,
        "zone": emp.location_zone,
        "base": emp.base_salary,
        "bonus_target": int(emp.base_salary * emp.bonus_target_pct),
        "equity_annual": annualized_equity_value(emp),
        "benefits": emp.benefits_annual,
        "total_comp": total_comp(emp),
        "performance": emp.performance_rating,
        "tenure_years": emp.tenure_years,
        "last_raise_months": emp.last_raise_months_ago,
        "band": band,
        "compa_ratio": None,
        "band_position": None,
        "vs_market_p50": None,
        "flags": [],
    }

    if band:
        cr = compa_ratio(emp.base_salary, band.band_mid)
        bp = band_position(emp.base_salary, band.band_min, band.band_max)
        result["compa_ratio"] = round(cr, 3)
        result["band_position"] = round(bp, 3)
        result["vs_market_p50"] = round((emp.base_salary - band.market_p50) / band.market_p50 * 100, 1)

        # Flags
        if emp.base_salary < band.band_min:
            result["flags"].append(("CRITICAL", "Base below band minimum — immediate attrition risk"))
        elif cr < 0.88:
            result["flags"].append(("HIGH", f"Compa-ratio {cr:.2f} — significantly below midpoint"))
        elif cr < 0.93:
            result["flags"].append(("MEDIUM", f"Compa-ratio {cr:.2f} — below target zone (0.95–1.05)"))

        if emp.base_salary > band.band_max:
            result["flags"].append(("HIGH", "Base above band maximum — review for promotion or band update"))

        if emp.performance_rating >= 4 and cr < 0.95:
            result["flags"].append(("HIGH", f"High performer (rating {emp.performance_rating}) underpaid — flight risk"))

        if emp.last_raise_months_ago > 18:
            result["flags"].append(("MEDIUM", f"No raise in {emp.last_raise_months_ago} months — review due"))

        if emp.equity_vest_years_remaining < 1.0 and (emp.last_equity_refresh_months_ago is None or emp.last_equity_refresh_months_ago > 24):
            result["flags"].append(("HIGH", "Equity nearly fully vested with no refresh — retention hook gone"))

    else:
        result["flags"].append(("INFO", "No band found for this level/function/zone"))

    return result


# ---------------------------------------------------------------------------
# Aggregate analysis
# ---------------------------------------------------------------------------

def pay_equity_audit(analyses: list[dict], employees: list[Employee]) -> dict:
    """Simple pay equity analysis by gender and ethnicity."""
    emp_by_id = {e.id: e for e in employees}

    def group_stats(group_key_fn):
        groups: dict[str, list[float]] = {}
        for a in analyses:
            if a["compa_ratio"] is None:
                continue
            emp = emp_by_id.get(a["id"])
            if not emp:
                continue
            key = group_key_fn(emp)
            if key not in groups:
                groups[key] = []
            groups[key].append(a["compa_ratio"])
        return {k: {"n": len(v), "avg_cr": round(sum(v)/len(v), 3), "min_cr": round(min(v), 3), "max_cr": round(max(v), 3)}
                for k, v in groups.items() if v}

    gender_stats = group_stats(lambda e: e.gender)
    ethnicity_stats = group_stats(lambda e: e.ethnicity)

    # Compute gap vs. the largest group
    def compute_gap(stats: dict) -> dict[str, float]:
        if not stats:
            return {}
        largest = max(stats.items(), key=lambda x: x[1]["n"])
        ref_cr = largest[1]["avg_cr"]
        return {k: round((v["avg_cr"] - ref_cr) / ref_cr * 100, 1) for k, v in stats.items()}

    gender_gaps = compute_gap(gender_stats)
    ethnicity_gaps = compute_gap(ethnicity_stats)

    return {
        "gender": gender_stats,
        "gender_gaps_pct": gender_gaps,
        "ethnicity": ethnicity_stats,
        "ethnicity_gaps_pct": ethnicity_gaps,
    }


def compa_ratio_distribution(analyses: list[dict]) -> dict:
    crs = [a["compa_ratio"] for a in analyses if a["compa_ratio"] is not None]
    if not crs:
        return {}
    buckets = {
        "< 0.85 (below band)": 0,
        "0.85–0.94 (developing)": 0,
        "0.95–1.05 (target zone)": 0,
        "1.06–1.15 (senior in role)": 0,
        "> 1.15 (above band)": 0,
    }
    for cr in crs:
        if cr < 0.85:
            buckets["< 0.85 (below band)"] += 1
        elif cr < 0.95:
            buckets["0.85–0.94 (developing)"] += 1
        elif cr <= 1.05:
            buckets["0.95–1.05 (target zone)"] += 1
        elif cr <= 1.15:
            buckets["1.06–1.15 (senior in role)"] += 1
        else:
            buckets["> 1.15 (above band)"] += 1
    avg = sum(crs) / len(crs)
    return {"distribution": buckets, "avg_compa_ratio": round(avg, 3), "n": len(crs)}


# ---------------------------------------------------------------------------
# Report output
# ---------------------------------------------------------------------------

def fmt(n) -> str:
    return f"${int(n):,.0f}"


def bar(value: float, width: int = 20) -> str:
    filled = min(width, max(0, int(value * width)))
    return "█" * filled + "░" * (width - filled)


def print_report(roster: CompRoster):
    WIDTH = 76
    SEP = "=" * WIDTH
    sep = "-" * WIDTH

    analyses = [analyze_employee(e, roster) for e in roster.employees]
    cr_dist = compa_ratio_distribution(analyses)
    equity_audit = pay_equity_audit(analyses, roster.employees)

    print(SEP)
    print(f"  COMPENSATION BENCHMARKING REPORT — {roster.company}")
    print(f"  As of: {roster.as_of_date}  |  Stage: {roster.funding_stage}  |  Target: {roster.comp_philosophy_target}")
    print(SEP)

    # Summary stats
    total_emps = len(roster.employees)
    flagged = sum(1 for a in analyses if any(s in ["CRITICAL", "HIGH"] for s, _ in a["flags"]))
    total_payroll = sum(e.base_salary for e in roster.employees)
    avg_total_comp = sum(a["total_comp"] for a in analyses) // total_emps if total_emps else 0

    print(f"\n[ SUMMARY ]")
    print(sep)
    print(f"  Employees analyzed:      {total_emps}")
    print(f"  Flagged (critical/high): {flagged}")
    print(f"  Total base payroll:      {fmt(total_payroll)}/year")
    print(f"  Avg total comp:          {fmt(avg_total_comp)}/year")
    if cr_dist:
        print(f"  Avg compa-ratio:         {cr_dist['avg_compa_ratio']:.3f}")

    # Compa-ratio distribution
    if cr_dist:
        print(f"\n[ COMPA-RATIO DISTRIBUTION ]")
        print(sep)
        total_n = cr_dist["n"]
        for label, count in cr_dist["distribution"].items():
            pct = count / total_n if total_n else 0
            bar_str = bar(pct, 25)
            print(f"  {label:<30} {bar_str}  {count:3d} ({pct*100:4.0f}%)")

    # Pay equity audit
    print(f"\n[ PAY EQUITY AUDIT ]")
    print(sep)

    print(f"  By Gender:")
    for group, stats in equity_audit["gender"].items():
        gap = equity_audit["gender_gaps_pct"].get(group, 0.0)
        gap_str = f"  gap: {gap:+.1f}%" if gap != 0 else "  (reference group)"
        flag = " ⚠" if abs(gap) > 5 else ""
        print(f"    {group:<15} n={stats['n']}  avg_CR={stats['avg_cr']:.3f}{gap_str}{flag}")

    print(f"\n  By Ethnicity:")
    for group, stats in equity_audit["ethnicity"].items():
        gap = equity_audit["ethnicity_gaps_pct"].get(group, 0.0)
        gap_str = f"  gap: {gap:+.1f}%" if gap != 0 else "  (reference group)"
        flag = " ⚠" if abs(gap) > 5 else ""
        print(f"    {group:<20} n={stats['n']}  avg_CR={stats['avg_cr']:.3f}{gap_str}{flag}")

    print(f"\n  ⚠ = gap > 5%. Investigate with regression controlling for level, tenure, and performance.")

    # Employee detail with flags
    print(f"\n[ EMPLOYEE DETAIL ]")
    print(sep)

    # Group by function
    functions = sorted(set(e.function for e in roster.employees))
    for fn in functions:
        fn_analyses = [a for a in analyses if a["function"] == fn]
        if not fn_analyses:
            continue
        print(f"\n  ── {fn} ──")
        print(f"  {'Name':<22} {'Role':<28} {'Lvl':<5} {'Base':>10} {'TotalComp':>11} {'CR':>6} {'Perf':>5}  Flags")
        print(f"  {'-'*22} {'-'*28} {'-'*5} {'-'*10} {'-'*11} {'-'*6} {'-'*5}  {'-'*20}")

        for a in sorted(fn_analyses, key=lambda x: -x["base"]):
            cr_str = f"{a['compa_ratio']:.2f}" if a["compa_ratio"] else "N/A"
            flag_summary = ", ".join(s for s, _ in a["flags"] if s in ("CRITICAL", "HIGH", "MEDIUM"))
            flag_str = flag_summary if flag_summary else "OK"
            print(f"  {a['name']:<22} {a['role']:<28} {a['level']:<5} "
                  f"{fmt(a['base']):>10} {fmt(a['total_comp']):>11} {cr_str:>6} {a['performance']:>5}  {flag_str}")

            # Print flag detail for critical/high
            for severity, msg in a["flags"]:
                if severity in ("CRITICAL", "HIGH"):
                    print(f"  {'':>22}   ↳ [{severity}] {msg}")

    # Action items
    critical = [(a["name"], msg) for a in analyses for sev, msg in a["flags"] if sev == "CRITICAL"]
    high = [(a["name"], msg) for a in analyses for sev, msg in a["flags"] if sev == "HIGH"]
    medium = [(a["name"], msg) for a in analyses for sev, msg in a["flags"] if sev == "MEDIUM"]

    print(f"\n[ ACTION ITEMS ]")
    print(sep)

    if critical:
        print(f"\n  CRITICAL — Address this review cycle:")
        for name, msg in critical:
            print(f"    • {name}: {msg}")

    if high:
        print(f"\n  HIGH — Address within 30 days:")
        for name, msg in high[:10]:
            print(f"    • {name}: {msg}")
        if len(high) > 10:
            print(f"    ... and {len(high)-10} more")

    if medium:
        print(f"\n  MEDIUM — Address in next comp cycle:")
        for name, msg in medium[:8]:
            print(f"    • {name}: {msg}")
        if len(medium) > 8:
            print(f"    ... and {len(medium)-8} more")

    if not critical and not high and not medium:
        print(f"\n  No critical or high-severity issues. Compensation appears well-managed.")

    # Remediation cost estimate
    below_min = [a for a in analyses if a["band"] and a["base"] < a["band"].band_min]
    below_mid = [a for a in analyses if a["compa_ratio"] and a["compa_ratio"] < 0.90]

    if below_min or below_mid:
        print(f"\n[ REMEDIATION COST ESTIMATE ]")
        print(sep)

        if below_min:
            cost_to_min = sum(a["band"].band_min - a["base"] for a in below_min)
            print(f"  Cost to bring below-minimum to band min:  {fmt(cost_to_min)}/year  ({len(below_min)} employees)")

        if below_mid:
            cost_to_90 = sum(int(a["band"].band_mid * 0.90) - a["base"] for a in below_mid if a["base"] < int(a["band"].band_mid * 0.90))
            cost_to_90 = max(0, cost_to_90)
            print(f"  Cost to bring CR < 0.90 to CR = 0.90:    {fmt(cost_to_90)}/year  ({len(below_mid)} employees)")

        total_payroll_impact = sum(e.base_salary for e in roster.employees)
        total_remediation = (below_min and cost_to_min or 0)
        print(f"\n  Total payroll before remediation:  {fmt(total_payroll_impact)}/year")
        print(f"  Remediation as % of payroll:       {total_remediation/total_payroll_impact*100:.1f}%")

    print(f"\n{SEP}\n")


def export_csv(roster: CompRoster) -> str:
    analyses = [analyze_employee(e, roster) for e in roster.employees]
    output = io.StringIO()
    writer = csv.writer(output)
    writer.writerow(["ID", "Name", "Role", "Level", "Function", "Zone",
                     "Base", "Bonus Target", "Equity Annual", "Benefits", "Total Comp",
                     "Compa Ratio", "Band Position", "vs Market P50 %",
                     "Performance", "Tenure Years", "Last Raise (mo)",
                     "Gender", "Ethnicity", "Critical Flags", "High Flags"])
    for a, e in zip(analyses, roster.employees):
        critical_flags = "; ".join(msg for sev, msg in a["flags"] if sev == "CRITICAL")
        high_flags = "; ".join(msg for sev, msg in a["flags"] if sev == "HIGH")
        writer.writerow([a["id"], a["name"], a["role"], a["level"], a["function"], a["zone"],
                         a["base"], a["bonus_target"], a["equity_annual"], a["benefits"], a["total_comp"],
                         a["compa_ratio"], a["band_position"], a["vs_market_p50"],
                         a["performance"], a["tenure_years"], a["last_raise_months"],
                         e.gender, e.ethnicity, critical_flags, high_flags])
    return output.getvalue()


# ---------------------------------------------------------------------------
# Sample data
# ---------------------------------------------------------------------------

def build_sample_roster() -> CompRoster:
    roster = CompRoster(
        company="AcmeTech (Series A)",
        as_of_date=date.today().isoformat(),
        funding_stage="Series A",
        comp_philosophy_target="P50",
        preferred_stock_price=8.50,
    )

    # Bands (Engineering, P50 target, Tier1 = SF/NYC)
    roster.bands = [
        BandDefinition("L2", "Engineering", 115_000, 132_000, 155_000, 110_000, 132_000, 155_000, "Tier1"),
        BandDefinition("L3", "Engineering", 148_000, 170_000, 198_000, 145_000, 170_000, 198_000, "Tier1"),
        BandDefinition("L4", "Engineering", 185_000, 215_000, 248_000, 182_000, 215_000, 250_000, "Tier1"),
        BandDefinition("M1", "Engineering", 170_000, 195_000, 225_000, 168_000, 195_000, 225_000, "Tier1"),
        BandDefinition("L2", "Engineering", 95_000, 108_000, 125_000, 92_000, 108_000, 126_000, "Tier2"),
        BandDefinition("L3", "Engineering", 122_000, 140_000, 162_000, 120_000, 140_000, 162_000, "Tier2"),
        BandDefinition("L2", "Sales",       80_000,  92_000, 108_000,  78_000,  92_000, 108_000, "Tier1"),
        BandDefinition("L3", "Sales",       95_000, 110_000, 128_000,  93_000, 110_000, 128_000, "Tier1"),
        BandDefinition("M1", "Sales",      130_000, 150_000, 172_000, 128_000, 150_000, 172_000, "Tier1"),
        BandDefinition("L2", "Product",    125_000, 145_000, 168_000, 123_000, 145_000, 168_000, "Tier1"),
        BandDefinition("L3", "Product",    155_000, 178_000, 205_000, 153_000, 178_000, 205_000, "Tier1"),
        BandDefinition("L2", "G&A",         85_000,  98_000, 115_000,  83_000,  98_000, 115_000, "Tier1"),
        BandDefinition("L3", "G&A",        110_000, 128_000, 148_000, 108_000, 128_000, 148_000, "Tier1"),
    ]

    roster.employees = [
        # Engineering — mix of scenarios
        Employee("E001", "Aarav Shah", "Senior SWE (Backend)", "L3", "Engineering", "Tier1",
                 base_salary=168_000, bonus_target_pct=0.0, equity_shares=40_000,
                 equity_strike=1.50, equity_current_409a=6.80, equity_vest_years_remaining=2.5,
                 benefits_annual=18_000, gender="M", ethnicity="Asian",
                 tenure_years=2.5, performance_rating=4, last_raise_months_ago=14,
                 last_equity_refresh_months_ago=None),

        Employee("E002", "Yuki Tanaka", "Senior SWE (Frontend)", "L3", "Engineering", "Tier1",
                 base_salary=152_000, bonus_target_pct=0.0, equity_shares=30_000,
                 equity_strike=2.20, equity_current_409a=6.80, equity_vest_years_remaining=0.5,
                 benefits_annual=18_000, gender="F", ethnicity="Asian",
                 tenure_years=3.8, performance_rating=5, last_raise_months_ago=11,
                 last_equity_refresh_months_ago=30),
        # Note: Yuki is high performer, near-vested, no recent refresh — flag expected

        Employee("E003", "Marcus Johnson", "SWE II (Backend)", "L2", "Engineering", "Tier1",
                 base_salary=110_000, bonus_target_pct=0.0, equity_shares=15_000,
                 equity_strike=2.50, equity_current_409a=6.80, equity_vest_years_remaining=3.0,
                 benefits_annual=15_000, gender="M", ethnicity="Black",
                 tenure_years=1.2, performance_rating=3, last_raise_months_ago=12,
                 last_equity_refresh_months_ago=None),
        # Note: Below band midpoint, recently hired — developing flag

        Employee("E004", "Priya Nair", "Staff SWE", "L4", "Engineering", "Tier1",
                 base_salary=222_000, bonus_target_pct=0.0, equity_shares=60_000,
                 equity_strike=0.80, equity_current_409a=6.80, equity_vest_years_remaining=2.0,
                 benefits_annual=18_000, gender="F", ethnicity="Asian",
                 tenure_years=4.2, performance_rating=5, last_raise_months_ago=8,
                 last_equity_refresh_months_ago=8),

        Employee("E005", "Tom Rivera", "SWE II (Platform)", "L2", "Engineering", "Tier2",
                 base_salary=88_000, bonus_target_pct=0.0, equity_shares=12_000,
                 equity_strike=3.00, equity_current_409a=6.80, equity_vest_years_remaining=2.5,
                 benefits_annual=14_000, gender="M", ethnicity="Hispanic",
                 tenure_years=1.8, performance_rating=4, last_raise_months_ago=22,
                 last_equity_refresh_months_ago=None),
        # Note: No raise in 22 months, high performer — flag expected

        Employee("E006", "Sarah Kim", "Eng Manager", "M1", "Engineering", "Tier1",
                 base_salary=192_000, bonus_target_pct=0.10, equity_shares=35_000,
                 equity_strike=1.20, equity_current_409a=6.80, equity_vest_years_remaining=1.8,
                 benefits_annual=18_000, gender="F", ethnicity="Asian",
                 tenure_years=2.8, performance_rating=4, last_raise_months_ago=9,
                 last_equity_refresh_months_ago=9),

        # Sales
        Employee("S001", "David Chen", "Account Executive (MM)", "L3", "Sales", "Tier1",
                 base_salary=105_000, bonus_target_pct=0.50, equity_shares=8_000,
                 equity_strike=3.50, equity_current_409a=6.80, equity_vest_years_remaining=2.0,
                 benefits_annual=15_000, gender="M", ethnicity="Asian",
                 tenure_years=1.5, performance_rating=3, last_raise_months_ago=15,
                 last_equity_refresh_months_ago=None),

        Employee("S002", "Amara Osei", "AE (Mid-Market)", "L3", "Sales", "Tier1",
                 base_salary=98_000, bonus_target_pct=0.50, equity_shares=6_000,
                 equity_strike=3.50, equity_current_409a=6.80, equity_vest_years_remaining=2.5,
                 benefits_annual=15_000, gender="F", ethnicity="Black",
                 tenure_years=1.0, performance_rating=4, last_raise_months_ago=12,
                 last_equity_refresh_months_ago=None),
        # Note: High performer, significantly below midpoint — flag expected

        Employee("S003", "Jordan Blake", "Sales Manager", "M1", "Sales", "Tier1",
                 base_salary=155_000, bonus_target_pct=0.20, equity_shares=20_000,
                 equity_strike=2.00, equity_current_409a=6.80, equity_vest_years_remaining=1.5,
                 benefits_annual=16_000, gender="NB", ethnicity="White",
                 tenure_years=2.2, performance_rating=3, last_raise_months_ago=10,
                 last_equity_refresh_months_ago=10),

        # Product
        Employee("P001", "Nina Patel", "Senior PM", "L3", "Product", "Tier1",
                 base_salary=176_000, bonus_target_pct=0.10, equity_shares=22_000,
                 equity_strike=1.80, equity_current_409a=6.80, equity_vest_years_remaining=2.0,
                 benefits_annual=17_000, gender="F", ethnicity="Asian",
                 tenure_years=2.0, performance_rating=4, last_raise_months_ago=12,
                 last_equity_refresh_months_ago=12),

        # G&A
        Employee("G001", "Chris Mueller", "Finance Manager", "L3", "G&A", "Tier1",
                 base_salary=125_000, bonus_target_pct=0.10, equity_shares=10_000,
                 equity_strike=2.80, equity_current_409a=6.80, equity_vest_years_remaining=3.0,
                 benefits_annual=16_000, gender="M", ethnicity="White",
                 tenure_years=1.5, performance_rating=3, last_raise_months_ago=15,
                 last_equity_refresh_months_ago=None),

        Employee("G002", "Fatima Al-Hassan", "HR Operations", "L2", "G&A", "Tier1",
                 base_salary=82_000, bonus_target_pct=0.08, equity_shares=5_000,
                 equity_strike=4.00, equity_current_409a=6.80, equity_vest_years_remaining=3.5,
                 benefits_annual=14_000, gender="F", ethnicity="Middle Eastern",
                 tenure_years=0.8, performance_rating=3, last_raise_months_ago=8,
                 last_equity_refresh_months_ago=None),
        # Note: Below band minimum — critical flag expected
    ]

    return roster


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def load_roster_from_json(path: str) -> CompRoster:
    with open(path) as f:
        data = json.load(f)
    employees = [Employee(**e) for e in data.pop("employees", [])]
    bands = [BandDefinition(**b) for b in data.pop("bands", [])]
    roster = CompRoster(**data)
    roster.employees = employees
    roster.bands = bands
    return roster


def main():
    parser = argparse.ArgumentParser(
        description="Compensation Benchmarker — salary analysis and pay equity audit",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python comp_benchmarker.py                          # Run sample roster
  python comp_benchmarker.py --config roster.json     # Load from JSON
  python comp_benchmarker.py --export-csv             # Output CSV
  python comp_benchmarker.py --export-json            # Output JSON template
        """
    )
    parser.add_argument("--config", help="Path to JSON roster file")
    parser.add_argument("--export-csv", action="store_true", help="Export analysis as CSV")
    parser.add_argument("--export-json", action="store_true", help="Export sample roster as JSON template")
    args = parser.parse_args()

    if args.config:
        roster = load_roster_from_json(args.config)
    else:
        roster = build_sample_roster()

    if args.export_json:
        data = asdict(roster)
        print(json.dumps(data, indent=2))
        return

    if args.export_csv:
        print(export_csv(roster))
        return

    print_report(roster)


if __name__ == "__main__":
    main()
