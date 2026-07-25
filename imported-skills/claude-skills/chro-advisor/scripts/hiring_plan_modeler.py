#!/usr/bin/env python3
"""
Hiring Plan Modeler
===================
Builds hiring plans from business goals with cost projections.
Outputs quarterly headcount plan, cost model, and risk assessment.

Usage:
    python hiring_plan_modeler.py                    # Run with built-in sample data
    python hiring_plan_modeler.py --config plan.json # Load from JSON config
    python hiring_plan_modeler.py --help
"""

import argparse
import json
import sys
from dataclasses import dataclass, field, asdict
from datetime import datetime, date
from typing import Optional
import csv
import io


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass
class HireTarget:
    """One planned hire."""
    role: str
    level: str              # L1, L2, L3, L4, M1, M2, M3, VP, C-Suite
    function: str           # Engineering, Sales, Product, G&A, Marketing, CS
    quarter: str            # Q1-2025, Q2-2025, etc.
    base_salary: int        # Annual, USD
    bonus_pct: float        # % of base (e.g., 0.10 for 10%)
    equity_annual_usd: int  # Annualized equity value at current 409A
    benefits_annual: int    # Employer-paid benefits
    recruiter_fee_pct: float= 0.20  # Agency fee if used (0 for internal recruiter)
    ramp_months: int        = 3     # Months to full productivity
    priority: str           = "High"  # High / Medium / Low
    business_case: str      = ""
    open_to_internal: bool  = False


@dataclass
class HiringPlan:
    company: str
    plan_period: str        # e.g., "2025 Annual"
    current_headcount: int
    target_revenue: int     # Annual target revenue ($)
    current_revenue: int    # Current ARR ($)
    hires: list[HireTarget] = field(default_factory=list)

    # Cost overheads beyond comp
    overhead_rate: float = 0.25     # Workspace, software, onboarding overhead as % of base
    internal_recruiter_cost: int = 0  # If you have an internal recruiter, annual cost


# ---------------------------------------------------------------------------
# Computation
# ---------------------------------------------------------------------------

def quarter_to_sortkey(q: str) -> tuple[int, int]:
    """Parse 'Q2-2025' → (2025, 2)"""
    parts = q.upper().split("-")
    if len(parts) == 2:
        q_num = int(parts[0].replace("Q", ""))
        year = int(parts[1])
        return (year, q_num)
    return (9999, 9)


def get_quarters(hires: list[HireTarget]) -> list[str]:
    """Return sorted unique quarters from hire list."""
    quarters = sorted(set(h.quarter for h in hires), key=quarter_to_sortkey)
    return quarters


def compute_hire_costs(hire: HireTarget) -> dict:
    """Compute total first-year cost for one hire."""
    total_comp = hire.base_salary + int(hire.base_salary * hire.bonus_pct) + hire.equity_annual_usd + hire.benefits_annual
    recruiter_fee = int(hire.base_salary * hire.recruiter_fee_pct)
    overhead = int(hire.base_salary * 0.25)  # workspace, tools, onboarding
    ramp_productivity_cost = int(hire.base_salary * (hire.ramp_months / 12))  # cost during ramp

    return {
        "base_salary": hire.base_salary,
        "target_bonus": int(hire.base_salary * hire.bonus_pct),
        "equity_annual": hire.equity_annual_usd,
        "benefits": hire.benefits_annual,
        "total_comp": total_comp,
        "recruiter_fee": recruiter_fee,
        "overhead": overhead,
        "ramp_cost": ramp_productivity_cost,
        "first_year_total": total_comp + recruiter_fee + overhead,
        "fully_loaded_first_year": total_comp + recruiter_fee + overhead + ramp_productivity_cost,
    }


def summarize_by_quarter(plan: HiringPlan) -> dict[str, dict]:
    """Aggregate headcount and costs per quarter."""
    quarters = get_quarters(plan.hires)
    summary = {}
    running_headcount = plan.current_headcount

    for q in quarters:
        q_hires = [h for h in plan.hires if h.quarter == q]
        q_costs = [compute_hire_costs(h) for h in q_hires]

        total_comp = sum(c["total_comp"] for c in q_costs)
        total_first_year = sum(c["first_year_total"] for c in q_costs)
        recruiter_fees = sum(c["recruiter_fee"] for c in q_costs)

        running_headcount += len(q_hires)

        summary[q] = {
            "new_hires": len(q_hires),
            "headcount_eop": running_headcount,
            "total_annual_comp_added": total_comp,
            "total_first_year_cost": total_first_year,
            "recruiter_fees": recruiter_fees,
            "hires": q_hires,
            "costs": q_costs,
        }

    return summary


def summarize_by_function(plan: HiringPlan) -> dict[str, dict]:
    """Aggregate headcount and costs per function."""
    functions: dict[str, dict] = {}
    for hire in plan.hires:
        fn = hire.function
        if fn not in functions:
            functions[fn] = {"count": 0, "total_comp": 0, "total_first_year": 0, "roles": []}
        costs = compute_hire_costs(hire)
        functions[fn]["count"] += 1
        functions[fn]["total_comp"] += costs["total_comp"]
        functions[fn]["total_first_year"] += costs["first_year_total"]
        functions[fn]["roles"].append(hire.role)
    return functions


def compute_totals(plan: HiringPlan) -> dict:
    all_costs = [compute_hire_costs(h) for h in plan.hires]
    total_hires = len(plan.hires)
    total_comp = sum(c["total_comp"] for c in all_costs)
    total_first_year = sum(c["first_year_total"] for c in all_costs)
    total_fully_loaded = sum(c["fully_loaded_first_year"] for c in all_costs)
    total_recruiter = sum(c["recruiter_fee"] for c in all_costs)

    final_headcount = plan.current_headcount + total_hires
    revenue_per_employee = plan.target_revenue / final_headcount if final_headcount > 0 else 0
    revenue_per_employee_current = plan.current_revenue / plan.current_headcount if plan.current_headcount > 0 else 0

    return {
        "total_hires": total_hires,
        "final_headcount": final_headcount,
        "headcount_growth_pct": ((final_headcount - plan.current_headcount) / plan.current_headcount * 100) if plan.current_headcount > 0 else 0,
        "total_annual_comp_added": total_comp,
        "total_first_year_cost": total_first_year,
        "total_fully_loaded_first_year": total_fully_loaded,
        "total_recruiter_fees": total_recruiter,
        "revenue_per_employee_target": revenue_per_employee,
        "revenue_per_employee_current": revenue_per_employee_current,
        "avg_comp_per_hire": total_comp // total_hires if total_hires > 0 else 0,
    }


# ---------------------------------------------------------------------------
# Risk assessment
# ---------------------------------------------------------------------------

def assess_risks(plan: HiringPlan, totals: dict) -> list[dict]:
    risks = []

    # Headcount growth too fast
    growth_pct = totals["headcount_growth_pct"]
    if growth_pct > 80:
        risks.append({
            "severity": "HIGH",
            "category": "Execution",
            "finding": f"Headcount growing {growth_pct:.0f}% this period. "
                       "Culture and processes rarely scale this fast without breakage.",
            "recommendation": "Stagger Q3/Q4 hires. Validate Q1/Q2 cohort is onboarded before next wave."
        })
    elif growth_pct > 50:
        risks.append({
            "severity": "MEDIUM",
            "category": "Execution",
            "finding": f"Headcount growing {growth_pct:.0f}% — significant scaling challenge.",
            "recommendation": "Ensure onboarding infrastructure scales. Assign buddy/mentor to each hire."
        })

    # High concentration in one quarter
    quarters = get_quarters(plan.hires)
    q_counts = {q: sum(1 for h in plan.hires if h.quarter == q) for q in quarters}
    max_q = max(q_counts.values()) if q_counts else 0
    if max_q > len(plan.hires) * 0.5 and max_q > 4:
        heavy_q = [q for q, c in q_counts.items() if c == max_q][0]
        risks.append({
            "severity": "MEDIUM",
            "category": "Hiring Execution",
            "finding": f"More than 50% of hires planned in {heavy_q} ({max_q} hires). "
                       "Recruiting capacity and onboarding bandwidth may be insufficient.",
            "recommendation": "Spread hires across quarters. Hiring pipeline needs to start 60–90 days before target start date."
        })

    # Revenue per employee declining
    if totals["revenue_per_employee_target"] < totals["revenue_per_employee_current"] * 0.7:
        risks.append({
            "severity": "HIGH",
            "category": "Financial",
            "finding": f"Revenue per employee declining from ${totals['revenue_per_employee_current']:,.0f} to "
                       f"${totals['revenue_per_employee_target']:,.0f} — a {((totals['revenue_per_employee_target']/totals['revenue_per_employee_current'])-1)*100:.0f}% drop.",
            "recommendation": "Validate that revenue model supports this headcount. Is target revenue achievable with this team?"
        })

    # Low priority hires consuming budget
    low_priority_hires = [h for h in plan.hires if h.priority == "Low"]
    if low_priority_hires:
        lp_cost = sum(compute_hire_costs(h)["first_year_total"] for h in low_priority_hires)
        risks.append({
            "severity": "MEDIUM",
            "category": "Prioritization",
            "finding": f"{len(low_priority_hires)} 'Low' priority hires consuming ${lp_cost:,.0f} in first-year costs.",
            "recommendation": "Consider deferring Low priority hires to preserve runway. Cut these first if budget tightens."
        })

    # Hires without business cases
    no_case = [h for h in plan.hires if not h.business_case]
    if no_case:
        risks.append({
            "severity": "MEDIUM",
            "category": "Governance",
            "finding": f"{len(no_case)} hires have no documented business case: {', '.join(h.role for h in no_case[:5])}{'...' if len(no_case) > 5 else ''}",
            "recommendation": "Every hire over $80K should have a written business case. What revenue or risk does this role address?"
        })

    # High recruiter fee exposure
    if totals["total_recruiter_fees"] > 100_000:
        risks.append({
            "severity": "LOW",
            "category": "Cost",
            "finding": f"${totals['total_recruiter_fees']:,.0f} in recruiter fees. "
                       "Consider whether internal recruiter investment would be cheaper at this hiring volume.",
            "recommendation": f"Internal recruiter at $120–150K fully loaded pays off at 3–4 hires/year vs. agency fees."
        })

    # No risks — that's itself a flag
    if not risks:
        risks.append({
            "severity": "INFO",
            "category": "General",
            "finding": "No major risks flagged. Plan appears well-structured.",
            "recommendation": "Validate assumptions: time-to-fill estimates, revenue model, and Q1 hiring pipeline status."
        })

    return risks


# ---------------------------------------------------------------------------
# Formatting / Output
# ---------------------------------------------------------------------------

def fmt(n: int) -> str:
    return f"${n:,.0f}"


def pct(n: float) -> str:
    return f"{n:.1f}%"


def print_report(plan: HiringPlan):
    WIDTH = 72
    SEP = "=" * WIDTH
    sep = "-" * WIDTH

    print(SEP)
    print(f"  HIRING PLAN: {plan.company}")
    print(f"  Period: {plan.plan_period}  |  Generated: {date.today().isoformat()}")
    print(SEP)

    totals = compute_totals(plan)
    q_summary = summarize_by_quarter(plan)
    fn_summary = summarize_by_function(plan)
    risks = assess_risks(plan, totals)

    # Executive summary
    print("\n[ EXECUTIVE SUMMARY ]")
    print(sep)
    print(f"  Current headcount:       {plan.current_headcount:>5}")
    print(f"  Planned hires:           {totals['total_hires']:>5}")
    print(f"  Final headcount:         {totals['final_headcount']:>5}  (+{totals['headcount_growth_pct']:.0f}%)")
    print(f"  Current ARR:             {fmt(plan.current_revenue):>12}")
    print(f"  Target revenue:          {fmt(plan.target_revenue):>12}")
    print(f"  Revenue/employee now:    {fmt(int(totals['revenue_per_employee_current'])):>12}")
    print(f"  Revenue/employee target: {fmt(int(totals['revenue_per_employee_target'])):>12}")
    print()
    print(f"  Total annual comp added: {fmt(totals['total_annual_comp_added']):>12}")
    print(f"  Total first-year cost:   {fmt(totals['total_first_year_cost']):>12}")
    print(f"  Fully loaded (w/ ramp):  {fmt(totals['total_fully_loaded_first_year']):>12}")
    print(f"  Recruiter fees:          {fmt(totals['total_recruiter_fees']):>12}")
    print(f"  Avg comp per hire:       {fmt(totals['avg_comp_per_hire']):>12}")

    # Quarterly breakdown
    print(f"\n[ QUARTERLY HEADCOUNT PLAN ]")
    print(sep)
    print(f"  {'Quarter':<10} {'New Hires':>10} {'HC (EOP)':>10} {'Comp Added':>14} {'1yr Cost':>14} {'Recruiter $':>12}")
    print(f"  {'-'*10} {'-'*10} {'-'*10} {'-'*14} {'-'*14} {'-'*12}")
    for q, data in q_summary.items():
        print(f"  {q:<10} {data['new_hires']:>10} {data['headcount_eop']:>10} "
              f"{fmt(data['total_annual_comp_added']):>14} "
              f"{fmt(data['total_first_year_cost']):>14} "
              f"{fmt(data['recruiter_fees']):>12}")

    # By function
    print(f"\n[ HEADCOUNT BY FUNCTION ]")
    print(sep)
    print(f"  {'Function':<18} {'Hires':>7} {'Annual Comp':>14} {'1yr Cost':>14}")
    print(f"  {'-'*18} {'-'*7} {'-'*14} {'-'*14}")
    for fn, data in sorted(fn_summary.items(), key=lambda x: -x[1]["count"]):
        print(f"  {fn:<18} {data['count']:>7} {fmt(data['total_comp']):>14} {fmt(data['total_first_year']):>14}")

    # Hire detail
    print(f"\n[ HIRE DETAIL ]")
    print(sep)
    print(f"  {'Role':<30} {'Fn':<14} {'Lvl':<6} {'Q':<8} {'Base':>10} {'Total Comp':>12} {'Priority':<8}")
    print(f"  {'-'*30} {'-'*14} {'-'*6} {'-'*8} {'-'*10} {'-'*12} {'-'*8}")
    for h in sorted(plan.hires, key=lambda x: quarter_to_sortkey(x.quarter)):
        costs = compute_hire_costs(h)
        print(f"  {h.role:<30} {h.function:<14} {h.level:<6} {h.quarter:<8} "
              f"{fmt(h.base_salary):>10} {fmt(costs['total_comp']):>12} {h.priority:<8}")
        if h.business_case:
            bc = h.business_case[:60] + "..." if len(h.business_case) > 60 else h.business_case
            print(f"  {'':>30}   ↳ {bc}")

    # Risk assessment
    print(f"\n[ RISK ASSESSMENT ]")
    print(sep)
    sev_order = {"HIGH": 0, "MEDIUM": 1, "LOW": 2, "INFO": 3}
    for risk in sorted(risks, key=lambda r: sev_order.get(r["severity"], 99)):
        sev = risk["severity"]
        marker = {"HIGH": "⚠ HIGH", "MEDIUM": "◆ MED ", "LOW": "◇ LOW ", "INFO": "ℹ INFO"}[sev]
        print(f"\n  [{marker}] {risk['category']}")
        # Wrap finding
        finding = risk["finding"]
        words = finding.split()
        line = "  Finding: "
        for w in words:
            if len(line) + len(w) + 1 > WIDTH - 2:
                print(line)
                line = "           " + w + " "
            else:
                line += w + " "
        if line.strip():
            print(line)
        reco = risk["recommendation"]
        words = reco.split()
        line = "  Action:  "
        for w in words:
            if len(line) + len(w) + 1 > WIDTH - 2:
                print(line)
                line = "           " + w + " "
            else:
                line += w + " "
        if line.strip():
            print(line)

    print(f"\n{SEP}\n")


def export_csv(plan: HiringPlan) -> str:
    """Return CSV of hire detail."""
    output = io.StringIO()
    writer = csv.writer(output)
    writer.writerow(["Role", "Function", "Level", "Quarter", "Priority",
                     "Base Salary", "Bonus Target", "Equity Annual", "Benefits",
                     "Total Comp", "Recruiter Fee", "Overhead", "First Year Total",
                     "Ramp Months", "Open to Internal", "Business Case"])
    for h in plan.hires:
        c = compute_hire_costs(h)
        writer.writerow([h.role, h.function, h.level, h.quarter, h.priority,
                         h.base_salary, c["target_bonus"], h.equity_annual_usd, h.benefits_annual,
                         c["total_comp"], c["recruiter_fee"], c["overhead"], c["first_year_total"],
                         h.ramp_months, h.open_to_internal, h.business_case])
    return output.getvalue()


# ---------------------------------------------------------------------------
# Sample data
# ---------------------------------------------------------------------------

def build_sample_plan() -> HiringPlan:
    """Sample Series A → B hiring plan."""
    plan = HiringPlan(
        company="AcmeTech (Series A)",
        plan_period="2025 Annual",
        current_headcount=32,
        current_revenue=3_500_000,
        target_revenue=8_000_000,
        overhead_rate=0.25,
        internal_recruiter_cost=140_000,
    )

    plan.hires = [
        # Q1 — Foundation hires
        HireTarget(
            role="Staff Software Engineer (Backend)",
            level="L4", function="Engineering", quarter="Q1-2025",
            base_salary=185_000, bonus_pct=0.0, equity_annual_usd=25_000,
            benefits_annual=18_000, recruiter_fee_pct=0.0, ramp_months=2,
            priority="High", open_to_internal=True,
            business_case="Core API team is bottleneck for 3 roadmap items. Staff-level needed to lead architecture."
        ),
        HireTarget(
            role="Account Executive (Mid-Market)",
            level="L3", function="Sales", quarter="Q1-2025",
            base_salary=95_000, bonus_pct=0.50, equity_annual_usd=10_000,
            benefits_annual=15_000, recruiter_fee_pct=0.18, ramp_months=4,
            priority="High",
            business_case="Pipeline coverage at 1.8x quota. Need 2.5x by Q2. AE adds $600K ARR/year at ramp."
        ),
        HireTarget(
            role="Product Designer (Senior)",
            level="L3", function="Product", quarter="Q1-2025",
            base_salary=145_000, bonus_pct=0.0, equity_annual_usd=18_000,
            benefits_annual=18_000, recruiter_fee_pct=0.0, ramp_months=2,
            priority="High",
            business_case="Single designer for 4 squads. UX debt slowing enterprise deals requiring onboarding improvements."
        ),

        # Q2 — Growth hires
        HireTarget(
            role="Engineering Manager (Frontend)",
            level="M1", function="Engineering", quarter="Q2-2025",
            base_salary=175_000, bonus_pct=0.10, equity_annual_usd=22_000,
            benefits_annual=18_000, recruiter_fee_pct=0.20, ramp_months=3,
            priority="High",
            business_case="Frontend team at 7 ICs with no dedicated EM. Performance review debt is high; manager needed."
        ),
        HireTarget(
            role="Account Executive (Mid-Market)",
            level="L2", function="Sales", quarter="Q2-2025",
            base_salary=85_000, bonus_pct=0.50, equity_annual_usd=8_000,
            benefits_annual=15_000, recruiter_fee_pct=0.18, ramp_months=4,
            priority="High",
            business_case="Second AE to reach 2.5x pipeline coverage target."
        ),
        HireTarget(
            role="Customer Success Manager",
            level="L2", function="Customer Success", quarter="Q2-2025",
            base_salary=90_000, bonus_pct=0.15, equity_annual_usd=8_000,
            benefits_annual=15_000, recruiter_fee_pct=0.0, ramp_months=2,
            priority="Medium",
            business_case="CSM:account ratio at 1:60, industry standard 1:30. NRR has dipped 4pts in 2 quarters."
        ),
        HireTarget(
            role="Data Engineer",
            level="L2", function="Engineering", quarter="Q2-2025",
            base_salary=155_000, bonus_pct=0.0, equity_annual_usd=18_000,
            benefits_annual=18_000, recruiter_fee_pct=0.0, ramp_months=3,
            priority="Medium",
            business_case="Analytics infrastructure blocking product analytics, customer dashboards, and board metrics."
        ),

        # Q3 — Scale hires
        HireTarget(
            role="Senior Software Engineer (Backend)",
            level="L3", function="Engineering", quarter="Q3-2025",
            base_salary=165_000, bonus_pct=0.0, equity_annual_usd=20_000,
            benefits_annual=18_000, recruiter_fee_pct=0.0, ramp_months=2,
            priority="High",
            business_case="Backend team needs capacity to deliver Q3 roadmap without delaying Q4 items."
        ),
        HireTarget(
            role="Head of Marketing",
            level="M3", function="Marketing", quarter="Q3-2025",
            base_salary=180_000, bonus_pct=0.15, equity_annual_usd=30_000,
            benefits_annual=18_000, recruiter_fee_pct=0.20, ramp_months=3,
            priority="High",
            business_case="No marketing function. 100% of pipeline is outbound. Need inbound by Q1-2026 for Series B."
        ),
        HireTarget(
            role="People Operations Manager",
            level="M1", function="G&A", quarter="Q3-2025",
            base_salary=120_000, bonus_pct=0.10, equity_annual_usd=12_000,
            benefits_annual=16_000, recruiter_fee_pct=0.0, ramp_months=2,
            priority="Medium",
            business_case="Founders spending 8hrs/week on HR ops at 40 employees. Unscalable. First dedicated HR hire."
        ),

        # Q4 — Stretch hires (conditional on revenue milestone)
        HireTarget(
            role="Senior Software Engineer (Frontend)",
            level="L3", function="Engineering", quarter="Q4-2025",
            base_salary=160_000, bonus_pct=0.0, equity_annual_usd=18_000,
            benefits_annual=18_000, recruiter_fee_pct=0.0, ramp_months=2,
            priority="Medium",
            business_case="Conditional on Q3 ARR exceeding $5.5M. Frontend team capacity planning for 2026 roadmap."
        ),
        HireTarget(
            role="Account Executive (Enterprise)",
            level="L4", function="Sales", quarter="Q4-2025",
            base_salary=120_000, bonus_pct=0.60, equity_annual_usd=15_000,
            benefits_annual=15_000, recruiter_fee_pct=0.20, ramp_months=6,
            priority="Low",
            business_case="Enterprise motion exploratory. Requires ICP validation in Q2-Q3 before committing."
        ),
        HireTarget(
            role="DevOps / Platform Engineer",
            level="L3", function="Engineering", quarter="Q4-2025",
            base_salary=150_000, bonus_pct=0.0, equity_annual_usd=18_000,
            benefits_annual=18_000, recruiter_fee_pct=0.0, ramp_months=3,
            priority="Low",
            business_case="Platform reliability becoming bottleneck. Conditional on uptime SLA breaches continuing in Q3."
        ),
    ]

    return plan


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def load_plan_from_json(path: str) -> HiringPlan:
    with open(path) as f:
        data = json.load(f)
    hires = [HireTarget(**h) for h in data.pop("hires", [])]
    plan = HiringPlan(**data)
    plan.hires = hires
    return plan


def main():
    parser = argparse.ArgumentParser(
        description="Hiring Plan Modeler — build headcount plans with cost projections",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python hiring_plan_modeler.py                       # Run sample plan
  python hiring_plan_modeler.py --config plan.json    # Load from JSON
  python hiring_plan_modeler.py --export-csv          # Output CSV of hires
  python hiring_plan_modeler.py --export-json         # Output plan as JSON template
        """
    )
    parser.add_argument("--config", help="Path to JSON plan file")
    parser.add_argument("--export-csv", action="store_true", help="Export hire detail as CSV")
    parser.add_argument("--export-json", action="store_true", help="Export sample plan as JSON template")
    args = parser.parse_args()

    if args.config:
        plan = load_plan_from_json(args.config)
    else:
        plan = build_sample_plan()

    if args.export_json:
        data = asdict(plan)
        print(json.dumps(data, indent=2))
        return

    if args.export_csv:
        print(export_csv(plan))
        return

    print_report(plan)


if __name__ == "__main__":
    main()
