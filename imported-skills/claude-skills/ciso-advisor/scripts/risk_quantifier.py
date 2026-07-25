#!/usr/bin/env python3
"""
CISO Risk Quantifier
====================
Quantifies security risks in business terms using the FAIR model.
Calculates ALE (Annual Loss Expectancy) and prioritizes by expected annual loss.

Usage:
  python risk_quantifier.py                    # Run with sample data
  python risk_quantifier.py --json             # Output JSON
  python risk_quantifier.py --csv output.csv   # Export CSV
  python risk_quantifier.py --budget 500000    # Show what fits in budget
  python risk_quantifier.py --add              # Interactive risk entry
"""

import json
import csv
import sys
import os
import argparse
from datetime import datetime
from typing import Optional


# ─── Data Model ─────────────────────────────────────────────────────────────

RISK_CATEGORIES = [
    "Data Breach",
    "Ransomware / Extortion",
    "Insider Threat",
    "Third-Party / Supply Chain",
    "Application Vulnerability",
    "Cloud Misconfiguration",
    "Social Engineering",
    "Physical Security",
    "Business Email Compromise",
    "DDoS / Availability",
]

BUSINESS_IMPACT_TYPES = [
    "Revenue Loss",
    "Regulatory Fine",
    "Legal / Litigation",
    "Reputational Damage",
    "Recovery / Remediation Cost",
    "Customer Churn",
    "Business Interruption",
]

MITIGATION_STATUSES = ["None", "Planned", "In Progress", "Mitigated", "Accepted"]


def build_risk(
    name: str,
    category: str,
    description: str,
    asset_value: float,
    exposure_factor: float,  # 0.0–1.0: fraction of asset value lost in breach
    annual_rate: float,      # ARO: expected incidents per year (0.01 = once per 100 years)
    mitigation_cost: float,
    mitigation_effectiveness: float,  # 0.0–1.0: fraction of risk reduced by control
    mitigation_status: str,
    business_impacts: dict,  # {impact_type: dollar_amount}
    notes: str = "",
) -> dict:
    """Construct a risk record with calculated metrics."""
    sle = asset_value * exposure_factor  # Single Loss Expectancy
    ale = sle * annual_rate             # Annual Loss Expectancy (inherent)
    mitigated_ale = ale * (1 - mitigation_effectiveness)  # Residual after mitigation
    mitigation_roi = ((ale - mitigated_ale - mitigation_cost) / mitigation_cost * 100
                      if mitigation_cost > 0 else 0)
    total_business_impact = sum(business_impacts.values())

    return {
        "name": name,
        "category": category,
        "description": description,
        "asset_value": asset_value,
        "exposure_factor": exposure_factor,
        "annual_rate": annual_rate,
        "mitigation_cost": mitigation_cost,
        "mitigation_effectiveness": mitigation_effectiveness,
        "mitigation_status": mitigation_status,
        "business_impacts": business_impacts,
        "notes": notes,
        # Calculated
        "sle": sle,
        "ale": ale,
        "mitigated_ale": mitigated_ale,
        "mitigation_roi_pct": mitigation_roi,
        "total_business_impact": total_business_impact,
        "priority_score": ale,  # Primary sort key
    }


# ─── Sample Data ─────────────────────────────────────────────────────────────

def load_sample_risks() -> list[dict]:
    """
    Sample risk register for a Series B SaaS company with ~$15M ARR,
    ~50K customer records, B2B enterprise focus.
    """
    risks = []

    risks.append(build_risk(
        name="Customer Database Breach",
        category="Data Breach",
        description=(
            "Unauthorized access to production database containing 50K+ customer records "
            "including PII (name, email, company, payment method). Attack vector: SQL injection, "
            "compromised credentials, or insider access."
        ),
        asset_value=5_000_000,   # Value of customer database (revenue impact + regulatory)
        exposure_factor=0.30,    # ~30% of asset value lost in a breach event
        annual_rate=0.12,        # ~12% chance per year (based on Verizon DBIR industry data)
        mitigation_cost=45_000,  # WAF + DAST + DB activity monitoring annual cost
        mitigation_effectiveness=0.80,
        mitigation_status="In Progress",
        business_impacts={
            "Regulatory Fine": 85_000,      # GDPR/CCPA exposure
            "Legal / Litigation": 150_000,  # Class action exposure
            "Customer Churn": 300_000,      # Lost ARR from breach-triggered churn
            "Reputational Damage": 200_000, # Brand impact / deal loss
            "Recovery / Remediation Cost": 65_000,
        },
        notes="SOC 2 Type II controls partially address. Next step: DB activity monitoring.",
    ))

    risks.append(build_risk(
        name="Ransomware Attack",
        category="Ransomware / Extortion",
        description=(
            "Ransomware encrypts production systems. Average ransom demand for a "
            "Series B company is $350K–$800K. Recovery without ransom payment: 2–6 weeks downtime. "
            "Attack vector: phishing email with malicious attachment, RDP exposure."
        ),
        asset_value=3_500_000,
        exposure_factor=0.25,
        annual_rate=0.15,
        mitigation_cost=60_000,  # EDR + email security + backup hardening
        mitigation_effectiveness=0.85,
        mitigation_status="Planned",
        business_impacts={
            "Business Interruption": 450_000,  # 4 weeks downtime × $112K/week revenue
            "Recovery / Remediation Cost": 180_000,
            "Customer Churn": 125_000,
            "Revenue Loss": 75_000,
        },
        notes="Offline, tested backups reduce recovery time and eliminate ransom pressure.",
    ))

    risks.append(build_risk(
        name="Privileged Insider Data Theft",
        category="Insider Threat",
        description=(
            "Disgruntled or financially motivated employee with elevated access exfiltrates "
            "customer data, IP, or trade secrets. Detection is typically slow (median: 197 days "
            "per IBM Cost of Data Breach Report)."
        ),
        asset_value=2_800_000,
        exposure_factor=0.20,
        annual_rate=0.08,
        mitigation_cost=35_000,  # DLP + UEBA + PAM
        mitigation_effectiveness=0.65,
        mitigation_status="None",
        business_impacts={
            "Legal / Litigation": 120_000,
            "Customer Churn": 90_000,
            "Reputational Damage": 75_000,
            "Recovery / Remediation Cost": 40_000,
        },
        notes="No DLP or UEBA currently deployed. Highest detection gap.",
    ))

    risks.append(build_risk(
        name="Critical SaaS Vendor Breach (Supply Chain)",
        category="Third-Party / Supply Chain",
        description=(
            "A critical SaaS vendor (e.g., Salesforce, Slack, AWS, GitHub) suffers a breach "
            "that compromises data entrusted to them or disrupts your operations. You have "
            "limited control but full liability to customers."
        ),
        asset_value=2_200_000,
        exposure_factor=0.15,
        annual_rate=0.18,
        mitigation_cost=20_000,  # Vendor risk assessment program
        mitigation_effectiveness=0.40,  # Limited — you can't control vendor security
        mitigation_status="Planned",
        business_impacts={
            "Business Interruption": 95_000,
            "Customer Churn": 75_000,
            "Reputational Damage": 50_000,
            "Recovery / Remediation Cost": 30_000,
        },
        notes="Third-party risk is partially transferable via contractual SLAs and cyber insurance.",
    ))

    risks.append(build_risk(
        name="Business Email Compromise (BEC)",
        category="Business Email Compromise",
        description=(
            "Attacker impersonates CEO, CFO, or vendor to redirect wire transfers, gift card "
            "purchases, or payroll. Median BEC loss: $125K. FBI IC3 reports BEC as #1 "
            "cybercrime by financial loss."
        ),
        asset_value=500_000,
        exposure_factor=0.40,
        annual_rate=0.30,
        mitigation_cost=12_000,  # Email authentication (DMARC) + training + callback procedures
        mitigation_effectiveness=0.90,
        mitigation_status="In Progress",
        business_impacts={
            "Revenue Loss": 125_000,       # Direct financial theft (often unrecoverable)
            "Recovery / Remediation Cost": 25_000,
            "Legal / Litigation": 15_000,
        },
        notes="DMARC deployed. Need to enforce wire transfer callback procedures.",
    ))

    risks.append(build_risk(
        name="Cloud Misconfiguration — S3 / Storage Exposure",
        category="Cloud Misconfiguration",
        description=(
            "Public exposure of S3 buckets, GCS buckets, or Azure Blob storage containing "
            "sensitive data. One of the most common causes of data breaches. Often undetected "
            "for months. 2023 IBM study: 82% of breaches involved data stored in cloud."
        ),
        asset_value=1_800_000,
        exposure_factor=0.20,
        annual_rate=0.20,
        mitigation_cost=18_000,  # CSPM tool + IaC scanning
        mitigation_effectiveness=0.90,
        mitigation_status="Planned",
        business_impacts={
            "Regulatory Fine": 60_000,
            "Reputational Damage": 120_000,
            "Legal / Litigation": 45_000,
            "Recovery / Remediation Cost": 35_000,
        },
        notes="No CSPM currently. High frequency, high detectability, low mitigation cost.",
    ))

    risks.append(build_risk(
        name="Credential Stuffing — Customer Accounts",
        category="Application Vulnerability",
        description=(
            "Attackers use leaked credential lists to compromise customer accounts. "
            "Account takeover leads to data theft, fraudulent transactions, and support burden. "
            "16 billion credentials available on darknet as of 2024."
        ),
        asset_value=1_200_000,
        exposure_factor=0.12,
        annual_rate=0.40,
        mitigation_cost=15_000,  # MFA + rate limiting + bot detection
        mitigation_effectiveness=0.95,
        mitigation_status="In Progress",
        business_impacts={
            "Customer Churn": 80_000,
            "Revenue Loss": 45_000,
            "Recovery / Remediation Cost": 19_000,
            "Reputational Damage": 30_000,
        },
        notes="MFA available but optional. Enforcing MFA cuts this risk by ~99%.",
    ))

    risks.append(build_risk(
        name="Phishing — Employee Credential Compromise",
        category="Social Engineering",
        description=(
            "Employee clicks phishing link, surrenders credentials. Without MFA, "
            "this provides full access to email, SaaS apps, and potentially production. "
            "Phishing is the #1 attack vector in the Verizon DBIR."
        ),
        asset_value=1_500_000,
        exposure_factor=0.15,
        annual_rate=0.35,
        mitigation_cost=25_000,  # MFA + security awareness training + email security
        mitigation_effectiveness=0.92,
        mitigation_status="In Progress",
        business_impacts={
            "Business Interruption": 65_000,
            "Customer Churn": 55_000,
            "Recovery / Remediation Cost": 45_000,
            "Reputational Damage": 60_000,
        },
        notes="Primary vector for ransomware and BEC. MFA is the single highest-ROI control.",
    ))

    risks.append(build_risk(
        name="Application API Vulnerability",
        category="Application Vulnerability",
        description=(
            "Unauthenticated or improperly authorized API endpoint exposes customer data "
            "or administrative functions. OWASP API Security Top 10 — broken object-level "
            "authorization is the most common API vulnerability."
        ),
        asset_value=2_000_000,
        exposure_factor=0.18,
        annual_rate=0.15,
        mitigation_cost=30_000,  # DAST + API gateway + code review
        mitigation_effectiveness=0.75,
        mitigation_status="Planned",
        business_impacts={
            "Regulatory Fine": 70_000,
            "Customer Churn": 90_000,
            "Reputational Damage": 100_000,
            "Legal / Litigation": 60_000,
        },
        notes="Need automated API security testing in CI/CD pipeline.",
    ))

    risks.append(build_risk(
        name="DDoS Attack — Production Service",
        category="DDoS / Availability",
        description=(
            "Distributed denial-of-service attack renders production service unavailable. "
            "Average DDoS duration: 4–8 hours. Enterprise SLA breach triggers contractual "
            "penalties. Increasingly used as extortion or distraction tactic."
        ),
        asset_value=1_000_000,
        exposure_factor=0.10,
        annual_rate=0.25,
        mitigation_cost=15_000,  # CDN with DDoS protection (Cloudflare, AWS Shield)
        mitigation_effectiveness=0.85,
        mitigation_status="Mitigated",
        business_impacts={
            "Business Interruption": 45_000,
            "Customer Churn": 30_000,
            "Revenue Loss": 25_000,
        },
        notes="Cloudflare deployed. Residual risk from very large volumetric attacks.",
    ))

    return risks


# ─── Analysis & Reporting ────────────────────────────────────────────────────

def calculate_portfolio_summary(risks: list[dict]) -> dict:
    """Aggregate portfolio-level metrics."""
    total_inherent_ale = sum(r["ale"] for r in risks)
    total_mitigated_ale = sum(r["mitigated_ale"] for r in risks)
    total_mitigation_cost = sum(r["mitigation_cost"] for r in risks)
    risk_reduction = total_inherent_ale - total_mitigated_ale
    portfolio_roi = ((risk_reduction - total_mitigation_cost) / total_mitigation_cost * 100
                     if total_mitigation_cost > 0 else 0)

    by_category = {}
    for r in risks:
        cat = r["category"]
        if cat not in by_category:
            by_category[cat] = {"count": 0, "total_ale": 0.0}
        by_category[cat]["count"] += 1
        by_category[cat]["total_ale"] += r["ale"]

    by_status = {}
    for r in risks:
        status = r["mitigation_status"]
        by_status[status] = by_status.get(status, 0) + 1

    return {
        "total_risks": len(risks),
        "total_inherent_ale": total_inherent_ale,
        "total_mitigated_ale": total_mitigated_ale,
        "total_risk_reduction": risk_reduction,
        "total_mitigation_cost": total_mitigation_cost,
        "portfolio_roi_pct": portfolio_roi,
        "by_category": dict(sorted(by_category.items(), key=lambda x: -x[1]["total_ale"])),
        "by_mitigation_status": by_status,
    }


def prioritize_risks(risks: list[dict], budget: Optional[float] = None) -> list[dict]:
    """Return risks sorted by ALE. If budget given, show what fits."""
    sorted_risks = sorted(risks, key=lambda r: -r["ale"])
    if budget is None:
        return sorted_risks

    # Greedy budget allocation by ROI
    actionable = [r for r in sorted_risks if r["mitigation_status"] in ("None", "Planned")
                  and r["mitigation_cost"] > 0]
    actionable.sort(key=lambda r: -r["mitigation_roi_pct"])

    allocated = []
    remaining = budget
    for risk in actionable:
        if risk["mitigation_cost"] <= remaining:
            allocated.append(risk)
            remaining -= risk["mitigation_cost"]

    return allocated


def fmt_dollars(amount: float) -> str:
    """Format a dollar amount."""
    if amount >= 1_000_000:
        return f"${amount/1_000_000:.2f}M"
    if amount >= 1_000:
        return f"${amount/1_000:.0f}K"
    return f"${amount:.0f}"


def fmt_pct(value: float) -> str:
    return f"{value:.1f}%"


def severity_label(ale: float) -> str:
    if ale >= 200_000:
        return "CRITICAL"
    if ale >= 75_000:
        return "HIGH"
    if ale >= 25_000:
        return "MEDIUM"
    return "LOW"


def severity_color(label: str) -> str:
    """ANSI color codes."""
    colors = {
        "CRITICAL": "\033[91m",  # Red
        "HIGH": "\033[93m",      # Yellow
        "MEDIUM": "\033[94m",    # Blue
        "LOW": "\033[92m",       # Green
    }
    return colors.get(label, "") + label + "\033[0m"


# ─── Display ─────────────────────────────────────────────────────────────────

def print_header():
    print("\n" + "=" * 80)
    print("  CISO RISK QUANTIFIER — Security Risk Portfolio")
    print(f"  Generated: {datetime.now().strftime('%Y-%m-%d %H:%M')}")
    print("=" * 80)


def print_portfolio_summary(summary: dict):
    print("\n📊 PORTFOLIO SUMMARY")
    print("-" * 60)
    print(f"  Total risks tracked:          {summary['total_risks']}")
    print(f"  Total inherent ALE:           {fmt_dollars(summary['total_inherent_ale'])}/yr")
    print(f"  Total ALE after mitigations:  {fmt_dollars(summary['total_mitigated_ale'])}/yr")
    print(f"  Risk reduction from controls: {fmt_dollars(summary['total_risk_reduction'])}/yr")
    print(f"  Total mitigation spend:       {fmt_dollars(summary['total_mitigation_cost'])}/yr")
    print(f"  Portfolio ROI:                {fmt_pct(summary['portfolio_roi_pct'])}")
    print()

    print("  Risk by Category (sorted by ALE):")
    for cat, data in summary["by_category"].items():
        print(f"    {cat:<35} {data['count']} risks  ALE: {fmt_dollars(data['total_ale'])}/yr")

    print()
    print("  Mitigation Status:")
    for status, count in summary["by_mitigation_status"].items():
        print(f"    {status:<20} {count} risks")


def print_risk_table(risks: list[dict], title: str = "RISK REGISTER"):
    print(f"\n🎯 {title}")
    print("-" * 80)
    header = f"{'#':<3} {'Risk Name':<35} {'Severity':<10} {'ALE/yr':<12} {'Mitig Cost':<12} {'ROI':<8} {'Status':<12}"
    print(header)
    print("-" * 80)

    for i, risk in enumerate(risks, 1):
        sev = severity_label(risk["ale"])
        sev_str = sev.ljust(10)
        roi = fmt_pct(risk["mitigation_roi_pct"]) if risk["mitigation_cost"] > 0 else "N/A"
        print(
            f"{i:<3} {risk['name'][:34]:<35} {sev_str} "
            f"{fmt_dollars(risk['ale']):<12} {fmt_dollars(risk['mitigation_cost']):<12} "
            f"{roi:<8} {risk['mitigation_status']}"
        )


def print_risk_detail(risk: dict, index: int):
    sev = severity_label(risk["ale"])
    print(f"\n{'─' * 70}")
    print(f"  #{index} — {risk['name']}  [{sev}]")
    print(f"{'─' * 70}")
    print(f"  Category:    {risk['category']}")
    print(f"  Description: {risk['description'][:120]}...")
    print()
    print(f"  RISK CALCULATION:")
    print(f"    Asset Value:             {fmt_dollars(risk['asset_value'])}")
    print(f"    Exposure Factor:         {fmt_pct(risk['exposure_factor'] * 100)}")
    print(f"    Single Loss Expectancy:  {fmt_dollars(risk['sle'])}")
    print(f"    Annual Rate (ARO):       {risk['annual_rate']:.2f}x/year")
    print(f"    Annual Loss Expectancy:  {fmt_dollars(risk['ale'])}/yr  ← INHERENT RISK")
    print()
    print(f"  MITIGATION:")
    print(f"    Mitigation Cost:         {fmt_dollars(risk['mitigation_cost'])}/yr")
    print(f"    Effectiveness:           {fmt_pct(risk['mitigation_effectiveness'] * 100)}")
    print(f"    Residual ALE:            {fmt_dollars(risk['mitigated_ale'])}/yr")
    print(f"    Mitigation ROI:          {fmt_pct(risk['mitigation_roi_pct'])}")
    print(f"    Status:                  {risk['mitigation_status']}")
    print()
    print(f"  BUSINESS IMPACT BREAKDOWN:")
    for impact_type, amount in risk["business_impacts"].items():
        print(f"    {impact_type:<30} {fmt_dollars(amount)}")
    print(f"    {'TOTAL':<30} {fmt_dollars(risk['total_business_impact'])}")
    if risk["notes"]:
        print(f"\n  NOTES: {risk['notes']}")


def print_board_summary(risks: list[dict], summary: dict):
    """One-page board-ready summary."""
    print("\n" + "═" * 80)
    print("  BOARD SECURITY REPORT — Risk Summary")
    print("═" * 80)

    critical = [r for r in risks if severity_label(r["ale"]) == "CRITICAL"]
    high = [r for r in risks if severity_label(r["ale"]) == "HIGH"]
    medium = [r for r in risks if severity_label(r["ale"]) == "MEDIUM"]
    low = [r for r in risks if severity_label(r["ale"]) == "LOW"]

    print(f"\n  RISK EXPOSURE SUMMARY")
    print(f"  ┌─────────────┬────────┬──────────────┐")
    print(f"  │ Severity    │ Count  │ Total ALE/yr │")
    print(f"  ├─────────────┼────────┼──────────────┤")
    for label, group in [("Critical", critical), ("High", high), ("Medium", medium), ("Low", low)]:
        ale = sum(r["ale"] for r in group)
        print(f"  │ {label:<11} │ {len(group):<6} │ {fmt_dollars(ale):<12} │")
    print(f"  └─────────────┴────────┴──────────────┘")

    print(f"\n  TOTAL INHERENT RISK:   {fmt_dollars(summary['total_inherent_ale'])}/yr")
    print(f"  SECURITY INVESTMENT:   {fmt_dollars(summary['total_mitigation_cost'])}/yr")
    print(f"  RESIDUAL RISK:         {fmt_dollars(summary['total_mitigated_ale'])}/yr")
    print(f"  RISK REDUCTION:        {fmt_dollars(summary['total_risk_reduction'])}/yr")
    print(f"  PORTFOLIO ROI:         {fmt_pct(summary['portfolio_roi_pct'])}")

    print(f"\n  TOP 3 RISKS BY EXPECTED ANNUAL LOSS:")
    top3 = sorted(risks, key=lambda r: -r["ale"])[:3]
    for i, risk in enumerate(top3, 1):
        print(f"    {i}. {risk['name']}: {fmt_dollars(risk['ale'])}/yr expected annual loss")
        print(f"       Mitigation: {fmt_dollars(risk['mitigation_cost'])}/yr | "
              f"Status: {risk['mitigation_status']}")

    unmitigated = [r for r in risks if r["mitigation_status"] == "None"]
    if unmitigated:
        print(f"\n  ⚠️  UNMITIGATED RISKS ({len(unmitigated)}):")
        for r in sorted(unmitigated, key=lambda x: -x["ale"]):
            print(f"    • {r['name']}: {fmt_dollars(r['ale'])}/yr — Action required")


def export_csv(risks: list[dict], filepath: str):
    fields = [
        "name", "category", "asset_value", "exposure_factor", "annual_rate",
        "sle", "ale", "mitigation_cost", "mitigation_effectiveness",
        "mitigated_ale", "mitigation_roi_pct", "mitigation_status", "notes"
    ]
    with open(filepath, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fields)
        writer.writeheader()
        for risk in risks:
            row = {k: risk.get(k, "") for k in fields}
            writer.writerow(row)
    print(f"✅ Exported {len(risks)} risks to {filepath}")


def export_json(risks: list[dict]) -> str:
    return json.dumps(risks, indent=2, default=str)


# ─── Interactive Entry ───────────────────────────────────────────────────────

def interactive_add_risk() -> dict:
    """Interactive CLI for adding a new risk."""
    print("\n── ADD NEW RISK ──────────────────────────────────────")
    name = input("Risk name: ").strip()

    print(f"Category options: {', '.join(RISK_CATEGORIES)}")
    category = input("Category: ").strip()

    description = input("Description (brief): ").strip()

    print("\nAsset valuation:")
    asset_value = float(input("  Asset value ($): ").replace(",", "").replace("$", ""))
    exposure_factor = float(input("  Exposure factor (0.0–1.0, fraction of value lost): "))
    annual_rate = float(input("  Annual rate of occurrence (e.g., 0.10 = once per 10 years): "))

    print("\nMitigation:")
    mitigation_cost = float(input("  Mitigation cost ($/yr): ").replace(",", "").replace("$", ""))
    mitigation_effectiveness = float(input("  Mitigation effectiveness (0.0–1.0): "))

    print(f"Status options: {', '.join(MITIGATION_STATUSES)}")
    mitigation_status = input("  Status: ").strip()

    print("\nBusiness impacts (enter 0 to skip):")
    business_impacts = {}
    for impact_type in BUSINESS_IMPACT_TYPES:
        val = input(f"  {impact_type} ($): ").replace(",", "").replace("$", "")
        amount = float(val) if val else 0
        if amount > 0:
            business_impacts[impact_type] = amount

    notes = input("\nNotes: ").strip()

    return build_risk(
        name=name,
        category=category,
        description=description,
        asset_value=asset_value,
        exposure_factor=exposure_factor,
        annual_rate=annual_rate,
        mitigation_cost=mitigation_cost,
        mitigation_effectiveness=mitigation_effectiveness,
        mitigation_status=mitigation_status,
        business_impacts=business_impacts,
        notes=notes,
    )


# ─── Main ────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="CISO Risk Quantifier — Quantify security risks in business terms"
    )
    parser.add_argument("--json", action="store_true", help="Output full JSON")
    parser.add_argument("--csv", metavar="FILE", help="Export CSV to file")
    parser.add_argument("--budget", type=float, metavar="DOLLARS",
                        help="Show recommended mitigations within budget")
    parser.add_argument("--board", action="store_true", help="Show board-ready summary only")
    parser.add_argument("--detail", action="store_true", help="Show detailed risk breakdowns")
    parser.add_argument("--add", action="store_true", help="Interactively add a risk")
    args = parser.parse_args()

    risks = load_sample_risks()

    if args.add:
        new_risk = interactive_add_risk()
        risks.append(new_risk)
        print(f"\n✅ Added risk: {new_risk['name']} | ALE: {fmt_dollars(new_risk['ale'])}/yr")

    # Sort by ALE descending
    risks_sorted = sorted(risks, key=lambda r: -r["ale"])
    summary = calculate_portfolio_summary(risks_sorted)

    if args.json:
        output = {
            "generated": datetime.now().isoformat(),
            "summary": summary,
            "risks": risks_sorted,
        }
        print(json.dumps(output, indent=2, default=str))
        return

    if args.csv:
        export_csv(risks_sorted, args.csv)
        return

    print_header()

    if args.board:
        print_board_summary(risks_sorted, summary)
        return

    print_portfolio_summary(summary)
    print_risk_table(risks_sorted)

    if args.detail:
        for i, risk in enumerate(risks_sorted, 1):
            print_risk_detail(risk, i)

    if args.budget:
        recommended = prioritize_risks(risks_sorted, args.budget)
        print(f"\n💰 BUDGET ALLOCATION — ${args.budget:,.0f}")
        print(f"   Recommended mitigations (sorted by ROI):")
        if recommended:
            for r in recommended:
                print(f"   • {r['name']}: {fmt_dollars(r['mitigation_cost'])}/yr "
                      f"| ALE reduction: {fmt_dollars(r['ale'] - r['mitigated_ale'])}/yr "
                      f"| ROI: {fmt_pct(r['mitigation_roi_pct'])}")
        else:
            print("   No actionable mitigations fit within budget.")

    print_board_summary(risks_sorted, summary)

    print("\n💡 NEXT STEPS")
    print("   1. Run `--detail` to see full breakdown of each risk")
    print("   2. Run `--budget 200000` to see what you can mitigate with a given budget")
    print("   3. Run `--board` for a board-ready one-page summary")
    print("   4. Run `--csv risks.csv` to export for stakeholder review")
    print("   5. Run `--add` to interactively add risks to the register")
    print()


if __name__ == "__main__":
    main()
