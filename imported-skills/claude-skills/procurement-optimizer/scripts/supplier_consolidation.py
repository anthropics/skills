#!/usr/bin/env python3
"""
supplier_consolidation.py — Duplicate-function clustering + risk-flagged consolidation plan.

Input: list of suppliers with category, annual spend, criticality tier, contract term,
integration count with other systems, switching cost estimate, renewal date, and an
optional break-glass flag for tier-1 suppliers.

Output: markdown consolidation plan that:
  - Clusters suppliers by category (duplicate-function detection)
  - Recommends a consolidation winner per cluster
  - REFUSES to recommend single-source consolidation for tier-1 categories without
    a documented break-glass plan
  - Estimates savings: current cluster spend - winner spend - migration cost
  - Surfaces renewal-date clusters (≥3 contracts in same calendar month destroys leverage)

Stdlib only. Deterministic. No LLM calls.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, field
from datetime import date, datetime
from pathlib import Path
from typing import Any


# ---------- Profile-driven category criticality overrides ----------

PROFILE_TIER1_CATEGORIES: dict[str, list[str]] = {
    "tech-startup": ["Cloud Infrastructure", "Data Warehouse", "Security Tooling", "CRM Platform"],
    "scaleup": ["Cloud Infrastructure", "CRM Platform", "HRIS / Payroll", "Data Warehouse"],
    "enterprise": ["Cloud Infrastructure", "HRIS / Payroll", "Business Insurance", "Outside Counsel"],
    "services": ["CRM Platform", "Outside Counsel", "Contractor / Freelance"],
    "manufacturing": ["Endpoint Devices", "Business Insurance", "Utilities"],
}


# ---------- Data model ----------

@dataclass
class Supplier:
    name: str
    category: str
    annual_spend: float
    criticality: str  # tier-1 | tier-2 | tier-3
    contract_term_months: int
    integration_count_with_other_systems: int
    switching_cost_estimate: float
    renewal_date: date | None
    break_glass_documented: bool = False

    @staticmethod
    def _parse_date(d: Any) -> date | None:
        if not d:
            return None
        if isinstance(d, date):
            return d
        try:
            return datetime.strptime(str(d)[:10], "%Y-%m-%d").date()
        except ValueError:
            return None

    @classmethod
    def from_dict(cls, d: dict[str, Any]) -> "Supplier":
        return cls(
            name=str(d.get("name", "")),
            category=str(d.get("category", "Uncategorized")),
            annual_spend=float(d.get("annual_spend", 0.0)),
            criticality=str(d.get("criticality", "tier-3")).lower(),
            contract_term_months=int(d.get("contract_term_months", 12)),
            integration_count_with_other_systems=int(
                d.get("integration_count_with_other_systems", 0)
            ),
            switching_cost_estimate=float(d.get("switching_cost_estimate", 0.0)),
            renewal_date=cls._parse_date(d.get("renewal_date")),
            break_glass_documented=bool(d.get("break_glass_documented", False)),
        )


@dataclass
class ClusterRecommendation:
    category: str
    members: list[Supplier]
    winner: Supplier | None
    losers: list[Supplier]
    annual_savings: float
    migration_cost: float
    net_year1_savings: float
    risk_flag: str  # OK | TIER1_NO_BREAKGLASS | LOW_SAVINGS
    rationale: str


# ---------- Clustering ----------

def cluster_by_category(suppliers: list[Supplier]) -> dict[str, list[Supplier]]:
    """Group suppliers by category; only categories with >= 2 suppliers are candidate clusters."""
    by_cat: dict[str, list[Supplier]] = {}
    for s in suppliers:
        by_cat.setdefault(s.category, []).append(s)
    return {cat: members for cat, members in by_cat.items() if len(members) >= 2}


# ---------- Winner selection ----------

def pick_winner(members: list[Supplier]) -> Supplier:
    """
    Winner selection:
      - If any member is tier-1, the highest-spend tier-1 wins (assume it has the most integrations and least switching cost away from).
      - If cluster is tier-2/3 only, the member with lowest total cost = (annual_spend - other_members_spend) + their switching_cost_estimate.
        Simpler proxy: highest integration_count_with_other_systems wins (the one that's most embedded).
        Tiebreak by lowest switching_cost_estimate.
    """
    tier1 = [m for m in members if m.criticality == "tier-1"]
    if tier1:
        return max(tier1, key=lambda m: m.annual_spend)

    return max(
        members,
        key=lambda m: (m.integration_count_with_other_systems, -m.switching_cost_estimate),
    )


# ---------- Risk assessment ----------

def assess_risk(
    category: str,
    members: list[Supplier],
    winner: Supplier,
    profile: str,
    annual_savings: float,
) -> str:
    """
    Risk classification:
      - TIER1_NO_BREAKGLASS — any tier-1 in cluster (or category is tier-1 by profile) AND winner has no break_glass_documented
      - LOW_SAVINGS — net Y1 savings < $10k (consolidating not worth the operational disruption)
      - OK — proceed
    """
    profile_tier1 = PROFILE_TIER1_CATEGORIES.get(profile, [])
    has_tier1_member = any(m.criticality == "tier-1" for m in members)
    is_tier1_category = category in profile_tier1

    if (has_tier1_member or is_tier1_category) and not winner.break_glass_documented:
        return "TIER1_NO_BREAKGLASS"

    if annual_savings < 10000:
        return "LOW_SAVINGS"

    return "OK"


# ---------- Plan generation ----------

def build_recommendations(
    suppliers: list[Supplier],
    profile: str,
) -> list[ClusterRecommendation]:
    clusters = cluster_by_category(suppliers)
    recs: list[ClusterRecommendation] = []

    for cat, members in clusters.items():
        winner = pick_winner(members)
        losers = [m for m in members if m.name != winner.name]
        if not losers:
            continue

        annual_savings = sum(m.annual_spend for m in losers)
        migration_cost = sum(m.switching_cost_estimate for m in losers)
        net_y1 = annual_savings - migration_cost
        risk = assess_risk(cat, members, winner, profile, annual_savings)

        if risk == "TIER1_NO_BREAKGLASS":
            rationale = (
                "DO NOT CONSOLIDATE — tier-1 category, no documented break-glass plan. "
                "Add a 72-hour contingency plan for the surviving supplier first, then revisit."
            )
        elif risk == "LOW_SAVINGS":
            rationale = (
                f"Marginal — net Y1 savings ${net_y1:,.0f} likely consumed by operational disruption. "
                "Defer unless integration debt or vendor risk justifies it."
            )
        else:
            rationale = (
                f"Consolidate to {winner.name}. {len(losers)} supplier(s) to offboard. "
                f"Net Y1 savings ${net_y1:,.0f} (gross ${annual_savings:,.0f} − migration ${migration_cost:,.0f})."
            )

        recs.append(ClusterRecommendation(
            category=cat,
            members=members,
            winner=winner,
            losers=losers,
            annual_savings=annual_savings,
            migration_cost=migration_cost,
            net_year1_savings=net_y1,
            risk_flag=risk,
            rationale=rationale,
        ))

    # Sort by net savings descending (biggest opportunities first)
    recs.sort(key=lambda r: -r.net_year1_savings)
    return recs


# ---------- Renewal cluster analysis ----------

def renewal_clusters(suppliers: list[Supplier]) -> dict[str, list[Supplier]]:
    """Find calendar months where >=3 contracts renew (zero leverage)."""
    by_month: dict[str, list[Supplier]] = {}
    for s in suppliers:
        if s.renewal_date is None:
            continue
        key = s.renewal_date.strftime("%Y-%m")
        by_month.setdefault(key, []).append(s)
    return {month: members for month, members in by_month.items() if len(members) >= 3}


# ---------- Rendering ----------

def render_markdown(
    profile: str,
    suppliers: list[Supplier],
    recs: list[ClusterRecommendation],
    renewals: dict[str, list[Supplier]],
) -> str:
    total_spend = sum(s.annual_spend for s in suppliers)
    total_net_savings = sum(
        r.net_year1_savings for r in recs if r.risk_flag == "OK"
    )

    lines: list[str] = []
    lines.append(f"# Supplier Consolidation Plan ({profile} profile)\n")
    lines.append(f"- **Suppliers analyzed:** {len(suppliers)}")
    lines.append(f"- **Total annual spend:** ${total_spend:,.0f}")
    lines.append(f"- **Duplicate-function clusters:** {len(recs)}")
    lines.append(f"- **Net Year-1 savings opportunity (OK clusters only):** ${total_net_savings:,.0f}\n")

    if not recs:
        lines.append("No duplicate-function clusters detected. No consolidation plan generated.\n")
    else:
        lines.append("## Recommendations (ranked by net Y1 savings)\n")
        for r in recs:
            badge = {
                "OK": "RECOMMEND",
                "TIER1_NO_BREAKGLASS": "DO NOT CONSOLIDATE",
                "LOW_SAVINGS": "DEFER",
            }[r.risk_flag]
            lines.append(f"### {r.category} — {badge}\n")
            lines.append(f"**Cluster:** {len(r.members)} suppliers — " +
                         ", ".join(f"{m.name} (${m.annual_spend:,.0f}, {m.criticality})" for m in r.members))
            if r.winner is not None:
                lines.append(f"\n**Proposed winner:** {r.winner.name} "
                             f"(integrations={r.winner.integration_count_with_other_systems}, "
                             f"break-glass={'yes' if r.winner.break_glass_documented else 'no'})")
            lines.append(f"\n**Offboard:** " + (", ".join(m.name for m in r.losers) or "—"))
            lines.append(f"\n- Gross annual savings: ${r.annual_savings:,.0f}")
            lines.append(f"- Migration cost: ${r.migration_cost:,.0f}")
            lines.append(f"- **Net Y1 savings: ${r.net_year1_savings:,.0f}**")
            lines.append(f"- Risk flag: `{r.risk_flag}`")
            lines.append(f"\n{r.rationale}\n")

    # Renewal-date clustering analysis
    lines.append("## Renewal-date clusters (negotiation leverage)\n")
    if not renewals:
        lines.append("No calendar months with ≥ 3 simultaneous renewals. Leverage is preserved.\n")
    else:
        lines.append(f"**{len(renewals)} month(s) have ≥ 3 simultaneous renewals — leverage destroyed:**\n")
        for month, members in sorted(renewals.items()):
            lines.append(f"### {month} — {len(members)} renewals\n")
            for m in members:
                lines.append(
                    f"- {m.name} ({m.category}) — ${m.annual_spend:,.0f}, renewal {m.renewal_date}"
                )
            lines.append("")
        lines.append(
            "Action: stagger renewals across the year. Renegotiate term lengths at next renewal "
            "(e.g., 18-month + 6-month + 12-month) to permanently de-cluster.\n"
        )

    # Action summary
    lines.append("## Action summary\n")
    ok_recs = [r for r in recs if r.risk_flag == "OK"]
    tier1_blocked = [r for r in recs if r.risk_flag == "TIER1_NO_BREAKGLASS"]
    deferred = [r for r in recs if r.risk_flag == "LOW_SAVINGS"]
    lines.append(f"- **Proceed now ({len(ok_recs)}):** " +
                 (", ".join(r.category for r in ok_recs) or "—"))
    lines.append(f"- **Blocked on break-glass plan ({len(tier1_blocked)}):** " +
                 (", ".join(r.category for r in tier1_blocked) or "—"))
    lines.append(f"- **Defer ({len(deferred)}):** " +
                 (", ".join(r.category for r in deferred) or "—"))
    return "\n".join(lines)


# ---------- Sample data ----------

SAMPLE_INPUT: list[dict[str, Any]] = [
    # Monitoring cluster (3 tools, tier-2)
    {"name": "Datadog", "category": "Monitoring / Observability", "annual_spend": 180000,
     "criticality": "tier-2", "contract_term_months": 12,
     "integration_count_with_other_systems": 12,
     "switching_cost_estimate": 80000, "renewal_date": "2026-09-15",
     "break_glass_documented": False},
    {"name": "New Relic", "category": "Monitoring / Observability", "annual_spend": 90000,
     "criticality": "tier-2", "contract_term_months": 12,
     "integration_count_with_other_systems": 4,
     "switching_cost_estimate": 25000, "renewal_date": "2026-09-30",
     "break_glass_documented": False},
    {"name": "Grafana Cloud", "category": "Monitoring / Observability", "annual_spend": 45000,
     "criticality": "tier-2", "contract_term_months": 12,
     "integration_count_with_other_systems": 6,
     "switching_cost_estimate": 18000, "renewal_date": "2026-09-22",
     "break_glass_documented": False},
    # Expense cluster (2 tools, tier-3)
    {"name": "Ramp", "category": "Expense / Spend Management", "annual_spend": 30000,
     "criticality": "tier-3", "contract_term_months": 12,
     "integration_count_with_other_systems": 8,
     "switching_cost_estimate": 15000, "renewal_date": "2026-09-10",
     "break_glass_documented": True},
    {"name": "Expensify", "category": "Expense / Spend Management", "annual_spend": 12000,
     "criticality": "tier-3", "contract_term_months": 12,
     "integration_count_with_other_systems": 2,
     "switching_cost_estimate": 5000, "renewal_date": "2026-09-05",
     "break_glass_documented": True},
    # Email marketing cluster (4 tools, tier-2 — note the tier-1 will trigger guard)
    {"name": "Klaviyo", "category": "Email Marketing Platform", "annual_spend": 36000,
     "criticality": "tier-1", "contract_term_months": 12,
     "integration_count_with_other_systems": 10,
     "switching_cost_estimate": 25000, "renewal_date": "2026-11-15",
     "break_glass_documented": False},
    {"name": "Mailchimp", "category": "Email Marketing Platform", "annual_spend": 8000,
     "criticality": "tier-3", "contract_term_months": 12,
     "integration_count_with_other_systems": 1,
     "switching_cost_estimate": 2000, "renewal_date": "2026-03-15",
     "break_glass_documented": False},
    {"name": "Iterable", "category": "Email Marketing Platform", "annual_spend": 50000,
     "criticality": "tier-2", "contract_term_months": 12,
     "integration_count_with_other_systems": 5,
     "switching_cost_estimate": 15000, "renewal_date": "2026-04-30",
     "break_glass_documented": False},
    {"name": "SendGrid", "category": "Email Marketing Platform", "annual_spend": 18000,
     "criticality": "tier-2", "contract_term_months": 12,
     "integration_count_with_other_systems": 4,
     "switching_cost_estimate": 8000, "renewal_date": "2026-06-30",
     "break_glass_documented": False},
    # AWS — single supplier, tier-1, not a cluster
    {"name": "AWS", "category": "Cloud Infrastructure", "annual_spend": 720000,
     "criticality": "tier-1", "contract_term_months": 36,
     "integration_count_with_other_systems": 40,
     "switching_cost_estimate": 600000, "renewal_date": "2027-03-31",
     "break_glass_documented": True},
]


# ---------- CLI ----------

def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--input", type=str, help="Path to JSON list of supplier records")
    p.add_argument(
        "--profile",
        type=str,
        default="tech-startup",
        choices=sorted(PROFILE_TIER1_CATEGORIES.keys()),
        help="Industry profile (default: tech-startup)",
    )
    p.add_argument("--output", type=str, help="Path to write markdown plan")
    p.add_argument("--sample", action="store_true", help="Run with built-in sample data")
    args = p.parse_args(argv)

    if args.sample:
        data = SAMPLE_INPUT
    elif args.input:
        try:
            data = json.loads(Path(args.input).read_text())
        except Exception as e:
            print(f"error reading {args.input}: {e}", file=sys.stderr)
            return 2
    else:
        p.print_help()
        return 0

    suppliers = [Supplier.from_dict(d) for d in data]
    recs = build_recommendations(suppliers, args.profile)
    renewals = renewal_clusters(suppliers)
    md = render_markdown(args.profile, suppliers, recs, renewals)

    if args.output:
        Path(args.output).write_text(md)
        print(f"wrote {args.output}")
    else:
        print(md)
    return 0


if __name__ == "__main__":
    sys.exit(main())
