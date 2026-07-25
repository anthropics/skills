#!/usr/bin/env python3
"""
Scenario War Room — Multi-Variable Cascade Modeler
Models cascading effects of compound adversity across business domains.
Stdlib only. Run with: python scenario_modeler.py
"""

import json
import sys
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple
from enum import Enum


class Severity(Enum):
    BASE = "base"       # One variable hits
    STRESS = "stress"   # Two variables hit
    SEVERE = "severe"   # All variables hit


class Domain(Enum):
    FINANCIAL = "Financial (CFO)"
    REVENUE = "Revenue (CRO)"
    PRODUCT = "Product (CPO)"
    ENGINEERING = "Engineering (CTO)"
    PEOPLE = "People (CHRO)"
    OPERATIONS = "Operations (COO)"
    SECURITY = "Security (CISO)"
    MARKET = "Market (CMO)"


@dataclass
class Variable:
    name: str
    description: str
    probability: float          # 0.0-1.0
    arrt_impact_pct: float      # % of ARR at risk (negative = loss)
    runway_impact_months: float # months lost from runway (negative = reduction)
    affected_domains: List[Domain]
    timeline_days: int          # when it hits


@dataclass
class CascadeEffect:
    trigger_domain: Domain
    caused_domain: Domain
    mechanism: str              # how A causes B
    severity_multiplier: float  # compounds the base impact


@dataclass
class Hedge:
    action: str
    cost_usd: int
    impact_description: str
    owner: str
    deadline_days: int
    reduces_probability: float  # how much it reduces scenario probability


@dataclass
class Scenario:
    name: str
    variables: List[Variable]
    cascades: List[CascadeEffect]
    hedges: List[Hedge]
    # Company baseline
    current_arr_usd: int = 2_000_000
    current_runway_months: int = 14
    monthly_burn_usd: int = 140_000


def calculate_impact(
    scenario: Scenario,
    severity: Severity
) -> Dict:
    """Calculate combined impact for a given severity level."""
    variables = scenario.variables

    # Select variables by severity
    if severity == Severity.BASE:
        active_vars = variables[:1]
    elif severity == Severity.STRESS:
        active_vars = variables[:2]
    else:
        active_vars = variables

    # Direct impacts
    total_arr_loss_pct = sum(abs(v.arrt_impact_pct) for v in active_vars)
    total_runway_reduction = sum(abs(v.runway_impact_months) for v in active_vars)

    arr_at_risk = scenario.current_arr_usd * (total_arr_loss_pct / 100)
    new_arr = scenario.current_arr_usd - arr_at_risk
    new_runway = scenario.current_runway_months - total_runway_reduction

    # Cascade multiplier (stress/severe amplify via domain cascades)
    cascade_multiplier = 1.0
    if len(active_vars) > 1:
        active_domains = set(d for v in active_vars for d in v.affected_domains)
        for cascade in scenario.cascades:
            if (cascade.trigger_domain in active_domains and
                    cascade.caused_domain in active_domains):
                cascade_multiplier *= cascade.severity_multiplier

    # Apply cascade
    effective_arr_loss = arr_at_risk * cascade_multiplier
    effective_arr = scenario.current_arr_usd - effective_arr_loss
    effective_runway = max(0, new_runway - (cascade_multiplier - 1.0) * 2)

    # New burn multiple
    new_monthly_burn = scenario.monthly_burn_usd * cascade_multiplier
    burn_multiple = (new_monthly_burn * 12) / max(effective_arr, 1)

    # Affected domains
    affected = set(d for v in active_vars for d in v.affected_domains)

    return {
        "severity": severity.value,
        "active_variables": [v.name for v in active_vars],
        "arr_at_risk_usd": int(effective_arr_loss),
        "arr_at_risk_pct": round(effective_arr_loss / scenario.current_arr_usd * 100, 1),
        "projected_arr_usd": int(effective_arr),
        "runway_months": round(effective_runway, 1),
        "runway_change": round(effective_runway - scenario.current_runway_months, 1),
        "cascade_multiplier": round(cascade_multiplier, 2),
        "new_burn_multiple": round(burn_multiple, 1),
        "affected_domains": [d.value for d in affected],
        "existential_risk": effective_runway < 6.0,
        "board_escalation_required": effective_runway < 9.0,
    }


def identify_triggers(variables: List[Variable]) -> List[Dict]:
    """Generate early warning triggers for each variable."""
    triggers = []
    for var in variables:
        trigger = {
            "variable": var.name,
            "timeline": f"Watch from day 1; expect signal ~{var.timeline_days // 2} days before impact",
            "signals": _generate_signals(var),
            "response_owner": _domain_to_owner(var.affected_domains[0] if var.affected_domains else Domain.FINANCIAL),
        }
        triggers.append(trigger)
    return triggers


def _generate_signals(var: Variable) -> List[str]:
    """Generate plausible early warning signals based on variable type."""
    signals = []
    name_lower = var.name.lower()

    if any(k in name_lower for k in ["customer", "churn", "account"]):
        signals = [
            "Executive sponsor unreachable for >2 weeks",
            "Product usage drops >20% month-over-month",
            "No QBR scheduled within 90 days of contract renewal",
            "Support ticket volume spikes >50% without explanation",
        ]
    elif any(k in name_lower for k in ["fundraise", "raise", "capital", "investor"]):
        signals = [
            "Fewer than 3 term sheets after 60 days of active process",
            "Lead investor requests 30+ day extension on diligence",
            "Comparable company raises at lower valuation (market signal)",
            "Investor meeting conversion rate below 20%",
        ]
    elif any(k in name_lower for k in ["engineer", "people", "team", "resign", "quit"]):
        signals = [
            "2+ engineers receive above-market counter-offer in 90 days",
            "Glassdoor activity increases from engineering team",
            "Key person requests 1:1 to 'talk about career' unexpectedly",
            "Referral interview requests from engineers increase",
        ]
    elif any(k in name_lower for k in ["market", "competitor", "competition"]):
        signals = [
            "Competitor raises $10M+ funding round",
            "Win/loss rate shifts >10% in 60 days",
            "Multiple prospects cite competitor by name in objections",
            "Competitor poaches 2+ of your customers in a quarter",
        ]
    else:
        signals = [
            f"Leading indicator for '{var.name}' deteriorates 20%+ vs baseline",
            "Weekly metric review shows 3-week trend in wrong direction",
            "External validation from customers or partners confirms risk",
        ]

    return signals[:3]  # Top 3


def _domain_to_owner(domain: Domain) -> str:
    mapping = {
        Domain.FINANCIAL: "CFO",
        Domain.REVENUE: "CRO",
        Domain.PRODUCT: "CPO",
        Domain.ENGINEERING: "CTO",
        Domain.PEOPLE: "CHRO",
        Domain.OPERATIONS: "COO",
        Domain.SECURITY: "CISO",
        Domain.MARKET: "CMO",
    }
    return mapping.get(domain, "CEO")


def format_currency(amount: int) -> str:
    if amount >= 1_000_000:
        return f"${amount / 1_000_000:.1f}M"
    elif amount >= 1_000:
        return f"${amount / 1_000:.0f}K"
    return f"${amount}"


def print_report(scenario: Scenario) -> None:
    """Print full scenario analysis report."""
    print("\n" + "=" * 70)
    print(f"SCENARIO WAR ROOM: {scenario.name.upper()}")
    print("=" * 70)

    # Baseline
    print(f"\n📊 BASELINE")
    print(f"   Current ARR:    {format_currency(scenario.current_arr_usd)}")
    print(f"   Monthly Burn:   {format_currency(scenario.monthly_burn_usd)}")
    print(f"   Runway:         {scenario.current_runway_months} months")

    # Variables
    print(f"\n⚡ SCENARIO VARIABLES ({len(scenario.variables)})")
    for i, var in enumerate(scenario.variables, 1):
        prob_pct = int(var.probability * 100)
        print(f"\n  Variable {i}: {var.name}")
        print(f"    {var.description}")
        print(f"    Probability: {prob_pct}%  |  Timeline: {var.timeline_days} days")
        print(f"    ARR impact: -{var.arrt_impact_pct}%  |  "
              f"Runway impact: -{var.runway_impact_months} months")
        print(f"    Affected: {', '.join(d.value for d in var.affected_domains)}")

    # Combined probability
    combined_prob = 1.0
    for var in scenario.variables:
        combined_prob *= var.probability
    print(f"\n  Combined probability (all hit): {combined_prob * 100:.1f}%")

    # Severity Levels
    print(f"\n{'=' * 70}")
    print("SEVERITY ANALYSIS")
    print("=" * 70)

    for severity in Severity:
        if severity == Severity.BASE and len(scenario.variables) < 1:
            continue
        if severity == Severity.STRESS and len(scenario.variables) < 2:
            continue

        impact = calculate_impact(scenario, severity)

        icon = {"base": "🟡", "stress": "🔴", "severe": "💀"}[impact["severity"]]
        print(f"\n{icon} {impact['severity'].upper()} SCENARIO")
        print(f"   Variables: {', '.join(impact['active_variables'])}")
        print(f"   ARR at risk: {format_currency(impact['arr_at_risk_usd'])} "
              f"({impact['arr_at_risk_pct']}%)")
        print(f"   Projected ARR: {format_currency(impact['projected_arr_usd'])}")
        print(f"   Runway: {impact['runway_months']} months "
              f"({impact['runway_change']:+.1f} months)")
        print(f"   Burn multiple: {impact['new_burn_multiple']}x")
        if impact['cascade_multiplier'] > 1.0:
            print(f"   Cascade amplifier: {impact['cascade_multiplier']}x "
                  f"(domains interact)")
        print(f"   Board escalation: {'⚠️  YES' if impact['board_escalation_required'] else 'No'}")
        print(f"   Existential risk: {'🚨 YES' if impact['existential_risk'] else 'No'}")

    # Cascade Map
    if scenario.cascades:
        print(f"\n{'=' * 70}")
        print("CASCADE MAP")
        print("=" * 70)
        for i, cascade in enumerate(scenario.cascades, 1):
            print(f"\n  [{i}] {cascade.trigger_domain.value}")
            print(f"       ↓ {cascade.mechanism}")
            print(f"       → {cascade.caused_domain.value} "
                  f"(amplified {cascade.severity_multiplier}x)")

    # Early Warning Triggers
    print(f"\n{'=' * 70}")
    print("EARLY WARNING TRIGGERS")
    print("=" * 70)
    triggers = identify_triggers(scenario.variables)
    for trigger in triggers:
        print(f"\n  📡 {trigger['variable']}")
        print(f"     Watch: {trigger['timeline']}")
        print(f"     Owner: {trigger['response_owner']}")
        for signal in trigger['signals']:
            print(f"     • {signal}")

    # Hedges
    if scenario.hedges:
        print(f"\n{'=' * 70}")
        print("HEDGING STRATEGIES (act now)")
        print("=" * 70)
        sorted_hedges = sorted(scenario.hedges,
                               key=lambda h: h.reduces_probability, reverse=True)
        for hedge in sorted_hedges:
            print(f"\n  ✅ {hedge.action}")
            print(f"     Cost: {format_currency(hedge.cost_usd)}/year  |  "
                  f"Owner: {hedge.owner}  |  Deadline: {hedge.deadline_days} days")
            print(f"     Impact: {hedge.impact_description}")
            print(f"     Risk reduction: {int(hedge.reduces_probability * 100)}%")

    print(f"\n{'=' * 70}\n")


def build_sample_scenario() -> Scenario:
    """Sample: Customer churn + fundraise miss compound scenario."""
    variables = [
        Variable(
            name="Top customer churn",
            description="Largest customer (28% of ARR) gives 60-day termination notice",
            probability=0.15,
            arrt_impact_pct=28.0,
            runway_impact_months=4.0,
            affected_domains=[
                Domain.FINANCIAL, Domain.REVENUE, Domain.OPERATIONS
            ],
            timeline_days=60,
        ),
        Variable(
            name="Series A delayed 6 months",
            description="Fundraise process extends beyond target close; bridge required",
            probability=0.25,
            arrt_impact_pct=0.0,         # No ARR impact directly
            runway_impact_months=3.0,     # Bridge terms reduce effective runway
            affected_domains=[
                Domain.FINANCIAL, Domain.PEOPLE, Domain.OPERATIONS
            ],
            timeline_days=120,
        ),
        Variable(
            name="Lead engineer resigns",
            description="Engineering lead + 1 senior resign during uncertainty",
            probability=0.20,
            arrt_impact_pct=5.0,          # Roadmap slip causes some revenue impact
            runway_impact_months=1.0,
            affected_domains=[
                Domain.ENGINEERING, Domain.PRODUCT, Domain.REVENUE
            ],
            timeline_days=30,
        ),
    ]

    cascades = [
        CascadeEffect(
            trigger_domain=Domain.REVENUE,
            caused_domain=Domain.FINANCIAL,
            mechanism="ARR loss increases burn multiple; runway compresses",
            severity_multiplier=1.3,
        ),
        CascadeEffect(
            trigger_domain=Domain.FINANCIAL,
            caused_domain=Domain.PEOPLE,
            mechanism="Hiring freeze + uncertainty triggers attrition risk",
            severity_multiplier=1.2,
        ),
        CascadeEffect(
            trigger_domain=Domain.PEOPLE,
            caused_domain=Domain.PRODUCT,
            mechanism="Engineering attrition slips roadmap; customer value drops",
            severity_multiplier=1.15,
        ),
    ]

    hedges = [
        Hedge(
            action="Establish $750K revolving credit line",
            cost_usd=7_500,
            impact_description="Buys 4+ months if churn hits before fundraise closes",
            owner="CFO",
            deadline_days=45,
            reduces_probability=0.40,
        ),
        Hedge(
            action="12-month retention bonuses for 3 key engineers",
            cost_usd=90_000,
            impact_description="Locks critical talent through fundraise uncertainty",
            owner="CHRO",
            deadline_days=30,
            reduces_probability=0.60,
        ),
        Hedge(
            action="Diversify revenue: reduce top customer to <20% ARR in 2 quarters",
            cost_usd=0,
            impact_description="Structural risk reduction; takes 6+ months to achieve",
            owner="CRO",
            deadline_days=14,
            reduces_probability=0.30,
        ),
        Hedge(
            action="Accelerate fundraise: start parallel process, compress timeline",
            cost_usd=15_000,
            impact_description="Closes before scenarios compound; reduces bridge risk",
            owner="CEO",
            deadline_days=7,
            reduces_probability=0.35,
        ),
    ]

    return Scenario(
        name="Customer Churn + Fundraise Miss + Eng Attrition",
        variables=variables,
        cascades=cascades,
        hedges=hedges,
        current_arr_usd=2_000_000,
        current_runway_months=14,
        monthly_burn_usd=140_000,
    )


def interactive_mode() -> Scenario:
    """Simple CLI for building a custom scenario."""
    print("\n🔴 SCENARIO WAR ROOM — Custom Scenario Builder")
    print("=" * 50)
    print("Define up to 3 scenario variables.\n")

    name = input("Scenario name: ").strip() or "Custom Scenario"

    current_arr = int(input("Current ARR ($): ").strip() or "2000000")
    current_runway = int(input("Current runway (months): ").strip() or "14")
    monthly_burn = int(current_arr / current_runway) if current_runway > 0 else 140000

    variables = []
    for i in range(1, 4):
        print(f"\nVariable {i} (press Enter to skip):")
        var_name = input("  Name: ").strip()
        if not var_name:
            break

        desc = input("  Description: ").strip() or var_name
        prob = float(input("  Probability (0-100%): ").strip() or "20") / 100
        arr_impact = float(input("  ARR impact (%): ").strip() or "10")
        runway_impact = float(input("  Runway impact (months): ").strip() or "2")
        timeline = int(input("  Timeline (days): ").strip() or "90")

        variables.append(Variable(
            name=var_name,
            description=desc,
            probability=prob,
            arrt_impact_pct=arr_impact,
            runway_impact_months=runway_impact,
            affected_domains=[Domain.FINANCIAL, Domain.REVENUE],
            timeline_days=timeline,
        ))

    if not variables:
        print("No variables defined. Using sample scenario.")
        return build_sample_scenario()

    return Scenario(
        name=name,
        variables=variables,
        cascades=[],
        hedges=[],
        current_arr_usd=current_arr,
        current_runway_months=current_runway,
        monthly_burn_usd=monthly_burn,
    )


def main():
    print("\n🔴 SCENARIO WAR ROOM")
    print("Multi-variable cascade modeler for startup adversity planning\n")

    if "--interactive" in sys.argv or "-i" in sys.argv:
        scenario = interactive_mode()
    else:
        print("Running sample scenario: Customer Churn + Fundraise Miss + Eng Attrition")
        print("(Use --interactive or -i for custom scenario)\n")
        scenario = build_sample_scenario()

    print_report(scenario)

    if "--json" in sys.argv:
        results = {}
        for severity in Severity:
            impact = calculate_impact(scenario, severity)
            results[severity.value] = impact
        print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
