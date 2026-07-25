#!/usr/bin/env python3
"""POC Planner - Plan proof-of-concept engagements with timeline, resources, and scorecards.

Generates structured POC plans including phased timelines, resource allocation,
success criteria with measurable metrics, evaluation scorecards, risk identification,
and go/no-go recommendation frameworks.

Usage:
    python poc_planner.py poc_data.json
    python poc_planner.py poc_data.json --format json
    python poc_planner.py poc_data.json --format text
"""

import argparse
import json
import sys
from typing import Any


# Default phase definitions
DEFAULT_PHASES = [
    {
        "name": "Setup",
        "duration_weeks": 1,
        "description": "Environment provisioning, data migration, initial configuration",
        "activities": [
            "Provision POC environment",
            "Configure authentication and access",
            "Migrate sample data sets",
            "Set up monitoring and logging",
            "Conduct kickoff meeting with stakeholders",
        ],
    },
    {
        "name": "Core Testing",
        "duration_weeks": 2,
        "description": "Primary use case validation and integration testing",
        "activities": [
            "Execute primary use case scenarios",
            "Test core integrations",
            "Validate data flow and transformations",
            "Conduct mid-point review with stakeholders",
            "Document findings and adjust test plan",
        ],
    },
    {
        "name": "Advanced Testing",
        "duration_weeks": 1,
        "description": "Edge cases, performance testing, and security validation",
        "activities": [
            "Execute edge case scenarios",
            "Run performance and load tests",
            "Validate security controls and compliance",
            "Test disaster recovery and failover",
            "Test administrative workflows",
        ],
    },
    {
        "name": "Evaluation",
        "duration_weeks": 1,
        "description": "Scorecard completion, stakeholder review, and go/no-go decision",
        "activities": [
            "Complete evaluation scorecard",
            "Compile POC results documentation",
            "Conduct final stakeholder review",
            "Present go/no-go recommendation",
            "Gather lessons learned",
        ],
    },
]

# Evaluation categories with default weights
DEFAULT_EVAL_CATEGORIES = {
    "Functionality": {
        "weight": 0.30,
        "criteria": [
            "Core feature completeness",
            "Use case coverage",
            "Customization flexibility",
            "Workflow automation",
        ],
    },
    "Performance": {
        "weight": 0.20,
        "criteria": [
            "Response time under load",
            "Throughput capacity",
            "Scalability characteristics",
            "Resource utilization",
        ],
    },
    "Integration": {
        "weight": 0.20,
        "criteria": [
            "API completeness and documentation",
            "Data migration ease",
            "Third-party connector availability",
            "Authentication/SSO integration",
        ],
    },
    "Usability": {
        "weight": 0.15,
        "criteria": [
            "User interface intuitiveness",
            "Learning curve assessment",
            "Documentation quality",
            "Admin console functionality",
        ],
    },
    "Support": {
        "weight": 0.15,
        "criteria": [
            "Technical support responsiveness",
            "Knowledge base quality",
            "Training resources availability",
            "Community and ecosystem",
        ],
    },
}


def safe_divide(numerator: float, denominator: float, default: float = 0.0) -> float:
    """Safely divide two numbers, returning default if denominator is zero."""
    if denominator == 0:
        return default
    return numerator / denominator


def load_poc_data(filepath: str) -> dict[str, Any]:
    """Load and validate POC data from a JSON file.

    Args:
        filepath: Path to the JSON file containing POC data.

    Returns:
        Parsed POC data dictionary.

    Raises:
        SystemExit: If the file cannot be read or parsed.
    """
    try:
        with open(filepath, "r", encoding="utf-8") as f:
            data = json.load(f)
    except FileNotFoundError:
        print(f"Error: File not found: {filepath}", file=sys.stderr)
        sys.exit(1)
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON in {filepath}: {e}", file=sys.stderr)
        sys.exit(1)

    if "poc_name" not in data:
        print("Error: JSON must contain 'poc_name' field.", file=sys.stderr)
        sys.exit(1)

    return data


def estimate_resources(data: dict[str, Any], phases: list[dict[str, Any]]) -> dict[str, Any]:
    """Estimate resource requirements for the POC.

    Args:
        data: POC data with scope and requirements.
        phases: List of phase definitions.

    Returns:
        Resource allocation dictionary.
    """
    total_weeks = sum(p["duration_weeks"] for p in phases)
    complexity = data.get("complexity", "medium").lower()
    scope_items = data.get("scope_items", [])
    num_integrations = data.get("num_integrations", 0)

    # Base SE hours per week by complexity
    se_hours_per_week = {"low": 15, "medium": 25, "high": 35}.get(complexity, 25)

    # Engineering support hours
    eng_base = {"low": 5, "medium": 10, "high": 20}.get(complexity, 10)
    eng_integration_hours = num_integrations * 8

    # Customer resource hours
    customer_hours_per_week = {"low": 5, "medium": 8, "high": 12}.get(complexity, 8)

    se_total = se_hours_per_week * total_weeks
    eng_total = (eng_base * total_weeks) + eng_integration_hours
    customer_total = customer_hours_per_week * total_weeks

    # Phase-level breakdown
    phase_resources = []
    for phase in phases:
        weeks = phase["duration_weeks"]
        # Setup phase has higher SE and eng effort
        se_multiplier = 1.3 if phase["name"] == "Setup" else (
            1.0 if phase["name"] in ("Core Testing", "Advanced Testing") else 0.7
        )
        eng_multiplier = 1.5 if phase["name"] == "Setup" else (
            1.0 if phase["name"] == "Core Testing" else (
                1.2 if phase["name"] == "Advanced Testing" else 0.5
            )
        )

        phase_resources.append({
            "phase": phase["name"],
            "duration_weeks": weeks,
            "se_hours": round(se_hours_per_week * weeks * se_multiplier),
            "engineering_hours": round(eng_base * weeks * eng_multiplier),
            "customer_hours": round(customer_hours_per_week * weeks),
        })

    return {
        "total_duration_weeks": total_weeks,
        "complexity": complexity,
        "totals": {
            "se_hours": se_total,
            "engineering_hours": eng_total,
            "customer_hours": customer_total,
            "total_hours": se_total + eng_total + customer_total,
        },
        "phase_breakdown": phase_resources,
        "additional_resources": {
            "integration_hours": eng_integration_hours,
            "num_integrations": num_integrations,
        },
    }


def generate_success_criteria(data: dict[str, Any]) -> list[dict[str, Any]]:
    """Generate success criteria based on POC scope and requirements.

    Args:
        data: POC data with scope and requirements.

    Returns:
        List of success criteria with metrics.
    """
    criteria = []

    # Custom criteria from input
    custom_criteria = data.get("success_criteria", [])
    for cc in custom_criteria:
        criteria.append({
            "criterion": cc.get("criterion", "Unnamed criterion"),
            "metric": cc.get("metric", "Pass/Fail"),
            "target": cc.get("target", "Met"),
            "category": cc.get("category", "Functionality"),
            "priority": cc.get("priority", "must-have"),
        })

    # Auto-generated criteria based on scope
    scope_items = data.get("scope_items", [])
    for item in scope_items:
        if isinstance(item, str):
            criteria.append({
                "criterion": f"Validate: {item}",
                "metric": "Pass/Fail",
                "target": "Pass",
                "category": "Functionality",
                "priority": "must-have",
            })
        elif isinstance(item, dict):
            criteria.append({
                "criterion": item.get("name", "Unnamed scope item"),
                "metric": item.get("metric", "Pass/Fail"),
                "target": item.get("target", "Pass"),
                "category": item.get("category", "Functionality"),
                "priority": item.get("priority", "must-have"),
            })

    # Default criteria if none provided
    if not criteria:
        criteria = [
            {
                "criterion": "Core use case validation",
                "metric": "Percentage of use cases successfully demonstrated",
                "target": ">90%",
                "category": "Functionality",
                "priority": "must-have",
            },
            {
                "criterion": "Performance under expected load",
                "metric": "Response time at target concurrency",
                "target": "<2 seconds p95",
                "category": "Performance",
                "priority": "must-have",
            },
            {
                "criterion": "Integration with existing systems",
                "metric": "Number of integrations successfully tested",
                "target": "All planned integrations",
                "category": "Integration",
                "priority": "must-have",
            },
            {
                "criterion": "User acceptance",
                "metric": "Stakeholder satisfaction score",
                "target": ">4.0/5.0",
                "category": "Usability",
                "priority": "should-have",
            },
        ]

    return criteria


def generate_evaluation_scorecard(data: dict[str, Any]) -> dict[str, Any]:
    """Generate the POC evaluation scorecard template.

    Args:
        data: POC data.

    Returns:
        Evaluation scorecard structure.
    """
    custom_categories = data.get("evaluation_categories", {})

    # Merge custom categories with defaults
    categories = {}
    for cat_name, cat_data in DEFAULT_EVAL_CATEGORIES.items():
        if cat_name in custom_categories:
            custom = custom_categories[cat_name]
            categories[cat_name] = {
                "weight": custom.get("weight", cat_data["weight"]),
                "criteria": custom.get("criteria", cat_data["criteria"]),
                "score": None,
                "notes": "",
            }
        else:
            categories[cat_name] = {
                "weight": cat_data["weight"],
                "criteria": cat_data["criteria"],
                "score": None,
                "notes": "",
            }

    # Normalize weights to sum to 1.0
    total_weight = sum(c["weight"] for c in categories.values())
    if total_weight > 0 and abs(total_weight - 1.0) > 0.01:
        for cat in categories.values():
            cat["weight"] = round(safe_divide(cat["weight"], total_weight), 2)

    return {
        "scoring_scale": {
            "5": "Exceeds requirements - superior capability",
            "4": "Meets requirements - full capability",
            "3": "Partially meets - acceptable with minor gaps",
            "2": "Below expectations - significant gaps",
            "1": "Does not meet - critical gaps",
        },
        "categories": categories,
        "pass_threshold": 3.5,
        "strong_pass_threshold": 4.0,
    }


def identify_risks(data: dict[str, Any], resources: dict[str, Any]) -> list[dict[str, Any]]:
    """Identify POC risks and generate mitigation strategies.

    Args:
        data: POC data.
        resources: Resource allocation data.

    Returns:
        List of risk entries with probability, impact, and mitigation.
    """
    risks = []
    complexity = data.get("complexity", "medium").lower()
    num_integrations = data.get("num_integrations", 0)
    total_weeks = resources["total_duration_weeks"]
    stakeholders = data.get("stakeholders", [])

    # Timeline risk
    if total_weeks > 6:
        risks.append({
            "risk": "Extended timeline may lose stakeholder attention",
            "probability": "high",
            "impact": "high",
            "mitigation": "Schedule weekly progress checkpoints; deliver early wins in week 2",
            "category": "Timeline",
        })
    elif total_weeks >= 4:
        risks.append({
            "risk": "Timeline may slip due to unforeseen technical issues",
            "probability": "medium",
            "impact": "medium",
            "mitigation": "Build 20% buffer into each phase; identify critical path early",
            "category": "Timeline",
        })

    # Integration risks
    if num_integrations > 3:
        risks.append({
            "risk": "Multiple integrations increase complexity and failure points",
            "probability": "high",
            "impact": "high",
            "mitigation": "Prioritize integrations by business value; test incrementally; have fallback demo data",
            "category": "Technical",
        })
    elif num_integrations > 0:
        risks.append({
            "risk": "Integration dependencies may cause delays",
            "probability": "medium",
            "impact": "medium",
            "mitigation": "Engage customer IT early; confirm API access and credentials in setup phase",
            "category": "Technical",
        })

    # Data risks
    risks.append({
        "risk": "Customer data quality or availability issues",
        "probability": "medium",
        "impact": "high",
        "mitigation": "Request sample data early; prepare synthetic data as fallback; validate data format in setup",
        "category": "Data",
    })

    # Stakeholder risks
    if len(stakeholders) > 5:
        risks.append({
            "risk": "Too many stakeholders may slow decision-making",
            "probability": "medium",
            "impact": "medium",
            "mitigation": "Identify decision-maker and champion; schedule focused reviews per stakeholder group",
            "category": "Stakeholder",
        })

    if not stakeholders:
        risks.append({
            "risk": "Undefined stakeholder map may lead to misaligned evaluation",
            "probability": "high",
            "impact": "high",
            "mitigation": "Confirm stakeholder list, roles, and evaluation criteria before setup phase",
            "category": "Stakeholder",
        })

    # Resource risks
    if complexity == "high":
        risks.append({
            "risk": "High complexity may require additional engineering resources",
            "probability": "medium",
            "impact": "high",
            "mitigation": "Secure engineering commitment upfront; identify escalation path for blockers",
            "category": "Resource",
        })

    # Competitive risk
    risks.append({
        "risk": "Competitor POC running in parallel may shift evaluation criteria",
        "probability": "medium",
        "impact": "medium",
        "mitigation": "Stay close to champion; align success criteria early; differentiate on unique strengths",
        "category": "Competitive",
    })

    return risks


def generate_go_no_go_framework(data: dict[str, Any]) -> dict[str, Any]:
    """Generate the go/no-go decision framework.

    Args:
        data: POC data.

    Returns:
        Go/no-go framework with criteria and thresholds.
    """
    return {
        "decision_criteria": [
            {
                "criterion": "Overall scorecard score",
                "go_threshold": ">=3.5 weighted average",
                "no_go_threshold": "<3.0 weighted average",
                "conditional_range": "3.0 - 3.5",
            },
            {
                "criterion": "Must-have success criteria met",
                "go_threshold": "100% of must-have criteria pass",
                "no_go_threshold": "<80% of must-have criteria pass",
                "conditional_range": "80-99% with mitigation plan",
            },
            {
                "criterion": "Stakeholder satisfaction",
                "go_threshold": "Champion and decision-maker both positive",
                "no_go_threshold": "Decision-maker negative",
                "conditional_range": "Mixed signals - needs follow-up",
            },
            {
                "criterion": "Technical blockers",
                "go_threshold": "No unresolved critical blockers",
                "no_go_threshold": ">2 unresolved critical blockers",
                "conditional_range": "1-2 blockers with clear resolution path",
            },
        ],
        "recommendation_logic": {
            "GO": "All criteria meet go thresholds, or majority go with no no-go triggers",
            "CONDITIONAL_GO": "Some criteria in conditional range, but no no-go triggers and clear resolution plan",
            "NO_GO": "Any criterion triggers no-go threshold without clear mitigation",
        },
    }


def plan_poc(data: dict[str, Any]) -> dict[str, Any]:
    """Run the complete POC planning pipeline.

    Args:
        data: Parsed POC data dictionary.

    Returns:
        Complete POC plan dictionary.
    """
    poc_info = {
        "poc_name": data.get("poc_name", "Unnamed POC"),
        "customer": data.get("customer", "Unknown Customer"),
        "opportunity_value": data.get("opportunity_value", "Not specified"),
        "complexity": data.get("complexity", "medium"),
        "start_date": data.get("start_date", "TBD"),
        "champion": data.get("champion", "Not identified"),
        "decision_maker": data.get("decision_maker", "Not identified"),
    }

    # Use custom phases if provided, otherwise defaults
    phases = data.get("phases", DEFAULT_PHASES)

    # Resource estimation
    resources = estimate_resources(data, phases)

    # Success criteria
    success_criteria = generate_success_criteria(data)

    # Evaluation scorecard
    scorecard = generate_evaluation_scorecard(data)

    # Risk identification
    risks = identify_risks(data, resources)

    # Go/No-Go framework
    go_no_go = generate_go_no_go_framework(data)

    # Timeline with phase details
    timeline = []
    current_week = 1
    for phase in phases:
        end_week = current_week + phase["duration_weeks"] - 1
        timeline.append({
            "phase": phase["name"],
            "start_week": current_week,
            "end_week": end_week,
            "duration_weeks": phase["duration_weeks"],
            "description": phase["description"],
            "activities": phase["activities"],
        })
        current_week = end_week + 1

    # Stakeholder plan
    stakeholders = data.get("stakeholders", [])
    stakeholder_plan = []
    for s in stakeholders:
        if isinstance(s, str):
            stakeholder_plan.append({
                "name": s,
                "role": "Evaluator",
                "engagement": "Weekly updates, phase reviews",
            })
        elif isinstance(s, dict):
            stakeholder_plan.append({
                "name": s.get("name", "Unknown"),
                "role": s.get("role", "Evaluator"),
                "engagement": s.get("engagement", "Weekly updates, phase reviews"),
            })

    return {
        "poc_info": poc_info,
        "timeline": timeline,
        "resource_allocation": resources,
        "success_criteria": success_criteria,
        "evaluation_scorecard": scorecard,
        "risk_register": risks,
        "go_no_go_framework": go_no_go,
        "stakeholder_plan": stakeholder_plan,
    }


def format_text(result: dict[str, Any]) -> str:
    """Format POC plan as human-readable text.

    Args:
        result: Complete POC plan dictionary.

    Returns:
        Formatted text string.
    """
    lines = []
    info = result["poc_info"]

    lines.append("=" * 70)
    lines.append("PROOF OF CONCEPT PLAN")
    lines.append("=" * 70)
    lines.append(f"POC Name:          {info['poc_name']}")
    lines.append(f"Customer:          {info['customer']}")
    lines.append(f"Opportunity Value: {info['opportunity_value']}")
    lines.append(f"Complexity:        {info['complexity'].upper()}")
    lines.append(f"Start Date:        {info['start_date']}")
    lines.append(f"Champion:          {info['champion']}")
    lines.append(f"Decision Maker:    {info['decision_maker']}")
    lines.append("")

    # Timeline
    lines.append("-" * 70)
    lines.append("TIMELINE")
    lines.append("-" * 70)
    for phase in result["timeline"]:
        week_range = (
            f"Week {phase['start_week']}"
            if phase["start_week"] == phase["end_week"]
            else f"Weeks {phase['start_week']}-{phase['end_week']}"
        )
        lines.append(f"\n  Phase: {phase['phase']} ({week_range})")
        lines.append(f"  {phase['description']}")
        lines.append("  Activities:")
        for activity in phase["activities"]:
            lines.append(f"    - {activity}")
    lines.append("")

    # Resource allocation
    res = result["resource_allocation"]
    lines.append("-" * 70)
    lines.append("RESOURCE ALLOCATION")
    lines.append("-" * 70)
    lines.append(f"Total Duration:    {res['total_duration_weeks']} weeks")
    lines.append(f"Complexity:        {res['complexity'].upper()}")
    lines.append("")
    lines.append("  Totals:")
    lines.append(f"    SE Hours:           {res['totals']['se_hours']}")
    lines.append(f"    Engineering Hours:  {res['totals']['engineering_hours']}")
    lines.append(f"    Customer Hours:     {res['totals']['customer_hours']}")
    lines.append(f"    Total Hours:        {res['totals']['total_hours']}")
    lines.append("")
    lines.append("  Phase Breakdown:")
    lines.append(f"    {'Phase':<20} {'Weeks':>5} {'SE':>6} {'Eng':>6} {'Cust':>6}")
    lines.append("    " + "-" * 45)
    for pr in res["phase_breakdown"]:
        lines.append(
            f"    {pr['phase']:<20} {pr['duration_weeks']:>5} "
            f"{pr['se_hours']:>5}h {pr['engineering_hours']:>5}h {pr['customer_hours']:>5}h"
        )
    lines.append("")

    # Success criteria
    criteria = result["success_criteria"]
    lines.append("-" * 70)
    lines.append("SUCCESS CRITERIA")
    lines.append("-" * 70)
    for i, sc in enumerate(criteria, 1):
        priority_marker = "[MUST]" if sc["priority"] == "must-have" else (
            "[SHOULD]" if sc["priority"] == "should-have" else "[NICE]"
        )
        lines.append(f"  {i}. {priority_marker} {sc['criterion']}")
        lines.append(f"     Metric: {sc['metric']}")
        lines.append(f"     Target: {sc['target']}")
        lines.append(f"     Category: {sc['category']}")
        lines.append("")

    # Evaluation scorecard
    scorecard = result["evaluation_scorecard"]
    lines.append("-" * 70)
    lines.append("EVALUATION SCORECARD")
    lines.append("-" * 70)
    lines.append(f"  Pass Threshold:        {scorecard['pass_threshold']}/5.0")
    lines.append(f"  Strong Pass Threshold: {scorecard['strong_pass_threshold']}/5.0")
    lines.append("")
    lines.append("  Scoring Scale:")
    for score, desc in scorecard["scoring_scale"].items():
        lines.append(f"    {score} = {desc}")
    lines.append("")
    lines.append("  Categories:")
    for cat_name, cat_data in scorecard["categories"].items():
        lines.append(f"\n    {cat_name} (weight: {cat_data['weight']:.0%})")
        for criterion in cat_data["criteria"]:
            lines.append(f"      [ ] {criterion}")
    lines.append("")

    # Risk register
    risks = result["risk_register"]
    lines.append("-" * 70)
    lines.append("RISK REGISTER")
    lines.append("-" * 70)
    for risk in risks:
        lines.append(f"  [{risk['impact'].upper()}] {risk['risk']}")
        lines.append(f"       Probability: {risk['probability']} | Impact: {risk['impact']}")
        lines.append(f"       Category: {risk['category']}")
        lines.append(f"       Mitigation: {risk['mitigation']}")
        lines.append("")

    # Go/No-Go framework
    framework = result["go_no_go_framework"]
    lines.append("-" * 70)
    lines.append("GO / NO-GO DECISION FRAMEWORK")
    lines.append("-" * 70)
    for dc in framework["decision_criteria"]:
        lines.append(f"  {dc['criterion']}:")
        lines.append(f"    GO:          {dc['go_threshold']}")
        lines.append(f"    CONDITIONAL: {dc['conditional_range']}")
        lines.append(f"    NO-GO:       {dc['no_go_threshold']}")
        lines.append("")

    lines.append("  Recommendation Logic:")
    for decision, logic in framework["recommendation_logic"].items():
        lines.append(f"    {decision}: {logic}")
    lines.append("")

    # Stakeholder plan
    stakeholders = result["stakeholder_plan"]
    if stakeholders:
        lines.append("-" * 70)
        lines.append("STAKEHOLDER PLAN")
        lines.append("-" * 70)
        for s in stakeholders:
            lines.append(f"  {s['name']} ({s['role']})")
            lines.append(f"    Engagement: {s['engagement']}")
            lines.append("")

    lines.append("=" * 70)

    return "\n".join(lines)


def main() -> None:
    """Main entry point for the POC Planner."""
    parser = argparse.ArgumentParser(
        description="Plan proof-of-concept engagements with timeline, resources, and evaluation scorecards.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "Default Phases:\n"
            "  Week 1:   Setup - Environment provisioning, configuration\n"
            "  Weeks 2-3: Core Testing - Primary use cases, integrations\n"
            "  Week 4:   Advanced Testing - Edge cases, performance, security\n"
            "  Week 5:   Evaluation - Scorecard, stakeholder review, go/no-go\n"
            "\n"
            "Example:\n"
            "  python poc_planner.py poc_data.json --format json\n"
        ),
    )
    parser.add_argument(
        "input_file",
        help="Path to JSON file containing POC scope and requirements",
    )
    parser.add_argument(
        "--format",
        choices=["json", "text"],
        default="text",
        dest="output_format",
        help="Output format: json or text (default: text)",
    )

    args = parser.parse_args()

    data = load_poc_data(args.input_file)
    result = plan_poc(data)

    if args.output_format == "json":
        print(json.dumps(result, indent=2))
    else:
        print(format_text(result))


if __name__ == "__main__":
    main()
