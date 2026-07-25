#!/usr/bin/env python3
"""RFP/RFI Response Analyzer - Score coverage, identify gaps, and recommend bid/no-bid.

Parses RFP/RFI requirements and scores coverage using Full/Partial/Planned/Gap
categories. Generates weighted coverage scores, gap analysis with mitigation
strategies, effort estimation, and bid/no-bid recommendations.

Usage:
    python rfp_response_analyzer.py rfp_data.json
    python rfp_response_analyzer.py rfp_data.json --format json
    python rfp_response_analyzer.py rfp_data.json --format text
"""

import argparse
import json
import sys
from typing import Any


# Coverage status to score mapping
COVERAGE_SCORES: dict[str, float] = {
    "full": 1.0,
    "partial": 0.5,
    "planned": 0.25,
    "gap": 0.0,
}

# Priority to weight mapping
PRIORITY_WEIGHTS: dict[str, float] = {
    "must-have": 3.0,
    "should-have": 2.0,
    "nice-to-have": 1.0,
}

# Bid thresholds
BID_THRESHOLD = 0.70
CONDITIONAL_THRESHOLD = 0.50
MAX_MUST_HAVE_GAPS_FOR_BID = 3


def safe_divide(numerator: float, denominator: float, default: float = 0.0) -> float:
    """Safely divide two numbers, returning default if denominator is zero."""
    if denominator == 0:
        return default
    return numerator / denominator


def load_rfp_data(filepath: str) -> dict[str, Any]:
    """Load and validate RFP data from a JSON file.

    Args:
        filepath: Path to the JSON file containing RFP data.

    Returns:
        Parsed RFP data dictionary.

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

    if "requirements" not in data:
        print("Error: JSON must contain a 'requirements' array.", file=sys.stderr)
        sys.exit(1)

    return data


def analyze_requirement(req: dict[str, Any]) -> dict[str, Any]:
    """Analyze a single requirement and compute its score.

    Args:
        req: Requirement dictionary with category, priority, coverage_status, etc.

    Returns:
        Enriched requirement with computed score and weight.
    """
    coverage_status = req.get("coverage_status", "gap").lower()
    priority = req.get("priority", "nice-to-have").lower()

    coverage_score = COVERAGE_SCORES.get(coverage_status, 0.0)
    weight = PRIORITY_WEIGHTS.get(priority, 1.0)
    weighted_score = coverage_score * weight
    max_weighted = weight

    effort_hours = req.get("effort_hours", 0)

    result = {
        "id": req.get("id", "unknown"),
        "requirement": req.get("requirement", "Unnamed requirement"),
        "category": req.get("category", "Uncategorized"),
        "priority": priority,
        "coverage_status": coverage_status,
        "coverage_score": coverage_score,
        "weight": weight,
        "weighted_score": weighted_score,
        "max_weighted": max_weighted,
        "effort_hours": effort_hours,
        "notes": req.get("notes", ""),
        "mitigation": req.get("mitigation", ""),
    }

    return result


def generate_gap_analysis(analyzed_reqs: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Generate gap analysis for requirements not fully covered.

    Args:
        analyzed_reqs: List of analyzed requirement dictionaries.

    Returns:
        List of gap entries with mitigation strategies.
    """
    gaps = []
    for req in analyzed_reqs:
        if req["coverage_status"] in ("gap", "partial", "planned"):
            severity = "critical" if req["priority"] == "must-have" else (
                "high" if req["priority"] == "should-have" else "low"
            )

            mitigation = req["mitigation"]
            if not mitigation:
                if req["coverage_status"] == "partial":
                    mitigation = "Enhance existing capability to achieve full coverage"
                elif req["coverage_status"] == "planned":
                    mitigation = "Communicate roadmap timeline and interim workaround"
                else:
                    mitigation = "Evaluate build vs. partner vs. no-bid for this requirement"

            gaps.append({
                "id": req["id"],
                "requirement": req["requirement"],
                "category": req["category"],
                "priority": req["priority"],
                "coverage_status": req["coverage_status"],
                "severity": severity,
                "effort_hours": req["effort_hours"],
                "mitigation": mitigation,
            })

    # Sort by severity: critical > high > low
    severity_order = {"critical": 0, "high": 1, "low": 2}
    gaps.sort(key=lambda g: severity_order.get(g["severity"], 3))

    return gaps


def compute_category_scores(analyzed_reqs: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    """Compute coverage scores grouped by requirement category.

    Args:
        analyzed_reqs: List of analyzed requirement dictionaries.

    Returns:
        Dictionary of category names to score summaries.
    """
    categories: dict[str, dict[str, float]] = {}

    for req in analyzed_reqs:
        cat = req["category"]
        if cat not in categories:
            categories[cat] = {
                "weighted_score": 0.0,
                "max_weighted": 0.0,
                "count": 0,
                "full_count": 0,
                "partial_count": 0,
                "planned_count": 0,
                "gap_count": 0,
                "effort_hours": 0,
            }

        categories[cat]["weighted_score"] += req["weighted_score"]
        categories[cat]["max_weighted"] += req["max_weighted"]
        categories[cat]["count"] += 1
        categories[cat]["effort_hours"] += req["effort_hours"]

        status_key = f"{req['coverage_status']}_count"
        if status_key in categories[cat]:
            categories[cat][status_key] += 1

    result = {}
    for cat, scores in categories.items():
        coverage_pct = safe_divide(scores["weighted_score"], scores["max_weighted"]) * 100
        result[cat] = {
            "coverage_percentage": round(coverage_pct, 1),
            "requirements_count": int(scores["count"]),
            "full": int(scores["full_count"]),
            "partial": int(scores["partial_count"]),
            "planned": int(scores["planned_count"]),
            "gap": int(scores["gap_count"]),
            "effort_hours": int(scores["effort_hours"]),
        }

    return result


def determine_bid_recommendation(
    overall_coverage: float,
    must_have_gaps: int,
    strategic_value: str,
) -> dict[str, Any]:
    """Determine bid/no-bid recommendation based on coverage and gaps.

    Args:
        overall_coverage: Overall weighted coverage percentage (0-100).
        must_have_gaps: Number of must-have requirements with gap status.
        strategic_value: Strategic value assessment (high, medium, low).

    Returns:
        Recommendation dictionary with decision and rationale.
    """
    coverage_ratio = overall_coverage / 100.0
    reasons = []

    # Primary decision logic
    if coverage_ratio >= BID_THRESHOLD and must_have_gaps <= MAX_MUST_HAVE_GAPS_FOR_BID:
        decision = "BID"
        reasons.append(f"Coverage score {overall_coverage:.1f}% exceeds {BID_THRESHOLD*100:.0f}% threshold")
        if must_have_gaps > 0:
            reasons.append(f"{must_have_gaps} must-have gap(s) within acceptable range (max {MAX_MUST_HAVE_GAPS_FOR_BID})")
    elif coverage_ratio >= CONDITIONAL_THRESHOLD or (
        must_have_gaps <= MAX_MUST_HAVE_GAPS_FOR_BID and coverage_ratio >= 0.4
    ):
        decision = "CONDITIONAL BID"
        reasons.append(f"Coverage score {overall_coverage:.1f}% in conditional range ({CONDITIONAL_THRESHOLD*100:.0f}%-{BID_THRESHOLD*100:.0f}%)")
        if must_have_gaps > 0:
            reasons.append(f"{must_have_gaps} must-have gap(s) require mitigation plan")
    else:
        decision = "NO-BID"
        if coverage_ratio < CONDITIONAL_THRESHOLD:
            reasons.append(f"Coverage score {overall_coverage:.1f}% below {CONDITIONAL_THRESHOLD*100:.0f}% minimum")
        if must_have_gaps > MAX_MUST_HAVE_GAPS_FOR_BID:
            reasons.append(f"{must_have_gaps} must-have gaps exceed maximum of {MAX_MUST_HAVE_GAPS_FOR_BID}")

    # Strategic value adjustment
    if strategic_value.lower() == "high" and decision == "CONDITIONAL BID":
        reasons.append("High strategic value supports pursuing despite coverage gaps")
    elif strategic_value.lower() == "low" and decision == "CONDITIONAL BID":
        decision = "NO-BID"
        reasons.append("Low strategic value does not justify investment for conditional coverage")

    confidence = "high" if coverage_ratio >= 0.80 else (
        "medium" if coverage_ratio >= 0.60 else "low"
    )

    return {
        "decision": decision,
        "confidence": confidence,
        "overall_coverage_percentage": round(overall_coverage, 1),
        "must_have_gaps": must_have_gaps,
        "strategic_value": strategic_value,
        "reasons": reasons,
    }


def generate_risk_assessment(
    analyzed_reqs: list[dict[str, Any]],
    gaps: list[dict[str, Any]],
) -> list[dict[str, str]]:
    """Generate risk assessment based on gaps and coverage patterns.

    Args:
        analyzed_reqs: List of analyzed requirement dictionaries.
        gaps: List of gap analysis entries.

    Returns:
        List of risk entries with impact and mitigation.
    """
    risks = []

    critical_gaps = [g for g in gaps if g["severity"] == "critical"]
    if critical_gaps:
        risks.append({
            "risk": "Critical requirement gaps",
            "impact": "high",
            "description": f"{len(critical_gaps)} must-have requirements not fully met",
            "mitigation": "Prioritize engineering effort or partner integration for gap closure",
        })

    total_effort = sum(r["effort_hours"] for r in analyzed_reqs if r["coverage_status"] != "full")
    if total_effort > 200:
        risks.append({
            "risk": "High customization effort",
            "impact": "high",
            "description": f"{total_effort} hours estimated for non-full requirements",
            "mitigation": "Evaluate resource availability and timeline feasibility before committing",
        })
    elif total_effort > 80:
        risks.append({
            "risk": "Moderate customization effort",
            "impact": "medium",
            "description": f"{total_effort} hours estimated for non-full requirements",
            "mitigation": "Phase implementation and set clear expectations on delivery timeline",
        })

    planned_count = sum(1 for r in analyzed_reqs if r["coverage_status"] == "planned")
    if planned_count > 3:
        risks.append({
            "risk": "Roadmap dependency",
            "impact": "medium",
            "description": f"{planned_count} requirements depend on planned product features",
            "mitigation": "Confirm roadmap timelines with product team; include contractual commitments if needed",
        })

    partial_count = sum(1 for r in analyzed_reqs if r["coverage_status"] == "partial")
    if partial_count > 5:
        risks.append({
            "risk": "Workaround complexity",
            "impact": "medium",
            "description": f"{partial_count} requirements need workarounds or configuration",
            "mitigation": "Document workarounds clearly; plan for native support in future releases",
        })

    if not risks:
        risks.append({
            "risk": "No significant risks identified",
            "impact": "low",
            "description": "Strong coverage across all requirement categories",
            "mitigation": "Maintain standard engagement process",
        })

    return risks


def analyze_rfp(data: dict[str, Any]) -> dict[str, Any]:
    """Run the complete RFP analysis pipeline.

    Args:
        data: Parsed RFP data with requirements array.

    Returns:
        Complete analysis results dictionary.
    """
    rfp_info = {
        "rfp_name": data.get("rfp_name", "Unnamed RFP"),
        "customer": data.get("customer", "Unknown Customer"),
        "due_date": data.get("due_date", "Not specified"),
        "strategic_value": data.get("strategic_value", "medium"),
        "deal_value": data.get("deal_value", "Not specified"),
    }

    # Analyze each requirement
    analyzed_reqs = [analyze_requirement(req) for req in data["requirements"]]

    # Compute overall scores
    total_weighted = sum(r["weighted_score"] for r in analyzed_reqs)
    total_max = sum(r["max_weighted"] for r in analyzed_reqs)
    overall_coverage = safe_divide(total_weighted, total_max) * 100

    # Coverage summary
    total_count = len(analyzed_reqs)
    full_count = sum(1 for r in analyzed_reqs if r["coverage_status"] == "full")
    partial_count = sum(1 for r in analyzed_reqs if r["coverage_status"] == "partial")
    planned_count = sum(1 for r in analyzed_reqs if r["coverage_status"] == "planned")
    gap_count = sum(1 for r in analyzed_reqs if r["coverage_status"] == "gap")

    # Must-have gap count
    must_have_gaps = sum(
        1 for r in analyzed_reqs
        if r["priority"] == "must-have" and r["coverage_status"] == "gap"
    )

    # Category breakdown
    category_scores = compute_category_scores(analyzed_reqs)

    # Gap analysis
    gaps = generate_gap_analysis(analyzed_reqs)

    # Bid recommendation
    bid_recommendation = determine_bid_recommendation(
        overall_coverage,
        must_have_gaps,
        rfp_info["strategic_value"],
    )

    # Risk assessment
    risks = generate_risk_assessment(analyzed_reqs, gaps)

    # Effort summary
    total_effort = sum(r["effort_hours"] for r in analyzed_reqs)
    gap_effort = sum(r["effort_hours"] for r in analyzed_reqs if r["coverage_status"] != "full")

    return {
        "rfp_info": rfp_info,
        "coverage_summary": {
            "overall_coverage_percentage": round(overall_coverage, 1),
            "total_requirements": total_count,
            "full": full_count,
            "partial": partial_count,
            "planned": planned_count,
            "gap": gap_count,
            "must_have_gaps": must_have_gaps,
        },
        "category_scores": category_scores,
        "bid_recommendation": bid_recommendation,
        "gap_analysis": gaps,
        "risk_assessment": risks,
        "effort_estimate": {
            "total_hours": total_effort,
            "gap_closure_hours": gap_effort,
            "full_coverage_hours": total_effort - gap_effort,
        },
        "requirements_detail": analyzed_reqs,
    }


def format_text(result: dict[str, Any]) -> str:
    """Format analysis results as human-readable text.

    Args:
        result: Complete analysis results dictionary.

    Returns:
        Formatted text string.
    """
    lines = []
    info = result["rfp_info"]
    lines.append("=" * 70)
    lines.append("RFP RESPONSE ANALYSIS")
    lines.append("=" * 70)
    lines.append(f"RFP:            {info['rfp_name']}")
    lines.append(f"Customer:       {info['customer']}")
    lines.append(f"Due Date:       {info['due_date']}")
    lines.append(f"Deal Value:     {info['deal_value']}")
    lines.append(f"Strategic Value: {info['strategic_value'].upper()}")
    lines.append("")

    # Coverage summary
    cs = result["coverage_summary"]
    lines.append("-" * 70)
    lines.append("COVERAGE SUMMARY")
    lines.append("-" * 70)
    lines.append(f"Overall Coverage:  {cs['overall_coverage_percentage']}%")
    lines.append(f"Total Requirements: {cs['total_requirements']}")
    lines.append(f"  Full:    {cs['full']}  |  Partial: {cs['partial']}  |  Planned: {cs['planned']}  |  Gap: {cs['gap']}")
    lines.append(f"Must-Have Gaps:    {cs['must_have_gaps']}")
    lines.append("")

    # Bid recommendation
    bid = result["bid_recommendation"]
    lines.append("-" * 70)
    lines.append(f"BID RECOMMENDATION: {bid['decision']}")
    lines.append(f"Confidence: {bid['confidence'].upper()}")
    lines.append("-" * 70)
    for reason in bid["reasons"]:
        lines.append(f"  - {reason}")
    lines.append("")

    # Category scores
    lines.append("-" * 70)
    lines.append("CATEGORY BREAKDOWN")
    lines.append("-" * 70)
    lines.append(f"{'Category':<25} {'Coverage':>8} {'Full':>5} {'Part':>5} {'Plan':>5} {'Gap':>5} {'Effort':>7}")
    lines.append("-" * 70)
    for cat, scores in result["category_scores"].items():
        lines.append(
            f"{cat:<25} {scores['coverage_percentage']:>7.1f}% "
            f"{scores['full']:>5} {scores['partial']:>5} "
            f"{scores['planned']:>5} {scores['gap']:>5} "
            f"{scores['effort_hours']:>6}h"
        )
    lines.append("")

    # Gap analysis
    gaps = result["gap_analysis"]
    if gaps:
        lines.append("-" * 70)
        lines.append("GAP ANALYSIS")
        lines.append("-" * 70)
        for gap in gaps:
            severity_marker = "!!!" if gap["severity"] == "critical" else (
                "!!" if gap["severity"] == "high" else "!"
            )
            lines.append(f"  [{severity_marker}] {gap['id']}: {gap['requirement']}")
            lines.append(f"       Category: {gap['category']} | Priority: {gap['priority']} | Status: {gap['coverage_status']}")
            lines.append(f"       Effort: {gap['effort_hours']}h | Mitigation: {gap['mitigation']}")
            lines.append("")

    # Risk assessment
    risks = result["risk_assessment"]
    lines.append("-" * 70)
    lines.append("RISK ASSESSMENT")
    lines.append("-" * 70)
    for risk in risks:
        lines.append(f"  [{risk['impact'].upper()}] {risk['risk']}")
        lines.append(f"       {risk['description']}")
        lines.append(f"       Mitigation: {risk['mitigation']}")
        lines.append("")

    # Effort estimate
    effort = result["effort_estimate"]
    lines.append("-" * 70)
    lines.append("EFFORT ESTIMATE")
    lines.append("-" * 70)
    lines.append(f"  Total Effort:         {effort['total_hours']} hours")
    lines.append(f"  Gap Closure Effort:   {effort['gap_closure_hours']} hours")
    lines.append(f"  Supported Effort:     {effort['full_coverage_hours']} hours")
    lines.append("")
    lines.append("=" * 70)

    return "\n".join(lines)


def main() -> None:
    """Main entry point for the RFP Response Analyzer."""
    parser = argparse.ArgumentParser(
        description="Analyze RFP/RFI requirements for coverage, gaps, and bid recommendation.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "Coverage Categories:\n"
            "  Full (100%)    - Requirement fully met\n"
            "  Partial (50%)  - Partially met, workaround needed\n"
            "  Planned (25%)  - On roadmap, not yet available\n"
            "  Gap (0%)       - Not supported\n"
            "\n"
            "Priority Weights:\n"
            "  Must-Have (3x) | Should-Have (2x) | Nice-to-Have (1x)\n"
            "\n"
            "Example:\n"
            "  python rfp_response_analyzer.py rfp_data.json --format json\n"
        ),
    )
    parser.add_argument(
        "input_file",
        help="Path to JSON file containing RFP requirements data",
    )
    parser.add_argument(
        "--format",
        choices=["json", "text"],
        default="text",
        dest="output_format",
        help="Output format: json or text (default: text)",
    )

    args = parser.parse_args()

    data = load_rfp_data(args.input_file)
    result = analyze_rfp(data)

    if args.output_format == "json":
        print(json.dumps(result, indent=2))
    else:
        print(format_text(result))


if __name__ == "__main__":
    main()
