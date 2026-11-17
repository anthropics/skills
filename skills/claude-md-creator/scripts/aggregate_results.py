#!/usr/bin/env python3
"""
Phase 5: Aggregate coherence and blind test results into a final evaluation summary.

Combines Phase 2 (coherence_report.json) and Phase 4 (blind_results.json)
into a single evaluation_summary.json with overall score, grade, top issues,
and actionable recommendations.

Usage:
    python -m scripts.aggregate_results <coherence.json> [--blind <blind_results.json>] [--output <path>]
"""

import argparse
import json
from pathlib import Path


# ---------------------------------------------------------------------------
# Grading
# ---------------------------------------------------------------------------

GRADE_THRESHOLDS = [
    (90, "A"),
    (80, "B"),
    (70, "C"),
    (60, "D"),
    (0, "F"),
]


def score_to_grade(score: float) -> str:
    for threshold, grade in GRADE_THRESHOLDS:
        if score >= threshold:
            return grade
    return "F"


# ---------------------------------------------------------------------------
# Issue extraction
# ---------------------------------------------------------------------------

SEVERITY_MAP = {
    "stale": "high",
    "partial": "medium",
}


def extract_issues(coherence_data: dict, claims_lookup: dict | None = None) -> list[dict]:
    """Extract top issues from coherence report."""
    issues = []

    for result in coherence_data.get("results", []):
        status = result.get("status")
        if status not in ("stale", "partial"):
            continue

        severity = SEVERITY_MAP.get(status, "low")
        issue = {
            "severity": severity,
            "claim_id": result["claim_id"],
            "type": result.get("type", "unknown"),
            "issue": result.get("evidence", "Unknown issue"),
        }
        if result.get("suggestion"):
            issue["suggestion"] = result["suggestion"]

        issues.append(issue)

    # Add vague/generic claims as low-severity issues
    if claims_lookup:
        for claim_id, claim in claims_lookup.items():
            if claim["type"] in ("vague", "generic"):
                issues.append({
                    "severity": "low",
                    "claim_id": claim_id,
                    "type": claim["type"],
                    "issue": claim["extracted"].get("issue", f"{claim['type']} instruction"),
                    "suggestion": claim["extracted"].get("suggestion", "Replace with specific instruction"),
                })

    # Sort by severity (high > medium > low)
    severity_order = {"high": 0, "medium": 1, "low": 2}
    issues.sort(key=lambda x: severity_order.get(x["severity"], 3))

    return issues


# ---------------------------------------------------------------------------
# Recommendation generation
# ---------------------------------------------------------------------------


def generate_recommendations(
    coherence_data: dict,
    blind_data: dict | None,
    issues: list[dict],
) -> dict:
    """Generate actionable recommendations."""
    recommendations: dict[str, list] = {
        "remove": [],
        "fix": [],
        "add": [],
        "strengthen": [],
    }

    for result in coherence_data.get("results", []):
        claim_id = result["claim_id"]
        status = result.get("status")
        claim_type = result.get("type", "")

        # Remove: vague/generic claims
        if status == "not_applicable" and claim_type in ("vague", "generic"):
            recommendations["remove"].append(claim_id)

        # Fix: stale claims with suggestions
        elif status == "stale" and result.get("suggestion"):
            recommendations["fix"].append({
                "claim_id": claim_id,
                "issue": result.get("evidence", ""),
                "suggested": result["suggestion"],
            })

        # Strengthen: partial adherence
        elif status == "partial":
            adherence = result.get("adherence_ratio")
            msg = f"{claim_id} partially followed"
            if adherence is not None:
                msg += f" ({adherence:.0%} adherence)"
            msg += " — consider adding linter rules to enforce"
            recommendations["strengthen"].append(msg)

    # Check for missing sections
    section_types = set()
    for result in coherence_data.get("results", []):
        section_types.add(result.get("type"))

    if "command" not in section_types:
        recommendations["add"].append("No build/test commands found — add Build & Run section")

    # Blind test insights
    if blind_data:
        summary = blind_data.get("summary", {})
        losses = summary.get("claude_md_losses", 0)
        if losses > 0:
            recommendations["add"].append(
                f"CLAUDE.md lost {losses} blind test(s) — review conventions that "
                "may conflict with Claude's default behavior"
            )

    return recommendations


# ---------------------------------------------------------------------------
# Main aggregation
# ---------------------------------------------------------------------------


def aggregate(
    coherence_data: dict,
    blind_data: dict | None = None,
    claims_data: dict | None = None,
) -> dict:
    """Aggregate all results into evaluation_summary.json."""
    # Build claims lookup
    claims_lookup = {}
    if claims_data:
        for claim in claims_data.get("claims", []):
            claims_lookup[claim["id"]] = claim

    # Coherence scores
    coherence_score = coherence_data.get("coherence_score", 0)
    coherence_summary = {
        "score": coherence_score,
        "total_claims": coherence_data.get("total_claims", 0),
        "verified": coherence_data.get("verified", 0),
        "stale": coherence_data.get("stale", 0),
        "partial": coherence_data.get("partial", 0),
        "unverifiable": coherence_data.get("unverifiable", 0),
    }

    # Effectiveness scores (from blind test)
    effectiveness_summary = None
    effectiveness_score = 0
    if blind_data and blind_data.get("summary"):
        summary = blind_data["summary"]
        total = summary.get("claude_md_wins", 0) + summary.get("ties", 0) + summary.get("claude_md_losses", 0)
        if total > 0:
            # Score: wins count full, ties count half
            effectiveness_score = round(
                (summary["claude_md_wins"] + summary.get("ties", 0) * 0.5) / total * 100,
                1,
            )
        else:
            effectiveness_score = 0

        pass_with = summary.get("programmatic_pass_rate_with", 0)
        pass_without = summary.get("programmatic_pass_rate_without", 0)
        delta = pass_with - pass_without

        effectiveness_summary = {
            "score": effectiveness_score,
            "total_tasks": summary.get("total_tasks", total),
            "claude_md_wins": summary.get("claude_md_wins", 0),
            "ties": summary.get("ties", 0),
            "losses": summary.get("claude_md_losses", 0),
            "programmatic_delta": f"+{delta:.0%}" if delta >= 0 else f"{delta:.0%}",
        }

    # Overall score: weighted average
    if effectiveness_summary:
        # 50% coherence + 50% effectiveness
        overall_score = round(coherence_score * 0.5 + effectiveness_score * 0.5, 1)
    else:
        # Quick eval: coherence only
        overall_score = round(coherence_score, 1)

    grade = score_to_grade(overall_score)

    # Issues and recommendations
    issues = extract_issues(coherence_data, claims_lookup)
    recommendations = generate_recommendations(coherence_data, blind_data, issues)

    result = {
        "overall_score": overall_score,
        "grade": grade,
        "coherence": coherence_summary,
        "top_issues": issues[:10],
        "recommendations": recommendations,
    }

    if effectiveness_summary:
        result["effectiveness"] = effectiveness_summary

    return result


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main():
    parser = argparse.ArgumentParser(description="Aggregate evaluation results")
    parser.add_argument("coherence_json", type=Path, help="Path to coherence_report.json")
    parser.add_argument("--blind", type=Path, default=None, help="Path to blind_results.json")
    parser.add_argument("--claims", type=Path, default=None, help="Path to claims.json (for vague/generic detection)")
    parser.add_argument("--output", type=Path, default=None)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()

    coherence_data = json.loads(args.coherence_json.read_text(encoding="utf-8"))

    blind_data = None
    if args.blind:
        blind_data = json.loads(args.blind.read_text(encoding="utf-8"))

    claims_data = None
    if args.claims:
        claims_data = json.loads(args.claims.read_text(encoding="utf-8"))

    result = aggregate(coherence_data, blind_data, claims_data)

    output_json = json.dumps(result, indent=2 if args.pretty else None, ensure_ascii=False)

    if args.output:
        args.output.write_text(output_json, encoding="utf-8")
        grade = result["grade"]
        score = result["overall_score"]
        print(f"Evaluation summary → {args.output}")
        print(f"Overall: {score}/100 (Grade {grade})")
        print(f"Issues: {len(result['top_issues'])} found")
    else:
        print(output_json)


if __name__ == "__main__":
    main()
