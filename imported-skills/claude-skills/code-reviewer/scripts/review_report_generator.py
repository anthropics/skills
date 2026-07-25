#!/usr/bin/env python3
"""
Review Report Generator

Generates comprehensive code review reports by combining PR analysis
and code quality findings into structured, actionable reports.

Usage:
    python review_report_generator.py /path/to/repo
    python review_report_generator.py . --pr-analysis pr_results.json --quality-analysis quality_results.json
    python review_report_generator.py /path/to/repo --format markdown --output review.md
"""

import argparse
import json
import os
import subprocess
import sys
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Tuple


# Severity weights for prioritization
SEVERITY_WEIGHTS = {
    "critical": 100,
    "high": 75,
    "medium": 50,
    "low": 25,
    "info": 10
}

# Review verdict thresholds
VERDICT_THRESHOLDS = {
    "approve": {"max_critical": 0, "max_high": 0, "max_score": 100},
    "approve_with_suggestions": {"max_critical": 0, "max_high": 2, "max_score": 85},
    "request_changes": {"max_critical": 0, "max_high": 5, "max_score": 70},
    "block": {"max_critical": float("inf"), "max_high": float("inf"), "max_score": 0}
}


def load_json_file(filepath: str) -> Optional[Dict]:
    """Load JSON file if it exists."""
    try:
        with open(filepath, "r") as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        return None


def run_pr_analyzer(repo_path: Path) -> Dict:
    """Run pr_analyzer.py and return results."""
    script_path = Path(__file__).parent / "pr_analyzer.py"
    if not script_path.exists():
        return {"status": "error", "message": "pr_analyzer.py not found"}

    try:
        result = subprocess.run(
            [sys.executable, str(script_path), str(repo_path), "--json"],
            capture_output=True,
            text=True,
            timeout=120
        )
        if result.returncode == 0:
            return json.loads(result.stdout)
        return {"status": "error", "message": result.stderr}
    except Exception as e:
        return {"status": "error", "message": str(e)}


def run_quality_checker(repo_path: Path) -> Dict:
    """Run code_quality_checker.py and return results."""
    script_path = Path(__file__).parent / "code_quality_checker.py"
    if not script_path.exists():
        return {"status": "error", "message": "code_quality_checker.py not found"}

    try:
        result = subprocess.run(
            [sys.executable, str(script_path), str(repo_path), "--json"],
            capture_output=True,
            text=True,
            timeout=300
        )
        if result.returncode == 0:
            return json.loads(result.stdout)
        return {"status": "error", "message": result.stderr}
    except Exception as e:
        return {"status": "error", "message": str(e)}


def calculate_review_score(pr_analysis: Dict, quality_analysis: Dict) -> int:
    """Calculate overall review score (0-100)."""
    score = 100

    # Deduct for PR risks
    if "risks" in pr_analysis:
        risks = pr_analysis["risks"]
        score -= len(risks.get("critical", [])) * 15
        score -= len(risks.get("high", [])) * 10
        score -= len(risks.get("medium", [])) * 5
        score -= len(risks.get("low", [])) * 2

    # Deduct for code quality issues
    if "issues" in quality_analysis:
        issues = quality_analysis["issues"]
        score -= len([i for i in issues if i.get("severity") == "critical"]) * 12
        score -= len([i for i in issues if i.get("severity") == "high"]) * 8
        score -= len([i for i in issues if i.get("severity") == "medium"]) * 4
        score -= len([i for i in issues if i.get("severity") == "low"]) * 1

    # Deduct for complexity
    if "summary" in pr_analysis:
        complexity = pr_analysis["summary"].get("complexity_score", 0)
        if complexity > 7:
            score -= 10
        elif complexity > 5:
            score -= 5

    return max(0, min(100, score))


def determine_verdict(score: int, critical_count: int, high_count: int) -> Tuple[str, str]:
    """Determine review verdict based on score and issue counts."""
    if critical_count > 0:
        return "block", "Critical issues must be resolved before merge"

    if score >= 90 and high_count == 0:
        return "approve", "Code meets quality standards"

    if score >= 75 and high_count <= 2:
        return "approve_with_suggestions", "Minor improvements recommended"

    if score >= 50:
        return "request_changes", "Several issues need to be addressed"

    return "block", "Significant issues prevent approval"


def generate_findings_list(pr_analysis: Dict, quality_analysis: Dict) -> List[Dict]:
    """Combine and prioritize all findings."""
    findings = []

    # Add PR risk findings
    if "risks" in pr_analysis:
        for severity, items in pr_analysis["risks"].items():
            for item in items:
                findings.append({
                    "source": "pr_analysis",
                    "severity": severity,
                    "category": item.get("name", "unknown"),
                    "message": item.get("message", ""),
                    "file": item.get("file", ""),
                    "count": item.get("count", 1)
                })

    # Add code quality findings
    if "issues" in quality_analysis:
        for issue in quality_analysis["issues"]:
            findings.append({
                "source": "quality_analysis",
                "severity": issue.get("severity", "medium"),
                "category": issue.get("type", "unknown"),
                "message": issue.get("message", ""),
                "file": issue.get("file", ""),
                "line": issue.get("line", 0)
            })

    # Sort by severity weight
    findings.sort(
        key=lambda x: -SEVERITY_WEIGHTS.get(x["severity"], 0)
    )

    return findings


def generate_action_items(findings: List[Dict]) -> List[Dict]:
    """Generate prioritized action items from findings."""
    action_items = []
    seen_categories = set()

    for finding in findings:
        category = finding["category"]
        severity = finding["severity"]

        # Group similar issues
        if category in seen_categories and severity not in ["critical", "high"]:
            continue

        action = {
            "priority": "P0" if severity == "critical" else "P1" if severity == "high" else "P2",
            "action": get_action_for_category(category, finding),
            "severity": severity,
            "files_affected": [finding["file"]] if finding.get("file") else []
        }
        action_items.append(action)
        seen_categories.add(category)

    return action_items[:15]  # Top 15 actions


def get_action_for_category(category: str, finding: Dict) -> str:
    """Get actionable recommendation for issue category."""
    actions = {
        "hardcoded_secrets": "Remove hardcoded credentials and use environment variables or a secrets manager",
        "sql_concatenation": "Use parameterized queries to prevent SQL injection",
        "debugger": "Remove debugger statements before merging",
        "console_log": "Remove or replace console statements with proper logging",
        "todo_fixme": "Address TODO/FIXME comments or create tracking issues",
        "disable_eslint": "Address the underlying issue instead of disabling lint rules",
        "any_type": "Replace 'any' types with proper type definitions",
        "long_function": "Break down function into smaller, focused units",
        "god_class": "Split class into smaller, single-responsibility classes",
        "too_many_params": "Use parameter objects or builder pattern",
        "deep_nesting": "Refactor using early returns, guard clauses, or extraction",
        "high_complexity": "Reduce cyclomatic complexity through refactoring",
        "missing_error_handling": "Add proper error handling and recovery logic",
        "duplicate_code": "Extract duplicate code into shared functions",
        "magic_numbers": "Replace magic numbers with named constants",
        "large_file": "Consider splitting into multiple smaller modules"
    }
    return actions.get(category, f"Review and address: {finding.get('message', category)}")


def format_markdown_report(report: Dict) -> str:
    """Generate markdown-formatted report."""
    lines = []

    # Header
    lines.append("# Code Review Report")
    lines.append("")
    lines.append(f"**Generated:** {report['metadata']['generated_at']}")
    lines.append(f"**Repository:** {report['metadata']['repository']}")
    lines.append("")

    # Executive Summary
    lines.append("## Executive Summary")
    lines.append("")
    summary = report["summary"]
    verdict = summary["verdict"]
    verdict_emoji = {
        "approve": "✅",
        "approve_with_suggestions": "✅",
        "request_changes": "⚠️",
        "block": "❌"
    }.get(verdict, "❓")

    lines.append(f"**Verdict:** {verdict_emoji} {verdict.upper().replace('_', ' ')}")
    lines.append(f"**Score:** {summary['score']}/100")
    lines.append(f"**Rationale:** {summary['rationale']}")
    lines.append("")

    # Issue Counts
    lines.append("### Issue Summary")
    lines.append("")
    lines.append("| Severity | Count |")
    lines.append("|----------|-------|")
    for severity in ["critical", "high", "medium", "low"]:
        count = summary["issue_counts"].get(severity, 0)
        lines.append(f"| {severity.capitalize()} | {count} |")
    lines.append("")

    # PR Statistics (if available)
    if "pr_summary" in report:
        pr = report["pr_summary"]
        lines.append("### Change Statistics")
        lines.append("")
        lines.append(f"- **Files Changed:** {pr.get('files_changed', 'N/A')}")
        lines.append(f"- **Lines Added:** +{pr.get('total_additions', 0)}")
        lines.append(f"- **Lines Removed:** -{pr.get('total_deletions', 0)}")
        lines.append(f"- **Complexity:** {pr.get('complexity_label', 'N/A')}")
        lines.append("")

    # Action Items
    if report.get("action_items"):
        lines.append("## Action Items")
        lines.append("")
        for i, item in enumerate(report["action_items"], 1):
            priority = item["priority"]
            emoji = "🔴" if priority == "P0" else "🟠" if priority == "P1" else "🟡"
            lines.append(f"{i}. {emoji} **[{priority}]** {item['action']}")
            if item.get("files_affected"):
                lines.append(f"   - Files: {', '.join(item['files_affected'][:3])}")
        lines.append("")

    # Critical Findings
    critical_findings = [f for f in report.get("findings", []) if f["severity"] == "critical"]
    if critical_findings:
        lines.append("## Critical Issues (Must Fix)")
        lines.append("")
        for finding in critical_findings:
            lines.append(f"- **{finding['category']}** in `{finding.get('file', 'unknown')}`")
            lines.append(f"  - {finding['message']}")
        lines.append("")

    # High Priority Findings
    high_findings = [f for f in report.get("findings", []) if f["severity"] == "high"]
    if high_findings:
        lines.append("## High Priority Issues")
        lines.append("")
        for finding in high_findings[:10]:
            lines.append(f"- **{finding['category']}** in `{finding.get('file', 'unknown')}`")
            lines.append(f"  - {finding['message']}")
        lines.append("")

    # Review Order (if available)
    if "review_order" in report:
        lines.append("## Suggested Review Order")
        lines.append("")
        for i, filepath in enumerate(report["review_order"][:10], 1):
            lines.append(f"{i}. `{filepath}`")
        lines.append("")

    # Footer
    lines.append("---")
    lines.append("*Generated by Code Reviewer*")

    return "\n".join(lines)


def format_text_report(report: Dict) -> str:
    """Generate plain text report."""
    lines = []

    lines.append("=" * 60)
    lines.append("CODE REVIEW REPORT")
    lines.append("=" * 60)
    lines.append("")
    lines.append(f"Generated: {report['metadata']['generated_at']}")
    lines.append(f"Repository: {report['metadata']['repository']}")
    lines.append("")

    summary = report["summary"]
    verdict = summary["verdict"].upper().replace("_", " ")
    lines.append(f"VERDICT: {verdict}")
    lines.append(f"SCORE: {summary['score']}/100")
    lines.append(f"RATIONALE: {summary['rationale']}")
    lines.append("")

    lines.append("--- ISSUE SUMMARY ---")
    for severity in ["critical", "high", "medium", "low"]:
        count = summary["issue_counts"].get(severity, 0)
        lines.append(f"  {severity.capitalize()}: {count}")
    lines.append("")

    if report.get("action_items"):
        lines.append("--- ACTION ITEMS ---")
        for i, item in enumerate(report["action_items"][:10], 1):
            lines.append(f"  {i}. [{item['priority']}] {item['action']}")
        lines.append("")

    critical = [f for f in report.get("findings", []) if f["severity"] == "critical"]
    if critical:
        lines.append("--- CRITICAL ISSUES ---")
        for f in critical:
            lines.append(f"  [{f.get('file', 'unknown')}] {f['message']}")
        lines.append("")

    lines.append("=" * 60)

    return "\n".join(lines)


def generate_report(
    repo_path: Path,
    pr_analysis: Optional[Dict] = None,
    quality_analysis: Optional[Dict] = None
) -> Dict:
    """Generate comprehensive review report."""
    # Run analyses if not provided
    if pr_analysis is None:
        pr_analysis = run_pr_analyzer(repo_path)

    if quality_analysis is None:
        quality_analysis = run_quality_checker(repo_path)

    # Generate findings
    findings = generate_findings_list(pr_analysis, quality_analysis)

    # Count issues by severity
    issue_counts = {
        "critical": len([f for f in findings if f["severity"] == "critical"]),
        "high": len([f for f in findings if f["severity"] == "high"]),
        "medium": len([f for f in findings if f["severity"] == "medium"]),
        "low": len([f for f in findings if f["severity"] == "low"])
    }

    # Calculate score and verdict
    score = calculate_review_score(pr_analysis, quality_analysis)
    verdict, rationale = determine_verdict(
        score,
        issue_counts["critical"],
        issue_counts["high"]
    )

    # Generate action items
    action_items = generate_action_items(findings)

    # Build report
    report = {
        "metadata": {
            "generated_at": datetime.now().isoformat(),
            "repository": str(repo_path),
            "version": "1.0.0"
        },
        "summary": {
            "score": score,
            "verdict": verdict,
            "rationale": rationale,
            "issue_counts": issue_counts
        },
        "findings": findings,
        "action_items": action_items
    }

    # Add PR summary if available
    if pr_analysis.get("status") == "analyzed":
        report["pr_summary"] = pr_analysis.get("summary", {})
        report["review_order"] = pr_analysis.get("review_order", [])

    # Add quality summary if available
    if quality_analysis.get("status") == "analyzed":
        report["quality_summary"] = quality_analysis.get("summary", {})

    return report


def main():
    parser = argparse.ArgumentParser(
        description="Generate comprehensive code review reports"
    )
    parser.add_argument(
        "repo_path",
        nargs="?",
        default=".",
        help="Path to repository (default: current directory)"
    )
    parser.add_argument(
        "--pr-analysis",
        help="Path to pre-computed PR analysis JSON"
    )
    parser.add_argument(
        "--quality-analysis",
        help="Path to pre-computed quality analysis JSON"
    )
    parser.add_argument(
        "--format", "-f",
        choices=["text", "markdown", "json"],
        default="text",
        help="Output format (default: text)"
    )
    parser.add_argument(
        "--output", "-o",
        help="Write output to file"
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output as JSON (shortcut for --format json)"
    )

    args = parser.parse_args()

    repo_path = Path(args.repo_path).resolve()
    if not repo_path.exists():
        print(f"Error: Path does not exist: {repo_path}", file=sys.stderr)
        sys.exit(1)

    # Load pre-computed analyses if provided
    pr_analysis = None
    quality_analysis = None

    if args.pr_analysis:
        pr_analysis = load_json_file(args.pr_analysis)
        if not pr_analysis:
            print(f"Warning: Could not load PR analysis from {args.pr_analysis}")

    if args.quality_analysis:
        quality_analysis = load_json_file(args.quality_analysis)
        if not quality_analysis:
            print(f"Warning: Could not load quality analysis from {args.quality_analysis}")

    # Generate report
    report = generate_report(repo_path, pr_analysis, quality_analysis)

    # Format output
    output_format = "json" if args.json else args.format

    if output_format == "json":
        output = json.dumps(report, indent=2)
    elif output_format == "markdown":
        output = format_markdown_report(report)
    else:
        output = format_text_report(report)

    # Write or print output
    if args.output:
        with open(args.output, "w") as f:
            f.write(output)
        print(f"Report written to {args.output}")
    else:
        print(output)


if __name__ == "__main__":
    main()
