#!/usr/bin/env python3
"""
Chapter Quality Check Script

This script evaluates individual chapters against quality standards.
Used after writing each chapter to ensure it meets threshold before proceeding.
"""

import json
from datetime import datetime
from typing import Dict, List

def create_chapter_evaluation_template() -> Dict:
    """Create template for evaluating a chapter."""
    return {
        "chapter_id": "",  # e.g., "chapter_2"
        "chapter_title": "",
        "target_word_count": 0,
        "actual_word_count": 0,
        "evaluation": {
            "argument_quality": {
                "score": 0,  # 1-4
                "notes": ""
            },
            "citation_quality": {
                "score": 0,  # 1-4
                "notes": ""
            },
            "clarity_readability": {
                "score": 0,  # 1-4
                "notes": ""
            },
            "structure_flow": {
                "score": 0,  # 1-4
                "notes": ""
            },
            "platform_conformity": {
                "score": 0,  # 1-4
                "notes": ""
            }
        },
        "issues": [],  # List of specific issues identified
        "revision_needed": ""  # "none", "minor", "moderate", "major"
    }

def calculate_chapter_score(evaluation: Dict) -> Dict:
    """Calculate total score and assess quality."""
    scores = evaluation.get("evaluation", {})

    total = sum([
        scores.get("argument_quality", {}).get("score", 0),
        scores.get("citation_quality", {}).get("score", 0),
        scores.get("clarity_readability", {}).get("score", 0),
        scores.get("structure_flow", {}).get("score", 0),
        scores.get("platform_conformity", {}).get("score", 0)
    ])

    percentage = (total / 20) * 100
    passes = total >= 16  # 80% threshold

    # Categorize scores
    if total >= 18:
        quality_level = "Excellent"
    elif total >= 16:
        quality_level = "Good"
    elif total >= 14:
        quality_level = "Acceptable (needs revision)"
    else:
        quality_level = "Poor (major revision required)"

    return {
        "total_score": total,
        "max_score": 20,
        "percentage": round(percentage, 1),
        "passes_threshold": passes,
        "quality_level": quality_level
    }

def analyze_word_count(target: int, actual: int) -> Dict:
    """Analyze word count variance."""
    if target == 0:
        return {
            "within_range": True,
            "variance_percent": 0,
            "assessment": "No target specified"
        }

    variance = abs(actual - target)
    variance_percent = (variance / target) * 100

    if variance_percent <= 5:
        within_range = True
        assessment = "Perfect"
    elif variance_percent <= 10:
        within_range = True
        assessment = "Good"
    elif variance_percent <= 20:
        within_range = False
        assessment = "Acceptable"
    else:
        within_range = False
        assessment = "Poor"

    return {
        "within_range": within_range,
        "variance_percent": round(variance_percent, 1),
        "assessment": assessment,
        "difference": actual - target
    }

def identify_weak_dimensions(evaluation: Dict) -> List[Dict]:
    """Identify dimensions scoring below 3."""
    scores = evaluation.get("evaluation", {})
    weak_dimensions = []

    dimensions = [
        ("argument_quality", "Argument Quality"),
        ("citation_quality", "Citation Quality"),
        ("clarity_readability", "Clarity & Readability"),
        ("structure_flow", "Structure & Flow"),
        ("platform_conformity", "Platform Style Conformity")
    ]

    for key, name in dimensions:
        dim_data = scores.get(key, {})
        score = dim_data.get("score", 0)

        if score < 3:
            weak_dimensions.append({
                "dimension": name,
                "score": score,
                "max_score": 4,
                "notes": dim_data.get("notes", ""),
                "severity": "high" if score <= 1 else "medium"
            })

    return weak_dimensions

def generate_recommendations(evaluation: Dict, weak_dims: List[Dict],
                            word_analysis: Dict) -> List[Dict]:
    """Generate specific revision recommendations."""
    recommendations = []

    # Word count issues
    if word_analysis["variance_percent"] > 20:
        recommendations.append({
            "category": "word_count",
            "priority": "medium",
            "issue": f"Word count off by {word_analysis['variance_percent']:.1f}% ({word_analysis['difference']:+d} words)",
            "action": "Cut or expand content to match target" if word_analysis['difference'] > 0 else "Expand content to match target"
        })

    # Weak dimensions
    for dim in weak_dims:
        priority = dim["severity"]
        recommendations.append({
            "category": dim["dimension"],
            "priority": priority,
            "issue": f"{dim['dimension']} scored {dim['score']}/4",
            "action": f"Address: {dim['notes']}" if dim['notes'] else f"Improve {dim['dimension'].lower()}"
        })

    # Custom issues from evaluation
    for issue in evaluation.get("issues", []):
        recommendations.append({
            "category": "custom",
            "priority": "high",
            "issue": issue,
            "action": "Address this specific issue"
        })

    # Sort by priority
    priority_order = {"high": 0, "medium": 1, "low": 2}
    recommendations.sort(key=lambda x: priority_order.get(x["priority"], 3))

    return recommendations

def generate_chapter_report(evaluation: Dict) -> str:
    """Generate comprehensive chapter evaluation report."""
    score_result = calculate_chapter_score(evaluation)
    word_analysis = analyze_word_count(
        evaluation.get("target_word_count", 0),
        evaluation.get("actual_word_count", 0)
    )
    weak_dims = identify_weak_dimensions(evaluation)
    recommendations = generate_recommendations(evaluation, weak_dims, word_analysis)

    report = f"""
# Chapter Quality Report

Generated: {datetime.now().strftime('%Y-%m-%d %H:%M')}

## Chapter Information

- **Chapter ID**: {evaluation.get('chapter_id', 'N/A')}
- **Title**: {evaluation.get('chapter_title', 'N/A')}
- **Target word count**: {evaluation.get('target_word_count', 'N/A')}
- **Actual word count**: {evaluation.get('actual_word_count', 'N/A')}

## Overall Assessment

- **Total Score**: {score_result['total_score']}/{score_result['max_score']} ({score_result['percentage']}%)
- **Quality Level**: {score_result['quality_level']}
- **Passes Threshold**: {'✓ YES' if score_result['passes_threshold'] else '✗ NO (16/20 required)'}

## Dimension Scores

"""

    # Add dimension breakdown
    scores = evaluation.get("evaluation", {})
    dimensions = [
        ("argument_quality", "Argument Quality"),
        ("citation_quality", "Citation Quality"),
        ("clarity_readability", "Clarity & Readability"),
        ("structure_flow", "Structure & Flow"),
        ("platform_conformity", "Platform Style Conformity")
    ]

    for key, name in dimensions:
        dim_data = scores.get(key, {})
        score = dim_data.get("score", 0)
        notes = dim_data.get("notes", "No notes")

        icon = "✓" if score >= 3 else "⚠"
        report += f"### {icon} {name}: {score}/4\n\n"
        report += f"{notes}\n\n"

    # Word count analysis
    report += "## Word Count Analysis\n\n"
    report += f"- **Variance**: {word_analysis['variance_percent']:.1f}% ({word_analysis['difference']:+d} words)\n"
    report += f"- **Assessment**: {word_analysis['assessment']}\n"

    if word_analysis['variance_percent'] > 10:
        report += f"- **Note**: Word count outside recommended ±10% range\n"

    report += "\n"

    # Weak dimensions
    if weak_dims:
        report += "## Weak Dimensions (Score <3)\n\n"
        for dim in weak_dims:
            report += f"### {dim['dimension']}: {dim['score']}/4 ({dim['severity'].upper()} priority)\n\n"
            if dim['notes']:
                report += f"{dim['notes']}\n\n"

    # Recommendations
    if recommendations:
        report += "## Revision Recommendations\n\n"
        report += "Prioritized list of recommended revisions:\n\n"

        for i, rec in enumerate(recommendations, 1):
            priority_icon = {"high": "🔴", "medium": "🟡", "low": "🟢"}.get(rec['priority'], "⚪")
            report += f"{i}. {priority_icon} **{rec['category'].title()}** ({rec['priority'].upper()} priority)\n"
            report += f"   - Issue: {rec['issue']}\n"
            report += f"   - Action: {rec['action']}\n\n"

    # Decision
    report += "## Decision\n\n"

    if score_result['passes_threshold']:
        report += "✓ **PROCEED**: Chapter meets quality threshold. Proceed to next chapter.\n\n"
        if weak_dims or word_analysis['variance_percent'] > 10:
            report += "**Optional improvements**:\n"
            report += "- Consider minor revisions to address noted issues\n"
            report += "- Not required before proceeding\n"
    else:
        report += "✗ **REVISE**: Chapter below quality threshold. Revise before proceeding.\n\n"
        report += "**Required actions**:\n"
        report += "1. Address all HIGH priority recommendations\n"
        report += "2. Re-evaluate chapter after revisions\n"
        report += "3. Verify score ≥16/20 before proceeding to next chapter\n\n"
        report += "**Why this matters**: Each chapter builds on previous ones. Low-quality chapters create cascading problems.\n"

    return report

def validate_evaluation(evaluation: Dict) -> Dict:
    """Validate that evaluation is complete and properly formatted."""
    issues = []
    warnings = []

    # Check required fields
    required_fields = ["chapter_id", "chapter_title", "target_word_count", "actual_word_count"]
    for field in required_fields:
        if not evaluation.get(field):
            issues.append(f"Missing required field: {field}")

    # Check scores present
    eval_data = evaluation.get("evaluation", {})
    dimensions = ["argument_quality", "citation_quality", "clarity_readability",
                 "structure_flow", "platform_conformity"]

    for dim in dimensions:
        if dim not in eval_data:
            issues.append(f"Missing dimension: {dim}")
        else:
            score = eval_data[dim].get("score", 0)
            if not isinstance(score, int) or score < 1 or score > 4:
                issues.append(f"Invalid score for {dim}: {score} (must be 1-4)")

            if not eval_data[dim].get("notes"):
                warnings.append(f"No notes provided for {dim} (recommended)")

    return {
        "valid": len(issues) == 0,
        "issues": issues,
        "warnings": warnings
    }

def compare_chapters(chapters: List[Dict]) -> str:
    """Generate comparison report across multiple chapters."""
    if not chapters:
        return "No chapters to compare."

    report = f"""
# Multi-Chapter Comparison Report

Generated: {datetime.now().strftime('%Y-%m-%d %H:%M')}

## Chapter Score Summary

| Chapter | Title | Score | % | Quality | Pass |
|---------|-------|-------|---|---------|------|
"""

    total_scores = []

    for ch in chapters:
        score_result = calculate_chapter_score(ch)
        total_scores.append(score_result['total_score'])

        pass_icon = "✓" if score_result['passes_threshold'] else "✗"
        report += f"| {ch.get('chapter_id', 'N/A')} | {ch.get('chapter_title', 'N/A')[:30]}... | {score_result['total_score']}/20 | {score_result['percentage']:.1f}% | {score_result['quality_level']} | {pass_icon} |\n"

    # Statistics
    avg_score = sum(total_scores) / len(total_scores) if total_scores else 0
    min_score = min(total_scores) if total_scores else 0
    max_score = max(total_scores) if total_scores else 0
    passing = sum(1 for s in total_scores if s >= 16)

    report += f"""

## Statistics

- **Average score**: {avg_score:.1f}/20 ({(avg_score/20)*100:.1f}%)
- **Range**: {min_score}-{max_score}
- **Passing chapters**: {passing}/{len(chapters)}

"""

    # Dimension comparison
    report += "## Dimension Averages\n\n"

    dimensions = [
        ("argument_quality", "Argument Quality"),
        ("citation_quality", "Citation Quality"),
        ("clarity_readability", "Clarity & Readability"),
        ("structure_flow", "Structure & Flow"),
        ("platform_conformity", "Platform Style Conformity")
    ]

    for key, name in dimensions:
        scores = [ch.get("evaluation", {}).get(key, {}).get("score", 0) for ch in chapters]
        avg = sum(scores) / len(scores) if scores else 0
        report += f"- **{name}**: {avg:.2f}/4\n"

    report += "\n## Overall Assessment\n\n"

    if passing == len(chapters):
        report += "✓ All chapters meet quality threshold. Ready for final quality assessment.\n"
    else:
        report += f"⚠ {len(chapters) - passing} chapter(s) below threshold. Revise before proceeding to final assessment.\n"

    return report

def main():
    """Interactive chapter quality check interface."""
    print("=" * 60)
    print("Chapter Quality Check Tool")
    print("=" * 60)
    print()

    print("Options:")
    print("1. Create evaluation template")
    print("2. Evaluate chapter from JSON")
    print("3. Compare multiple chapters")
    print()

    choice = input("Select option (1-3): ").strip()

    if choice == "1":
        # Create template
        chapter_id = input("Chapter ID (e.g., 'chapter_2'): ").strip()
        chapter_title = input("Chapter title: ").strip()
        target_wc = int(input("Target word count: ").strip())

        template = create_chapter_evaluation_template()
        template["chapter_id"] = chapter_id
        template["chapter_title"] = chapter_title
        template["target_word_count"] = target_wc

        filename = f"{chapter_id}_evaluation.json"
        with open(filename, 'w') as f:
            json.dump(template, f, indent=2)

        print(f"\nTemplate saved to {filename}")
        print("Fill in the evaluation scores and notes, then use option 2 to generate report.")

    elif choice == "2":
        # Evaluate chapter
        filename = input("Enter evaluation JSON filename: ").strip()
        try:
            with open(filename, 'r') as f:
                evaluation = json.load(f)

            # Validate
            validation = validate_evaluation(evaluation)
            if not validation['valid']:
                print("\n⚠ Validation Issues:")
                for issue in validation['issues']:
                    print(f"  - {issue}")
                print("\nPlease fix issues before generating report.")
                return

            if validation['warnings']:
                print("\nℹ️ Warnings:")
                for warning in validation['warnings']:
                    print(f"  - {warning}")
                print()

            # Generate report
            report = generate_chapter_report(evaluation)
            print("\n" + report)

            # Save report
            report_filename = filename.replace('.json', '_report.md')
            with open(report_filename, 'w') as f:
                f.write(report)
            print(f"\nReport saved to {report_filename}")

        except FileNotFoundError:
            print(f"Error: File '{filename}' not found")
        except json.JSONDecodeError:
            print(f"Error: '{filename}' is not valid JSON")

    elif choice == "3":
        # Compare chapters
        filename = input("Enter JSON filename with list of chapter evaluations: ").strip()
        try:
            with open(filename, 'r') as f:
                chapters = json.load(f)

            report = compare_chapters(chapters)
            print("\n" + report)

            report_filename = filename.replace('.json', '_comparison_report.md')
            with open(report_filename, 'w') as f:
                f.write(report)
            print(f"\nComparison report saved to {report_filename}")

        except FileNotFoundError:
            print(f"Error: File '{filename}' not found")
        except json.JSONDecodeError:
            print(f"Error: '{filename}' is not valid JSON")

    else:
        print("Invalid option")

if __name__ == "__main__":
    main()
