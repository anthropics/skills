#!/usr/bin/env python3
"""
Final Paper Evaluation Script

This script evaluates the complete paper against quality standards before submission.
Uses 7-dimension assessment (10 points each, 70 total).
"""

import json
from datetime import datetime
from typing import Dict, List

def create_final_evaluation_template() -> Dict:
    """Create template for final paper evaluation."""
    return {
        "paper_title": "",
        "total_word_count": 0,
        "target_platform": "",
        "evaluation_date": "",
        "evaluation": {
            "overall_argument_quality": {
                "score": 0,  # 1-10
                "notes": ""
            },
            "literature_integration": {
                "score": 0,  # 1-10
                "citation_count": 0,
                "notes": ""
            },
            "clarity_accessibility": {
                "score": 0,  # 1-10
                "notes": ""
            },
            "originality_contribution": {
                "score": 0,  # 1-10
                "notes": ""
            },
            "methodological_rigor": {
                "score": 0,  # 1-10
                "notes": ""
            },
            "structure_organization": {
                "score": 0,  # 1-10
                "notes": ""
            },
            "platform_conformity": {
                "score": 0,  # 1-10
                "notes": ""
            }
        },
        "completeness_checklist": {
            "structural": {
                "abstract": False,
                "introduction": False,
                "main_chapters": False,
                "conclusion": False,
                "references": False
            },
            "content": {
                "promises_fulfilled": False,
                "claims_supported": False,
                "terms_defined": False,
                "objections_addressed": False,
                "limitations_acknowledged": False
            },
            "citations": {
                "text_has_bibliography": False,
                "bibliography_cited": False,
                "format_consistent": False,
                "complete_information": False
            },
            "format": {
                "title_page": False,
                "section_numbering": False,
                "heading_hierarchy": False,
                "platform_requirements": False
            }
        },
        "identified_issues": [],
        "submission_ready": False
    }

def calculate_final_score(evaluation: Dict) -> Dict:
    """Calculate total score and determine submission readiness."""
    scores = evaluation.get("evaluation", {})

    total = sum([
        scores.get("overall_argument_quality", {}).get("score", 0),
        scores.get("literature_integration", {}).get("score", 0),
        scores.get("clarity_accessibility", {}).get("score", 0),
        scores.get("originality_contribution", {}).get("score", 0),
        scores.get("methodological_rigor", {}).get("score", 0),
        scores.get("structure_organization", {}).get("score", 0),
        scores.get("platform_conformity", {}).get("score", 0)
    ])

    percentage = (total / 70) * 100
    passes = total >= 56  # 80% threshold

    # Categorize quality
    if total >= 63:  # 90%
        quality_level = "Excellent"
        recommendation = "Ready for immediate submission"
    elif total >= 56:  # 80%
        quality_level = "Good"
        recommendation = "Ready for submission with minor optional improvements"
    elif total >= 49:  # 70%
        quality_level = "Acceptable"
        recommendation = "Moderate revisions recommended before submission"
    else:
        quality_level = "Needs Improvement"
        recommendation = "Major revisions required before submission"

    return {
        "total_score": total,
        "max_score": 70,
        "percentage": round(percentage, 1),
        "passes_threshold": passes,
        "quality_level": quality_level,
        "recommendation": recommendation
    }

def evaluate_completeness(checklist: Dict) -> Dict:
    """Evaluate completeness across all categories."""
    categories = ["structural", "content", "citations", "format"]

    results = {}
    total_items = 0
    completed_items = 0

    for category in categories:
        cat_data = checklist.get(category, {})
        cat_total = len(cat_data)
        cat_completed = sum(1 for v in cat_data.values() if v)

        results[category] = {
            "completed": cat_completed,
            "total": cat_total,
            "percentage": (cat_completed / cat_total * 100) if cat_total > 0 else 0,
            "complete": cat_completed == cat_total
        }

        total_items += cat_total
        completed_items += cat_completed

    overall_complete = completed_items == total_items

    return {
        "by_category": results,
        "overall": {
            "completed": completed_items,
            "total": total_items,
            "percentage": (completed_items / total_items * 100) if total_items > 0 else 0,
            "complete": overall_complete
        }
    }

def identify_weak_dimensions(evaluation: Dict) -> List[Dict]:
    """Identify dimensions scoring below 7."""
    scores = evaluation.get("evaluation", {})
    weak_dimensions = []

    dimensions = [
        ("overall_argument_quality", "Overall Argument Quality"),
        ("literature_integration", "Literature Integration"),
        ("clarity_accessibility", "Clarity & Accessibility"),
        ("originality_contribution", "Originality & Contribution"),
        ("methodological_rigor", "Methodological Rigor"),
        ("structure_organization", "Structure & Organization"),
        ("platform_conformity", "Platform & Style Conformity")
    ]

    for key, name in dimensions:
        dim_data = scores.get(key, {})
        score = dim_data.get("score", 0)

        if score < 7:
            severity = "high" if score <= 4 else "medium"
            weak_dimensions.append({
                "dimension": name,
                "score": score,
                "max_score": 10,
                "notes": dim_data.get("notes", ""),
                "severity": severity
            })

    return weak_dimensions

def generate_recommendations(evaluation: Dict, weak_dims: List[Dict],
                            completeness: Dict) -> List[Dict]:
    """Generate prioritized revision recommendations."""
    recommendations = []

    # Completeness issues
    if not completeness['overall']['complete']:
        for category, data in completeness['by_category'].items():
            if not data['complete']:
                recommendations.append({
                    "category": "completeness",
                    "priority": "high",
                    "issue": f"{category.title()} completeness: {data['completed']}/{data['total']} items",
                    "action": f"Complete all {category} checklist items before submission"
                })

    # Weak dimensions
    for dim in weak_dims:
        recommendations.append({
            "category": dim["dimension"],
            "priority": dim["severity"],
            "issue": f"{dim['dimension']} scored {dim['score']}/10",
            "action": f"Address: {dim['notes']}" if dim['notes'] else f"Improve {dim['dimension'].lower()}"
        })

    # Citation count check
    lit_data = evaluation.get("evaluation", {}).get("literature_integration", {})
    citation_count = lit_data.get("citation_count", 0)

    if citation_count < 20:
        recommendations.append({
            "category": "citations",
            "priority": "high",
            "issue": f"Only {citation_count} citations (minimum 20 recommended)",
            "action": "Expand literature review and add supporting citations"
        })
    elif citation_count < 30:
        recommendations.append({
            "category": "citations",
            "priority": "medium",
            "issue": f"{citation_count} citations (30-40 recommended for philosophy)",
            "action": "Consider adding more citations to strengthen arguments"
        })

    # Custom issues
    for issue in evaluation.get("identified_issues", []):
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

def generate_final_report(evaluation: Dict) -> str:
    """Generate comprehensive final evaluation report."""
    score_result = calculate_final_score(evaluation)
    completeness = evaluate_completeness(evaluation.get("completeness_checklist", {}))
    weak_dims = identify_weak_dimensions(evaluation)
    recommendations = generate_recommendations(evaluation, weak_dims, completeness)

    report = f"""
# Final Paper Evaluation Report

Generated: {datetime.now().strftime('%Y-%m-%d %H:%M')}

## Paper Information

- **Title**: {evaluation.get('paper_title', 'N/A')}
- **Total word count**: {evaluation.get('total_word_count', 'N/A')}
- **Target platform**: {evaluation.get('target_platform', 'N/A')}
- **Evaluation date**: {evaluation.get('evaluation_date', datetime.now().strftime('%Y-%m-%d'))}

---

## Overall Assessment

- **Total Score**: {score_result['total_score']}/{score_result['max_score']} ({score_result['percentage']}%)
- **Quality Level**: {score_result['quality_level']}
- **Passes Threshold**: {'✓ YES' if score_result['passes_threshold'] else '✗ NO (56/70 required)'}
- **Recommendation**: {score_result['recommendation']}

---

## 7-Dimension Evaluation

"""

    # Dimension scores
    scores = evaluation.get("evaluation", {})
    dimensions = [
        ("overall_argument_quality", "Overall Argument Quality"),
        ("literature_integration", "Literature Integration"),
        ("clarity_accessibility", "Clarity & Accessibility"),
        ("originality_contribution", "Originality & Contribution"),
        ("methodological_rigor", "Methodological Rigor"),
        ("structure_organization", "Structure & Organization"),
        ("platform_conformity", "Platform & Style Conformity")
    ]

    for key, name in dimensions:
        dim_data = scores.get(key, {})
        score = dim_data.get("score", 0)
        notes = dim_data.get("notes", "No notes provided")

        icon = "✓" if score >= 7 else "⚠"
        report += f"### {icon} {name}: {score}/10\n\n"
        report += f"{notes}\n\n"

        # Add citation count for literature dimension
        if key == "literature_integration":
            citation_count = dim_data.get("citation_count", 0)
            report += f"**Citation count**: {citation_count}\n\n"

    # Completeness assessment
    report += "---\n\n## Completeness Assessment\n\n"

    overall_comp = completeness['overall']
    report += f"**Overall**: {overall_comp['completed']}/{overall_comp['total']} items complete ({overall_comp['percentage']:.1f}%)\n\n"

    for category, data in completeness['by_category'].items():
        icon = "✓" if data['complete'] else "⚠"
        report += f"### {icon} {category.title()}: {data['completed']}/{data['total']} ({data['percentage']:.1f}%)\n\n"

        # List incomplete items
        cat_checklist = evaluation.get("completeness_checklist", {}).get(category, {})
        incomplete = [item for item, done in cat_checklist.items() if not done]

        if incomplete:
            report += "**Incomplete items**:\n"
            for item in incomplete:
                report += f"- {item.replace('_', ' ').title()}\n"
            report += "\n"

    # Weak dimensions
    if weak_dims:
        report += "---\n\n## Weak Dimensions (Score <7)\n\n"
        for dim in weak_dims:
            report += f"### {dim['dimension']}: {dim['score']}/10 ({dim['severity'].upper()} priority)\n\n"
            if dim['notes']:
                report += f"{dim['notes']}\n\n"

    # Recommendations
    if recommendations:
        report += "---\n\n## Revision Recommendations\n\n"
        report += "Prioritized list of recommended revisions:\n\n"

        for i, rec in enumerate(recommendations, 1):
            priority_icon = {"high": "🔴", "medium": "🟡", "low": "🟢"}.get(rec['priority'], "⚪")
            report += f"{i}. {priority_icon} **{rec['category'].title()}** ({rec['priority'].upper()} priority)\n"
            report += f"   - Issue: {rec['issue']}\n"
            report += f"   - Action: {rec['action']}\n\n"

    # Submission decision
    report += "---\n\n## Submission Decision\n\n"

    submission_ready = evaluation.get('submission_ready', False)

    if score_result['passes_threshold'] and completeness['overall']['complete']:
        report += f"✓ **READY FOR SUBMISSION**: Paper meets quality threshold ({score_result['percentage']}%) and all completeness checks passed.\n\n"

        if score_result['percentage'] >= 90:
            report += "**Quality**: Excellent. No revisions required.\n\n"
        else:
            report += "**Optional improvements**:\n"
            if recommendations:
                for rec in recommendations[:3]:  # Top 3
                    report += f"- {rec['action']}\n"
            else:
                report += "- No critical issues identified\n"
            report += "\n**Note**: These improvements are optional. Paper is ready for submission as is.\n"

    else:
        report += f"✗ **NOT READY**: Paper requires revisions before submission.\n\n"

        if not score_result['passes_threshold']:
            report += f"**Quality issue**: Score {score_result['total_score']}/70 is below 56/70 threshold.\n"

        if not completeness['overall']['complete']:
            report += f"**Completeness issue**: {overall_comp['total'] - overall_comp['completed']} checklist items incomplete.\n"

        report += "\n**Required actions**:\n"
        report += "1. Address all HIGH priority recommendations\n"
        report += "2. Complete all checklist items\n"
        report += "3. Re-evaluate paper after revisions\n"
        report += "4. Verify score ≥56/70 and all items complete\n"

    # Platform-specific submission checklist
    report += "\n---\n\n## Platform-Specific Submission Checklist\n\n"

    platform = evaluation.get('target_platform', '').lower()

    if 'philarchive' in platform or 'philpapers' in platform:
        report += """**PhilArchive/PhilPapers**:
- [ ] PDF format
- [ ] Abstract <500 words
- [ ] Proper metadata (title, keywords, AMS classification)
- [ ] Author information complete
- [ ] No formatting issues in PDF
"""

    elif 'arxiv' in platform:
        report += """**arXiv**:
- [ ] LaTeX or PDF format
- [ ] Abstract <1920 characters
- [ ] Proper category selection (cs.AI, q-bio.NC, etc.)
- [ ] No embedded fonts issues
- [ ] Author affiliations included
"""

    elif 'philsci' in platform:
        report += """**PhilSci-Archive**:
- [ ] PDF format
- [ ] Proper subject classification
- [ ] Keywords provided (3-5 recommended)
- [ ] No copyrighted material without permission
- [ ] Author contact information
"""

    else:
        report += f"**{evaluation.get('target_platform', 'Platform')}**:\n"
        report += "- [ ] Check platform-specific requirements\n"
        report += "- [ ] Verify format compliance\n"
        report += "- [ ] Prepare all required metadata\n"

    report += "\n---\n\n## Next Steps\n\n"

    if score_result['passes_threshold'] and completeness['overall']['complete']:
        report += "1. Review optional improvements (if desired)\n"
        report += "2. Complete platform-specific submission checklist\n"
        report += "3. Generate final PDF\n"
        report += "4. Submit to platform\n"
        report += "5. Monitor for feedback/acceptance\n"
    else:
        report += "1. Implement HIGH priority revisions\n"
        report += "2. Complete all checklist items\n"
        report += "3. Re-run final evaluation\n"
        report += "4. When passing, proceed with submission steps\n"

    return report

def validate_evaluation(evaluation: Dict) -> Dict:
    """Validate that evaluation is complete and properly formatted."""
    issues = []
    warnings = []

    # Check required fields
    required_fields = ["paper_title", "total_word_count", "target_platform"]
    for field in required_fields:
        if not evaluation.get(field):
            warnings.append(f"Missing recommended field: {field}")

    # Check all dimensions scored
    eval_data = evaluation.get("evaluation", {})
    dimensions = ["overall_argument_quality", "literature_integration",
                 "clarity_accessibility", "originality_contribution",
                 "methodological_rigor", "structure_organization",
                 "platform_conformity"]

    for dim in dimensions:
        if dim not in eval_data:
            issues.append(f"Missing dimension: {dim}")
        else:
            score = eval_data[dim].get("score", 0)
            if not isinstance(score, int) or score < 1 or score > 10:
                issues.append(f"Invalid score for {dim}: {score} (must be 1-10)")

            if not eval_data[dim].get("notes"):
                warnings.append(f"No notes provided for {dim} (recommended)")

    # Check completeness checklist
    checklist = evaluation.get("completeness_checklist", {})
    if not checklist:
        issues.append("Missing completeness_checklist")

    return {
        "valid": len(issues) == 0,
        "issues": issues,
        "warnings": warnings
    }

def main():
    """Interactive final evaluation interface."""
    print("=" * 60)
    print("Final Paper Evaluation Tool")
    print("=" * 60)
    print()

    print("Options:")
    print("1. Create evaluation template")
    print("2. Evaluate paper from JSON")
    print()

    choice = input("Select option (1-2): ").strip()

    if choice == "1":
        # Create template
        title = input("Paper title: ").strip()
        word_count = int(input("Total word count: ").strip())
        platform = input("Target platform: ").strip()

        template = create_final_evaluation_template()
        template["paper_title"] = title
        template["total_word_count"] = word_count
        template["target_platform"] = platform
        template["evaluation_date"] = datetime.now().strftime('%Y-%m-%d')

        filename = "final_evaluation.json"
        with open(filename, 'w') as f:
            json.dump(template, f, indent=2)

        print(f"\nTemplate saved to {filename}")
        print("Fill in the evaluation scores, notes, and checklist, then use option 2 to generate report.")

    elif choice == "2":
        # Evaluate paper
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
            report = generate_final_report(evaluation)
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

    else:
        print("Invalid option")

if __name__ == "__main__":
    main()
