#!/usr/bin/env python3
"""
Research Gap Analysis Script

This script helps structure and evaluate identified research gaps.
It provides templates and validation for gap documentation.
"""

import json
from datetime import datetime
from typing import List, Dict

def create_gap_template() -> Dict:
    """Create template for documenting a research gap."""
    return {
        "gap_id": "",  # e.g., "GAP-001"
        "title": "",
        "type": "",  # complete/partial/controversy
        "definition": "",
        "evidence": [
            {
                "citation": "",  # "Author (Year)"
                "quote": "",
                "context": ""
            }
        ],
        "significance": "",  # high/medium/low
        "feasibility": "",
        "why_matters": "",
        "user_approach": ""
    }

def validate_gap(gap: Dict) -> Dict:
    """
    Validate a research gap against quality standards.

    Requirements:
    - Specific definition
    - At least 3 pieces of evidence
    - Clear significance and feasibility assessment
    """
    issues = []
    warnings = []

    # Check required fields
    required_fields = ["title", "type", "definition", "significance", "feasibility", "why_matters"]
    for field in required_fields:
        if not gap.get(field):
            issues.append(f"Missing required field: {field}")

    # Check gap type
    valid_types = ["complete", "partial", "controversy"]
    if gap.get("type") and gap.get("type") not in valid_types:
        issues.append(f"Invalid type: '{gap.get('type')}'. Must be one of: {', '.join(valid_types)}")

    # Check evidence count
    evidence_count = len(gap.get("evidence", []))
    if evidence_count < 3:
        issues.append(f"Insufficient evidence: {evidence_count}/3 required")
    elif evidence_count < 5:
        warnings.append(f"Evidence count ({evidence_count}) is acceptable but 5+ recommended")

    # Check evidence quality
    for i, ev in enumerate(gap.get("evidence", []), 1):
        if not ev.get("citation"):
            issues.append(f"Evidence #{i}: Missing citation")
        if not ev.get("quote"):
            issues.append(f"Evidence #{i}: Missing quote")
        if not ev.get("context"):
            warnings.append(f"Evidence #{i}: Missing context (recommended)")

    # Check significance
    valid_significance = ["high", "medium", "low"]
    if gap.get("significance") and gap.get("significance") not in valid_significance:
        issues.append(f"Invalid significance: '{gap.get('significance')}'. Must be one of: {', '.join(valid_significance)}")

    # Check definition length
    definition_length = len(gap.get("definition", "").split())
    if definition_length < 20:
        warnings.append(f"Definition too short ({definition_length} words). Aim for 50-100 words.")
    elif definition_length > 150:
        warnings.append(f"Definition too long ({definition_length} words). Aim for 50-100 words.")

    # Check why_matters length
    why_matters_length = len(gap.get("why_matters", "").split())
    if why_matters_length < 50:
        warnings.append(f"'Why matters' too short ({why_matters_length} words). Aim for 100-200 words.")

    return {
        "valid": len(issues) == 0,
        "issues": issues,
        "warnings": warnings,
        "evidence_count": evidence_count,
        "definition_length": definition_length,
        "why_matters_length": why_matters_length
    }

def analyze_gap_portfolio(gaps: List[Dict]) -> Dict:
    """Analyze the overall gap portfolio quality."""
    if not gaps:
        return {
            "meets_standard": False,
            "recommendation": "⚠ No gaps identified. Minimum 3 gaps required."
        }

    gap_count = len(gaps)
    valid_gaps = [g for g in gaps if validate_gap(g)["valid"]]
    valid_count = len(valid_gaps)

    # Type distribution
    types = [g.get("type", "") for g in gaps]
    type_distribution = {
        "complete": types.count("complete"),
        "partial": types.count("partial"),
        "controversy": types.count("controversy")
    }

    # Significance distribution
    significance = [g.get("significance", "") for g in gaps]
    high_sig_count = significance.count("high")

    # Average evidence per gap
    total_evidence = sum(len(g.get("evidence", [])) for g in gaps)
    avg_evidence = total_evidence / gap_count if gap_count > 0 else 0

    # Meets standards check
    meets_standard = (
        gap_count >= 3 and
        valid_count >= 3 and
        high_sig_count >= 1 and
        avg_evidence >= 3
    )

    return {
        "total_gaps": gap_count,
        "valid_gaps": valid_count,
        "type_distribution": type_distribution,
        "high_significance_count": high_sig_count,
        "average_evidence": round(avg_evidence, 1),
        "meets_standard": meets_standard,
        "recommendation": _get_portfolio_recommendation(
            gap_count, valid_count, high_sig_count, avg_evidence
        )
    }

def _get_portfolio_recommendation(total: int, valid: int, high_sig: int, avg_evidence: float) -> str:
    """Generate recommendation for gap portfolio."""
    if total < 3:
        return f"⚠ Insufficient gaps: {total}/3 minimum required"

    if valid < 3:
        return f"⚠ Only {valid}/{total} gaps are valid. Fix validation issues."

    if high_sig < 1:
        return "⚠ No high-significance gaps. At least 1 required."

    if avg_evidence < 3:
        return f"⚠ Average evidence ({avg_evidence:.1f}) below 3.0 minimum"

    return "✓ Gap portfolio meets quality standards"

def generate_gap_report(gaps: List[Dict]) -> str:
    """Generate comprehensive gap analysis report."""
    portfolio = analyze_gap_portfolio(gaps)

    report = f"""
# Research Gap Analysis Report

Generated: {datetime.now().strftime('%Y-%m-%d %H:%M')}

## Portfolio Summary

- **Total gaps identified**: {portfolio['total_gaps']}
- **Valid gaps**: {portfolio['valid_gaps']}/{portfolio['total_gaps']}
- **High-significance gaps**: {portfolio['high_significance_count']}
- **Average evidence per gap**: {portfolio['average_evidence']}
- **Quality**: {"✓ PASS" if portfolio['meets_standard'] else "⚠ NEEDS IMPROVEMENT"}

## Gap Type Distribution

- Complete gaps (unexplored): {portfolio['type_distribution']['complete']}
- Partial gaps (understudied): {portfolio['type_distribution']['partial']}
- Controversy gaps (unresolved): {portfolio['type_distribution']['controversy']}

## Portfolio Assessment

{portfolio['recommendation']}

## Detailed Gap Analysis

"""

    for i, gap in enumerate(gaps, 1):
        validation = validate_gap(gap)

        status_icon = "✓" if validation['valid'] else "⚠"
        report += f"### {status_icon} Gap {i}: {gap.get('title', 'Untitled')}\n\n"

        report += f"**ID**: {gap.get('gap_id', 'N/A')}\n\n"
        report += f"**Type**: {gap.get('type', 'N/A')}\n\n"
        report += f"**Significance**: {gap.get('significance', 'N/A')}\n\n"
        report += f"**Feasibility**: {gap.get('feasibility', 'N/A')}\n\n"

        report += "**Definition**:\n"
        report += f"{gap.get('definition', 'N/A')}\n\n"

        report += f"**Evidence** ({validation['evidence_count']} pieces):\n\n"
        for j, evidence in enumerate(gap.get('evidence', []), 1):
            report += f"{j}. **{evidence.get('citation', 'No citation')}**\n"
            report += f"   > \"{evidence.get('quote', 'No quote')}\"\n"
            if evidence.get('context'):
                report += f"   - Context: {evidence.get('context')}\n"
            report += "\n"

        report += "**Why This Matters**:\n"
        report += f"{gap.get('why_matters', 'N/A')}\n\n"

        # Validation results
        if not validation['valid']:
            report += "**⚠ Validation Issues**:\n"
            for issue in validation['issues']:
                report += f"- {issue}\n"
            report += "\n"

        if validation['warnings']:
            report += "**ℹ️ Warnings**:\n"
            for warning in validation['warnings']:
                report += f"- {warning}\n"
            report += "\n"

        report += "---\n\n"

    report += "## Recommendations\n\n"

    if portfolio['meets_standard']:
        report += "✓ **PROCEED**: Gap portfolio meets quality standards.\n\n"
        report += "Next steps:\n"
        report += "1. Proceed to originality assessment (Phase 2.2)\n"
        report += "2. Discuss core concepts with user (Phase 2.3)\n"
        report += "3. Begin outline design (Phase 3)\n"
    else:
        report += "⚠ **REVISE**: Address the following before proceeding:\n\n"
        report += f"- {portfolio['recommendation']}\n"

        # Specific actionable items
        for i, gap in enumerate(gaps, 1):
            validation = validate_gap(gap)
            if not validation['valid']:
                report += f"\n**Gap {i} ({gap.get('title', 'Untitled')})**:\n"
                for issue in validation['issues']:
                    report += f"  - Fix: {issue}\n"

    return report

def generate_gap_evidence_package(gap: Dict) -> str:
    """Generate evidence package for a single gap (for documentation)."""
    package = f"""
# Gap Evidence Package: {gap.get('title', 'Untitled')}

**Gap ID**: {gap.get('gap_id', 'N/A')}

## Definition

{gap.get('definition', 'No definition provided')}

## Evidence from Literature

"""

    for i, evidence in enumerate(gap.get('evidence', []), 1):
        package += f"### Evidence {i}\n\n"
        package += f"**Citation**: {evidence.get('citation', 'No citation')}\n\n"
        package += f"**Quote**: \"{evidence.get('quote', 'No quote')}\"\n\n"
        package += f"**Context**: {evidence.get('context', 'No context provided')}\n\n"

    package += f"""
## Why This Gap Matters

{gap.get('why_matters', 'No justification provided')}

## Feasibility Assessment

{gap.get('feasibility', 'No assessment provided')}

## User's Approach

{gap.get('user_approach', 'No approach specified')}
"""

    return package

def main():
    """Interactive gap analysis interface."""
    print("=" * 60)
    print("Research Gap Analysis Tool")
    print("=" * 60)
    print()

    print("Options:")
    print("1. Create gap template")
    print("2. Validate gap from JSON")
    print("3. Generate portfolio report")
    print("4. Generate evidence package for single gap")
    print()

    choice = input("Select option (1-4): ").strip()

    if choice == "1":
        # Create template
        num_gaps = int(input("Number of gaps to document: ").strip())
        gaps = [create_gap_template() for _ in range(num_gaps)]

        # Assign IDs
        for i, gap in enumerate(gaps, 1):
            gap["gap_id"] = f"GAP-{i:03d}"

        filename = input("Save template to (filename.json): ").strip()
        with open(filename, 'w') as f:
            json.dump(gaps, f, indent=2)

        print(f"\nTemplate saved to {filename}")
        print("Fill in the template, then use option 3 to validate.")

    elif choice == "2":
        # Validate single gap
        filename = input("Enter gap JSON filename: ").strip()
        try:
            with open(filename, 'r') as f:
                gap = json.load(f)

            validation = validate_gap(gap)

            print(f"\nValidation Results for: {gap.get('title', 'Untitled')}")
            print(f"Status: {"✓ VALID" if validation['valid'] else "⚠ INVALID"}")
            print(f"Evidence count: {validation['evidence_count']}")
            print(f"Definition length: {validation['definition_length']} words")
            print(f"'Why matters' length: {validation['why_matters_length']} words")

            if validation['issues']:
                print("\n⚠ Issues:")
                for issue in validation['issues']:
                    print(f"  - {issue}")

            if validation['warnings']:
                print("\nℹ️ Warnings:")
                for warning in validation['warnings']:
                    print(f"  - {warning}")

        except FileNotFoundError:
            print(f"Error: File '{filename}' not found")
        except json.JSONDecodeError:
            print(f"Error: '{filename}' is not valid JSON")

    elif choice == "3":
        # Generate portfolio report
        filename = input("Enter gaps JSON filename: ").strip()
        try:
            with open(filename, 'r') as f:
                gaps = json.load(f)

            print(f"\nAnalyzing {len(gaps)} gaps...")
            report = generate_gap_report(gaps)
            print("\n" + report)

            report_filename = filename.replace('.json', '_gap_report.md')
            with open(report_filename, 'w') as f:
                f.write(report)
            print(f"\nReport saved to {report_filename}")

        except FileNotFoundError:
            print(f"Error: File '{filename}' not found")
        except json.JSONDecodeError:
            print(f"Error: '{filename}' is not valid JSON")

    elif choice == "4":
        # Generate evidence package
        filename = input("Enter single gap JSON filename: ").strip()
        try:
            with open(filename, 'r') as f:
                gap = json.load(f)

            package = generate_gap_evidence_package(gap)
            print("\n" + package)

            package_filename = f"evidence_package_{gap.get('gap_id', 'gap')}.md"
            with open(package_filename, 'w') as f:
                f.write(package)
            print(f"\nEvidence package saved to {package_filename}")

        except FileNotFoundError:
            print(f"Error: File '{filename}' not found")
        except json.JSONDecodeError:
            print(f"Error: '{filename}' is not valid JSON")

    else:
        print("Invalid option")

if __name__ == "__main__":
    main()
