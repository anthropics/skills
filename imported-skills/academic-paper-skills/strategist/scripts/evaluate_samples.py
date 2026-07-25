#!/usr/bin/env python3
"""
Sample Paper Evaluation Script

This script helps evaluate collected sample papers against quality standards.
It provides structured prompts and scoring templates for manual evaluation.
"""

import json
from datetime import datetime
from typing import List, Dict

def create_evaluation_template() -> Dict:
    """Create an empty evaluation template for a sample paper."""
    return {
        "title": "",
        "authors": "",
        "publication_date": "",
        "doi_or_url": "",
        "relevance_score": 0,  # 0-10
        "selection_reason": "",
        "time_category": "",  # recent/current/classic
        "quality_indicators": {
            "has_doi": False,
            "complete_abstract": False,
            "proper_citations": False,
            "platform_match": False
        },
        "extracted_features": {
            "abstract_structure": "",
            "chapter_organization": "",
            "citation_style": "",
            "language_style": "",  # first-person/passive
            "average_section_length": ""
        }
    }

def evaluate_time_distribution(papers: List[Dict]) -> Dict:
    """
    Evaluate whether time distribution meets quality standards.

    Standards:
    - Recent (last 6 months): 3 papers
    - Current (1-2 years): 3 papers
    - Classic (highly cited): 2 papers
    """
    from datetime import datetime, timedelta
    from dateutil.parser import parse

    now = datetime.now()
    six_months_ago = now - timedelta(days=180)
    two_years_ago = now - timedelta(days=730)

    recent = []
    current = []
    classic = []

    for paper in papers:
        try:
            pub_date = parse(paper.get("publication_date", ""))
            if pub_date >= six_months_ago:
                recent.append(paper)
            elif pub_date >= two_years_ago:
                current.append(paper)
            else:
                classic.append(paper)
        except:
            continue

    return {
        "recent_count": len(recent),
        "current_count": len(current),
        "classic_count": len(classic),
        "meets_standard": len(recent) >= 3 and len(current) >= 3 and len(classic) >= 2,
        "recommendation": _get_time_distribution_recommendation(
            len(recent), len(current), len(classic)
        )
    }

def _get_time_distribution_recommendation(recent: int, current: int, classic: int) -> str:
    """Generate recommendation based on time distribution."""
    issues = []
    if recent < 3:
        issues.append(f"Need {3-recent} more recent papers (last 6 months)")
    if current < 3:
        issues.append(f"Need {3-current} more current papers (1-2 years)")
    if classic < 2:
        issues.append(f"Need {2-classic} more classic papers (highly cited)")

    if not issues:
        return "✓ Time distribution meets standards"
    return "⚠ " + "; ".join(issues)

def calculate_average_relevance(papers: List[Dict]) -> Dict:
    """Calculate average relevance score and check if meets standard (≥8.0)."""
    scores = [p.get("relevance_score", 0) for p in papers if p.get("relevance_score", 0) > 0]

    if not scores:
        return {
            "average": 0,
            "count": 0,
            "meets_standard": False,
            "recommendation": "⚠ No relevance scores provided"
        }

    avg = sum(scores) / len(scores)
    meets = avg >= 8.0

    return {
        "average": round(avg, 2),
        "count": len(scores),
        "meets_standard": meets,
        "recommendation": (
            "✓ Average relevance meets standard"
            if meets
            else f"⚠ Average relevance ({avg:.2f}) below 8.0 threshold"
        )
    }

def check_diversity(papers: List[Dict]) -> Dict:
    """Check author and perspective diversity."""
    authors = set()
    for paper in papers:
        paper_authors = paper.get("authors", "").split(";")
        authors.update([a.strip() for a in paper_authors if a.strip()])

    unique_author_count = len(authors)

    # Note: Perspective diversity requires manual assessment
    return {
        "unique_authors": unique_author_count,
        "meets_author_diversity": unique_author_count >= 5,
        "recommendation": (
            "✓ Author diversity meets standard (≥5 different authors)"
            if unique_author_count >= 5
            else f"⚠ Need {5 - unique_author_count} more unique authors"
        ),
        "note": "Perspective diversity (≥3 different schools/approaches) requires manual verification"
    }

def generate_evaluation_report(papers: List[Dict]) -> str:
    """Generate comprehensive evaluation report."""
    time_dist = evaluate_time_distribution(papers)
    relevance = calculate_average_relevance(papers)
    diversity = check_diversity(papers)

    report = f"""
# Sample Paper Evaluation Report

Generated: {datetime.now().strftime('%Y-%m-%d %H:%M')}

## Executive Summary

- **Papers analyzed**: {len(papers)}
- **Average relevance**: {relevance['average']}/10
- **Time distribution**: {"✓ Balanced" if time_dist['meets_standard'] else "⚠ Needs adjustment"}
- **Author diversity**: {"✓ Sufficient" if diversity['meets_author_diversity'] else "⚠ Insufficient"}
- **Overall quality**: {"✓ PASS" if all([time_dist['meets_standard'], relevance['meets_standard'], diversity['meets_author_diversity']]) else "⚠ NEEDS IMPROVEMENT"}

## Time Distribution

{time_dist['recommendation']}

- Recent (last 6 months): {time_dist['recent_count']}/3 required
- Current (1-2 years): {time_dist['current_count']}/3 required
- Classic (highly cited): {time_dist['classic_count']}/2 required

## Relevance Analysis

{relevance['recommendation']}

- Average score: {relevance['average']}/10
- Papers scored: {relevance['count']}
- Threshold: 8.0/10

## Diversity Check

{diversity['recommendation']}

- Unique authors: {diversity['unique_authors']}
- Minimum required: 5

{diversity['note']}

## Detailed Paper List

"""

    # Add table of papers
    report += "| # | Title | Authors | Date | Relevance | Category |\n"
    report += "|---|-------|---------|------|-----------|----------|\n"

    for i, paper in enumerate(papers, 1):
        title = paper.get("title", "")[:50] + "..." if len(paper.get("title", "")) > 50 else paper.get("title", "")
        authors = paper.get("authors", "")[:30] + "..." if len(paper.get("authors", "")) > 30 else paper.get("authors", "")
        date = paper.get("publication_date", "")
        relevance_score = paper.get("relevance_score", "N/A")
        category = paper.get("time_category", "")

        report += f"| {i} | {title} | {authors} | {date} | {relevance_score}/10 | {category} |\n"

    report += "\n## Quality Indicators Summary\n\n"

    has_doi_count = sum(1 for p in papers if p.get("quality_indicators", {}).get("has_doi", False))
    complete_abstract_count = sum(1 for p in papers if p.get("quality_indicators", {}).get("complete_abstract", False))

    report += f"- Papers with DOI: {has_doi_count}/{len(papers)}\n"
    report += f"- Papers with complete abstract: {complete_abstract_count}/{len(papers)}\n"

    report += "\n## Recommendations\n\n"

    if time_dist['meets_standard'] and relevance['meets_standard'] and diversity['meets_author_diversity']:
        report += "✓ **PROCEED**: Sample quality meets all standards. Extract writing guidelines and proceed to Phase 2.\n"
    else:
        report += "⚠ **RE-SEARCH**: Address the following issues before proceeding:\n\n"
        if not time_dist['meets_standard']:
            report += f"- {time_dist['recommendation']}\n"
        if not relevance['meets_standard']:
            report += f"- {relevance['recommendation']}\n"
        if not diversity['meets_author_diversity']:
            report += f"- {diversity['recommendation']}\n"

    return report

def main():
    """Interactive evaluation interface."""
    print("=" * 60)
    print("Sample Paper Evaluation Tool")
    print("=" * 60)
    print()
    print("This tool helps evaluate sample papers against quality standards.")
    print()

    # Option 1: Load from JSON
    print("Options:")
    print("1. Load papers from JSON file")
    print("2. Create evaluation template")
    print("3. Generate report from JSON")
    print()

    choice = input("Select option (1-3): ").strip()

    if choice == "1":
        # Load and evaluate
        filename = input("Enter JSON filename: ").strip()
        try:
            with open(filename, 'r') as f:
                papers = json.load(f)
            print(f"\nLoaded {len(papers)} papers from {filename}")
            print("\nGenerating evaluation report...\n")
            report = generate_evaluation_report(papers)
            print(report)

            # Save report
            save = input("\nSave report to file? (y/n): ").strip().lower()
            if save == 'y':
                report_filename = filename.replace('.json', '_evaluation_report.md')
                with open(report_filename, 'w') as f:
                    f.write(report)
                print(f"Report saved to {report_filename}")
        except FileNotFoundError:
            print(f"Error: File '{filename}' not found")
        except json.JSONDecodeError:
            print(f"Error: '{filename}' is not valid JSON")

    elif choice == "2":
        # Create template
        num_papers = int(input("Number of papers to evaluate: ").strip())
        papers = [create_evaluation_template() for _ in range(num_papers)]

        filename = input("Save template to (filename.json): ").strip()
        with open(filename, 'w') as f:
            json.dump(papers, f, indent=2)

        print(f"\nTemplate saved to {filename}")
        print("Fill in the template with paper details, then use option 3 to generate report.")

    elif choice == "3":
        # Generate report only
        filename = input("Enter JSON filename: ").strip()
        try:
            with open(filename, 'r') as f:
                papers = json.load(f)
            report = generate_evaluation_report(papers)
            print("\n" + report)

            report_filename = filename.replace('.json', '_evaluation_report.md')
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
