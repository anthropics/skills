#!/usr/bin/env python3
"""
Content Audit Analyzer

Analyzes Confluence page inventory for content health. Identifies stale pages,
low-engagement content, orphaned pages, oversized documents, and produces a
health score with actionable recommendations.

Usage:
    python content_audit_analyzer.py pages.json
    python content_audit_analyzer.py pages.json --format json
"""

import argparse
import json
import sys
from datetime import datetime, timedelta
from typing import Any, Dict, List, Optional, Tuple


# ---------------------------------------------------------------------------
# Audit Configuration
# ---------------------------------------------------------------------------

STALE_THRESHOLD_DAYS = 90
OUTDATED_THRESHOLD_DAYS = 180
LOW_VIEW_THRESHOLD = 5
OVERSIZED_WORD_THRESHOLD = 5000
IDEAL_WORD_RANGE = (200, 3000)

HEALTH_WEIGHTS = {
    "freshness": 0.30,
    "engagement": 0.25,
    "organization": 0.20,
    "size_balance": 0.15,
    "completeness": 0.10,
}


# ---------------------------------------------------------------------------
# Audit Checks
# ---------------------------------------------------------------------------

def check_stale_pages(
    pages: List[Dict[str, Any]],
    reference_date: datetime,
) -> Dict[str, Any]:
    """Identify pages not updated within the stale threshold."""
    stale = []
    outdated = []

    for page in pages:
        last_modified = _parse_date(page.get("last_modified", ""))
        if not last_modified:
            continue

        days_since_update = (reference_date - last_modified).days

        if days_since_update > OUTDATED_THRESHOLD_DAYS:
            outdated.append({
                "title": page.get("title", "Untitled"),
                "days_since_update": days_since_update,
                "last_modified": page.get("last_modified", ""),
                "author": page.get("author", "unknown"),
            })
        elif days_since_update > STALE_THRESHOLD_DAYS:
            stale.append({
                "title": page.get("title", "Untitled"),
                "days_since_update": days_since_update,
                "last_modified": page.get("last_modified", ""),
                "author": page.get("author", "unknown"),
            })

    total = len(pages)
    stale_count = len(stale) + len(outdated)
    fresh_ratio = 1 - (stale_count / total) if total > 0 else 1
    score = max(0, fresh_ratio * 100)

    return {
        "score": score,
        "stale_pages": stale,
        "outdated_pages": outdated,
        "stale_count": len(stale),
        "outdated_count": len(outdated),
        "fresh_count": total - stale_count,
    }


def check_engagement(pages: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Identify low-engagement pages based on view counts."""
    low_engagement = []
    view_counts = []

    for page in pages:
        views = page.get("view_count", 0)
        view_counts.append(views)

        if views < LOW_VIEW_THRESHOLD:
            low_engagement.append({
                "title": page.get("title", "Untitled"),
                "view_count": views,
                "author": page.get("author", "unknown"),
            })

    total = len(pages)
    avg_views = sum(view_counts) / total if total > 0 else 0
    engaged_ratio = 1 - (len(low_engagement) / total) if total > 0 else 1
    score = max(0, engaged_ratio * 100)

    return {
        "score": score,
        "low_engagement_pages": low_engagement,
        "low_engagement_count": len(low_engagement),
        "average_views": round(avg_views, 1),
        "max_views": max(view_counts) if view_counts else 0,
        "min_views": min(view_counts) if view_counts else 0,
    }


def check_organization(pages: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Identify orphaned pages with no labels."""
    orphaned = []

    for page in pages:
        labels = page.get("labels", [])
        if not labels:
            orphaned.append({
                "title": page.get("title", "Untitled"),
                "author": page.get("author", "unknown"),
            })

    total = len(pages)
    labeled_ratio = 1 - (len(orphaned) / total) if total > 0 else 1
    score = max(0, labeled_ratio * 100)

    # Collect label distribution
    label_counts = {}
    for page in pages:
        for label in page.get("labels", []):
            label_counts[label] = label_counts.get(label, 0) + 1

    return {
        "score": score,
        "orphaned_pages": orphaned,
        "orphaned_count": len(orphaned),
        "labeled_count": total - len(orphaned),
        "label_distribution": dict(sorted(label_counts.items(), key=lambda x: -x[1])[:20]),
    }


def check_size_balance(pages: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Check for oversized or undersized pages."""
    oversized = []
    undersized = []
    word_counts = []

    for page in pages:
        word_count = page.get("word_count", 0)
        word_counts.append(word_count)

        if word_count > OVERSIZED_WORD_THRESHOLD:
            oversized.append({
                "title": page.get("title", "Untitled"),
                "word_count": word_count,
                "recommendation": "Split into multiple focused pages",
            })
        elif word_count < 50 and word_count > 0:
            undersized.append({
                "title": page.get("title", "Untitled"),
                "word_count": word_count,
                "recommendation": "Expand content or merge with related page",
            })

    total = len(pages)
    well_sized = total - len(oversized) - len(undersized)
    balance_ratio = well_sized / total if total > 0 else 1
    score = max(0, balance_ratio * 100)
    avg_words = sum(word_counts) / total if total > 0 else 0

    return {
        "score": score,
        "oversized_pages": oversized,
        "undersized_pages": undersized,
        "oversized_count": len(oversized),
        "undersized_count": len(undersized),
        "average_word_count": round(avg_words),
    }


def check_completeness(pages: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Check pages for required metadata completeness."""
    incomplete = []
    required_fields = ["title", "last_modified", "author"]

    for page in pages:
        missing = [f for f in required_fields if not page.get(f)]
        if missing:
            incomplete.append({
                "title": page.get("title", "Untitled"),
                "missing_fields": missing,
            })

    total = len(pages)
    complete_ratio = 1 - (len(incomplete) / total) if total > 0 else 1
    score = max(0, complete_ratio * 100)

    return {
        "score": score,
        "incomplete_pages": incomplete,
        "incomplete_count": len(incomplete),
        "complete_count": total - len(incomplete),
    }


# ---------------------------------------------------------------------------
# Main Analysis
# ---------------------------------------------------------------------------

def analyze_content_health(data: Dict[str, Any]) -> Dict[str, Any]:
    """Run full content audit analysis."""
    pages = data.get("pages", [])

    if not pages:
        return {
            "health_score": 0,
            "grade": "invalid",
            "error": "No pages found in input data",
            "dimensions": {},
            "action_items": [],
        }

    reference_date = datetime.now()

    # Run all checks
    dimensions = {
        "freshness": check_stale_pages(pages, reference_date),
        "engagement": check_engagement(pages),
        "organization": check_organization(pages),
        "size_balance": check_size_balance(pages),
        "completeness": check_completeness(pages),
    }

    # Calculate weighted health score
    weighted_scores = []
    for dim_name, dim_result in dimensions.items():
        weight = HEALTH_WEIGHTS.get(dim_name, 0.1)
        weighted_scores.append(dim_result["score"] * weight)

    health_score = sum(weighted_scores)

    if health_score >= 85:
        grade = "excellent"
    elif health_score >= 70:
        grade = "good"
    elif health_score >= 55:
        grade = "fair"
    else:
        grade = "poor"

    # Generate action items
    action_items = _generate_action_items(dimensions)

    return {
        "health_score": round(health_score, 1),
        "grade": grade,
        "total_pages": len(pages),
        "dimensions": dimensions,
        "action_items": action_items,
    }


def _generate_action_items(dimensions: Dict[str, Any]) -> List[Dict[str, str]]:
    """Generate prioritized action items from audit findings."""
    items = []

    # Freshness actions
    freshness = dimensions.get("freshness", {})
    if freshness.get("outdated_count", 0) > 0:
        items.append({
            "priority": "high",
            "action": f"Review and update or archive {freshness['outdated_count']} outdated pages (>180 days old)",
            "category": "freshness",
        })
    if freshness.get("stale_count", 0) > 0:
        items.append({
            "priority": "medium",
            "action": f"Review {freshness['stale_count']} stale pages (90-180 days old) for relevance",
            "category": "freshness",
        })

    # Engagement actions
    engagement = dimensions.get("engagement", {})
    if engagement.get("low_engagement_count", 0) > 0:
        items.append({
            "priority": "medium",
            "action": f"Investigate {engagement['low_engagement_count']} low-engagement pages - consider improving discoverability or archiving",
            "category": "engagement",
        })

    # Organization actions
    organization = dimensions.get("organization", {})
    if organization.get("orphaned_count", 0) > 0:
        items.append({
            "priority": "medium",
            "action": f"Add labels to {organization['orphaned_count']} orphaned pages for better categorization",
            "category": "organization",
        })

    # Size actions
    size = dimensions.get("size_balance", {})
    if size.get("oversized_count", 0) > 0:
        items.append({
            "priority": "low",
            "action": f"Split {size['oversized_count']} oversized pages (>5000 words) into focused sub-pages",
            "category": "size",
        })

    # Completeness actions
    completeness = dimensions.get("completeness", {})
    if completeness.get("incomplete_count", 0) > 0:
        items.append({
            "priority": "low",
            "action": f"Fill in missing metadata for {completeness['incomplete_count']} incomplete pages",
            "category": "completeness",
        })

    return items


def _parse_date(date_str: str) -> Optional[datetime]:
    """Parse date string in common formats."""
    formats = [
        "%Y-%m-%d",
        "%Y-%m-%dT%H:%M:%S",
        "%Y-%m-%dT%H:%M:%SZ",
        "%Y-%m-%dT%H:%M:%S.%f",
        "%Y-%m-%dT%H:%M:%S.%fZ",
        "%d/%m/%Y",
        "%m/%d/%Y",
    ]
    for fmt in formats:
        try:
            return datetime.strptime(date_str, fmt)
        except ValueError:
            continue
    return None


# ---------------------------------------------------------------------------
# Output Formatting
# ---------------------------------------------------------------------------

def format_text_output(result: Dict[str, Any]) -> str:
    """Format results as readable text report."""
    lines = []
    lines.append("=" * 60)
    lines.append("CONTENT AUDIT REPORT")
    lines.append("=" * 60)
    lines.append("")

    if "error" in result:
        lines.append(f"ERROR: {result['error']}")
        return "\n".join(lines)

    lines.append("HEALTH SUMMARY")
    lines.append("-" * 30)
    lines.append(f"Health Score: {result['health_score']}/100")
    lines.append(f"Grade: {result['grade'].title()}")
    lines.append(f"Total Pages Analyzed: {result['total_pages']}")
    lines.append("")

    # Dimension scores
    lines.append("DIMENSION SCORES")
    lines.append("-" * 30)
    for dim_name, dim_data in result.get("dimensions", {}).items():
        weight = HEALTH_WEIGHTS.get(dim_name, 0)
        lines.append(f"{dim_name.replace('_', ' ').title()} (Weight: {weight:.0%})")
        lines.append(f"  Score: {dim_data['score']:.1f}/100")

        if dim_name == "freshness":
            lines.append(f"  Stale: {dim_data.get('stale_count', 0)}, Outdated: {dim_data.get('outdated_count', 0)}, Fresh: {dim_data.get('fresh_count', 0)}")
        elif dim_name == "engagement":
            lines.append(f"  Low Engagement: {dim_data.get('low_engagement_count', 0)}, Avg Views: {dim_data.get('average_views', 0)}")
        elif dim_name == "organization":
            lines.append(f"  Orphaned (no labels): {dim_data.get('orphaned_count', 0)}, Labeled: {dim_data.get('labeled_count', 0)}")
        elif dim_name == "size_balance":
            lines.append(f"  Oversized: {dim_data.get('oversized_count', 0)}, Undersized: {dim_data.get('undersized_count', 0)}, Avg Words: {dim_data.get('average_word_count', 0)}")
        elif dim_name == "completeness":
            lines.append(f"  Incomplete: {dim_data.get('incomplete_count', 0)}, Complete: {dim_data.get('complete_count', 0)}")
        lines.append("")

    # Action items
    action_items = result.get("action_items", [])
    if action_items:
        lines.append("ACTION ITEMS")
        lines.append("-" * 30)
        for i, item in enumerate(action_items, 1):
            priority = item["priority"].upper()
            lines.append(f"{i}. [{priority}] {item['action']}")
        lines.append("")

    return "\n".join(lines)


def format_json_output(result: Dict[str, Any]) -> Dict[str, Any]:
    """Format results as JSON."""
    return result


# ---------------------------------------------------------------------------
# CLI Interface
# ---------------------------------------------------------------------------

def main() -> int:
    """Main CLI entry point."""
    parser = argparse.ArgumentParser(
        description="Analyze Confluence page inventory for content health"
    )
    parser.add_argument(
        "pages_file",
        help="JSON file with page list (title, last_modified, view_count, author, labels, word_count)",
    )
    parser.add_argument(
        "--format",
        choices=["text", "json"],
        default="text",
        help="Output format (default: text)",
    )

    args = parser.parse_args()

    try:
        with open(args.pages_file, "r") as f:
            data = json.load(f)

        result = analyze_content_health(data)

        if args.format == "json":
            print(json.dumps(format_json_output(result), indent=2))
        else:
            print(format_text_output(result))

        return 0

    except FileNotFoundError:
        print(f"Error: File '{args.pages_file}' not found", file=sys.stderr)
        return 1
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON in '{args.pages_file}': {e}", file=sys.stderr)
        return 1
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
