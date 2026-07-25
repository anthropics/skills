#!/usr/bin/env python3
"""
Space Structure Generator

Generates recommended Confluence space hierarchy from team or project
descriptions. Produces page tree structures, labels, and permission
suggestions based on team type and size.

Usage:
    python space_structure_generator.py team_info.json
    python space_structure_generator.py team_info.json --format json
"""

import argparse
import json
import sys
from typing import Any, Dict, List, Optional


# ---------------------------------------------------------------------------
# Space Templates
# ---------------------------------------------------------------------------

BASE_SECTIONS = [
    {
        "title": "Home",
        "description": "Space landing page with quick links and team overview",
        "labels": ["home", "landing"],
        "children": [],
    },
    {
        "title": "Getting Started",
        "description": "Onboarding guide for new team members",
        "labels": ["onboarding", "getting-started"],
        "children": [
            {"title": "Team Charter", "labels": ["charter"]},
            {"title": "Tools & Access", "labels": ["tools", "access"]},
            {"title": "Communication Guidelines", "labels": ["communication"]},
            {"title": "Key Contacts", "labels": ["contacts"]},
        ],
    },
    {
        "title": "Meeting Notes",
        "description": "Recurring and ad-hoc meeting documentation",
        "labels": ["meetings"],
        "children": [
            {"title": "Weekly Standups", "labels": ["standup", "recurring"]},
            {"title": "Team Syncs", "labels": ["sync", "recurring"]},
            {"title": "Ad-hoc Meetings", "labels": ["ad-hoc"]},
        ],
    },
    {
        "title": "Templates",
        "description": "Reusable page templates for the team",
        "labels": ["templates"],
        "children": [],
    },
    {
        "title": "Archive",
        "description": "Archived and deprecated content",
        "labels": ["archive"],
        "children": [],
    },
]

TEAM_TYPE_SECTIONS = {
    "engineering": [
        {
            "title": "Architecture",
            "description": "System architecture, design decisions, and technical standards",
            "labels": ["architecture", "technical"],
            "children": [
                {"title": "Architecture Decision Records", "labels": ["adr", "decisions"]},
                {"title": "System Design Documents", "labels": ["design", "system"]},
                {"title": "API Documentation", "labels": ["api", "reference"]},
                {"title": "Tech Stack", "labels": ["tech-stack"]},
            ],
        },
        {
            "title": "Development",
            "description": "Development workflows, coding standards, and CI/CD",
            "labels": ["development"],
            "children": [
                {"title": "Coding Standards", "labels": ["standards", "code"]},
                {"title": "Git Workflow", "labels": ["git", "workflow"]},
                {"title": "CI/CD Pipeline", "labels": ["ci-cd", "devops"]},
                {"title": "Environment Setup", "labels": ["environment", "setup"]},
            ],
        },
        {
            "title": "Runbooks",
            "description": "Operational runbooks and incident response",
            "labels": ["runbooks", "operations"],
            "children": [
                {"title": "Incident Response", "labels": ["incident", "response"]},
                {"title": "Deployment Procedures", "labels": ["deployment"]},
                {"title": "Troubleshooting Guides", "labels": ["troubleshooting"]},
            ],
        },
    ],
    "product": [
        {
            "title": "Strategy",
            "description": "Product vision, roadmap, and strategic planning",
            "labels": ["strategy", "product"],
            "children": [
                {"title": "Product Vision", "labels": ["vision"]},
                {"title": "Roadmap", "labels": ["roadmap"]},
                {"title": "OKRs & Goals", "labels": ["okr", "goals"]},
                {"title": "Competitive Analysis", "labels": ["competitive", "analysis"]},
            ],
        },
        {
            "title": "Research",
            "description": "User research, personas, and market analysis",
            "labels": ["research"],
            "children": [
                {"title": "User Personas", "labels": ["personas"]},
                {"title": "User Interview Notes", "labels": ["interviews", "research"]},
                {"title": "Survey Results", "labels": ["surveys"]},
                {"title": "Usability Testing", "labels": ["usability", "testing"]},
            ],
        },
        {
            "title": "Requirements",
            "description": "Product requirements and feature specifications",
            "labels": ["requirements", "specs"],
            "children": [
                {"title": "Feature Specifications", "labels": ["features", "specs"]},
                {"title": "User Stories", "labels": ["user-stories"]},
                {"title": "Acceptance Criteria", "labels": ["acceptance-criteria"]},
            ],
        },
    ],
    "marketing": [
        {
            "title": "Strategy",
            "description": "Marketing strategy, brand guidelines, and campaign plans",
            "labels": ["strategy", "marketing"],
            "children": [
                {"title": "Brand Guidelines", "labels": ["brand", "guidelines"]},
                {"title": "Marketing Plan", "labels": ["plan"]},
                {"title": "Target Audiences", "labels": ["audience", "targeting"]},
                {"title": "Channel Strategy", "labels": ["channels"]},
            ],
        },
        {
            "title": "Campaigns",
            "description": "Active and past campaign documentation",
            "labels": ["campaigns"],
            "children": [
                {"title": "Active Campaigns", "labels": ["active"]},
                {"title": "Campaign Results", "labels": ["results", "analytics"]},
                {"title": "Campaign Templates", "labels": ["templates"]},
            ],
        },
        {
            "title": "Content",
            "description": "Content calendar, assets, and style guides",
            "labels": ["content"],
            "children": [
                {"title": "Content Calendar", "labels": ["calendar"]},
                {"title": "Content Assets", "labels": ["assets"]},
                {"title": "Style Guide", "labels": ["style-guide"]},
            ],
        },
    ],
    "project": [
        {
            "title": "Project Overview",
            "description": "Project charter, scope, and stakeholders",
            "labels": ["project", "overview"],
            "children": [
                {"title": "Project Charter", "labels": ["charter"]},
                {"title": "Scope & Deliverables", "labels": ["scope", "deliverables"]},
                {"title": "Stakeholder Map", "labels": ["stakeholders"]},
                {"title": "Timeline & Milestones", "labels": ["timeline", "milestones"]},
            ],
        },
        {
            "title": "Status & Reporting",
            "description": "Project status updates and reports",
            "labels": ["status", "reporting"],
            "children": [
                {"title": "Weekly Status Reports", "labels": ["status", "weekly"]},
                {"title": "Risk Register", "labels": ["risks"]},
                {"title": "Decision Log", "labels": ["decisions"]},
            ],
        },
        {
            "title": "Resources",
            "description": "Project resources, documentation, and references",
            "labels": ["resources"],
            "children": [
                {"title": "Technical Documentation", "labels": ["technical", "docs"]},
                {"title": "Vendor Information", "labels": ["vendor"]},
                {"title": "Budget & Financials", "labels": ["budget"]},
            ],
        },
    ],
}

# Permission suggestions by team type
PERMISSION_TEMPLATES = {
    "engineering": {
        "admins": ["team-leads", "engineering-managers"],
        "contributors": ["developers", "qa-engineers"],
        "viewers": ["product-team", "stakeholders"],
        "restrictions": [
            "Restrict 'Runbooks' section to engineering team only",
            "Allow product team view-only access to Architecture",
        ],
    },
    "product": {
        "admins": ["product-managers", "product-leads"],
        "contributors": ["product-designers", "product-analysts"],
        "viewers": ["engineering-team", "marketing-team", "stakeholders"],
        "restrictions": [
            "Restrict 'Research' raw data to product team only",
            "Share 'Strategy' with leadership and stakeholders",
        ],
    },
    "marketing": {
        "admins": ["marketing-managers", "marketing-leads"],
        "contributors": ["content-creators", "designers"],
        "viewers": ["sales-team", "product-team"],
        "restrictions": [
            "Restrict campaign budgets to marketing leadership",
            "Share brand guidelines broadly",
        ],
    },
    "project": {
        "admins": ["project-managers"],
        "contributors": ["project-team-members"],
        "viewers": ["stakeholders", "sponsors"],
        "restrictions": [
            "Restrict 'Budget & Financials' to project managers and sponsors",
            "Share status reports with all stakeholders",
        ],
    },
}


# ---------------------------------------------------------------------------
# Structure Generator
# ---------------------------------------------------------------------------

def generate_space_structure(team_info: Dict[str, Any]) -> Dict[str, Any]:
    """Generate Confluence space structure from team information."""
    team_name = team_info.get("name", "Team")
    team_type = team_info.get("type", "project").lower()
    team_size = team_info.get("size", 5)
    projects = team_info.get("projects", [])

    if team_type not in TEAM_TYPE_SECTIONS:
        team_type = "project"

    # Build page tree
    page_tree = []

    # Add base sections
    for section in BASE_SECTIONS:
        page_tree.append(_deep_copy_section(section))

    # Add team-type-specific sections
    type_sections = TEAM_TYPE_SECTIONS.get(team_type, [])
    for section in type_sections:
        page_tree.append(_deep_copy_section(section))

    # Add project-specific pages if projects are listed
    if projects:
        project_section = {
            "title": "Projects",
            "description": "Individual project documentation",
            "labels": ["projects"],
            "children": [],
        }
        for project in projects:
            project_name = project if isinstance(project, str) else project.get("name", "Project")
            project_section["children"].append({
                "title": project_name,
                "labels": ["project", _slugify(project_name)],
                "children": [
                    {"title": f"{project_name} - Overview", "labels": ["overview"]},
                    {"title": f"{project_name} - Requirements", "labels": ["requirements"]},
                    {"title": f"{project_name} - Status", "labels": ["status"]},
                ],
            })
        page_tree.append(project_section)

    # Get permissions
    permissions = PERMISSION_TEMPLATES.get(team_type, PERMISSION_TEMPLATES["project"])

    # Generate label taxonomy
    all_labels = set()
    _collect_labels(page_tree, all_labels)

    # Build recommendations
    recommendations = _generate_recommendations(team_name, team_type, team_size, projects)

    return {
        "space_key": _generate_space_key(team_name),
        "space_name": f"{team_name} Space",
        "team_type": team_type,
        "team_size": team_size,
        "page_tree": page_tree,
        "total_pages": _count_pages(page_tree),
        "labels": sorted(all_labels),
        "permissions": permissions,
        "recommendations": recommendations,
    }


def _deep_copy_section(section: Dict[str, Any]) -> Dict[str, Any]:
    """Create a deep copy of a section dict."""
    copy = {
        "title": section["title"],
        "labels": list(section.get("labels", [])),
    }
    if "description" in section:
        copy["description"] = section["description"]
    if "children" in section:
        copy["children"] = [_deep_copy_section(child) for child in section["children"]]
    return copy


def _slugify(text: str) -> str:
    """Convert text to a URL-safe slug."""
    return text.lower().replace(" ", "-").replace("_", "-")


def _generate_space_key(team_name: str) -> str:
    """Generate a space key from team name."""
    words = team_name.upper().split()
    if len(words) == 1:
        return words[0][:10]
    return "".join(w[0] for w in words[:5])


def _collect_labels(pages: List[Dict], labels: set) -> None:
    """Recursively collect all labels from page tree."""
    for page in pages:
        for label in page.get("labels", []):
            labels.add(label)
        children = page.get("children", [])
        if children:
            _collect_labels(children, labels)


def _count_pages(pages: List[Dict]) -> int:
    """Count total pages in tree."""
    count = len(pages)
    for page in pages:
        children = page.get("children", [])
        if children:
            count += _count_pages(children)
    return count


def _generate_recommendations(
    team_name: str,
    team_type: str,
    team_size: int,
    projects: List,
) -> List[str]:
    """Generate setup recommendations."""
    recs = []

    recs.append(f"Create the space with key '{_generate_space_key(team_name)}' and enable the blog feature for announcements.")

    if team_size > 10:
        recs.append("Large team detected. Consider sub-spaces or restricted sections for sub-teams.")

    if team_size <= 3:
        recs.append("Small team. Simplify the structure by merging low-traffic sections.")

    if len(projects) > 5:
        recs.append("Many projects listed. Consider a separate space per project for better isolation.")

    if team_type == "engineering":
        recs.append("Set up page templates for ADRs, runbooks, and design docs.")
        recs.append("Enable the Jira macro on Architecture pages for traceability.")
    elif team_type == "product":
        recs.append("Set up page templates for feature specs and user research notes.")
        recs.append("Link roadmap pages to Jira epics for real-time status.")
    elif team_type == "marketing":
        recs.append("Enable the calendar macro on the Content Calendar page.")
        recs.append("Use labels consistently to enable filtered content views.")

    recs.append("Review and update space permissions quarterly.")
    recs.append("Archive pages older than 6 months that are no longer actively referenced.")

    return recs


# ---------------------------------------------------------------------------
# Output Formatting
# ---------------------------------------------------------------------------

def _format_page_tree(pages: List[Dict], indent: int = 0) -> List[str]:
    """Format page tree as indented text."""
    lines = []
    prefix = "  " * indent
    for page in pages:
        title = page["title"]
        labels = page.get("labels", [])
        label_str = f" [{', '.join(labels)}]" if labels else ""
        lines.append(f"{prefix}|- {title}{label_str}")
        if page.get("description"):
            lines.append(f"{prefix}   {page['description']}")
        children = page.get("children", [])
        if children:
            lines.extend(_format_page_tree(children, indent + 1))
    return lines


def format_text_output(result: Dict[str, Any]) -> str:
    """Format results as readable text report."""
    lines = []
    lines.append("=" * 60)
    lines.append("CONFLUENCE SPACE STRUCTURE")
    lines.append("=" * 60)
    lines.append("")

    lines.append("SPACE INFO")
    lines.append("-" * 30)
    lines.append(f"Space Name: {result['space_name']}")
    lines.append(f"Space Key: {result['space_key']}")
    lines.append(f"Team Type: {result['team_type'].title()}")
    lines.append(f"Team Size: {result['team_size']}")
    lines.append(f"Total Pages: {result['total_pages']}")
    lines.append("")

    lines.append("PAGE TREE")
    lines.append("-" * 30)
    lines.extend(_format_page_tree(result["page_tree"]))
    lines.append("")

    lines.append("LABELS")
    lines.append("-" * 30)
    lines.append(", ".join(result["labels"]))
    lines.append("")

    permissions = result.get("permissions", {})
    if permissions:
        lines.append("PERMISSION SUGGESTIONS")
        lines.append("-" * 30)
        lines.append(f"Admins: {', '.join(permissions.get('admins', []))}")
        lines.append(f"Contributors: {', '.join(permissions.get('contributors', []))}")
        lines.append(f"Viewers: {', '.join(permissions.get('viewers', []))}")
        for restriction in permissions.get("restrictions", []):
            lines.append(f"  - {restriction}")
        lines.append("")

    recommendations = result.get("recommendations", [])
    if recommendations:
        lines.append("RECOMMENDATIONS")
        lines.append("-" * 30)
        for i, rec in enumerate(recommendations, 1):
            lines.append(f"{i}. {rec}")

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
        description="Generate Confluence space hierarchy from team/project description"
    )
    parser.add_argument(
        "team_file",
        help="JSON file with team info (name, size, type, projects)",
    )
    parser.add_argument(
        "--format",
        choices=["text", "json"],
        default="text",
        help="Output format (default: text)",
    )

    args = parser.parse_args()

    try:
        with open(args.team_file, "r") as f:
            data = json.load(f)

        result = generate_space_structure(data)

        if args.format == "json":
            print(json.dumps(format_json_output(result), indent=2))
        else:
            print(format_text_output(result))

        return 0

    except FileNotFoundError:
        print(f"Error: File '{args.team_file}' not found", file=sys.stderr)
        return 1
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON in '{args.team_file}': {e}", file=sys.stderr)
        return 1
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
