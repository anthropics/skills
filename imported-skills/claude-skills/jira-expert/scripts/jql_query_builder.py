#!/usr/bin/env python3
"""
JQL Query Builder

Pattern-matching JQL builder from natural language descriptions. Maps common
phrases to JQL operators and constructs valid queries with syntax validation.

Usage:
    python jql_query_builder.py "high priority bugs in PROJECT assigned to me"
    python jql_query_builder.py "overdue tasks in PROJ" --format json
    python jql_query_builder.py --patterns
"""

import argparse
import json
import re
import sys
from datetime import datetime
from typing import Any, Dict, List, Optional, Tuple


# ---------------------------------------------------------------------------
# Pattern Library
# ---------------------------------------------------------------------------

PATTERN_LIBRARY = {
    "my_open_bugs": {
        "phrases": ["my open bugs", "my bugs", "bugs assigned to me"],
        "jql": 'assignee = currentUser() AND type = Bug AND status != Done',
        "description": "All open bugs assigned to current user",
    },
    "high_priority_bugs": {
        "phrases": ["high priority bugs", "critical bugs", "urgent bugs", "p1 bugs"],
        "jql": 'type = Bug AND priority in (Highest, High) AND status != Done',
        "description": "High and highest priority open bugs",
    },
    "my_open_tasks": {
        "phrases": ["my open tasks", "my tasks", "tasks assigned to me", "my work"],
        "jql": 'assignee = currentUser() AND status != Done',
        "description": "All open issues assigned to current user",
    },
    "unassigned_issues": {
        "phrases": ["unassigned", "unassigned issues", "no assignee"],
        "jql": 'assignee is EMPTY AND status != Done',
        "description": "Issues with no assignee",
    },
    "recently_created": {
        "phrases": ["recently created", "new issues", "created this week", "recent"],
        "jql": 'created >= -7d ORDER BY created DESC',
        "description": "Issues created in the last 7 days",
    },
    "recently_updated": {
        "phrases": ["recently updated", "updated this week", "recent changes"],
        "jql": 'updated >= -7d ORDER BY updated DESC',
        "description": "Issues updated in the last 7 days",
    },
    "overdue": {
        "phrases": ["overdue", "past due", "missed deadline", "overdue tasks"],
        "jql": 'duedate < now() AND status != Done',
        "description": "Issues past their due date",
    },
    "due_this_week": {
        "phrases": ["due this week", "due soon", "upcoming deadlines"],
        "jql": 'duedate >= startOfWeek() AND duedate <= endOfWeek() AND status != Done',
        "description": "Issues due this week",
    },
    "blocked_issues": {
        "phrases": ["blocked", "blocked issues", "impediments"],
        "jql": 'status = Blocked OR status = Impediment',
        "description": "Issues in blocked or impediment status",
    },
    "in_progress": {
        "phrases": ["in progress", "being worked on", "active work"],
        "jql": 'status = "In Progress"',
        "description": "Issues currently in progress",
    },
    "sprint_issues": {
        "phrases": ["current sprint", "this sprint", "active sprint"],
        "jql": 'sprint in openSprints()',
        "description": "Issues in the current active sprint",
    },
    "backlog": {
        "phrases": ["backlog", "backlog items", "not started"],
        "jql": 'sprint is EMPTY AND status = "To Do" ORDER BY priority DESC',
        "description": "Issues in the backlog not assigned to a sprint",
    },
    "stories_without_estimates": {
        "phrases": ["no estimates", "unestimated", "missing estimates", "no story points"],
        "jql": 'type = Story AND (storyPoints is EMPTY OR storyPoints = 0) AND status != Done',
        "description": "Stories missing story point estimates",
    },
    "epics_in_progress": {
        "phrases": ["active epics", "epics in progress", "open epics"],
        "jql": 'type = Epic AND status != Done ORDER BY priority DESC',
        "description": "Epics that are not yet completed",
    },
    "done_this_week": {
        "phrases": ["done this week", "completed this week", "resolved this week"],
        "jql": 'status changed to Done DURING (startOfWeek(), now())',
        "description": "Issues completed during the current week",
    },
    "created_vs_resolved": {
        "phrases": ["created vs resolved", "issue flow", "throughput"],
        "jql": 'created >= -30d ORDER BY created DESC',
        "description": "Issues created in the last 30 days for flow analysis",
    },
    "my_reported_issues": {
        "phrases": ["my reported", "reported by me", "i created", "i reported"],
        "jql": 'reporter = currentUser() ORDER BY created DESC',
        "description": "Issues reported by current user",
    },
    "stale_issues": {
        "phrases": ["stale", "stale issues", "not updated", "abandoned"],
        "jql": 'updated <= -30d AND status != Done ORDER BY updated ASC',
        "description": "Issues not updated in 30+ days",
    },
    "subtasks_without_parent": {
        "phrases": ["orphan subtasks", "subtasks no parent", "loose subtasks"],
        "jql": 'type = Sub-task AND parent is EMPTY',
        "description": "Subtasks missing parent issues",
    },
    "high_priority_unassigned": {
        "phrases": ["high priority unassigned", "urgent unassigned", "critical no owner"],
        "jql": 'priority in (Highest, High) AND assignee is EMPTY AND status != Done',
        "description": "High priority issues with no assignee",
    },
    "bugs_by_component": {
        "phrases": ["bugs by component", "component bugs"],
        "jql": 'type = Bug AND status != Done ORDER BY component ASC',
        "description": "Open bugs organized by component",
    },
    "resolved_recently": {
        "phrases": ["resolved recently", "recently resolved", "fixed this month"],
        "jql": 'resolved >= -30d ORDER BY resolved DESC',
        "description": "Issues resolved in the last 30 days",
    },
}

# Keyword-to-JQL fragment mapping for dynamic query building
KEYWORD_FRAGMENTS = {
    # Issue types
    "bug": ("type", "= Bug"),
    "bugs": ("type", "= Bug"),
    "story": ("type", "= Story"),
    "stories": ("type", "= Story"),
    "task": ("type", "= Task"),
    "tasks": ("type", "= Task"),
    "epic": ("type", "= Epic"),
    "epics": ("type", "= Epic"),
    "subtask": ("type", "= Sub-task"),
    "sub-task": ("type", "= Sub-task"),
    # Statuses
    "open": ("status", "!= Done"),
    "closed": ("status", "= Done"),
    "done": ("status", "= Done"),
    "resolved": ("status", "= Done"),
    "todo": ("status", '= "To Do"'),
    # Priorities
    "critical": ("priority", "= Highest"),
    "highest": ("priority", "= Highest"),
    "high": ("priority", "in (Highest, High)"),
    "medium": ("priority", "= Medium"),
    "low": ("priority", "in (Low, Lowest)"),
    "lowest": ("priority", "= Lowest"),
    # Assignee
    "me": ("assignee", "= currentUser()"),
    "mine": ("assignee", "= currentUser()"),
    "unassigned": ("assignee", "is EMPTY"),
    # Time
    "overdue": ("duedate", "< now()"),
    "today": ("duedate", "= now()"),
}

PROJECT_PATTERN = re.compile(r'\b([A-Z]{2,10})\b')
ASSIGNEE_PATTERN = re.compile(r'assigned\s+to\s+(\w+)', re.IGNORECASE)
LABEL_PATTERN = re.compile(r'label[s]?\s*[=:]\s*["\']?(\w+)["\']?', re.IGNORECASE)
COMPONENT_PATTERN = re.compile(r'component[s]?\s*[=:]\s*["\']?(\w+)["\']?', re.IGNORECASE)
DATE_RANGE_PATTERN = re.compile(r'last\s+(\d+)\s+(day|week|month)s?', re.IGNORECASE)
SPRINT_NAME_PATTERN = re.compile(r'sprint\s+["\']?(\w[\w\s]*\w)["\']?', re.IGNORECASE)

# Words to exclude from project matching
EXCLUDED_WORDS = {
    "AND", "OR", "NOT", "IN", "IS", "TO", "BY", "ON", "DO", "BE",
    "THE", "ALL", "MY", "NO", "OF", "AT", "AS", "IF", "IT",
    "BUG", "BUGS", "TASK", "TASKS", "STORY", "EPIC", "DONE",
    "HIGH", "LOW", "MEDIUM", "JQL",
}


# ---------------------------------------------------------------------------
# Query Builder
# ---------------------------------------------------------------------------

def find_matching_pattern(description: str) -> Optional[Dict[str, Any]]:
    """Check if description matches a known pattern exactly."""
    desc_lower = description.lower().strip()
    for pattern_name, pattern_data in PATTERN_LIBRARY.items():
        for phrase in pattern_data["phrases"]:
            if phrase in desc_lower or desc_lower in phrase:
                return {
                    "pattern_name": pattern_name,
                    "jql": pattern_data["jql"],
                    "description": pattern_data["description"],
                    "match_type": "exact_pattern",
                }
    return None


def build_jql_from_description(description: str) -> Dict[str, Any]:
    """Build JQL query from natural language description."""
    # First try exact pattern match
    pattern_match = find_matching_pattern(description)
    if pattern_match:
        # Augment with project if mentioned
        project = _extract_project(description)
        if project:
            pattern_match["jql"] = f'project = {project} AND {pattern_match["jql"]}'
        return pattern_match

    # Dynamic query building
    clauses = []
    used_fields = set()
    desc_lower = description.lower()

    # Extract project
    project = _extract_project(description)
    if project:
        clauses.append(f"project = {project}")
        used_fields.add("project")

    # Extract keyword-based fragments
    for keyword, (field, fragment) in KEYWORD_FRAGMENTS.items():
        if keyword in desc_lower.split() and field not in used_fields:
            clauses.append(f"{field} {fragment}")
            used_fields.add(field)

    # Extract explicit assignee
    assignee_match = ASSIGNEE_PATTERN.search(description)
    if assignee_match and "assignee" not in used_fields:
        assignee = assignee_match.group(1)
        if assignee.lower() in ("me", "myself"):
            clauses.append("assignee = currentUser()")
        else:
            clauses.append(f'assignee = "{assignee}"')
        used_fields.add("assignee")

    # Extract labels
    label_match = LABEL_PATTERN.search(description)
    if label_match:
        clauses.append(f'labels = "{label_match.group(1)}"')

    # Extract component
    component_match = COMPONENT_PATTERN.search(description)
    if component_match:
        clauses.append(f'component = "{component_match.group(1)}"')

    # Extract date ranges
    date_match = DATE_RANGE_PATTERN.search(description)
    if date_match:
        amount = date_match.group(1)
        unit = date_match.group(2).lower()
        unit_char = {"day": "d", "week": "w", "month": "m"}.get(unit, "d")
        clauses.append(f"created >= -{amount}{unit_char}")

    # Extract sprint reference
    sprint_match = SPRINT_NAME_PATTERN.search(description)
    if sprint_match:
        sprint_name = sprint_match.group(1).strip()
        if sprint_name.lower() in ("current", "active", "open"):
            clauses.append("sprint in openSprints()")
        else:
            clauses.append(f'sprint = "{sprint_name}"')

    # Default: if no status clause and not looking for done items
    if "status" not in used_fields and "done" not in desc_lower and "closed" not in desc_lower:
        clauses.append("status != Done")

    if not clauses:
        return {
            "jql": "",
            "description": "Could not build query from description",
            "match_type": "no_match",
            "error": "No recognizable patterns found in description",
        }

    jql = " AND ".join(clauses)

    # Add ORDER BY for common scenarios
    if "recent" in desc_lower or "latest" in desc_lower:
        jql += " ORDER BY created DESC"
    elif "priority" in desc_lower or "urgent" in desc_lower:
        jql += " ORDER BY priority DESC"

    return {
        "jql": jql,
        "description": f"Dynamic query from: {description}",
        "match_type": "dynamic",
        "clauses_used": len(clauses),
    }


def _extract_project(description: str) -> Optional[str]:
    """Extract project key from description."""
    # Look for IN/in PROJECT pattern
    in_project = re.search(r'\bin\s+([A-Z]{2,10})\b', description)
    if in_project and in_project.group(1) not in EXCLUDED_WORDS:
        return in_project.group(1)

    # Look for standalone project keys
    for match in PROJECT_PATTERN.finditer(description):
        word = match.group(1)
        if word not in EXCLUDED_WORDS:
            return word

    return None


def validate_jql_syntax(jql: str) -> Dict[str, Any]:
    """Basic JQL syntax validation."""
    issues = []

    if not jql.strip():
        return {"valid": False, "issues": ["Empty query"]}

    # Check balanced quotes
    single_quotes = jql.count("'")
    double_quotes = jql.count('"')
    if single_quotes % 2 != 0:
        issues.append("Unbalanced single quotes")
    if double_quotes % 2 != 0:
        issues.append("Unbalanced double quotes")

    # Check balanced parentheses
    open_parens = jql.count("(")
    close_parens = jql.count(")")
    if open_parens != close_parens:
        issues.append(f"Unbalanced parentheses: {open_parens} open, {close_parens} close")

    # Check for known JQL operators
    valid_operators = {"=", "!=", ">", "<", ">=", "<=", "~", "!~", "in", "not in", "is", "is not", "was", "was not", "changed"}
    jql_upper = jql.upper()

    # Check AND/OR placement
    if jql_upper.strip().startswith("AND") or jql_upper.strip().startswith("OR"):
        issues.append("Query cannot start with AND/OR")
    if jql_upper.strip().endswith("AND") or jql_upper.strip().endswith("OR"):
        issues.append("Query cannot end with AND/OR")

    # Check ORDER BY syntax
    order_match = re.search(r'ORDER\s+BY\s+(\w+)(?:\s+(ASC|DESC))?', jql, re.IGNORECASE)
    if "ORDER" in jql_upper and not order_match:
        issues.append("Invalid ORDER BY syntax")

    return {
        "valid": len(issues) == 0,
        "issues": issues,
        "query_length": len(jql),
    }


# ---------------------------------------------------------------------------
# Output Formatting
# ---------------------------------------------------------------------------

def format_text_output(result: Dict[str, Any]) -> str:
    """Format results as readable text report."""
    lines = []
    lines.append("=" * 60)
    lines.append("JQL QUERY BUILDER RESULTS")
    lines.append("=" * 60)
    lines.append("")

    if "error" in result:
        lines.append(f"ERROR: {result['error']}")
        return "\n".join(lines)

    lines.append(f"Match Type: {result.get('match_type', 'unknown')}")
    lines.append(f"Description: {result.get('description', '')}")
    lines.append("")
    lines.append("GENERATED JQL")
    lines.append("-" * 30)
    lines.append(result.get("jql", ""))
    lines.append("")

    validation = result.get("validation", {})
    if validation:
        lines.append("VALIDATION")
        lines.append("-" * 30)
        lines.append(f"Valid: {'Yes' if validation.get('valid') else 'No'}")
        if validation.get("issues"):
            for issue in validation["issues"]:
                lines.append(f"  - {issue}")

    if result.get("pattern_name"):
        lines.append("")
        lines.append(f"Matched Pattern: {result['pattern_name']}")

    return "\n".join(lines)


def format_patterns_output(output_format: str) -> str:
    """Format available patterns list."""
    if output_format == "json":
        patterns = {}
        for name, data in PATTERN_LIBRARY.items():
            patterns[name] = {
                "description": data["description"],
                "phrases": data["phrases"],
                "jql": data["jql"],
            }
        return json.dumps(patterns, indent=2)

    lines = []
    lines.append("=" * 60)
    lines.append("AVAILABLE JQL PATTERNS")
    lines.append("=" * 60)
    lines.append("")

    for name, data in PATTERN_LIBRARY.items():
        lines.append(f"  {name}")
        lines.append(f"    Description: {data['description']}")
        lines.append(f"    Phrases: {', '.join(data['phrases'])}")
        lines.append(f"    JQL: {data['jql']}")
        lines.append("")

    lines.append(f"Total patterns: {len(PATTERN_LIBRARY)}")
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
        description="Build JQL queries from natural language descriptions"
    )
    parser.add_argument(
        "description",
        nargs="?",
        help="Natural language description of the query",
    )
    parser.add_argument(
        "--format",
        choices=["text", "json"],
        default="text",
        help="Output format (default: text)",
    )
    parser.add_argument(
        "--patterns",
        action="store_true",
        help="List all available query patterns",
    )

    args = parser.parse_args()

    try:
        if args.patterns:
            print(format_patterns_output(args.format))
            return 0

        if not args.description:
            parser.error("description is required unless --patterns is used")

        # Build query
        result = build_jql_from_description(args.description)

        # Validate
        if result.get("jql"):
            result["validation"] = validate_jql_syntax(result["jql"])

        # Output results
        if args.format == "json":
            output = format_json_output(result)
            print(json.dumps(output, indent=2))
        else:
            output = format_text_output(result)
            print(output)

        return 0

    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
