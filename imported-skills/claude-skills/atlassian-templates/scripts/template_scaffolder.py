#!/usr/bin/env python3
"""
Template Scaffolder

Generates Confluence page template markup in storage-format XHTML. Supports
built-in template types and custom section definitions with optional macros.

Usage:
    python template_scaffolder.py meeting-notes
    python template_scaffolder.py decision-log --format json
    python template_scaffolder.py custom --sections "Overview,Goals,Action Items" --macros toc,status
    python template_scaffolder.py --list
"""

import argparse
import json
import sys
from datetime import datetime
from typing import Any, Dict, List, Optional


# ---------------------------------------------------------------------------
# Macro Generators
# ---------------------------------------------------------------------------

def macro_toc() -> str:
    """Generate table of contents macro."""
    return '<ac:structured-macro ac:name="toc"><ac:parameter ac:name="printable">true</ac:parameter><ac:parameter ac:name="style">disc</ac:parameter><ac:parameter ac:name="maxLevel">3</ac:parameter></ac:structured-macro>'


def macro_status(text: str = "IN PROGRESS", color: str = "Yellow") -> str:
    """Generate status macro."""
    return f'<ac:structured-macro ac:name="status"><ac:parameter ac:name="colour">{color}</ac:parameter><ac:parameter ac:name="title">{text}</ac:parameter></ac:structured-macro>'


def macro_info_panel(content: str) -> str:
    """Generate info panel macro."""
    return f'<ac:structured-macro ac:name="info"><ac:rich-text-body><p>{content}</p></ac:rich-text-body></ac:structured-macro>'


def macro_warning_panel(content: str) -> str:
    """Generate warning panel macro."""
    return f'<ac:structured-macro ac:name="warning"><ac:rich-text-body><p>{content}</p></ac:rich-text-body></ac:structured-macro>'


def macro_note_panel(content: str) -> str:
    """Generate note panel macro."""
    return f'<ac:structured-macro ac:name="note"><ac:rich-text-body><p>{content}</p></ac:rich-text-body></ac:structured-macro>'


def macro_expand(title: str, content: str) -> str:
    """Generate expand/collapse macro."""
    return f'<ac:structured-macro ac:name="expand"><ac:parameter ac:name="title">{title}</ac:parameter><ac:rich-text-body>{content}</ac:rich-text-body></ac:structured-macro>'


def macro_jira_issues(jql: str) -> str:
    """Generate Jira issues macro."""
    return f'<ac:structured-macro ac:name="jira"><ac:parameter ac:name="jqlQuery">{jql}</ac:parameter><ac:parameter ac:name="columns">key,summary,type,created,updated,due,assignee,reporter,priority,status,resolution</ac:parameter></ac:structured-macro>'


MACRO_MAP = {
    "toc": macro_toc,
    "status": macro_status,
    "info": macro_info_panel,
    "warning": macro_warning_panel,
    "note": macro_note_panel,
    "expand": macro_expand,
    "jira-issues": macro_jira_issues,
}


# ---------------------------------------------------------------------------
# Built-in Templates
# ---------------------------------------------------------------------------

def _section(title: str, content: str) -> str:
    """Generate a section with heading and content."""
    return f'<h2>{title}</h2>\n{content}\n'


def _table(headers: List[str], rows: List[List[str]]) -> str:
    """Generate an XHTML table."""
    parts = ['<table><colgroup>']
    for _ in headers:
        parts.append('<col />')
    parts.append('</colgroup><thead><tr>')
    for h in headers:
        parts.append(f'<th><p>{h}</p></th>')
    parts.append('</tr></thead><tbody>')
    for row in rows:
        parts.append('<tr>')
        for cell in row:
            parts.append(f'<td><p>{cell}</p></td>')
        parts.append('</tr>')
    parts.append('</tbody></table>')
    return ''.join(parts)


def template_meeting_notes() -> Dict[str, Any]:
    """Generate meeting notes template."""
    today = datetime.now().strftime("%Y-%m-%d")
    body = macro_toc() + '\n'
    body += macro_info_panel("Replace placeholder text with your meeting details.") + '\n'
    body += _section("Meeting Details", _table(
        ["Field", "Value"],
        [["Date", today], ["Time", ""], ["Location", ""], ["Facilitator", ""], ["Note Taker", ""]],
    ))
    body += _section("Attendees", '<ul><li><p>Name 1</p></li><li><p>Name 2</p></li></ul>')
    body += _section("Agenda", '<ol><li><p>Item 1</p></li><li><p>Item 2</p></li><li><p>Item 3</p></li></ol>')
    body += _section("Discussion Notes", '<p>Summary of discussion points...</p>')
    body += _section("Decisions Made", _table(
        ["Decision", "Owner", "Date"],
        [["", "", today]],
    ))
    body += _section("Action Items", _table(
        ["Action", "Owner", "Due Date", "Status"],
        [["", "", "", macro_status("TODO", "Grey")]],
    ))
    body += _section("Next Meeting", '<p>Date: TBD</p><p>Agenda items for next time:</p><ul><li><p></p></li></ul>')

    return {"name": "Meeting Notes", "body": body, "labels": ["meeting-notes", "template"]}


def template_decision_log() -> Dict[str, Any]:
    """Generate decision log template."""
    today = datetime.now().strftime("%Y-%m-%d")
    body = macro_toc() + '\n'
    body += _section("Decision Log", macro_info_panel("Track key decisions, context, and outcomes."))
    body += _table(
        ["ID", "Date", "Decision", "Context", "Alternatives Considered", "Outcome", "Owner", "Status"],
        [
            ["D-001", today, "", "", "", "", "", macro_status("DECIDED", "Green")],
            ["D-002", "", "", "", "", "", "", macro_status("PENDING", "Yellow")],
        ],
    )
    body += '\n'
    body += _section("Decision Template", macro_expand("Decision Details Template",
        '<h3>Context</h3><p>What is the issue or situation requiring a decision?</p>'
        '<h3>Options</h3><ol><li><p>Option A - pros/cons</p></li><li><p>Option B - pros/cons</p></li></ol>'
        '<h3>Decision</h3><p>What was decided and why?</p>'
        '<h3>Consequences</h3><p>What are the expected outcomes?</p>'
    ))

    return {"name": "Decision Log", "body": body, "labels": ["decision-log", "template"]}


def template_runbook() -> Dict[str, Any]:
    """Generate runbook template."""
    body = macro_toc() + '\n'
    body += macro_warning_panel("This runbook should be tested and reviewed quarterly.") + '\n'
    body += _section("Overview", '<p>Brief description of what this runbook covers.</p>'
        + _table(["Field", "Value"], [
            ["Service/System", ""], ["Owner", ""], ["Last Tested", ""],
            ["Severity", ""], ["Estimated Duration", ""],
        ]))
    body += _section("Prerequisites", '<ul><li><p>Access to system X</p></li><li><p>VPN connected</p></li><li><p>Required tools installed</p></li></ul>')
    body += _section("Steps", '<ol><li><p><strong>Step 1:</strong> Description</p><ac:structured-macro ac:name="code"><ac:parameter ac:name="language">bash</ac:parameter><ac:plain-text-body><![CDATA[# command here]]></ac:plain-text-body></ac:structured-macro></li>'
        '<li><p><strong>Step 2:</strong> Description</p></li>'
        '<li><p><strong>Step 3:</strong> Description</p></li></ol>')
    body += _section("Verification", '<p>How to verify the issue is resolved:</p><ul><li><p>Check 1</p></li><li><p>Check 2</p></li></ul>')
    body += _section("Rollback", macro_note_panel("If the above steps do not resolve the issue, follow these rollback steps.") +
        '<ol><li><p>Rollback step 1</p></li><li><p>Rollback step 2</p></li></ol>')
    body += _section("Escalation", _table(
        ["Level", "Contact", "When to Escalate"],
        [["L1", "", ""], ["L2", "", ""], ["L3", "", ""]],
    ))

    return {"name": "Runbook", "body": body, "labels": ["runbook", "operations", "template"]}


def template_project_kickoff() -> Dict[str, Any]:
    """Generate project kickoff template."""
    today = datetime.now().strftime("%Y-%m-%d")
    body = macro_toc() + '\n'
    body += _section("Project Overview", _table(
        ["Field", "Value"],
        [["Project Name", ""], ["Start Date", today], ["Target End Date", ""],
         ["Project Lead", ""], ["Sponsor", ""], ["Status", macro_status("KICKOFF", "Blue")]],
    ))
    body += _section("Vision & Goals", '<h3>Vision</h3><p>What does success look like?</p>'
        '<h3>Goals</h3><ol><li><p>Goal 1</p></li><li><p>Goal 2</p></li><li><p>Goal 3</p></li></ol>')
    body += _section("Scope", '<h3>In Scope</h3><ul><li><p></p></li></ul><h3>Out of Scope</h3><ul><li><p></p></li></ul>')
    body += _section("Stakeholders", _table(
        ["Name", "Role", "Responsibility", "Communication Preference"],
        [["", "", "", ""]],
    ))
    body += _section("Timeline & Milestones", _table(
        ["Milestone", "Target Date", "Status"],
        [["Phase 1", "", macro_status("NOT STARTED", "Grey")],
         ["Phase 2", "", macro_status("NOT STARTED", "Grey")]],
    ))
    body += _section("Risks", _table(
        ["Risk", "Likelihood", "Impact", "Mitigation"],
        [["", "High/Medium/Low", "High/Medium/Low", ""]],
    ))
    body += _section("Next Steps", '<ul><li><p></p></li></ul>')

    return {"name": "Project Kickoff", "body": body, "labels": ["project-kickoff", "template"]}


def template_sprint_retro() -> Dict[str, Any]:
    """Generate sprint retrospective template."""
    body = macro_toc() + '\n'
    body += _section("Sprint Info", _table(
        ["Field", "Value"],
        [["Sprint", ""], ["Date Range", ""], ["Facilitator", ""],
         ["Velocity", ""], ["Commitment", ""], ["Completion Rate", ""]],
    ))
    body += _section("What Went Well", '<ul><li><p></p></li></ul>')
    body += _section("What Could Be Improved", '<ul><li><p></p></li></ul>')
    body += _section("Action Items from Last Retro", _table(
        ["Action", "Owner", "Status"],
        [["", "", macro_status("DONE", "Green")], ["", "", macro_status("IN PROGRESS", "Yellow")]],
    ))
    body += _section("New Action Items", _table(
        ["Action", "Owner", "Due Date", "Priority"],
        [["", "", "", "High/Medium/Low"]],
    ))
    body += _section("Team Health Check", macro_info_panel("Rate each area 1-5 (1=needs work, 5=great)") + _table(
        ["Area", "Rating", "Trend", "Notes"],
        [["Teamwork", "", "", ""], ["Delivery", "", "", ""],
         ["Fun", "", "", ""], ["Learning", "", "", ""]],
    ))

    return {"name": "Sprint Retrospective", "body": body, "labels": ["sprint-retro", "agile", "template"]}


def template_how_to_guide() -> Dict[str, Any]:
    """Generate how-to guide template."""
    body = macro_toc() + '\n'
    body += macro_info_panel("This guide explains how to accomplish a specific task.") + '\n'
    body += _section("Overview", '<p>Brief description of what this guide covers and who it is for.</p>')
    body += _section("Prerequisites", '<ul><li><p>Prerequisite 1</p></li><li><p>Prerequisite 2</p></li></ul>')
    body += _section("Step-by-Step Instructions",
        '<h3>Step 1: Title</h3><p>Description of what to do.</p>'
        '<h3>Step 2: Title</h3><p>Description of what to do.</p>'
        '<h3>Step 3: Title</h3><p>Description of what to do.</p>')
    body += _section("Troubleshooting", macro_expand("Common Issues",
        '<h3>Issue 1</h3><p>Solution...</p>'
        '<h3>Issue 2</h3><p>Solution...</p>'))
    body += _section("Related Resources", '<ul><li><p>Link 1</p></li><li><p>Link 2</p></li></ul>')

    return {"name": "How-To Guide", "body": body, "labels": ["how-to", "guide", "template"]}


TEMPLATE_REGISTRY = {
    "meeting-notes": template_meeting_notes,
    "decision-log": template_decision_log,
    "runbook": template_runbook,
    "project-kickoff": template_project_kickoff,
    "sprint-retro": template_sprint_retro,
    "how-to-guide": template_how_to_guide,
}


# ---------------------------------------------------------------------------
# Custom Template Builder
# ---------------------------------------------------------------------------

def build_custom_template(
    sections: List[str],
    macros: List[str],
) -> Dict[str, Any]:
    """Build a custom template from sections and macros."""
    body = ""

    # Add requested macros at the top
    if "toc" in macros:
        body += macro_toc() + '\n'
    if "status" in macros:
        body += '<p>Status: ' + macro_status() + '</p>\n'

    for section in sections:
        section = section.strip()
        if not section:
            continue
        body += _section(section, '<p></p>')

    # Add panels if requested
    if "info" in macros:
        body = macro_info_panel("Add instructions or context here.") + '\n' + body
    if "warning" in macros:
        body += macro_warning_panel("Add warnings here.") + '\n'
    if "note" in macros:
        body += macro_note_panel("Add notes here.") + '\n'

    return {"name": "Custom Template", "body": body, "labels": ["custom", "template"]}


# ---------------------------------------------------------------------------
# Output Formatting
# ---------------------------------------------------------------------------

def format_text_output(result: Dict[str, Any]) -> str:
    """Format results as readable text report."""
    lines = []
    lines.append("=" * 60)
    lines.append(f"TEMPLATE: {result['name']}")
    lines.append("=" * 60)
    lines.append("")
    lines.append(f"Labels: {', '.join(result.get('labels', []))}")
    lines.append("")
    lines.append("CONFLUENCE STORAGE FORMAT MARKUP")
    lines.append("-" * 30)
    lines.append(result["body"])

    return "\n".join(lines)


def format_json_output(result: Dict[str, Any]) -> Dict[str, Any]:
    """Format results as JSON."""
    return result


def format_list_output(output_format: str) -> str:
    """Format available templates list."""
    if output_format == "json":
        templates = {}
        for name, func in TEMPLATE_REGISTRY.items():
            result = func()
            templates[name] = {
                "name": result["name"],
                "labels": result["labels"],
            }
        return json.dumps(templates, indent=2)

    lines = []
    lines.append("=" * 60)
    lines.append("AVAILABLE TEMPLATES")
    lines.append("=" * 60)
    lines.append("")
    for name, func in TEMPLATE_REGISTRY.items():
        result = func()
        lines.append(f"  {name}")
        lines.append(f"    Name: {result['name']}")
        lines.append(f"    Labels: {', '.join(result['labels'])}")
        lines.append("")
    lines.append(f"Total templates: {len(TEMPLATE_REGISTRY)}")
    lines.append("")
    lines.append("Usage:")
    lines.append("  python template_scaffolder.py <template-name>")
    lines.append('  python template_scaffolder.py custom --sections "Section1,Section2" --macros toc,status')
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# CLI Interface
# ---------------------------------------------------------------------------

def main() -> int:
    """Main CLI entry point."""
    parser = argparse.ArgumentParser(
        description="Generate Confluence page template markup"
    )
    parser.add_argument(
        "template",
        nargs="?",
        help="Template name or 'custom' for custom template",
    )
    parser.add_argument(
        "--format",
        choices=["text", "json"],
        default="text",
        help="Output format (default: text)",
    )
    parser.add_argument(
        "--list",
        action="store_true",
        help="List all available template types",
    )
    parser.add_argument(
        "--sections",
        help='Comma-separated section names for custom template (e.g., "Overview,Goals,Action Items")',
    )
    parser.add_argument(
        "--macros",
        help='Comma-separated macro names to include (e.g., "toc,status,info")',
    )

    args = parser.parse_args()

    try:
        if args.list:
            print(format_list_output(args.format))
            return 0

        if not args.template:
            parser.error("template name is required unless --list is used")

        template_name = args.template.lower()

        if template_name == "custom":
            if not args.sections:
                parser.error("--sections is required for custom templates")
            sections = [s.strip() for s in args.sections.split(",")]
            macros = [m.strip() for m in args.macros.split(",")] if args.macros else []
            result = build_custom_template(sections, macros)
        elif template_name in TEMPLATE_REGISTRY:
            result = TEMPLATE_REGISTRY[template_name]()
        else:
            available = ", ".join(sorted(TEMPLATE_REGISTRY.keys()))
            print(f"Error: Unknown template '{template_name}'. Available: {available}", file=sys.stderr)
            return 1

        if args.format == "json":
            print(json.dumps(format_json_output(result), indent=2))
        else:
            print(format_text_output(result))

        return 0

    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
