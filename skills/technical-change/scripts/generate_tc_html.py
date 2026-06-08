#!/usr/bin/env python3
"""TC Record HTML Generator — Converts tc_record.json into accessible HTML.

Reads a TC record JSON file, validates it, inlines the shared CSS, and produces
a self-contained HTML page with dark theme, WCAG AA+ accessibility, and rem-based
typography.

Usage:
    python generate_tc_html.py <path_to_tc_record.json> [--output <output_path.html>]

If --output is not specified, writes tc_record.html in the same directory as the input.

Exit codes:
    0 = SUCCESS
    1 = VALIDATION ERRORS
    2 = FILE NOT FOUND or other errors
"""

from __future__ import annotations

import json
import sys
from datetime import datetime, timezone
from html import escape
from pathlib import Path

# Add parent dir to path so we can import the validator
_SKILL_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_SKILL_ROOT / "validators"))

from validate_tc import validate_tc_record  # noqa: E402


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _esc(value) -> str:
    """HTML-escape any value, converting non-strings to str first."""
    if value is None:
        return '<span class="dim">—</span>'
    return escape(str(value))


def _format_datetime(iso_str: str | None) -> str:
    """Format an ISO datetime string for display."""
    if not iso_str:
        return "—"
    try:
        dt = datetime.fromisoformat(iso_str)
        return dt.strftime("%Y-%m-%d %H:%M %Z").strip()
    except (ValueError, TypeError):
        return _esc(iso_str)


def _status_display(status: str) -> str:
    """Convert status slug to display text."""
    return status.replace("_", " ").title()


def _load_css() -> str:
    """Load the shared CSS file."""
    css_path = _SKILL_ROOT / "templates" / "tc_styles.css"
    if css_path.exists():
        return css_path.read_text(encoding="utf-8")
    return "/* CSS not found — using inline fallback */\nbody { font-family: sans-serif; background: #0d0d18; color: #e0dcd0; }"


# ---------------------------------------------------------------------------
# Section Builders
# ---------------------------------------------------------------------------

def build_stats_grid(record: dict) -> str:
    """Build the stats grid HTML."""
    files_count = len(record.get("files_affected", []))
    revisions_count = len(record.get("revision_history", []))
    test_cases = record.get("test_cases", [])
    tests_total = len(test_cases)
    tests_pass = sum(1 for t in test_cases if t.get("status") == "pass")
    sub_tc_count = len(record.get("sub_tcs", []))
    sessions_count = len(record.get("session_context", {}).get("session_history", [])) + 1

    cards = [
        (str(files_count), "Files Affected"),
        (f"{tests_pass}/{tests_total}", "Tests Passing"),
        (str(revisions_count), "Revisions"),
        (str(sessions_count), "Sessions"),
        (str(sub_tc_count), "Sub-TCs"),
        (_esc(record.get("priority", "medium")).title(), "Priority"),
    ]

    html_parts = []
    for value, label in cards:
        html_parts.append(
            f'<div class="stat-card">'
            f'<span class="stat-value">{value}</span>'
            f'<span class="stat-label">{_esc(label)}</span>'
            f'</div>'
        )
    return "\n".join(html_parts)


def build_overview(record: dict) -> str:
    """Build the overview section content."""
    desc = record.get("description", {})
    parts = []

    parts.append(f'<div class="card">')
    parts.append(f'<h3>Summary</h3>')
    parts.append(f'<p>{_esc(desc.get("summary", ""))}</p>')
    parts.append(f'</div>')

    parts.append(f'<div class="card">')
    parts.append(f'<h3>Motivation</h3>')
    parts.append(f'<p>{_esc(desc.get("motivation", ""))}</p>')
    parts.append(f'</div>')

    if desc.get("detailed_design"):
        parts.append(f'<div class="card">')
        parts.append(f'<h3>Detailed Design</h3>')
        parts.append(f'<p>{_esc(desc["detailed_design"])}</p>')
        parts.append(f'</div>')

    if desc.get("breaking_changes"):
        parts.append(f'<div class="card">')
        parts.append(f'<h3>Breaking Changes</h3>')
        parts.append(f'<ul class="handoff-list">')
        for bc in desc["breaking_changes"]:
            parts.append(f'<li>{_esc(bc)}</li>')
        parts.append(f'</ul></div>')

    if desc.get("dependencies"):
        parts.append(f'<div class="card">')
        parts.append(f'<h3>Dependencies</h3>')
        parts.append(f'<ul class="handoff-list">')
        for dep in desc["dependencies"]:
            parts.append(f'<li>{_esc(dep)}</li>')
        parts.append(f'</ul></div>')

    # Metadata
    meta = record.get("metadata", {})
    parts.append(f'<div class="card">')
    parts.append(f'<h3>Metadata</h3>')
    parts.append(f'<div class="session-info">')
    for label, value in [
        ("Created", _format_datetime(record.get("created"))),
        ("Updated", _format_datetime(record.get("updated"))),
        ("Created By", _esc(record.get("created_by", ""))),
        ("Last Modified By", _esc(meta.get("last_modified_by", ""))),
        ("Effort", _esc(meta.get("estimated_effort", "—")).title()),
    ]:
        parts.append(
            f'<div class="session-field">'
            f'<div class="field-label">{label}</div>'
            f'<div class="field-value">{value}</div>'
            f'</div>'
        )
    parts.append(f'</div></div>')

    # Tags
    tags = record.get("tags", [])
    if tags:
        parts.append(f'<div class="card">')
        parts.append(f'<h3>Tags</h3>')
        parts.append(f'<div style="display:flex;flex-wrap:wrap;gap:var(--space-sm)">')
        for tag in tags:
            parts.append(f'<span class="badge badge-enhancement">{_esc(tag)}</span>')
        parts.append(f'</div></div>')

    # Related TCs
    related = record.get("related_tcs", [])
    if related:
        parts.append(f'<div class="card">')
        parts.append(f'<h3>Related TCs</h3>')
        parts.append(f'<ul class="handoff-list">')
        for r in related:
            parts.append(f'<li>{_esc(r)}</li>')
        parts.append(f'</ul></div>')

    # Notes
    notes = record.get("notes", "")
    if notes:
        parts.append(f'<div class="card">')
        parts.append(f'<h3>Notes</h3>')
        parts.append(f'<p>{_esc(notes)}</p>')
        parts.append(f'</div>')

    return "\n".join(parts)


def build_files(record: dict) -> str:
    """Build the files affected section."""
    files = record.get("files_affected", [])
    if not files:
        return '<div class="empty-state"><p>No files affected yet.</p></div>'

    action_badges = {
        "created": "badge-feature",
        "modified": "badge-refactor",
        "deleted": "badge-bugfix",
        "renamed": "badge-enhancement",
    }

    parts = ['<div class="table-wrap"><table>', "<thead><tr>"]
    parts.append("<th>File</th><th>Action</th><th>Description</th><th>+/-</th>")
    parts.append("</tr></thead><tbody>")

    for f in files:
        action = f.get("action", "")
        badge_cls = action_badges.get(action, "")
        added = f.get("lines_added")
        removed = f.get("lines_removed")
        diff_str = ""
        if added is not None:
            diff_str += f'<span class="new-value">+{added}</span>'
        if removed is not None:
            if diff_str:
                diff_str += " / "
            diff_str += f'<span class="old-value">-{removed}</span>'
        if not diff_str:
            diff_str = "—"

        parts.append(
            f"<tr>"
            f'<td><code>{_esc(f.get("path", ""))}</code></td>'
            f'<td><span class="badge {badge_cls}">{_esc(action)}</span></td>'
            f'<td>{_esc(f.get("description", ""))}</td>'
            f"<td>{diff_str}</td>"
            f"</tr>"
        )

    parts.append("</tbody></table></div>")
    return "\n".join(parts)


def build_revisions(record: dict) -> str:
    """Build the revision history timeline."""
    revisions = record.get("revision_history", [])
    if not revisions:
        return '<div class="empty-state"><p>No revisions recorded.</p></div>'

    parts = ['<div class="timeline">']

    for rev in reversed(revisions):
        parts.append('<div class="timeline-item">')
        parts.append(
            f'<span class="revision-id">{_esc(rev.get("revision_id", ""))}</span>'
            f' <span class="revision-meta">'
            f'{_format_datetime(rev.get("timestamp"))} by {_esc(rev.get("author", ""))}'
            f'</span>'
        )
        parts.append(f'<div class="revision-summary">{_esc(rev.get("summary", ""))}</div>')

        field_changes = rev.get("field_changes", [])
        if field_changes:
            for fc in field_changes:
                action = fc.get("action", "")
                parts.append(f'<div class="field-change">')
                parts.append(f'<span class="field-name">{_esc(fc.get("field", ""))}</span> ')

                if action == "changed":
                    parts.append(
                        f'<span class="old-value">{_esc(fc.get("old_value"))}</span> '
                        f'&rarr; <span class="new-value">{_esc(fc.get("new_value"))}</span>'
                    )
                elif action == "set":
                    parts.append(f'set to <span class="new-value">{_esc(fc.get("new_value"))}</span>')
                elif action == "added":
                    parts.append(f'<span class="new-value">+ {_esc(fc.get("new_value"))}</span>')
                elif action == "removed":
                    parts.append(f'<span class="old-value">- {_esc(fc.get("old_value"))}</span>')

                reason = fc.get("reason")
                if reason:
                    parts.append(f'<br><small style="color:var(--dim)">Reason: {_esc(reason)}</small>')

                parts.append('</div>')

        parts.append('</div>')

    parts.append('</div>')
    return "\n".join(parts)


def build_sub_tcs(record: dict) -> str:
    """Build the sub-TCs section."""
    subs = record.get("sub_tcs", [])
    if not subs:
        return '<div class="empty-state"><p>No sub-TCs defined.</p></div>'

    parts = []
    for sub in subs:
        status = sub.get("status", "planned")
        parts.append(f'<div class="card">')
        parts.append(f'<div class="card-header">')
        parts.append(f'<div>')
        parts.append(f'<span class="card-title">{_esc(sub.get("title", ""))}</span>')
        parts.append(f'<br><code style="color:var(--dim);font-size:var(--font-sm)">{_esc(sub.get("sub_id", ""))}</code>')
        parts.append(f'</div>')
        parts.append(f'<span class="badge badge-{_esc(status)}">{_status_display(status)}</span>')
        parts.append(f'</div>')
        if sub.get("description"):
            parts.append(f'<p>{_esc(sub["description"])}</p>')
        if sub.get("files_affected"):
            parts.append(f'<div style="margin-top:var(--space-sm)"><strong style="color:var(--dim);font-size:var(--font-sm)">Files:</strong>')
            for fp in sub["files_affected"]:
                parts.append(f' <code style="font-size:var(--font-sm)">{_esc(fp)}</code>')
            parts.append(f'</div>')
        parts.append(f'</div>')

    return "\n".join(parts)


def build_tests(record: dict) -> str:
    """Build the test cases section."""
    tests = record.get("test_cases", [])
    if not tests:
        return '<div class="empty-state"><p>No test cases defined yet.</p></div>'

    parts = []
    for tc in tests:
        status = tc.get("status", "pending")
        parts.append(f'<div class="test-case">')
        parts.append(f'<div class="test-header">')
        parts.append(
            f'<div>'
            f'<span class="test-id">{_esc(tc.get("test_id", ""))}</span> '
            f'<span class="test-title">{_esc(tc.get("title", ""))}</span>'
            f'</div>'
            f'<span class="badge badge-{_esc(status)}">{_esc(status).upper()}</span>'
        )
        parts.append(f'</div>')

        # Procedure
        procedure = tc.get("procedure", [])
        if procedure:
            parts.append(f'<div class="result-label">Procedure</div>')
            parts.append(f'<ol class="procedure-steps">')
            for step in procedure:
                parts.append(f'<li>{_esc(step)}</li>')
            parts.append(f'</ol>')

        # Expected
        parts.append(f'<div class="result-label">Expected Result</div>')
        parts.append(f'<div class="result-value">{_esc(tc.get("expected_result", ""))}</div>')

        # Actual
        actual = tc.get("actual_result")
        if actual:
            parts.append(f'<div class="result-label">Actual Result</div>')
            parts.append(f'<div class="result-value">{_esc(actual)}</div>')

        # Evidence
        evidence = tc.get("evidence", [])
        if evidence:
            parts.append(f'<div class="result-label">Evidence</div>')
            for ev in evidence:
                ev_type = ev.get("type", "")
                parts.append(f'<div class="card" style="margin-bottom:var(--space-sm)">')
                parts.append(
                    f'<span class="badge badge-infrastructure">{_esc(ev_type)}</span> '
                    f'{_esc(ev.get("description", ""))}'
                )
                content = ev.get("content")
                if content:
                    parts.append(f'<div class="code-block">{_esc(content)}</div>')
                path = ev.get("path")
                if path:
                    parts.append(f'<p style="margin-top:var(--space-xs)"><code>{_esc(path)}</code></p>')
                parts.append(f'</div>')

        # Tested by/date
        tested_by = tc.get("tested_by")
        tested_date = tc.get("tested_date")
        if tested_by or tested_date:
            parts.append(f'<div class="card-meta" style="margin-top:var(--space-sm)">')
            if tested_by:
                parts.append(f'Tested by: {_esc(tested_by)}')
            if tested_date:
                parts.append(f' on {_format_datetime(tested_date)}')
            parts.append(f'</div>')

        parts.append(f'</div>')

    return "\n".join(parts)


def build_session(record: dict) -> str:
    """Build the session context section."""
    ctx = record.get("session_context", {})
    parts = []

    # Current session
    cs = ctx.get("current_session", {})
    parts.append(f'<h3>Current Session</h3>')
    parts.append(f'<div class="session-info">')
    for label, value in [
        ("Session ID", _esc(cs.get("session_id", "—"))),
        ("Platform", _esc(cs.get("platform", "—"))),
        ("Model", _esc(cs.get("model", "—"))),
        ("Started", _format_datetime(cs.get("started"))),
        ("Last Active", _format_datetime(cs.get("last_active"))),
    ]:
        parts.append(
            f'<div class="session-field">'
            f'<div class="field-label">{label}</div>'
            f'<div class="field-value">{value}</div>'
            f'</div>'
        )
    parts.append(f'</div>')

    # Handoff data
    handoff = ctx.get("handoff", {})
    has_handoff = any([
        handoff.get("progress_summary"),
        handoff.get("next_steps"),
        handoff.get("blockers"),
        handoff.get("key_context"),
        handoff.get("files_in_progress"),
        handoff.get("decisions_made"),
    ])

    if has_handoff:
        parts.append(f'<div class="handoff-section">')
        parts.append(f'<h3>Handoff Data</h3>')

        if handoff.get("progress_summary"):
            parts.append(f'<div class="result-label">Progress Summary</div>')
            parts.append(f'<p class="result-value">{_esc(handoff["progress_summary"])}</p>')

        if handoff.get("next_steps"):
            parts.append(f'<div class="result-label">Next Steps</div>')
            parts.append(f'<ul class="handoff-list">')
            for step in handoff["next_steps"]:
                parts.append(f'<li>{_esc(step)}</li>')
            parts.append(f'</ul>')

        if handoff.get("blockers"):
            parts.append(f'<div class="result-label">Blockers</div>')
            parts.append(f'<ul class="handoff-list">')
            for b in handoff["blockers"]:
                parts.append(f'<li style="color:var(--status-blocked-text)">{_esc(b)}</li>')
            parts.append(f'</ul>')

        if handoff.get("key_context"):
            parts.append(f'<div class="result-label">Key Context</div>')
            parts.append(f'<ul class="handoff-list">')
            for c in handoff["key_context"]:
                parts.append(f'<li>{_esc(c)}</li>')
            parts.append(f'</ul>')

        if handoff.get("files_in_progress"):
            parts.append(f'<div class="result-label">Files In Progress</div>')
            parts.append(f'<div class="table-wrap"><table>')
            parts.append(f'<thead><tr><th>File</th><th>State</th><th>Notes</th></tr></thead>')
            parts.append(f'<tbody>')
            for fip in handoff["files_in_progress"]:
                state = fip.get("state", "")
                parts.append(
                    f'<tr>'
                    f'<td><code>{_esc(fip.get("path", ""))}</code></td>'
                    f'<td><span class="badge badge-{_esc(state)}">{_esc(state)}</span></td>'
                    f'<td>{_esc(fip.get("notes", ""))}</td>'
                    f'</tr>'
                )
            parts.append(f'</tbody></table></div>')

        if handoff.get("decisions_made"):
            parts.append(f'<div class="result-label">Decisions Made</div>')
            for d in handoff["decisions_made"]:
                parts.append(f'<div class="card" style="margin-bottom:var(--space-sm)">')
                parts.append(f'<strong>{_esc(d.get("decision", ""))}</strong>')
                parts.append(f'<br><span style="color:var(--dim)">{_esc(d.get("rationale", ""))}</span>')
                parts.append(f'<br><small style="color:var(--dim)">{_format_datetime(d.get("timestamp"))}</small>')
                parts.append(f'</div>')

        parts.append(f'</div>')

    # Session history
    history = ctx.get("session_history", [])
    if history:
        parts.append(f'<h3 style="margin-top:var(--space-xl)">Session History</h3>')
        for sess in reversed(history):
            parts.append(f'<div class="card">')
            parts.append(
                f'<div class="card-header">'
                f'<span class="card-title">{_esc(sess.get("platform", ""))} — {_esc(sess.get("model", ""))}</span>'
                f'<span class="card-meta">{_format_datetime(sess.get("started"))} - {_format_datetime(sess.get("ended"))}</span>'
                f'</div>'
            )
            parts.append(f'<p>{_esc(sess.get("summary", ""))}</p>')
            changes = sess.get("changes_made", [])
            if changes:
                parts.append(f'<ul class="handoff-list" style="margin-top:var(--space-sm)">')
                for ch in changes:
                    parts.append(f'<li>{_esc(ch)}</li>')
                parts.append(f'</ul>')
            parts.append(f'</div>')

    return "\n".join(parts)


def build_approval(record: dict) -> str:
    """Build the approval section."""
    appr = record.get("approval", {})
    approved = appr.get("approved", False)
    coverage = appr.get("test_coverage_status", "none")

    cls = "approved" if approved else "not-approved"
    icon = "&#10003;" if approved else "&#10007;"
    label = "Approved" if approved else "Not Yet Approved"

    parts = [f'<div class="approval-status {cls}">']
    parts.append(f'<span style="font-size:var(--font-3xl)">{icon}</span>')
    parts.append(f'<div>')
    parts.append(f'<strong style="font-size:var(--font-xl)">{label}</strong>')

    if approved:
        parts.append(f'<br>By: {_esc(appr.get("approved_by", ""))} on {_format_datetime(appr.get("approved_date"))}')

    parts.append(f'<br>Test Coverage: <span class="badge badge-{_esc(coverage)}">{_esc(coverage).upper()}</span>')

    if appr.get("approval_notes"):
        parts.append(f'<br><span style="color:var(--dim)">{_esc(appr["approval_notes"])}</span>')

    parts.append(f'</div></div>')
    return "\n".join(parts)


# ---------------------------------------------------------------------------
# Main Generator
# ---------------------------------------------------------------------------

def generate_tc_html(record: dict, css: str) -> str:
    """Generate the complete HTML document for a TC record."""
    tc_id = record.get("tc_id", "Unknown")
    title = record.get("title", "Unknown")
    project = record.get("project", "Unknown")
    status = record.get("status", "planned")
    scope = record.get("description", {}).get("scope", "feature")
    priority = record.get("priority", "medium")

    now_str = datetime.now(timezone.utc).astimezone().strftime("%Y-%m-%d %H:%M %Z").strip()

    # Read the template
    template_path = _SKILL_ROOT / "templates" / "tc_record_template.html"
    if template_path.exists():
        template = template_path.read_text(encoding="utf-8")
    else:
        # Minimal fallback
        template = (
            '<!DOCTYPE html><html lang="en"><head><meta charset="UTF-8">'
            '<meta name="viewport" content="width=device-width,initial-scale=1.0">'
            '<title>{{TC_ID}}</title><style>{{CSS}}</style></head>'
            '<body><div class="container"><main id="main-content">'
            '{{OVERVIEW_CONTENT}}{{FILES_CONTENT}}{{REVISIONS_CONTENT}}'
            '{{TESTS_CONTENT}}{{SESSION_CONTENT}}{{APPROVAL_CONTENT}}'
            '</main></div></body></html>'
        )

    # Build all sections
    replacements = {
        "{{CSS}}": css,
        "{{TC_ID}}": _esc(tc_id),
        "{{TITLE}}": _esc(title),
        "{{PROJECT}}": _esc(project),
        "{{STATUS}}": _esc(status),
        "{{STATUS_DISPLAY}}": _status_display(status),
        "{{SCOPE}}": _esc(scope),
        "{{PRIORITY}}": _esc(priority),
        "{{STATS_GRID}}": build_stats_grid(record),
        "{{OVERVIEW_CONTENT}}": build_overview(record),
        "{{FILES_CONTENT}}": build_files(record),
        "{{REVISIONS_CONTENT}}": build_revisions(record),
        "{{SUB_TCS_CONTENT}}": build_sub_tcs(record),
        "{{TESTS_CONTENT}}": build_tests(record),
        "{{SESSION_CONTENT}}": build_session(record),
        "{{APPROVAL_CONTENT}}": build_approval(record),
        "{{GENERATED_DATE}}": now_str,
    }

    html = template
    for placeholder, value in replacements.items():
        html = html.replace(placeholder, value)

    return html


# ---------------------------------------------------------------------------
# CLI Entry Point
# ---------------------------------------------------------------------------

def main() -> int:
    """CLI entry point."""
    if len(sys.argv) < 2:
        print("Usage: python generate_tc_html.py <tc_record.json> [--output <path>]")
        return 2

    input_path = Path(sys.argv[1])
    output_path = None

    if "--output" in sys.argv:
        idx = sys.argv.index("--output")
        if idx + 1 < len(sys.argv):
            output_path = Path(sys.argv[idx + 1])

    if not input_path.exists():
        print(f"ERROR: File not found: {input_path}")
        return 2

    try:
        with open(input_path, "r", encoding="utf-8") as f:
            record = json.load(f)
    except json.JSONDecodeError as e:
        print(f"ERROR: Invalid JSON: {e}")
        return 2

    # Validate
    errors = validate_tc_record(record)
    if errors:
        print(f"VALIDATION ERRORS ({len(errors)}):")
        for i, err in enumerate(errors, 1):
            print(f"  {i}. {err}")
        return 1

    # Generate
    css = _load_css()
    html = generate_tc_html(record, css)

    # Write output
    if output_path is None:
        output_path = input_path.parent / "tc_record.html"

    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, "w", encoding="utf-8") as f:
        f.write(html)

    print(f"Generated: {output_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
