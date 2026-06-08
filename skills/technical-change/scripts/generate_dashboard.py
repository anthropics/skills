#!/usr/bin/env python3
"""TC Dashboard HTML Generator — Converts tc_registry.json into a dashboard page.

Reads the TC registry and optionally all individual TC records to build an
interactive (CSS-only) dashboard with status metrics, filters, and activity feed.

Usage:
    python generate_dashboard.py <path_to_tc_registry.json> [--output <output_path.html>]

If --output is not specified, writes index.html in the same directory as the registry.

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

# Add parent dir to path for validator import
_SKILL_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_SKILL_ROOT / "validators"))

from validate_tc import validate_registry, VALID_STATUSES, VALID_SCOPES  # noqa: E402


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _esc(value) -> str:
    if value is None:
        return "—"
    return escape(str(value))


def _format_datetime(iso_str: str | None) -> str:
    if not iso_str:
        return "—"
    try:
        dt = datetime.fromisoformat(iso_str)
        return dt.strftime("%Y-%m-%d %H:%M").strip()
    except (ValueError, TypeError):
        return _esc(iso_str)


def _relative_time(iso_str: str | None) -> str:
    """Return a human-readable relative time string."""
    if not iso_str:
        return "—"
    try:
        dt = datetime.fromisoformat(iso_str)
        now = datetime.now(timezone.utc)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        diff = now - dt
        seconds = int(diff.total_seconds())
        if seconds < 60:
            return "just now"
        if seconds < 3600:
            m = seconds // 60
            return f"{m}m ago"
        if seconds < 86400:
            h = seconds // 3600
            return f"{h}h ago"
        d = seconds // 86400
        if d == 1:
            return "yesterday"
        if d < 30:
            return f"{d}d ago"
        return _format_datetime(iso_str)
    except (ValueError, TypeError):
        return _esc(iso_str)


def _status_display(status: str) -> str:
    return status.replace("_", " ").title()


def _load_css() -> str:
    css_path = _SKILL_ROOT / "templates" / "tc_styles.css"
    if css_path.exists():
        return css_path.read_text(encoding="utf-8")
    return "body { font-family: sans-serif; background: #0d0d18; color: #e0dcd0; }"


# ---------------------------------------------------------------------------
# Section Builders
# ---------------------------------------------------------------------------

def build_status_stats(stats: dict) -> str:
    """Build the 6 status stat cards."""
    by_status = stats.get("by_status", {})
    parts = []
    for status in VALID_STATUSES:
        count = by_status.get(status, 0)
        parts.append(
            f'<div class="stat-card">'
            f'<span class="stat-value">{count}</span>'
            f'<span class="stat-label"><span class="badge badge-{_esc(status)}">{_status_display(status)}</span></span>'
            f'</div>'
        )
    return "\n".join(parts)


def build_status_bar(stats: dict) -> tuple[str, str]:
    """Build the status distribution bar. Returns (html, aria_label)."""
    total = stats.get("total", 0)
    if total == 0:
        return '<div class="empty-state"><p>No TCs yet.</p></div>', "No technical changes"

    by_status = stats.get("by_status", {})
    parts = []
    aria_parts = []

    for status in VALID_STATUSES:
        count = by_status.get(status, 0)
        if count == 0:
            continue
        pct = (count / total) * 100
        label = _status_display(status)
        parts.append(
            f'<div class="status-bar-segment seg-{_esc(status)}" '
            f'style="flex-basis:{pct:.1f}%" '
            f'title="{label}: {count} ({pct:.0f}%)">'
            f'{count}'
            f'</div>'
        )
        aria_parts.append(f"{label}: {count} ({pct:.0f}%)")

    return "\n".join(parts), ", ".join(aria_parts)


def build_filter_radios() -> str:
    """Build the CSS-only filter radio buttons."""
    parts = ['<div class="filter-bar">']

    # All filter (default checked)
    parts.append('<input type="radio" name="filter" id="filter-all" checked>')
    parts.append('<label for="filter-all">All</label>')

    for status in VALID_STATUSES:
        safe = _esc(status)
        parts.append(f'<input type="radio" name="filter" id="filter-{safe}">')
        parts.append(f'<label for="filter-{safe}">{_status_display(status)}</label>')

    parts.append('</div>')
    return "\n".join(parts)


def build_tc_cards(records: list[dict], tc_root: Path | None = None) -> str:
    """Build the TC card list."""
    if not records:
        return '<div class="empty-state"><p>No technical changes yet. Use /tc create to start tracking.</p></div>'

    # Sort by updated descending
    sorted_records = sorted(records, key=lambda r: r.get("updated", ""), reverse=True)

    parts = []
    for rec in sorted_records:
        tc_id = rec.get("tc_id", "")
        status = rec.get("status", "planned")
        scope = rec.get("scope", "feature")
        priority = rec.get("priority", "medium")
        title = rec.get("title", "")
        path = rec.get("path", "")

        # Build link to tc_record.html
        href = f"{path}/tc_record.html" if path else "#"

        # Test summary
        ts = rec.get("test_summary", {})
        test_str = ""
        if ts.get("total", 0) > 0:
            test_str = f'Tests: {ts.get("pass", 0)}/{ts.get("total", 0)} pass'

        parts.append(
            f'<div class="tc-card" data-status="{_esc(status)}">'
            f'<a href="{_esc(href)}">'
            f'<div class="tc-card-header">'
            f'<div>'
            f'<div class="tc-card-id">{_esc(tc_id)}</div>'
            f'<div class="tc-card-title">{_esc(title)}</div>'
            f'</div>'
            f'<span class="badge badge-{_esc(status)}">{_status_display(status)}</span>'
            f'</div>'
            f'<div class="tc-card-meta">'
            f'<span class="badge badge-{_esc(scope)}">{_esc(scope)}</span>'
            f'<span class="badge badge-{_esc(priority)}">{_esc(priority)}</span>'
            f'<span>Updated: {_relative_time(rec.get("updated"))}</span>'
        )
        if test_str:
            parts.append(f'<span>{_esc(test_str)}</span>')
        if rec.get("sub_tc_count", 0) > 0:
            parts.append(f'<span>Sub-TCs: {rec["sub_tc_count"]}</span>')

        parts.append(f'</div></a></div>')

    return "\n".join(parts)


def build_activity_feed(tc_root: Path | None, records: list[dict]) -> str:
    """Build the recent activity feed from revision histories."""
    if not tc_root or not records:
        return '<div class="empty-state"><p>No activity yet.</p></div>'

    # Collect recent revisions across all TCs
    activities: list[tuple[str, str, str, str]] = []  # (timestamp, tc_id, revision_id, summary)

    for rec in records:
        tc_id = rec.get("tc_id", "")
        path = rec.get("path", "")
        record_path = tc_root / path / "tc_record.json"

        if record_path.exists():
            try:
                with open(record_path, "r", encoding="utf-8") as f:
                    full_record = json.load(f)
                for rev in full_record.get("revision_history", []):
                    activities.append((
                        rev.get("timestamp", ""),
                        tc_id,
                        rev.get("revision_id", ""),
                        rev.get("summary", ""),
                    ))
            except (json.JSONDecodeError, OSError):
                pass

    if not activities:
        return '<div class="empty-state"><p>No activity recorded yet.</p></div>'

    # Sort by timestamp descending, take last 10
    activities.sort(key=lambda x: x[0], reverse=True)
    activities = activities[:10]

    parts = []
    for ts, tc_id, rev_id, summary in activities:
        parts.append(
            f'<div class="activity-item">'
            f'<span class="activity-time">{_relative_time(ts)}</span>'
            f'<span class="activity-text">'
            f'<strong>{_esc(tc_id)}</strong> {_esc(rev_id)}: {_esc(summary)}'
            f'</span>'
            f'</div>'
        )

    return "\n".join(parts)


def build_scope_stats(stats: dict) -> str:
    """Build scope breakdown stat cards."""
    by_scope = stats.get("by_scope", {})
    parts = []
    for scope in VALID_SCOPES:
        count = by_scope.get(scope, 0)
        if count > 0:
            parts.append(
                f'<div class="stat-card">'
                f'<span class="stat-value">{count}</span>'
                f'<span class="stat-label"><span class="badge badge-{_esc(scope)}">{_esc(scope)}</span></span>'
                f'</div>'
            )
    if not parts:
        return '<div class="empty-state"><p>No scope data.</p></div>'
    return "\n".join(parts)


# ---------------------------------------------------------------------------
# Main Generator
# ---------------------------------------------------------------------------

def generate_dashboard_html(registry: dict, css: str, tc_root: Path | None = None) -> str:
    """Generate the complete dashboard HTML."""
    project = registry.get("project_name", "Project")
    total = registry.get("statistics", {}).get("total", 0)
    records = registry.get("records", [])
    stats = registry.get("statistics", {})

    now_str = datetime.now(timezone.utc).astimezone().strftime("%Y-%m-%d %H:%M %Z").strip()

    status_bar_html, status_bar_aria = build_status_bar(stats)

    # Read the template
    template_path = _SKILL_ROOT / "templates" / "tc_dashboard_template.html"
    if template_path.exists():
        template = template_path.read_text(encoding="utf-8")
    else:
        template = (
            '<!DOCTYPE html><html lang="en"><head><meta charset="UTF-8">'
            '<title>{{PROJECT}} — TC Dashboard</title><style>{{CSS}}</style></head>'
            '<body><div class="container"><main id="main-content">'
            '{{STATUS_STATS}}{{TC_CARDS}}'
            '</main></div></body></html>'
        )

    replacements = {
        "{{CSS}}": css,
        "{{PROJECT}}": _esc(project),
        "{{TOTAL_TCS}}": str(total),
        "{{LAST_UPDATED}}": now_str,
        "{{STATUS_STATS}}": build_status_stats(stats),
        "{{STATUS_BAR}}": status_bar_html,
        "{{STATUS_BAR_ARIA}}": status_bar_aria,
        "{{FILTER_RADIOS}}": build_filter_radios(),
        "{{TC_CARDS}}": build_tc_cards(records, tc_root),
        "{{ACTIVITY_FEED}}": build_activity_feed(tc_root, records),
        "{{SCOPE_STATS}}": build_scope_stats(stats),
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
        print("Usage: python generate_dashboard.py <tc_registry.json> [--output <path>]")
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
            registry = json.load(f)
    except json.JSONDecodeError as e:
        print(f"ERROR: Invalid JSON: {e}")
        return 2

    # Validate
    errors = validate_registry(registry)
    if errors:
        print(f"VALIDATION ERRORS ({len(errors)}):")
        for i, err in enumerate(errors, 1):
            print(f"  {i}. {err}")
        return 1

    # Generate
    css = _load_css()
    tc_root = input_path.parent
    html = generate_dashboard_html(registry, css, tc_root)

    # Write output
    if output_path is None:
        output_path = input_path.parent / "index.html"

    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, "w", encoding="utf-8") as f:
        f.write(html)

    print(f"Generated: {output_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
