#!/usr/bin/env python3
"""Report CLI — file organization, indexing, and opening for Claude session reports."""

import argparse
import json
import os
import platform
import re
import subprocess
import sys
from datetime import datetime, timedelta
from pathlib import Path

REPORTS_DIR = Path.home() / "claude-reports"
INDEX_FILE = REPORTS_DIR / "index.json"


def slugify(text: str) -> str:
    """Convert text to URL-friendly slug."""
    text = text.lower().strip()
    text = re.sub(r'[^\w\s-]', '', text)
    text = re.sub(r'[\s_]+', '-', text)
    text = re.sub(r'-+', '-', text)
    return text[:60].strip('-')


def get_path(project: str, title: str, report_type: str) -> str:
    """Generate report file path and ensure directories exist."""
    now = datetime.now()
    date_str = now.strftime("%Y-%m-%d")
    time_str = now.strftime("%H%M%S")
    slug = slugify(title)

    report_dir = REPORTS_DIR / project / date_str
    report_dir.mkdir(parents=True, exist_ok=True)

    filename = f"{time_str}-{slug}.html"
    return str(report_dir / filename)


def load_index() -> list:
    """Load index.json, return empty list on failure."""
    try:
        if INDEX_FILE.exists():
            return json.loads(INDEX_FILE.read_text())
    except Exception:
        pass
    return []


def save_index(entries: list) -> None:
    """Save index.json."""
    REPORTS_DIR.mkdir(parents=True, exist_ok=True)
    INDEX_FILE.write_text(json.dumps(entries, indent=2))


def extract_meta_from_html(filepath: Path) -> dict:
    """Extract report metadata from HTML file."""
    meta = {"title": filepath.stem, "type": "task-completion"}
    try:
        content = filepath.read_text()
        # Try embedded JSON metadata first
        json_match = re.search(r'<script[^>]*id="report-meta"[^>]*>(.*?)</script>', content, re.DOTALL)
        if json_match:
            data = json.loads(json_match.group(1))
            meta.update(data)
            return meta
        # Fall back to meta tags
        for tag in re.finditer(r'<meta\s+name="report-(\w+)"\s+content="([^"]*)"', content):
            meta[tag.group(1)] = tag.group(2)
        # Try title tag
        title_match = re.search(r'<title>(.*?)</title>', content)
        if title_match:
            meta["title"] = title_match.group(1)
    except Exception:
        pass
    return meta


def add_to_index(filepath: str) -> None:
    """Add a report to the index."""
    path = Path(filepath)
    if not path.exists():
        return

    rel = path.relative_to(REPORTS_DIR)
    parts = rel.parts  # project/date/filename.html
    if len(parts) < 3:
        return

    project = parts[0]
    date_str = parts[1]
    time_str = path.stem.split('-')[0] if '-' in path.stem else "000000"

    meta = extract_meta_from_html(path)

    entry = {
        "path": str(rel),
        "project": project,
        "title": meta.get("title", path.stem),
        "type": meta.get("type", "task-completion"),
        "date": date_str,
        "time": f"{time_str[:2]}:{time_str[2:4]}:{time_str[4:6]}" if len(time_str) >= 6 else time_str,
    }

    entries = load_index()
    # Remove existing entry for same path
    entries = [e for e in entries if e.get("path") != str(rel)]
    entries.append(entry)
    # Sort by date+time descending
    entries.sort(key=lambda e: (e.get("date", ""), e.get("time", "")), reverse=True)
    save_index(entries)


def open_report(filepath: str) -> None:
    """Open report in browser (cross-platform)."""
    path = Path(filepath)
    if not path.exists():
        print(f"Error: {filepath} not found", file=sys.stderr)
        sys.exit(1)

    # Add to index
    try:
        if path.is_relative_to(REPORTS_DIR):
            add_to_index(filepath)
    except Exception:
        pass

    # Open in browser — cross-platform
    system = platform.system()
    if system == "Darwin":
        subprocess.run(["open", str(path)], check=False)
    elif system == "Linux":
        subprocess.run(["xdg-open", str(path)], check=False)
    elif system == "Windows":
        os.startfile(str(path))
    else:
        print(f"Auto-open not supported on {system}. Open manually: {path}")
        return

    print(f"Opened: {path.name}")


def list_reports(project: str = None, report_type: str = None, days: int = 30) -> None:
    """List reports as JSON, filtered by project/type/days."""
    entries = load_index()

    # If index is empty or corrupt, rebuild
    if not entries:
        rebuild_index()
        entries = load_index()

    cutoff = (datetime.now() - timedelta(days=days)).strftime("%Y-%m-%d")

    filtered = []
    for e in entries:
        if e.get("date", "") < cutoff:
            continue
        if project and e.get("project") != project:
            continue
        if report_type and e.get("type") != report_type:
            continue
        filtered.append(e)

    print(json.dumps(filtered, indent=2))


def rebuild_index() -> None:
    """Rebuild index.json from disk scan."""
    entries = []
    if not REPORTS_DIR.exists():
        save_index(entries)
        return

    for html_file in sorted(REPORTS_DIR.rglob("*.html"), reverse=True):
        try:
            rel = html_file.relative_to(REPORTS_DIR)
            parts = rel.parts
            if len(parts) < 3:
                continue

            project = parts[0]
            date_str = parts[1]
            time_str = html_file.stem.split('-')[0] if '-' in html_file.stem else "000000"
            meta = extract_meta_from_html(html_file)

            entries.append({
                "path": str(rel),
                "project": project,
                "title": meta.get("title", html_file.stem),
                "type": meta.get("type", "task-completion"),
                "date": date_str,
                "time": f"{time_str[:2]}:{time_str[2:4]}:{time_str[4:6]}" if len(time_str) >= 6 else time_str,
            })
        except Exception:
            continue

    entries.sort(key=lambda e: (e.get("date", ""), e.get("time", "")), reverse=True)
    save_index(entries)
    print(f"Indexed {len(entries)} reports")


def main():
    parser = argparse.ArgumentParser(description="Report CLI for Claude sessions")
    parser.add_argument("--path", action="store_true", help="Generate report file path")
    parser.add_argument("--open", metavar="FILE", help="Open report in browser")
    parser.add_argument("--list", action="store_true", help="List reports as JSON")
    parser.add_argument("--index", action="store_true", help="Rebuild index from disk")
    parser.add_argument("--project", help="Project name")
    parser.add_argument("--title", help="Report title")
    parser.add_argument("--type", dest="report_type", help="Report type",
                       choices=["task-completion", "research", "audit", "error-blocker", "comparison"])
    parser.add_argument("--days", type=int, default=30, help="Days to look back (default: 30)")

    args = parser.parse_args()

    if args.path:
        if not args.project or not args.title or not args.report_type:
            parser.error("--path requires --project, --title, and --type")
        print(get_path(args.project, args.title, args.report_type))
    elif args.open:
        open_report(args.open)
    elif args.list:
        list_reports(args.project, args.report_type, args.days)
    elif args.index:
        rebuild_index()
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
