#!/usr/bin/env python3
"""Scaffold PRD directory structure from frontend_analyzer.py output.

Reads analysis JSON and creates the prd/ directory with README.md,
per-page stubs, and appendix files pre-populated with extracted data.

Stdlib only — no third-party dependencies.

Usage:
    python3 frontend_analyzer.py /path/to/project -o analysis.json
    python3 prd_scaffolder.py analysis.json
    python3 prd_scaffolder.py analysis.json --output-dir ./prd --project-name "My App"
"""

import argparse
import json
import re
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, Optional
from pathlib import Path
from typing import Any, Dict, List


def slugify(text: str) -> str:
    """Convert text to a filename-safe slug."""
    text = text.strip().lower()
    text = re.sub(r"[/:{}*?\"<>|]", "-", text)
    text = re.sub(r"[^a-z0-9\-]", "-", text)
    text = re.sub(r"-+", "-", text)
    return text.strip("-")


def route_to_page_name(route: str) -> str:
    """Convert a route path to a human-readable page name."""
    if route == "/" or route == "":
        return "Home"
    parts = route.strip("/").split("/")
    # Remove dynamic segments for naming
    clean = [p for p in parts if not p.startswith(":") and not p.startswith("*")]
    if not clean:
        clean = [p.lstrip(":*") for p in parts]
    return " ".join(w.capitalize() for w in "-".join(clean).replace("_", "-").split("-"))


def generate_readme(project_name: str, routes: List[Dict], summary: Dict, date: str) -> str:
    """Generate the PRD README.md."""
    lines = [
        f"# {project_name} — Product Requirements Document",
        "",
        f"> Generated: {date}",
        "",
        "## System Overview",
        "",
        f"<!-- TODO: Describe what {project_name} does, its business context, and primary users -->",
        "",
        "## Summary",
        "",
        f"| Metric | Count |",
        f"|--------|-------|",
        f"| Pages | {summary.get('pages', 0)} |",
        f"| API Endpoints | {summary.get('api_endpoints', 0)} |",
        f"| Integrated APIs | {summary.get('api_integrated', 0)} |",
        f"| Mock APIs | {summary.get('api_mock', 0)} |",
        f"| Enums/Constants | {summary.get('enums', 0)} |",
        f"| i18n | {'Yes' if summary.get('has_i18n') else 'No'} |",
        f"| State Management | {'Yes' if summary.get('has_state_management') else 'No'} |",
        "",
        "## Module Overview",
        "",
        "| Module | Pages | Core Functionality |",
        "|--------|-------|--------------------|",
        "| <!-- TODO: Group pages into modules --> | | |",
        "",
        "## Page Inventory",
        "",
        "| # | Page Name | Route | Module | Doc Link |",
        "|---|-----------|-------|--------|----------|",
    ]

    for i, route in enumerate(routes, 1):
        path = route.get("path", "/")
        name = route_to_page_name(path)
        slug = slugify(name) or f"page-{i}"
        filename = f"{i:02d}-{slug}.md"
        lines.append(f"| {i} | {name} | `{path}` | <!-- TODO --> | [→](./pages/{filename}) |")

    lines.extend([
        "",
        "## Global Notes",
        "",
        "### Permission Model",
        "<!-- TODO: Summarize auth/role system if present -->",
        "",
        "### Common Interaction Patterns",
        "<!-- TODO: Global rules — delete confirmations, default sort, etc. -->",
        "",
    ])

    return "\n".join(lines)


def generate_page_stub(route: Dict, index: int, date: str) -> str:
    """Generate a per-page PRD stub."""
    path = route.get("path", "/")
    name = route_to_page_name(path)
    source = route.get("source", "unknown")

    return f"""# {name}

> **Route:** `{path}`
> **Module:** <!-- TODO -->
> **Source:** `{source}`
> **Generated:** {date}

## Overview
<!-- TODO: 2-3 sentences — core function and use case -->

## Layout
<!-- TODO: Region breakdown — search area, table, detail panel, action bar, etc. -->

## Fields

### Search / Filters
| Field | Type | Required | Options / Enum | Default | Notes |
|-------|------|----------|---------------|---------|-------|
| <!-- TODO --> | | | | | |

### Data Table
| Column | Format | Sortable | Filterable | Notes |
|--------|--------|----------|-----------|-------|
| <!-- TODO --> | | | | |

### Actions
| Button | Visibility Condition | Behavior |
|--------|---------------------|----------|
| <!-- TODO --> | | |

## Interactions

### Page Load
<!-- TODO: What happens on mount — default queries, preloaded data -->

### Search
- **Trigger:** <!-- TODO -->
- **Behavior:** <!-- TODO -->
- **Special rules:** <!-- TODO -->

### Create / Edit
- **Trigger:** <!-- TODO -->
- **Modal/drawer content:** <!-- TODO -->
- **Validation:** <!-- TODO -->
- **On success:** <!-- TODO -->

### Delete
- **Trigger:** <!-- TODO -->
- **Confirmation:** <!-- TODO -->
- **On success:** <!-- TODO -->

## API Dependencies

| API | Method | Path | Trigger | Integrated | Notes |
|-----|--------|------|---------|-----------|-------|
| <!-- TODO --> | | | | | |

## Page Relationships
- **From:** <!-- TODO: Source pages + params -->
- **To:** <!-- TODO: Target pages + params -->
- **Data coupling:** <!-- TODO: Cross-page refresh triggers -->

## Business Rules
<!-- TODO: Anything that doesn't fit above -->
"""


def generate_enum_dictionary(enums: List[Dict]) -> str:
    """Generate the enum dictionary appendix."""
    lines = [
        "# Enum & Constant Dictionary",
        "",
        "All enums, status codes, and type mappings extracted from the codebase.",
        "",
    ]

    if not enums:
        lines.append("*No enums detected. Manual review recommended.*")
        return "\n".join(lines)

    for e in enums:
        lines.append(f"## {e['name']}")
        lines.append(f"**Type:** {e.get('type', 'unknown')} | **Source:** `{e.get('source', 'unknown').split('/')[-1]}`")
        lines.append("")
        if e.get("values"):
            lines.append("| Key | Value |")
            lines.append("|-----|-------|")
            for k, v in e["values"].items():
                lines.append(f"| `{k}` | {v} |")
        lines.append("")

    return "\n".join(lines)


def generate_api_inventory(apis: List[Dict]) -> str:
    """Generate the API inventory appendix."""
    lines = [
        "# API Inventory",
        "",
        "All API endpoints detected in the codebase.",
        "",
    ]

    if not apis:
        lines.append("*No API calls detected. Manual review recommended.*")
        return "\n".join(lines)

    integrated = [a for a in apis if a.get("integrated")]
    mocked = [a for a in apis if a.get("mock_detected") and not a.get("integrated")]
    unknown = [a for a in apis if not a.get("integrated") and not a.get("mock_detected")]

    for label, group in [("Integrated APIs", integrated), ("Mock / Stub APIs", mocked), ("Unknown Status", unknown)]:
        if group:
            lines.append(f"## {label}")
            lines.append("")
            lines.append("| Method | Path | Source | Notes |")
            lines.append("|--------|------|--------|-------|")
            for a in group:
                src = a.get("source", "").split("/")[-1]
                lines.append(f"| {a.get('method', '?')} | `{a.get('path', '?')}` | {src} | |")
            lines.append("")

    return "\n".join(lines)


def generate_page_relationships(routes: List[Dict]) -> str:
    """Generate page relationships appendix stub."""
    lines = [
        "# Page Relationships",
        "",
        "Navigation flow and data coupling between pages.",
        "",
        "## Navigation Map",
        "",
        "<!-- TODO: Fill in after page-by-page analysis -->",
        "",
        "```",
        "Home",
    ]

    for r in routes[:20]:  # Cap at 20 for readability
        name = route_to_page_name(r.get("path", "/"))
        lines.append(f"  ├── {name}")

    if len(routes) > 20:
        lines.append(f"  └── ... ({len(routes) - 20} more)")

    lines.extend([
        "```",
        "",
        "## Cross-Page Data Dependencies",
        "",
        "| Source Page | Target Page | Trigger | Data Passed |",
        "|-----------|------------|---------|------------|",
        "| <!-- TODO --> | | | |",
        "",
    ])

    return "\n".join(lines)


def scaffold(analysis: Dict[str, Any], output_dir: Path, project_name: Optional[str] = None):
    """Create the full PRD directory structure."""
    date = datetime.now().strftime("%Y-%m-%d")
    name = project_name or analysis.get("project", {}).get("name", "Project")
    routes = analysis.get("routes", {}).get("pages", [])
    apis = analysis.get("apis", {}).get("endpoints", [])
    enums = analysis.get("enums", {}).get("definitions", [])
    summary = analysis.get("summary", {})

    # Create directories
    pages_dir = output_dir / "pages"
    appendix_dir = output_dir / "appendix"
    pages_dir.mkdir(parents=True, exist_ok=True)
    appendix_dir.mkdir(parents=True, exist_ok=True)

    # README.md
    readme = generate_readme(name, routes, summary, date)
    (output_dir / "README.md").write_text(readme)
    print(f"  Created: README.md")

    # Per-page stubs
    for i, route in enumerate(routes, 1):
        page_name = route_to_page_name(route.get("path", "/"))
        slug = slugify(page_name) or f"page-{i}"
        filename = f"{i:02d}-{slug}.md"
        content = generate_page_stub(route, i, date)
        (pages_dir / filename).write_text(content)
        print(f"  Created: pages/{filename}")

    # Appendix
    (appendix_dir / "enum-dictionary.md").write_text(generate_enum_dictionary(enums))
    print(f"  Created: appendix/enum-dictionary.md")

    (appendix_dir / "api-inventory.md").write_text(generate_api_inventory(apis))
    print(f"  Created: appendix/api-inventory.md")

    (appendix_dir / "page-relationships.md").write_text(generate_page_relationships(routes))
    print(f"  Created: appendix/page-relationships.md")

    print(f"\n✅ PRD scaffold complete: {output_dir}")
    print(f"   {len(routes)} page stubs, {len(apis)} API endpoints, {len(enums)} enums")
    print(f"\n   Next: Review each page stub and fill in the TODO sections.")


def validate_analysis(analysis: Dict[str, Any]) -> List[str]:
    """Validate analysis JSON has the required structure. Returns list of errors."""
    errors = []

    if not isinstance(analysis, dict):
        return ["Analysis must be a JSON object"]

    if "error" in analysis:
        errors.append(f"Analysis contains error: {analysis['error']}")

    required_keys = ["project", "routes", "apis"]
    for key in required_keys:
        if key not in analysis:
            errors.append(f"Missing required key: '{key}'")

    if "project" in analysis:
        proj = analysis["project"]
        if not isinstance(proj, dict):
            errors.append("'project' must be an object")
        elif "framework" not in proj:
            errors.append("'project.framework' is missing")

    if "routes" in analysis:
        routes = analysis["routes"]
        if not isinstance(routes, dict):
            errors.append("'routes' must be an object")
        elif "pages" not in routes and "frontend_pages" not in routes and "backend_endpoints" not in routes:
            errors.append("'routes' must contain 'pages', 'frontend_pages', or 'backend_endpoints'")

    if "apis" in analysis:
        apis = analysis["apis"]
        if not isinstance(apis, dict):
            errors.append("'apis' must be an object")
        elif "endpoints" not in apis:
            errors.append("'apis.endpoints' is missing")

    return errors


def print_summary(output_dir: Path, analysis: Dict[str, Any]):
    """Print a structured summary of what was generated."""
    routes = analysis.get("routes", {}).get("pages", [])
    apis = analysis.get("apis", {}).get("endpoints", [])
    enums = analysis.get("enums", {}).get("definitions", [])
    models = analysis.get("models", {}).get("definitions", [])
    summary = analysis.get("summary", {})
    stack = summary.get("stack_type", "unknown")

    print(f"\nPRD scaffold complete: {output_dir}/")
    print(f"  Stack type:     {stack}")
    print(f"  Page stubs:     {len(routes)}")
    print(f"  API endpoints:  {len(apis)}")
    print(f"  Enums:          {len(enums)}")
    if models:
        print(f"  Models:         {len(models)}")
    print(f"\n  Next: Review each page stub and fill in the TODO sections.")


def main():
    parser = argparse.ArgumentParser(
        description="Scaffold PRD directory from codebase analysis"
    )
    parser.add_argument("analysis", help="Path to analysis JSON from codebase_analyzer.py")
    parser.add_argument("-o", "--output-dir", default="prd", help="Output directory (default: prd/)")
    parser.add_argument("-n", "--project-name", help="Override project name")
    parser.add_argument("--validate-only", action="store_true",
                        help="Validate analysis JSON without generating files")
    parser.add_argument("--dry-run", action="store_true",
                        help="Show what would be created without writing files")
    args = parser.parse_args()

    analysis_path = Path(args.analysis)
    if not analysis_path.exists():
        print(f"Error: Analysis file not found: {analysis_path}")
        raise SystemExit(2)

    try:
        with open(analysis_path) as f:
            analysis = json.load(f)
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON in {analysis_path}: {e}")
        raise SystemExit(2)

    # Validate
    errors = validate_analysis(analysis)
    if errors:
        print(f"Validation errors in {analysis_path}:")
        for err in errors:
            print(f"  - {err}")
        raise SystemExit(1)

    if args.validate_only:
        print(f"Analysis file is valid: {analysis_path}")
        routes = analysis.get("routes", {}).get("pages", [])
        print(f"  {len(routes)} routes, "
              f"{len(analysis.get('apis', {}).get('endpoints', []))} APIs, "
              f"{len(analysis.get('enums', {}).get('definitions', []))} enums")
        return

    output_dir = Path(args.output_dir)

    if args.dry_run:
        routes = analysis.get("routes", {}).get("pages", [])
        print(f"Dry run — would create in {output_dir}/:\n")
        print(f"  {output_dir}/README.md")
        for i, route in enumerate(routes, 1):
            name = route_to_page_name(route.get("path", "/"))
            slug = slugify(name) or f"page-{i}"
            print(f"  {output_dir}/pages/{i:02d}-{slug}.md")
        print(f"  {output_dir}/appendix/enum-dictionary.md")
        print(f"  {output_dir}/appendix/api-inventory.md")
        print(f"  {output_dir}/appendix/page-relationships.md")
        print(f"\n  Total: {len(routes) + 4} files")
        return

    print(f"Scaffolding PRD in {output_dir}/...\n")
    scaffold(analysis, output_dir, args.project_name)
    print_summary(output_dir, analysis)


if __name__ == "__main__":
    main()
