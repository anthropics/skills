#!/usr/bin/env python3
"""
Google Workspace CLI Output Analyzer — Parse, filter, and aggregate JSON/NDJSON output.

Reads JSON arrays or NDJSON streams from stdin or file, applies filters,
projections, sorting, grouping, and outputs in table/csv/json format.

Usage:
    gws drive files list | python3 output_analyzer.py --count
    gws drive files list | python3 output_analyzer.py --filter "mimeType=application/pdf"
    gws drive files list | python3 output_analyzer.py --select "name,size" --format table
    python3 output_analyzer.py --input results.json --group-by "mimeType"
    python3 output_analyzer.py --demo --select "name,mimeType,size" --format table
"""

import argparse
import csv
import io
import json
import sys
from dataclasses import dataclass
from typing import List, Dict, Any, Optional


DEMO_DATA = [
    {"id": "1", "name": "Q1 Report.pdf", "mimeType": "application/pdf", "size": "245760",
     "modifiedTime": "2026-03-10T14:30:00Z", "shared": True, "owners": [{"displayName": "Alice"}]},
    {"id": "2", "name": "Budget 2026.xlsx", "mimeType": "application/vnd.google-apps.spreadsheet",
     "size": "0", "modifiedTime": "2026-03-09T09:15:00Z", "shared": True,
     "owners": [{"displayName": "Bob"}]},
    {"id": "3", "name": "Meeting Notes.docx", "mimeType": "application/vnd.google-apps.document",
     "size": "0", "modifiedTime": "2026-03-08T16:00:00Z", "shared": False,
     "owners": [{"displayName": "Alice"}]},
    {"id": "4", "name": "Logo.png", "mimeType": "image/png", "size": "102400",
     "modifiedTime": "2026-03-07T11:00:00Z", "shared": False,
     "owners": [{"displayName": "Charlie"}]},
    {"id": "5", "name": "Presentation.pptx", "mimeType": "application/vnd.google-apps.presentation",
     "size": "0", "modifiedTime": "2026-03-06T10:00:00Z", "shared": True,
     "owners": [{"displayName": "Alice"}]},
    {"id": "6", "name": "Invoice-001.pdf", "mimeType": "application/pdf", "size": "89000",
     "modifiedTime": "2026-03-05T08:30:00Z", "shared": False,
     "owners": [{"displayName": "Bob"}]},
    {"id": "7", "name": "Project Plan.xlsx", "mimeType": "application/vnd.google-apps.spreadsheet",
     "size": "0", "modifiedTime": "2026-03-04T13:45:00Z", "shared": True,
     "owners": [{"displayName": "Charlie"}]},
    {"id": "8", "name": "Contract Draft.docx", "mimeType": "application/vnd.google-apps.document",
     "size": "0", "modifiedTime": "2026-03-03T09:00:00Z", "shared": False,
     "owners": [{"displayName": "Alice"}]},
]


def read_input(input_file: Optional[str]) -> List[Dict[str, Any]]:
    """Read JSON array or NDJSON from file or stdin."""
    if input_file:
        with open(input_file, "r") as f:
            text = f.read().strip()
    else:
        if sys.stdin.isatty():
            return []
        text = sys.stdin.read().strip()

    if not text:
        return []

    # Try JSON array first
    try:
        data = json.loads(text)
        if isinstance(data, list):
            return data
        if isinstance(data, dict):
            # Some gws commands wrap results in a key
            for key in ("files", "messages", "events", "items", "results",
                        "spreadsheets", "spaces", "tasks", "users", "groups"):
                if key in data and isinstance(data[key], list):
                    return data[key]
            return [data]
    except json.JSONDecodeError:
        pass

    # Try NDJSON
    records = []
    for line in text.split("\n"):
        line = line.strip()
        if line:
            try:
                records.append(json.loads(line))
            except json.JSONDecodeError:
                continue
    return records


def get_nested(obj: Dict, path: str) -> Any:
    """Get a nested value by dot-separated path."""
    parts = path.split(".")
    current = obj
    for part in parts:
        if isinstance(current, dict):
            current = current.get(part)
        elif isinstance(current, list) and part.isdigit():
            idx = int(part)
            current = current[idx] if idx < len(current) else None
        else:
            return None
        if current is None:
            return None
    return current


def apply_filter(records: List[Dict], filter_expr: str) -> List[Dict]:
    """Filter records by field=value expression."""
    if "=" not in filter_expr:
        return records
    field_path, value = filter_expr.split("=", 1)
    result = []
    for rec in records:
        rec_val = get_nested(rec, field_path)
        if rec_val is None:
            continue
        rec_str = str(rec_val).lower()
        if rec_str == value.lower() or value.lower() in rec_str:
            result.append(rec)
    return result


def apply_select(records: List[Dict], fields: str) -> List[Dict]:
    """Project specific fields from records."""
    field_list = [f.strip() for f in fields.split(",")]
    result = []
    for rec in records:
        projected = {}
        for f in field_list:
            projected[f] = get_nested(rec, f)
        result.append(projected)
    return result


def apply_sort(records: List[Dict], sort_field: str, reverse: bool = False) -> List[Dict]:
    """Sort records by a field."""
    def sort_key(rec):
        val = get_nested(rec, sort_field)
        if val is None:
            return ""
        if isinstance(val, (int, float)):
            return val
        try:
            return float(val)
        except (ValueError, TypeError):
            return str(val).lower()
    return sorted(records, key=sort_key, reverse=reverse)


def apply_group_by(records: List[Dict], field: str) -> Dict[str, int]:
    """Group records by a field and count."""
    groups: Dict[str, int] = {}
    for rec in records:
        val = get_nested(rec, field)
        key = str(val) if val is not None else "(null)"
        groups[key] = groups.get(key, 0) + 1
    return dict(sorted(groups.items(), key=lambda x: x[1], reverse=True))


def compute_stats(records: List[Dict], field: str) -> Dict[str, Any]:
    """Compute min/max/avg/sum for a numeric field."""
    values = []
    for rec in records:
        val = get_nested(rec, field)
        if val is not None:
            try:
                values.append(float(val))
            except (ValueError, TypeError):
                continue
    if not values:
        return {"field": field, "count": 0, "error": "No numeric values found"}
    return {
        "field": field,
        "count": len(values),
        "min": min(values),
        "max": max(values),
        "sum": sum(values),
        "avg": sum(values) / len(values),
    }


def format_table(records: List[Dict]) -> str:
    """Format records as an aligned text table."""
    if not records:
        return "(no records)"

    headers = list(records[0].keys())
    # Calculate column widths
    widths = {h: len(h) for h in headers}
    for rec in records:
        for h in headers:
            val = str(rec.get(h, ""))
            if len(val) > 60:
                val = val[:57] + "..."
            widths[h] = max(widths[h], len(val))

    # Header
    header_line = "  ".join(h.ljust(widths[h]) for h in headers)
    sep_line = "  ".join("-" * widths[h] for h in headers)
    lines = [header_line, sep_line]

    # Rows
    for rec in records:
        row = []
        for h in headers:
            val = str(rec.get(h, ""))
            if len(val) > 60:
                val = val[:57] + "..."
            row.append(val.ljust(widths[h]))
        lines.append("  ".join(row))

    return "\n".join(lines)


def format_csv_output(records: List[Dict]) -> str:
    """Format records as CSV."""
    if not records:
        return ""
    output = io.StringIO()
    writer = csv.DictWriter(output, fieldnames=records[0].keys())
    writer.writeheader()
    writer.writerows(records)
    return output.getvalue()


def main():
    parser = argparse.ArgumentParser(
        description="Parse, filter, and aggregate JSON/NDJSON from gws CLI output",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  gws drive files list | %(prog)s --count
  gws drive files list | %(prog)s --filter "mimeType=pdf" --select "name,size"
  gws drive files list | %(prog)s --group-by "mimeType" --format table
  gws drive files list | %(prog)s --sort "size" --reverse --format table
  gws drive files list | %(prog)s --stats "size"
  %(prog)s --input results.json --select "name,mimeType" --format csv
  %(prog)s --demo --select "name,mimeType,size" --format table
        """,
    )
    parser.add_argument("--input", help="Input file (default: stdin)")
    parser.add_argument("--demo", action="store_true", help="Use demo data")
    parser.add_argument("--count", action="store_true", help="Count records")
    parser.add_argument("--filter", help="Filter by field=value")
    parser.add_argument("--select", help="Comma-separated fields to project")
    parser.add_argument("--sort", help="Sort by field")
    parser.add_argument("--reverse", action="store_true", help="Reverse sort order")
    parser.add_argument("--group-by", help="Group by field and count")
    parser.add_argument("--stats", help="Compute stats for a numeric field")
    parser.add_argument("--format", choices=["json", "table", "csv"], default="json",
                        help="Output format (default: json)")
    parser.add_argument("--json", action="store_true",
                        help="Shorthand for --format json")
    args = parser.parse_args()

    if args.json:
        args.format = "json"

    # Read input
    if args.demo:
        records = DEMO_DATA[:]
    else:
        records = read_input(args.input)

    if not records and not args.demo:
        # If no pipe input and no file, use demo
        records = DEMO_DATA[:]
        print("(No input detected, using demo data)\n", file=sys.stderr)

    # Apply operations in order
    if args.filter:
        records = apply_filter(records, args.filter)

    if args.sort:
        records = apply_sort(records, args.sort, args.reverse)

    # Count
    if args.count:
        if args.format == "json":
            print(json.dumps({"count": len(records)}))
        else:
            print(f"Count: {len(records)}")
        return

    # Group by
    if args.group_by:
        groups = apply_group_by(records, args.group_by)
        if args.format == "json":
            print(json.dumps(groups, indent=2))
        elif args.format == "csv":
            print(f"{args.group_by},count")
            for k, v in groups.items():
                print(f"{k},{v}")
        else:
            print(f"\n  Group by: {args.group_by}\n")
            for k, v in groups.items():
                print(f"  {k:<50} {v}")
            print(f"\n  Total groups: {len(groups)}")
        return

    # Stats
    if args.stats:
        stats = compute_stats(records, args.stats)
        if args.format == "json":
            print(json.dumps(stats, indent=2))
        else:
            print(f"\n  Stats for '{args.stats}':")
            for k, v in stats.items():
                if isinstance(v, float):
                    print(f"    {k}: {v:,.2f}")
                else:
                    print(f"    {k}: {v}")
        return

    # Select fields
    if args.select:
        records = apply_select(records, args.select)

    # Output
    if args.format == "json":
        print(json.dumps(records, indent=2))
    elif args.format == "csv":
        print(format_csv_output(records))
    else:
        print(f"\n{format_table(records)}\n")
        print(f"  ({len(records)} records)\n")


if __name__ == "__main__":
    main()
