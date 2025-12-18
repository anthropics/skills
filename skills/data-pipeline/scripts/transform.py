#!/usr/bin/env python3
"""
Data Transformation Script

Transform data between formats (JSON, CSV, Markdown) with filtering,
field selection, and basic transformations.
"""

import argparse
import json
import sys
from pathlib import Path


def load_data(file_path: str) -> tuple[list, str]:
    """Load data from JSON or CSV file."""
    path = Path(file_path)

    if not path.exists():
        raise FileNotFoundError(f"File not found: {file_path}")

    suffix = path.suffix.lower()

    if suffix == ".json":
        with open(path) as f:
            data = json.load(f)

        # Handle nested data structures
        if isinstance(data, dict):
            if "results" in data:
                data = data["results"]
            elif "data" in data:
                data = data["data"]
            elif "items" in data:
                data = data["items"]

        return data if isinstance(data, list) else [data], "json"

    elif suffix == ".csv":
        import csv

        with open(path, newline="") as f:
            reader = csv.DictReader(f)
            data = list(reader)
        return data, "csv"

    else:
        raise ValueError(f"Unsupported file type: {suffix}")


def filter_records(data: list, filters: dict) -> list:
    """Filter records based on field conditions.

    Supports operators: =, !=, >, <, >=, <=, contains, startswith, endswith
    """
    if not filters:
        return data

    filtered = []

    for record in data:
        match = True

        for field, condition in filters.items():
            value = record.get(field)

            # Parse operator from condition
            if condition.startswith("!="):
                op, target = "!=", condition[2:]
            elif condition.startswith(">="):
                op, target = ">=", condition[2:]
            elif condition.startswith("<="):
                op, target = "<=", condition[2:]
            elif condition.startswith(">"):
                op, target = ">", condition[1:]
            elif condition.startswith("<"):
                op, target = "<", condition[1:]
            elif condition.startswith("~"):  # contains
                op, target = "contains", condition[1:]
            elif condition.startswith("^"):  # startswith
                op, target = "startswith", condition[1:]
            elif condition.startswith("$"):  # endswith
                op, target = "endswith", condition[1:]
            else:
                op, target = "=", condition

            # Convert target to appropriate type
            str_value = str(value) if value is not None else ""

            try:
                if op in [">", "<", ">=", "<="]:
                    num_value = float(value) if value else 0
                    num_target = float(target)
            except (ValueError, TypeError):
                num_value = 0
                num_target = 0

            # Apply operator
            if op == "=" and str_value != target:
                match = False
            elif op == "!=" and str_value == target:
                match = False
            elif op == ">" and num_value <= num_target:
                match = False
            elif op == "<" and num_value >= num_target:
                match = False
            elif op == ">=" and num_value < num_target:
                match = False
            elif op == "<=" and num_value > num_target:
                match = False
            elif op == "contains" and target.lower() not in str_value.lower():
                match = False
            elif op == "startswith" and not str_value.lower().startswith(
                target.lower()
            ):
                match = False
            elif op == "endswith" and not str_value.lower().endswith(target.lower()):
                match = False

        if match:
            filtered.append(record)

    return filtered


def select_fields(data: list, fields: list) -> list:
    """Select specific fields from records."""
    if not fields:
        return data

    return [
        {field: record.get(field) for field in fields if field in record}
        for record in data
    ]


def rename_fields(data: list, renames: dict) -> list:
    """Rename fields in records."""
    if not renames:
        return data

    result = []
    for record in data:
        new_record = {}
        for key, value in record.items():
            new_key = renames.get(key, key)
            new_record[new_key] = value
        result.append(new_record)

    return result


def sort_records(data: list, sort_field: str, reverse: bool = False) -> list:
    """Sort records by a field."""
    if not sort_field:
        return data

    def sort_key(record):
        value = record.get(sort_field)
        if value is None:
            return (1, "")  # Nulls last
        try:
            return (0, float(value))
        except (ValueError, TypeError):
            return (0, str(value).lower())

    return sorted(data, key=sort_key, reverse=reverse)


def limit_records(data: list, limit: int = None, offset: int = 0) -> list:
    """Limit and offset records."""
    if offset:
        data = data[offset:]
    if limit:
        data = data[:limit]
    return data


def to_json(data: list, pretty: bool = True) -> str:
    """Convert data to JSON."""
    indent = 2 if pretty else None
    return json.dumps(data, indent=indent, default=str)


def to_csv(data: list) -> str:
    """Convert data to CSV."""
    if not data:
        return ""

    # Get all headers
    headers = []
    for record in data:
        for key in record.keys():
            if key not in headers:
                headers.append(key)

    lines = [",".join(headers)]

    for record in data:
        values = []
        for header in headers:
            value = record.get(header, "")
            # Escape and quote values
            str_value = str(value) if value is not None else ""
            if "," in str_value or '"' in str_value or "\n" in str_value:
                str_value = '"' + str_value.replace('"', '""') + '"'
            values.append(str_value)
        lines.append(",".join(values))

    return "\n".join(lines)


def to_markdown(data: list, title: str = None) -> str:
    """Convert data to markdown table."""
    if not data:
        return "No data"

    # Get headers
    headers = list(data[0].keys())

    lines = []

    if title:
        lines.append(f"# {title}")
        lines.append("")

    # Table header
    lines.append("| " + " | ".join(headers) + " |")
    lines.append("| " + " | ".join(["---"] * len(headers)) + " |")

    # Table rows
    for record in data[:100]:  # Limit rows
        values = []
        for header in headers:
            value = record.get(header, "")
            str_value = str(value)[:50] if value else ""  # Truncate
            str_value = str_value.replace("|", "\\|").replace("\n", " ")
            values.append(str_value)
        lines.append("| " + " | ".join(values) + " |")

    if len(data) > 100:
        lines.append(f"\n*... and {len(data) - 100} more records*")

    return "\n".join(lines)


def transform_data(
    file_path: str,
    to_format: str = "json",
    filters: dict = None,
    fields: list = None,
    renames: dict = None,
    sort_by: str = None,
    reverse: bool = False,
    limit: int = None,
    offset: int = 0,
    title: str = None,
    verbose: bool = False,
) -> str:
    """Apply transformations and convert format."""

    # Load
    data, source_format = load_data(file_path)

    if verbose:
        print(f"[INFO] Loaded {len(data)} records from {source_format}")

    # Transform
    if filters:
        data = filter_records(data, filters)
        if verbose:
            print(f"[INFO] After filter: {len(data)} records")

    if fields:
        data = select_fields(data, fields)
        if verbose:
            print(f"[INFO] Selected fields: {fields}")

    if renames:
        data = rename_fields(data, renames)
        if verbose:
            print(f"[INFO] Renamed fields: {renames}")

    if sort_by:
        data = sort_records(data, sort_by, reverse)
        if verbose:
            print(f"[INFO] Sorted by: {sort_by} {'(desc)' if reverse else '(asc)'}")

    data = limit_records(data, limit, offset)
    if verbose and (limit or offset):
        print(f"[INFO] Limit: {limit}, Offset: {offset}")

    # Convert
    if to_format == "json":
        return to_json(data)
    elif to_format == "csv":
        return to_csv(data)
    elif to_format == "markdown":
        return to_markdown(data, title)
    else:
        raise ValueError(f"Unsupported output format: {to_format}")


def parse_filter(filter_str: str) -> tuple[str, str]:
    """Parse filter string like 'field:condition'."""
    if ":" not in filter_str:
        raise ValueError(f"Invalid filter format: {filter_str} (use field:condition)")
    parts = filter_str.split(":", 1)
    return parts[0], parts[1]


def parse_rename(rename_str: str) -> tuple[str, str]:
    """Parse rename string like 'old_name:new_name'."""
    if ":" not in rename_str:
        raise ValueError(f"Invalid rename format: {rename_str} (use old:new)")
    parts = rename_str.split(":", 1)
    return parts[0], parts[1]


def main():
    parser = argparse.ArgumentParser(
        description="Transform data between formats with filtering and selection"
    )
    parser.add_argument("file", help="Path to JSON or CSV data file")
    parser.add_argument(
        "--to",
        "-t",
        choices=["json", "csv", "markdown"],
        default="json",
        help="Output format (default: json)",
    )
    parser.add_argument("--output", "-o", help="Save output to file")
    parser.add_argument(
        "--filter",
        "-f",
        nargs="+",
        metavar="FIELD:CONDITION",
        help="Filter records (e.g., status:active stars:>100 name:~search)",
    )
    parser.add_argument(
        "--select", "-s", nargs="+", metavar="FIELD", help="Select specific fields"
    )
    parser.add_argument(
        "--rename",
        "-r",
        nargs="+",
        metavar="OLD:NEW",
        help="Rename fields (e.g., old_name:new_name)",
    )
    parser.add_argument("--sort", help="Sort by field")
    parser.add_argument("--desc", action="store_true", help="Sort descending")
    parser.add_argument("--limit", "-l", type=int, help="Limit number of records")
    parser.add_argument("--offset", type=int, default=0, help="Skip first N records")
    parser.add_argument("--title", help="Title for markdown output")
    parser.add_argument(
        "--verbose", "-v", action="store_true", help="Show transformation steps"
    )

    args = parser.parse_args()

    # Parse filters
    filters = {}
    if args.filter:
        for f in args.filter:
            field, condition = parse_filter(f)
            filters[field] = condition

    # Parse renames
    renames = {}
    if args.rename:
        for r in args.rename:
            old, new = parse_rename(r)
            renames[old] = new

    try:
        output = transform_data(
            file_path=args.file,
            to_format=args.to,
            filters=filters if filters else None,
            fields=args.select,
            renames=renames if renames else None,
            sort_by=args.sort,
            reverse=args.desc,
            limit=args.limit,
            offset=args.offset,
            title=args.title,
            verbose=args.verbose,
        )

        if args.output:
            Path(args.output).write_text(output)
            print(f"Output saved to: {args.output}")
        else:
            print(output)

    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
