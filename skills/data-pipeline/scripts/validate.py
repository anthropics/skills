#!/usr/bin/env python3
"""
Data Validation Script

Validates data files for completeness, schema, and quality.
Supports JSON and CSV formats with configurable rules.
"""

import argparse
import json
import sys
from pathlib import Path


def load_data(file_path: str) -> tuple[list | dict, str]:
    """Load data from JSON or CSV file."""
    path = Path(file_path)

    if not path.exists():
        raise FileNotFoundError(f"File not found: {file_path}")

    suffix = path.suffix.lower()

    if suffix == ".json":
        with open(path) as f:
            data = json.load(f)
        return data, "json"

    elif suffix == ".csv":
        import csv

        with open(path, newline="") as f:
            reader = csv.DictReader(f)
            data = list(reader)
        return data, "csv"

    else:
        raise ValueError(f"Unsupported file type: {suffix}")


def validate_schema(data: list, required_fields: list = None) -> dict:
    """Validate that data has consistent schema."""
    if not data or not isinstance(data, list):
        return {"valid": False, "error": "Data must be a non-empty list of records"}

    # Get fields from first record
    if isinstance(data[0], dict):
        base_fields = set(data[0].keys())
    else:
        return {"valid": False, "error": "Records must be dictionaries"}

    issues = []

    # Check required fields
    if required_fields:
        missing_required = set(required_fields) - base_fields
        if missing_required:
            issues.append(f"Missing required fields: {missing_required}")

    # Check schema consistency
    for i, record in enumerate(data[1:], start=2):
        if not isinstance(record, dict):
            issues.append(f"Record {i} is not a dictionary")
            continue

        record_fields = set(record.keys())

        missing = base_fields - record_fields
        extra = record_fields - base_fields

        if missing:
            issues.append(f"Record {i}: missing fields {missing}")
        if extra:
            issues.append(f"Record {i}: unexpected fields {extra}")

    return {
        "valid": len(issues) == 0,
        "fields": list(base_fields),
        "record_count": len(data),
        "issues": issues[:20],  # Limit issue count
        "total_issues": len(issues),
    }


def validate_completeness(data: list, allow_null: list = None) -> dict:
    """Check for null/empty values."""
    allow_null = allow_null or []

    if not data or not isinstance(data[0], dict):
        return {"valid": False, "error": "Invalid data format"}

    fields = list(data[0].keys())
    null_counts = {field: 0 for field in fields}
    empty_counts = {field: 0 for field in fields}

    for record in data:
        for field in fields:
            value = record.get(field)
            if value is None:
                null_counts[field] += 1
            elif value == "" or value == []:
                empty_counts[field] += 1

    total = len(data)
    issues = []

    for field in fields:
        if field in allow_null:
            continue

        null_pct = (null_counts[field] / total) * 100
        empty_pct = (empty_counts[field] / total) * 100

        if null_pct > 0:
            issues.append(f"{field}: {null_counts[field]} nulls ({null_pct:.1f}%)")
        if empty_pct > 0:
            issues.append(f"{field}: {empty_counts[field]} empty ({empty_pct:.1f}%)")

    return {
        "valid": len(issues) == 0,
        "null_counts": {k: v for k, v in null_counts.items() if v > 0},
        "empty_counts": {k: v for k, v in empty_counts.items() if v > 0},
        "issues": issues,
        "completeness_pct": 100
        - (sum(null_counts.values()) + sum(empty_counts.values()))
        / (total * len(fields))
        * 100,
    }


def validate_types(data: list, type_hints: dict = None) -> dict:
    """Validate data types in fields."""
    if not data or not isinstance(data[0], dict):
        return {"valid": False, "error": "Invalid data format"}

    # Infer types from first non-null values
    inferred_types = {}
    for record in data:
        for field, value in record.items():
            if field not in inferred_types and value is not None and value != "":
                inferred_types[field] = type(value).__name__

    # Apply type hints if provided
    if type_hints:
        for field, expected in type_hints.items():
            if field in inferred_types:
                inferred_types[field] = expected

    issues = []
    type_mismatches = {field: 0 for field in inferred_types}

    for i, record in enumerate(data):
        for field, expected_type in inferred_types.items():
            value = record.get(field)
            if value is None or value == "":
                continue

            actual_type = type(value).__name__

            # Allow numeric coercion
            numeric_types = {"int", "float", "str"}
            if expected_type in numeric_types and actual_type in numeric_types:
                continue

            if actual_type != expected_type:
                type_mismatches[field] += 1
                if type_mismatches[field] <= 3:  # Limit examples
                    issues.append(
                        f"Record {i+1}, {field}: expected {expected_type}, got {actual_type}"
                    )

    return {
        "valid": all(v == 0 for v in type_mismatches.values()),
        "inferred_types": inferred_types,
        "type_mismatches": {k: v for k, v in type_mismatches.items() if v > 0},
        "issues": issues,
    }


def validate_data(
    file_path: str,
    required_fields: list = None,
    allow_null: list = None,
    type_hints: dict = None,
) -> dict:
    """Run all validations on a data file."""

    try:
        data, format_type = load_data(file_path)
    except Exception as e:
        return {"valid": False, "error": str(e), "file": file_path}

    # Handle nested data
    if isinstance(data, dict):
        if "results" in data:
            data = data["results"]
        elif "data" in data:
            data = data["data"]
        elif "items" in data:
            data = data["items"]

    if not isinstance(data, list):
        return {
            "valid": False,
            "error": "Data must be a list of records",
            "file": file_path,
        }

    schema_result = validate_schema(data, required_fields)
    completeness_result = validate_completeness(data, allow_null)
    type_result = validate_types(data, type_hints)

    all_valid = (
        schema_result.get("valid", False)
        and completeness_result.get("valid", False)
        and type_result.get("valid", False)
    )

    return {
        "valid": all_valid,
        "file": file_path,
        "format": format_type,
        "record_count": len(data),
        "schema": schema_result,
        "completeness": completeness_result,
        "types": type_result,
    }


def format_report(result: dict, format_type: str = "summary") -> str:
    """Format validation results."""

    if format_type == "json":
        return json.dumps(result, indent=2)

    # Summary format
    lines = [
        "=" * 50,
        "DATA VALIDATION REPORT",
        "=" * 50,
        f"File: {result.get('file', 'N/A')}",
        f"Format: {result.get('format', 'N/A')}",
        f"Records: {result.get('record_count', 0)}",
        f"Status: {'VALID ✓' if result.get('valid') else 'INVALID ✗'}",
        "",
    ]

    if "error" in result:
        lines.append(f"Error: {result['error']}")
        return "\n".join(lines)

    # Schema
    schema = result.get("schema", {})
    lines.append("SCHEMA")
    lines.append("-" * 30)
    lines.append(f"Fields: {', '.join(schema.get('fields', []))}")
    if schema.get("issues"):
        lines.append(f"Issues: {len(schema.get('issues', []))}")
        for issue in schema.get("issues", [])[:5]:
            lines.append(f"  • {issue}")
    else:
        lines.append("Status: Valid ✓")
    lines.append("")

    # Completeness
    comp = result.get("completeness", {})
    lines.append("COMPLETENESS")
    lines.append("-" * 30)
    lines.append(f"Completeness: {comp.get('completeness_pct', 0):.1f}%")
    if comp.get("null_counts"):
        lines.append("Null fields:")
        for field, count in comp.get("null_counts", {}).items():
            lines.append(f"  • {field}: {count}")
    if comp.get("empty_counts"):
        lines.append("Empty fields:")
        for field, count in comp.get("empty_counts", {}).items():
            lines.append(f"  • {field}: {count}")
    if not comp.get("issues"):
        lines.append("Status: Complete ✓")
    lines.append("")

    # Types
    types = result.get("types", {})
    lines.append("TYPES")
    lines.append("-" * 30)
    if types.get("inferred_types"):
        for field, ftype in types.get("inferred_types", {}).items():
            lines.append(f"  {field}: {ftype}")
    if types.get("type_mismatches"):
        lines.append("Mismatches:")
        for field, count in types.get("type_mismatches", {}).items():
            lines.append(f"  • {field}: {count} issues")
    else:
        lines.append("Status: Consistent ✓")

    lines.append("")
    lines.append("=" * 50)

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Validate data files for schema, completeness, and types"
    )
    parser.add_argument("file", help="Path to JSON or CSV data file")
    parser.add_argument(
        "--required", "-r", nargs="+", help="Required fields that must exist"
    )
    parser.add_argument(
        "--allow-null", "-n", nargs="+", help="Fields where null values are acceptable"
    )
    parser.add_argument(
        "--format",
        "-f",
        choices=["summary", "json"],
        default="summary",
        help="Output format (default: summary)",
    )
    parser.add_argument("--output", "-o", help="Save report to file")
    parser.add_argument(
        "--strict", action="store_true", help="Exit with error code if validation fails"
    )

    args = parser.parse_args()

    # Run validation
    result = validate_data(
        file_path=args.file, required_fields=args.required, allow_null=args.allow_null
    )

    # Format output
    output = format_report(result, args.format)

    # Save or print
    if args.output:
        Path(args.output).write_text(output)
        print(f"Report saved to: {args.output}")
        status = "VALID" if result.get("valid") else "INVALID"
        print(f"Validation: {status}")
    else:
        print(output)

    # Exit code
    if args.strict and not result.get("valid"):
        sys.exit(1)


if __name__ == "__main__":
    main()
