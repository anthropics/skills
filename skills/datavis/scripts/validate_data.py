#!/usr/bin/env python3
"""
Data Validation Script for Visualization

Validates datasets before visualization to catch common issues:
- Missing values
- Type mismatches
- Range violations
- Outliers
- Consistency checks

Returns JSON report with issues and suggestions.
"""

import argparse
import csv
import json
import statistics
import sys
from collections import Counter
from pathlib import Path


def load_data(filepath: str) -> tuple[list[dict], str]:
    """Load data from CSV or JSON file."""
    path = Path(filepath)

    if not path.exists():
        raise FileNotFoundError(f"File not found: {filepath}")

    suffix = path.suffix.lower()

    if suffix == ".json":
        with open(path) as f:
            data = json.load(f)
            if isinstance(data, list):
                return data, "json"
            elif isinstance(data, dict) and "data" in data:
                return data["data"], "json"
            else:
                raise ValueError("JSON must be array or object with 'data' key")

    elif suffix == ".csv":
        with open(path) as f:
            reader = csv.DictReader(f)
            return list(reader), "csv"

    else:
        raise ValueError(f"Unsupported format: {suffix}")


def infer_type(values: list) -> str:
    """Infer the type of a column from its values."""
    non_null = [v for v in values if v is not None and v != ""]

    if not non_null:
        return "empty"

    # Check if numeric
    numeric_count = 0
    for v in non_null:
        try:
            float(v)
            numeric_count += 1
        except (ValueError, TypeError):
            pass

    if numeric_count == len(non_null):
        # Check if all integers
        try:
            if all(float(v) == int(float(v)) for v in non_null):
                return "integer"
        except (ValueError, TypeError):
            pass
        return "number"

    # Check if boolean
    bool_values = {"true", "false", "yes", "no", "1", "0", "t", "f"}
    if all(str(v).lower() in bool_values for v in non_null):
        return "boolean"

    # Check if date-like
    date_indicators = ["-", "/", ":"]
    if any(any(ind in str(v) for ind in date_indicators) for v in non_null[:10]):
        # Simple heuristic - could use dateutil.parser
        return "date"

    return "string"


def analyze_column(name: str, values: list) -> dict:
    """Analyze a single column and return statistics."""
    result = {
        "name": name,
        "type": infer_type(values),
        "count": len(values),
        "missing": sum(1 for v in values if v is None or v == ""),
        "unique": len(set(str(v) for v in values if v is not None and v != "")),
    }

    result["missing_pct"] = (
        result["missing"] / result["count"] * 100 if result["count"] > 0 else 0
    )

    # For numeric columns
    if result["type"] in ["number", "integer"]:
        numeric_values = []
        for v in values:
            try:
                numeric_values.append(float(v))
            except (ValueError, TypeError):
                pass

        if numeric_values:
            result["min"] = min(numeric_values)
            result["max"] = max(numeric_values)
            result["mean"] = statistics.mean(numeric_values)
            result["median"] = statistics.median(numeric_values)
            if len(numeric_values) > 1:
                result["stdev"] = statistics.stdev(numeric_values)

                # Detect outliers using IQR method
                q1 = statistics.quantiles(numeric_values, n=4)[0]
                q3 = statistics.quantiles(numeric_values, n=4)[2]
                iqr = q3 - q1
                lower_bound = q1 - 1.5 * iqr
                upper_bound = q3 + 1.5 * iqr
                outliers = [
                    v for v in numeric_values if v < lower_bound or v > upper_bound
                ]
                result["outlier_count"] = len(outliers)

    # For categorical columns
    elif result["type"] == "string":
        value_counts = Counter(str(v) for v in values if v is not None and v != "")
        result["top_values"] = dict(value_counts.most_common(5))

        # Suggest if should be categorical
        if result["unique"] < 20 and result["unique"] < result["count"] * 0.1:
            result["suggestion"] = "Consider as categorical"

    return result


def validate_dataset(data: list[dict]) -> dict:
    """Validate a dataset and return comprehensive report."""
    if not data:
        return {"error": "Empty dataset"}

    # Get all fields from first record
    fields = list(data[0].keys())

    report = {
        "record_count": len(data),
        "field_count": len(fields),
        "fields": {},
        "issues": [],
        "suggestions": [],
    }

    # Analyze each field
    for field in fields:
        values = [record.get(field) for record in data]
        analysis = analyze_column(field, values)
        report["fields"][field] = analysis

        # Check for issues
        if analysis["missing_pct"] > 50:
            report["issues"].append(
                {
                    "severity": "high",
                    "field": field,
                    "issue": f"More than 50% missing values ({analysis['missing_pct']:.1f}%)",
                }
            )
        elif analysis["missing_pct"] > 10:
            report["issues"].append(
                {
                    "severity": "medium",
                    "field": field,
                    "issue": f"Significant missing values ({analysis['missing_pct']:.1f}%)",
                }
            )

        if analysis.get("outlier_count", 0) > len(data) * 0.05:
            report["issues"].append(
                {
                    "severity": "medium",
                    "field": field,
                    "issue": f"Many outliers detected ({analysis['outlier_count']})",
                }
            )

        if "suggestion" in analysis:
            report["suggestions"].append(
                {"field": field, "suggestion": analysis["suggestion"]}
            )

    # Check for data quality summary
    total_cells = len(data) * len(fields)
    total_missing = sum(f["missing"] for f in report["fields"].values())
    report["completeness"] = (
        (total_cells - total_missing) / total_cells * 100 if total_cells > 0 else 0
    )

    # Overall status
    high_issues = sum(1 for i in report["issues"] if i["severity"] == "high")
    if high_issues > 0:
        report["status"] = "issues_found"
    elif report["issues"]:
        report["status"] = "warnings"
    else:
        report["status"] = "valid"

    return report


def check_visualization_readiness(report: dict, viz_type: str) -> dict:
    """Check if data is ready for specific visualization type."""
    readiness = {
        "viz_type": viz_type,
        "ready": True,
        "requirements": [],
        "warnings": [],
    }

    fields = report.get("fields", {})

    if viz_type == "bar":
        # Need at least one categorical and one numeric
        categorical = [
            f for f, v in fields.items() if v["type"] in ["string", "boolean"]
        ]
        numeric = [f for f, v in fields.items() if v["type"] in ["number", "integer"]]

        if not categorical:
            readiness["ready"] = False
            readiness["requirements"].append(
                "Need at least one categorical field for x-axis"
            )
        if not numeric:
            readiness["ready"] = False
            readiness["requirements"].append(
                "Need at least one numeric field for y-axis"
            )

    elif viz_type == "scatter":
        numeric = [f for f, v in fields.items() if v["type"] in ["number", "integer"]]
        if len(numeric) < 2:
            readiness["ready"] = False
            readiness["requirements"].append(
                "Need at least two numeric fields for x/y axes"
            )

    elif viz_type == "network":
        # Need source/target or nodes/links
        has_source_target = "source" in fields and "target" in fields
        has_nodes_links = any("node" in f.lower() for f in fields)

        if not has_source_target and not has_nodes_links:
            readiness["ready"] = False
            readiness["requirements"].append(
                "Need 'source' and 'target' fields, or node/link structure"
            )

    elif viz_type == "choropleth":
        # Need geographic identifier
        geo_fields = [
            f
            for f in fields
            if any(
                g in f.lower()
                for g in ["fips", "county", "state", "country", "geo", "code"]
            )
        ]
        if not geo_fields:
            readiness["warnings"].append("No obvious geographic identifier found")

    return readiness


def main():
    parser = argparse.ArgumentParser(description="Validate datasets for visualization")
    parser.add_argument("file", help="Path to CSV or JSON data file")
    parser.add_argument(
        "--viz-type",
        "-v",
        choices=["bar", "line", "scatter", "pie", "network", "choropleth", "treemap"],
        help="Check readiness for specific visualization type",
    )
    parser.add_argument(
        "--format",
        "-f",
        choices=["json", "summary"],
        default="summary",
        help="Output format (default: summary)",
    )
    parser.add_argument(
        "--strict", action="store_true", help="Exit with error code if issues found"
    )

    args = parser.parse_args()

    try:
        data, file_type = load_data(args.file)
        report = validate_dataset(data)

        if args.viz_type:
            readiness = check_visualization_readiness(report, args.viz_type)
            report["visualization_readiness"] = readiness

        if args.format == "json":
            print(json.dumps(report, indent=2, default=str))
        else:
            # Summary format
            print(f"\n{'='*60}")
            print("DATA VALIDATION REPORT")
            print(f"{'='*60}")
            print(f"File: {args.file}")
            print(f"Records: {report['record_count']}")
            print(f"Fields: {report['field_count']}")
            print(f"Completeness: {report['completeness']:.1f}%")
            print(f"Status: {report['status'].upper()}")

            if report["issues"]:
                print(f"\n--- Issues ({len(report['issues'])}) ---")
                for issue in report["issues"]:
                    print(
                        f"  [{issue['severity'].upper()}] {issue['field']}: {issue['issue']}"
                    )

            if report["suggestions"]:
                print(f"\n--- Suggestions ({len(report['suggestions'])}) ---")
                for s in report["suggestions"]:
                    print(f"  {s['field']}: {s['suggestion']}")

            print("\n--- Field Summary ---")
            for name, field in report["fields"].items():
                missing = (
                    f", {field['missing_pct']:.0f}% missing"
                    if field["missing"] > 0
                    else ""
                )
                print(f"  {name}: {field['type']} ({field['unique']} unique{missing})")

            if "visualization_readiness" in report:
                r = report["visualization_readiness"]
                print(f"\n--- {r['viz_type'].upper()} Readiness ---")
                print(f"  Ready: {'Yes' if r['ready'] else 'No'}")
                for req in r["requirements"]:
                    print(f"  [REQUIRED] {req}")
                for warn in r["warnings"]:
                    print(f"  [WARNING] {warn}")

        if args.strict and report["status"] == "issues_found":
            sys.exit(1)

    except Exception as e:
        print(json.dumps({"error": str(e)}, indent=2))
        sys.exit(1)


if __name__ == "__main__":
    main()
