#!/usr/bin/env python3
"""
Python Linting Script

Runs ruff linter with optional auto-fix capability.
Supports rule selection, ignore patterns, and various output formats.
"""

import argparse
import json
import subprocess
import sys
from pathlib import Path


def run_ruff(
    path: str,
    fix: bool = False,
    select: list = None,
    ignore: list = None,
    line_length: int = 88,
    output_format: str = "text",
    verbose: bool = False,
) -> dict:
    """Run ruff linter on specified path."""

    cmd = ["ruff", "check", path]

    if fix:
        cmd.append("--fix")

    if select:
        cmd.extend(["--select", ",".join(select)])

    if ignore:
        cmd.extend(["--ignore", ",".join(ignore)])

    cmd.extend(["--line-length", str(line_length)])

    if output_format == "json":
        cmd.append("--output-format=json")
    elif output_format == "github":
        cmd.append("--output-format=github")

    if verbose:
        cmd.append("--verbose")

    if verbose:
        print(f"Running: {' '.join(cmd)}")

    try:
        result = subprocess.run(cmd, capture_output=True, text=True)

        return {
            "success": result.returncode == 0,
            "output": result.stdout,
            "errors": result.stderr,
            "exit_code": result.returncode,
            "command": " ".join(cmd),
        }

    except FileNotFoundError:
        return {
            "success": False,
            "output": "",
            "errors": "ruff not found. Install with: pip install ruff",
            "exit_code": 1,
            "command": " ".join(cmd),
        }


def parse_ruff_output(output: str) -> dict:
    """Parse ruff text output into structured format."""
    lines = output.strip().split("\n") if output.strip() else []
    issues = []

    for line in lines:
        if ":" in line and not line.startswith("Found"):
            # Format: file.py:10:5: E501 Line too long
            parts = line.split(":", 3)
            if len(parts) >= 4:
                issues.append(
                    {
                        "file": parts[0],
                        "line": int(parts[1]) if parts[1].isdigit() else 0,
                        "column": int(parts[2]) if parts[2].isdigit() else 0,
                        "message": parts[3].strip(),
                    }
                )

    # Extract summary
    summary_line = [l for l in lines if l.startswith("Found")]
    summary = summary_line[0] if summary_line else "No issues found"

    return {"issues": issues, "count": len(issues), "summary": summary}


def format_output(result: dict, parsed: dict, format_type: str = "text") -> str:
    """Format results for display."""
    if format_type == "json":
        return json.dumps(
            {
                "success": result["success"],
                "issues": parsed["issues"],
                "count": parsed["count"],
                "summary": parsed["summary"],
            },
            indent=2,
        )

    elif format_type == "markdown":
        lines = [
            "# Lint Report",
            "",
            f"**Status**: {'PASS' if result['success'] else 'FAIL'}",
            f"**Issues**: {parsed['count']}",
            "",
        ]

        if parsed["issues"]:
            lines.append("## Issues")
            lines.append("")
            lines.append("| File | Line | Issue |")
            lines.append("|------|------|-------|")
            for issue in parsed["issues"][:50]:  # Limit display
                lines.append(
                    f"| {issue['file']} | {issue['line']} | {issue['message']} |"
                )

            if len(parsed["issues"]) > 50:
                lines.append(f"| ... | ... | +{len(parsed['issues']) - 50} more |")

        return "\n".join(lines)

    else:
        # Default text format
        if result["output"]:
            return result["output"]
        elif result["errors"]:
            return f"Error: {result['errors']}"
        else:
            return "No issues found"


def main():
    parser = argparse.ArgumentParser(description="Lint Python code with ruff")
    parser.add_argument(
        "path", nargs="?", default=".", help="Path to lint (default: current directory)"
    )
    parser.add_argument(
        "--fix",
        "-f",
        action="store_true",
        help="Automatically fix issues where possible",
    )
    parser.add_argument(
        "--select", "-s", nargs="+", help="Rule codes to enable (e.g., E F B)"
    )
    parser.add_argument(
        "--ignore", "-i", nargs="+", help="Rule codes to ignore (e.g., E501)"
    )
    parser.add_argument(
        "--line-length",
        "-l",
        type=int,
        default=88,
        help="Maximum line length (default: 88)",
    )
    parser.add_argument(
        "--format",
        choices=["text", "json", "markdown", "github"],
        default="text",
        help="Output format (default: text)",
    )
    parser.add_argument("--output", "-o", help="Save output to file")
    parser.add_argument(
        "--verbose", "-v", action="store_true", help="Show detailed output"
    )
    parser.add_argument(
        "--strict", action="store_true", help="Exit with error code if any issues found"
    )

    args = parser.parse_args()

    # Run ruff
    result = run_ruff(
        path=args.path,
        fix=args.fix,
        select=args.select,
        ignore=args.ignore,
        line_length=args.line_length,
        output_format="json" if args.format == "json" else "text",
        verbose=args.verbose,
    )

    # Parse and format output
    if args.format == "json" and result["output"]:
        try:
            parsed = {"issues": json.loads(result["output"]), "count": 0, "summary": ""}
            parsed["count"] = len(parsed["issues"])
        except json.JSONDecodeError:
            parsed = parse_ruff_output(result["output"])
    else:
        parsed = parse_ruff_output(result["output"])

    output = format_output(result, parsed, args.format)

    # Output
    if args.output:
        Path(args.output).write_text(output)
        print(f"Report saved to: {args.output}")
        print(f"Issues found: {parsed['count']}")
    else:
        print(output)

    # Exit code
    if args.strict and not result["success"]:
        sys.exit(1)
    elif result["exit_code"] != 0 and "not found" in result.get("errors", ""):
        sys.exit(1)


if __name__ == "__main__":
    main()
