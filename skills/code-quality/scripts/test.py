#!/usr/bin/env python3
"""
Test Runner Script

Run pytest with coverage, markers, and various output options.
"""

import argparse
import json
import subprocess
import sys
from pathlib import Path


def run_pytest(
    path: str = None,
    markers: str = None,
    keywords: str = None,
    coverage: bool = False,
    coverage_source: str = None,
    coverage_html: bool = False,
    min_coverage: int = None,
    verbose: bool = False,
    quiet: bool = False,
    failfast: bool = False,
    last_failed: bool = False,
    collect_only: bool = False,
    extra_args: list = None,
) -> dict:
    """Run pytest with specified options."""

    cmd = ["pytest"]

    if path:
        cmd.append(path)

    if markers:
        cmd.extend(["-m", markers])

    if keywords:
        cmd.extend(["-k", keywords])

    if coverage:
        source = coverage_source or "."
        cmd.extend([f"--cov={source}", "--cov-report=term-missing"])

        if coverage_html:
            cmd.append("--cov-report=html")

        if min_coverage:
            cmd.append(f"--cov-fail-under={min_coverage}")

    if verbose:
        cmd.append("-v")

    if quiet:
        cmd.append("-q")

    if failfast:
        cmd.append("-x")

    if last_failed:
        cmd.append("--lf")

    if collect_only:
        cmd.append("--collect-only")

    if extra_args:
        cmd.extend(extra_args)

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
            "errors": "pytest not found. Install with: pip install pytest",
            "exit_code": 1,
            "command": " ".join(cmd),
        }


def parse_pytest_output(output: str) -> dict:
    """Parse pytest output for summary info."""

    summary = {
        "passed": 0,
        "failed": 0,
        "skipped": 0,
        "errors": 0,
        "warnings": 0,
        "total": 0,
        "duration": None,
    }

    lines = output.split("\n")

    for line in lines:
        line_lower = line.lower()

        # Look for summary line like "5 passed, 2 failed in 1.23s"
        if "passed" in line_lower or "failed" in line_lower:
            if "in" in line_lower and ("s" in line_lower or "second" in line_lower):
                parts = line.split()
                for i, part in enumerate(parts):
                    if "passed" in part.lower() and i > 0:
                        try:
                            summary["passed"] = int(parts[i - 1])
                        except ValueError:
                            pass
                    elif "failed" in part.lower() and i > 0:
                        try:
                            summary["failed"] = int(parts[i - 1])
                        except ValueError:
                            pass
                    elif "skipped" in part.lower() and i > 0:
                        try:
                            summary["skipped"] = int(parts[i - 1])
                        except ValueError:
                            pass
                    elif "error" in part.lower() and i > 0:
                        try:
                            summary["errors"] = int(parts[i - 1])
                        except ValueError:
                            pass
                    elif "warning" in part.lower() and i > 0:
                        try:
                            summary["warnings"] = int(parts[i - 1])
                        except ValueError:
                            pass

                # Extract duration
                for part in parts:
                    if part.endswith("s") and part[:-1].replace(".", "").isdigit():
                        summary["duration"] = part
                        break

    summary["total"] = (
        summary["passed"] + summary["failed"] + summary["skipped"] + summary["errors"]
    )

    return summary


def format_output(result: dict, summary: dict, format_type: str = "text") -> str:
    """Format test results."""

    if format_type == "json":
        return json.dumps(
            {
                "success": result["success"],
                "summary": summary,
                "output": result["output"][:5000],  # Truncate
                "command": result["command"],
            },
            indent=2,
        )

    # Default text output - just return pytest's output
    output = result["output"]

    if result["errors"]:
        output += "\n" + result["errors"]

    return output


def main():
    parser = argparse.ArgumentParser(description="Run tests with pytest")
    parser.add_argument("path", nargs="?", help="Test file or directory")
    parser.add_argument(
        "--marker",
        "-m",
        help='Run tests matching marker expression (e.g., "unit", "not slow")',
    )
    parser.add_argument("--keyword", "-k", help="Run tests matching keyword expression")
    parser.add_argument(
        "--coverage", "-c", action="store_true", help="Run with coverage"
    )
    parser.add_argument(
        "--cov-source", help="Source directory for coverage (default: .)"
    )
    parser.add_argument(
        "--html", action="store_true", help="Generate HTML coverage report"
    )
    parser.add_argument(
        "--min-coverage", type=int, help="Minimum coverage percentage (fails if below)"
    )
    parser.add_argument("--verbose", "-v", action="store_true", help="Verbose output")
    parser.add_argument("--quiet", "-q", action="store_true", help="Quiet output")
    parser.add_argument(
        "--failfast", "-x", action="store_true", help="Stop on first failure"
    )
    parser.add_argument(
        "--last-failed", "--lf", action="store_true", help="Run only last failed tests"
    )
    parser.add_argument(
        "--collect-only", action="store_true", help="Only collect tests, do not run"
    )
    parser.add_argument(
        "--format",
        "-f",
        choices=["text", "json"],
        default="text",
        help="Output format (default: text)",
    )
    parser.add_argument("--output", "-o", help="Save output to file")
    parser.add_argument("extra", nargs="*", help="Additional pytest arguments")

    args = parser.parse_args()

    # Run tests
    result = run_pytest(
        path=args.path,
        markers=args.marker,
        keywords=args.keyword,
        coverage=args.coverage,
        coverage_source=args.cov_source,
        coverage_html=args.html,
        min_coverage=args.min_coverage,
        verbose=args.verbose,
        quiet=args.quiet,
        failfast=args.failfast,
        last_failed=args.last_failed,
        collect_only=args.collect_only,
        extra_args=args.extra,
    )

    # Parse summary
    summary = parse_pytest_output(result["output"])

    # Format output
    output = format_output(result, summary, args.format)

    if args.output:
        Path(args.output).write_text(output)
        print(f"Results saved to: {args.output}")

        # Print summary
        status = "PASS" if result["success"] else "FAIL"
        print(f"Status: {status}")
        print(
            f"Tests: {summary['passed']} passed, {summary['failed']} failed, {summary['skipped']} skipped"
        )
        if summary["duration"]:
            print(f"Duration: {summary['duration']}")
    else:
        print(output)

    # Exit code
    sys.exit(result["exit_code"])


if __name__ == "__main__":
    main()
