#!/usr/bin/env python3
"""
Python Formatting Script

Format Python code with black and optionally sort imports with isort.
Supports check mode, diff preview, and various formatting options.
"""

import argparse
import subprocess
import sys


def run_black(
    path: str,
    check: bool = False,
    diff: bool = False,
    line_length: int = 88,
    target_version: str = None,
    verbose: bool = False,
) -> dict:
    """Run black formatter."""

    cmd = ["black", path]

    if check:
        cmd.append("--check")

    if diff:
        cmd.append("--diff")

    cmd.extend(["--line-length", str(line_length)])

    if target_version:
        cmd.extend(["--target-version", target_version])

    if verbose:
        cmd.append("--verbose")

    if verbose:
        print(f"Running: {' '.join(cmd)}")

    try:
        result = subprocess.run(cmd, capture_output=True, text=True)

        return {
            "success": result.returncode == 0,
            "output": result.stdout + result.stderr,
            "exit_code": result.returncode,
            "command": " ".join(cmd),
        }

    except FileNotFoundError:
        return {
            "success": False,
            "output": "black not found. Install with: pip install black",
            "exit_code": 1,
            "command": " ".join(cmd),
        }


def run_isort(
    path: str,
    check: bool = False,
    diff: bool = False,
    profile: str = "black",
    verbose: bool = False,
) -> dict:
    """Run isort import sorter."""

    cmd = ["isort", path]

    if check:
        cmd.append("--check-only")

    if diff:
        cmd.append("--diff")

    cmd.extend(["--profile", profile])

    if verbose:
        cmd.append("--verbose")

    if verbose:
        print(f"Running: {' '.join(cmd)}")

    try:
        result = subprocess.run(cmd, capture_output=True, text=True)

        return {
            "success": result.returncode == 0,
            "output": result.stdout + result.stderr,
            "exit_code": result.returncode,
            "command": " ".join(cmd),
        }

    except FileNotFoundError:
        return {
            "success": False,
            "output": "isort not found. Install with: pip install isort",
            "exit_code": 1,
            "command": " ".join(cmd),
        }


def run_ruff_format(
    path: str,
    check: bool = False,
    diff: bool = False,
    line_length: int = 88,
    verbose: bool = False,
) -> dict:
    """Run ruff format (alternative to black)."""

    cmd = ["ruff", "format", path]

    if check:
        cmd.append("--check")

    if diff:
        cmd.append("--diff")

    cmd.extend(["--line-length", str(line_length)])

    if verbose:
        print(f"Running: {' '.join(cmd)}")

    try:
        result = subprocess.run(cmd, capture_output=True, text=True)

        return {
            "success": result.returncode == 0,
            "output": result.stdout + result.stderr,
            "exit_code": result.returncode,
            "command": " ".join(cmd),
        }

    except FileNotFoundError:
        return {
            "success": False,
            "output": "ruff not found. Install with: pip install ruff",
            "exit_code": 1,
            "command": " ".join(cmd),
        }


def format_code(
    path: str,
    check: bool = False,
    diff: bool = False,
    sort_imports: bool = True,
    line_length: int = 88,
    target_version: str = None,
    use_ruff: bool = False,
    verbose: bool = False,
) -> dict:
    """Format Python code."""

    results = {"path": path, "check_mode": check, "success": True, "steps": []}

    # Sort imports first
    if sort_imports:
        if use_ruff:
            # Use ruff for import sorting
            isort_cmd = ["ruff", "check", path, "--select", "I", "--fix"]
            if check:
                isort_cmd = ["ruff", "check", path, "--select", "I"]

            try:
                isort_result = subprocess.run(isort_cmd, capture_output=True, text=True)
                results["steps"].append(
                    {
                        "tool": "ruff (imports)",
                        "success": isort_result.returncode == 0,
                        "output": isort_result.stdout + isort_result.stderr,
                    }
                )
            except FileNotFoundError:
                results["steps"].append(
                    {
                        "tool": "ruff (imports)",
                        "success": False,
                        "output": "ruff not found",
                    }
                )
        else:
            isort_result = run_isort(path, check, diff, verbose=verbose)
            results["steps"].append(
                {
                    "tool": "isort",
                    "success": isort_result["success"],
                    "output": isort_result["output"],
                }
            )
            if not isort_result["success"]:
                results["success"] = False

    # Format code
    if use_ruff:
        format_result = run_ruff_format(path, check, diff, line_length, verbose)
        results["steps"].append(
            {
                "tool": "ruff format",
                "success": format_result["success"],
                "output": format_result["output"],
            }
        )
    else:
        format_result = run_black(
            path, check, diff, line_length, target_version, verbose
        )
        results["steps"].append(
            {
                "tool": "black",
                "success": format_result["success"],
                "output": format_result["output"],
            }
        )

    if not format_result["success"]:
        results["success"] = False

    return results


def format_output(results: dict, format_type: str = "text") -> str:
    """Format results for display."""

    if format_type == "json":
        import json

        return json.dumps(results, indent=2)

    lines = []

    if results.get("check_mode"):
        lines.append("FORMAT CHECK RESULTS")
    else:
        lines.append("FORMAT RESULTS")

    lines.append("=" * 40)
    lines.append(f"Path: {results.get('path', 'N/A')}")
    lines.append(f"Status: {'PASS' if results.get('success') else 'FAIL'}")
    lines.append("")

    for step in results.get("steps", []):
        tool = step.get("tool", "unknown")
        success = step.get("success", False)
        output = step.get("output", "").strip()

        status = "✓" if success else "✗"
        lines.append(f"{status} {tool}")

        if output:
            for line in output.split("\n")[:20]:  # Limit output
                lines.append(f"  {line}")

        lines.append("")

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Format Python code with black/ruff and isort"
    )
    parser.add_argument(
        "path",
        nargs="?",
        default=".",
        help="Path to format (default: current directory)",
    )
    parser.add_argument(
        "--check",
        "-c",
        action="store_true",
        help="Check formatting without making changes",
    )
    parser.add_argument(
        "--diff", "-d", action="store_true", help="Show diff of changes"
    )
    parser.add_argument(
        "--no-sort-imports", action="store_true", help="Skip import sorting"
    )
    parser.add_argument(
        "--imports-only", action="store_true", help="Only sort imports, skip formatting"
    )
    parser.add_argument(
        "--check-imports", action="store_true", help="Check import sorting only"
    )
    parser.add_argument(
        "--line-length",
        "-l",
        type=int,
        default=88,
        help="Maximum line length (default: 88)",
    )
    parser.add_argument(
        "--target-version",
        "-t",
        choices=["py38", "py39", "py310", "py311", "py312"],
        help="Target Python version",
    )
    parser.add_argument(
        "--use-ruff",
        action="store_true",
        help="Use ruff instead of black for formatting",
    )
    parser.add_argument(
        "--format",
        "-f",
        choices=["text", "json"],
        default="text",
        help="Output format (default: text)",
    )
    parser.add_argument(
        "--verbose", "-v", action="store_true", help="Show detailed output"
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Exit with error code if formatting needed",
    )

    args = parser.parse_args()

    # Handle imports-only mode
    if args.imports_only or args.check_imports:
        result = run_isort(
            args.path, check=args.check_imports, diff=args.diff, verbose=args.verbose
        )
        print(result["output"])
        if args.strict and not result["success"]:
            sys.exit(1)
        return

    # Full format
    results = format_code(
        path=args.path,
        check=args.check,
        diff=args.diff,
        sort_imports=not args.no_sort_imports,
        line_length=args.line_length,
        target_version=args.target_version,
        use_ruff=args.use_ruff,
        verbose=args.verbose,
    )

    output = format_output(results, args.format)
    print(output)

    if args.strict and not results["success"]:
        sys.exit(1)


if __name__ == "__main__":
    main()
