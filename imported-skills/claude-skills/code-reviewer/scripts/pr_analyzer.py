#!/usr/bin/env python3
"""
PR Analyzer

Analyzes pull request changes for review complexity, risk assessment,
and generates review priorities.

Usage:
    python pr_analyzer.py /path/to/repo
    python pr_analyzer.py . --base main --head feature-branch
    python pr_analyzer.py /path/to/repo --json
"""

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Optional, Tuple


# File categories for review prioritization
FILE_CATEGORIES = {
    "critical": {
        "patterns": [
            r"auth", r"security", r"password", r"token", r"secret",
            r"payment", r"billing", r"crypto", r"encrypt"
        ],
        "weight": 5,
        "description": "Security-sensitive files requiring careful review"
    },
    "high": {
        "patterns": [
            r"api", r"database", r"migration", r"schema", r"model",
            r"config", r"env", r"middleware"
        ],
        "weight": 4,
        "description": "Core infrastructure files"
    },
    "medium": {
        "patterns": [
            r"service", r"controller", r"handler", r"util", r"helper"
        ],
        "weight": 3,
        "description": "Business logic files"
    },
    "low": {
        "patterns": [
            r"test", r"spec", r"mock", r"fixture", r"story",
            r"readme", r"docs", r"\.md$"
        ],
        "weight": 1,
        "description": "Tests and documentation"
    }
}

# Risky patterns to flag
RISK_PATTERNS = [
    {
        "name": "hardcoded_secrets",
        "pattern": r"(password|secret|api_key|token|connection_?string)\s*[=:]\s*['\"][^'\"]+['\"]",
        "severity": "critical",
        "message": "Potential hardcoded secret or connection string detected"
    },
    {
        "name": "todo_fixme",
        "pattern": r"(TODO|FIXME|HACK|XXX):",
        "severity": "low",
        "message": "TODO/FIXME comment found"
    },
    {
        "name": "console_log",
        "pattern": (
            r"console\.(log|debug|info|warn|error)\(|\bDebug\.WriteLine\(|"
            r"\bSystem\.out\.print(?:ln)?\(|\.printStackTrace\("
        ),
        "severity": "medium",
        "message": (
            "Debug output statement found "
            "(console.* / Debug.WriteLine / System.out / printStackTrace)"
        )
    },
    {
        "name": "debugger",
        "pattern": r"\bdebugger\b",
        "severity": "high",
        "message": "Debugger statement found"
    },
    {
        "name": "analyzer_disable",
        "pattern": (
            r"eslint-disable|#pragma\s+warning\s+disable|\[SuppressMessage|"
            r"@SuppressWarnings"
        ),
        "severity": "medium",
        "message": (
            "Static-analyzer rule disabled "
            "(ESLint / Roslyn / SuppressMessage / @SuppressWarnings)"
        )
    },
    {
        "name": "loose_type",
        "pattern": r":\s*any\b|\bdynamic\s+\w+\s*[=;]",
        "severity": "medium",
        "message": "Loose type used (TypeScript 'any' or C# 'dynamic')"
    },
    {
        "name": "sql_concatenation",
        "pattern": r"(SELECT|INSERT|UPDATE|DELETE).*\+.*['\"]|(?:FromSql|ExecuteSql)\w*\([^)]*\$\"",
        "severity": "critical",
        "message": "Potential SQL injection (string concatenation or interpolation in query)"
    },
    {
        "name": "csharp_unsafe_block",
        "pattern": (
            r"\bunsafe\s+(?:\{|public|private|protected|internal|static|sealed|"
            r"partial|class|struct|void|int|string|long|short|byte|double|float|"
            r"bool|char|ref|out|fixed)\b"
        ),
        "severity": "high",
        "message": "C# 'unsafe' code — requires memory-safety review"
    },
    {
        "name": "csharp_null_forgiving",
        "pattern": r"(?:\)\s*!\.|\w+!\.\w+)",
        "severity": "medium",
        "message": "Null-forgiving operator (!) used — verify the value is truly non-null"
    },
    {
        "name": "csharp_async_void",
        "pattern": r"\basync\s+void\s+\w+\s*\(",
        "severity": "high",
        "message": "'async void' method — use only for event handlers"
    },
    {
        "name": "csharp_blocking_async",
        "pattern": r"\.(?:Result\b|Wait\(\)|GetAwaiter\(\)\.GetResult\(\))",
        "severity": "high",
        "message": "Blocking call on async operation — can deadlock in ASP.NET contexts"
    }
]


def run_git_command(cmd: List[str], cwd: Path) -> Tuple[bool, str]:
    """Run a git command and return success status and output."""
    try:
        result = subprocess.run(
            cmd,
            cwd=cwd,
            capture_output=True,
            text=True,
            timeout=30
        )
        return result.returncode == 0, result.stdout.strip()
    except subprocess.TimeoutExpired:
        return False, "Command timed out"
    except Exception as e:
        return False, str(e)


def get_changed_files(repo_path: Path, base: str, head: str) -> List[Dict]:
    """Get list of changed files between two refs."""
    success, output = run_git_command(
        ["git", "diff", "--name-status", f"{base}...{head}"],
        repo_path
    )

    if not success:
        # Try without the triple dot (for uncommitted changes)
        success, output = run_git_command(
            ["git", "diff", "--name-status", base, head],
            repo_path
        )

    if not success or not output:
        # Fall back to staged changes
        success, output = run_git_command(
            ["git", "diff", "--name-status", "--cached"],
            repo_path
        )

    files = []
    for line in output.split("\n"):
        if not line.strip():
            continue
        parts = line.split("\t")
        if len(parts) >= 2:
            status = parts[0][0]  # First character of status
            filepath = parts[-1]  # Handle renames (R100\told\tnew)
            status_map = {
                "A": "added",
                "M": "modified",
                "D": "deleted",
                "R": "renamed",
                "C": "copied"
            }
            files.append({
                "path": filepath,
                "status": status_map.get(status, "modified")
            })

    return files


def get_file_diff(repo_path: Path, filepath: str, base: str, head: str) -> str:
    """Get diff content for a specific file."""
    success, output = run_git_command(
        ["git", "diff", f"{base}...{head}", "--", filepath],
        repo_path
    )
    if not success:
        success, output = run_git_command(
            ["git", "diff", "--cached", "--", filepath],
            repo_path
        )
    return output if success else ""


def categorize_file(filepath: str) -> Tuple[str, int]:
    """Categorize a file based on its path and name."""
    filepath_lower = filepath.lower()

    for category, info in FILE_CATEGORIES.items():
        for pattern in info["patterns"]:
            if re.search(pattern, filepath_lower):
                return category, info["weight"]

    return "medium", 2  # Default category


def analyze_diff_for_risks(diff_content: str, filepath: str) -> List[Dict]:
    """Analyze diff content for risky patterns."""
    risks = []

    # Only analyze added lines (starting with +)
    added_lines = [
        line[1:] for line in diff_content.split("\n")
        if line.startswith("+") and not line.startswith("+++")
    ]

    content = "\n".join(added_lines)

    for risk in RISK_PATTERNS:
        matches = re.findall(risk["pattern"], content, re.IGNORECASE)
        if matches:
            risks.append({
                "name": risk["name"],
                "severity": risk["severity"],
                "message": risk["message"],
                "file": filepath,
                "count": len(matches)
            })

    return risks


def count_changes(diff_content: str) -> Dict[str, int]:
    """Count additions and deletions in diff."""
    additions = 0
    deletions = 0

    for line in diff_content.split("\n"):
        if line.startswith("+") and not line.startswith("+++"):
            additions += 1
        elif line.startswith("-") and not line.startswith("---"):
            deletions += 1

    return {"additions": additions, "deletions": deletions}


def calculate_complexity_score(files: List[Dict], all_risks: List[Dict]) -> int:
    """Calculate overall PR complexity score (1-10)."""
    score = 0

    # File count contribution (max 3 points)
    file_count = len(files)
    if file_count > 20:
        score += 3
    elif file_count > 10:
        score += 2
    elif file_count > 5:
        score += 1

    # Total changes contribution (max 3 points)
    total_changes = sum(f.get("additions", 0) + f.get("deletions", 0) for f in files)
    if total_changes > 500:
        score += 3
    elif total_changes > 200:
        score += 2
    elif total_changes > 50:
        score += 1

    # Risk severity contribution (max 4 points)
    critical_risks = sum(1 for r in all_risks if r["severity"] == "critical")
    high_risks = sum(1 for r in all_risks if r["severity"] == "high")

    score += min(2, critical_risks)
    score += min(2, high_risks)

    return min(10, max(1, score))


def analyze_commit_messages(repo_path: Path, base: str, head: str) -> Dict:
    """Analyze commit messages in the PR."""
    success, output = run_git_command(
        ["git", "log", "--oneline", f"{base}...{head}"],
        repo_path
    )

    if not success or not output:
        return {"commits": 0, "issues": []}

    commits = output.strip().split("\n")
    issues = []

    for commit in commits:
        if len(commit) < 10:
            continue

        # Check for conventional commit format
        message = commit[8:] if len(commit) > 8 else commit  # Skip hash

        if not re.match(r"^(feat|fix|docs|style|refactor|test|chore|perf|ci|build|revert)(\(.+\))?:", message):
            issues.append({
                "commit": commit[:7],
                "issue": "Does not follow conventional commit format"
            })

        if len(message) > 72:
            issues.append({
                "commit": commit[:7],
                "issue": "Commit message exceeds 72 characters"
            })

    return {
        "commits": len(commits),
        "issues": issues
    }


def analyze_pr(
    repo_path: Path,
    base: str = "main",
    head: str = "HEAD"
) -> Dict:
    """Perform complete PR analysis."""
    # Get changed files
    changed_files = get_changed_files(repo_path, base, head)

    if not changed_files:
        return {
            "status": "no_changes",
            "message": "No changes detected between branches"
        }

    # Analyze each file
    all_risks = []
    file_analyses = []

    for file_info in changed_files:
        filepath = file_info["path"]
        category, weight = categorize_file(filepath)

        # Get diff for the file
        diff = get_file_diff(repo_path, filepath, base, head)
        changes = count_changes(diff)
        risks = analyze_diff_for_risks(diff, filepath)

        all_risks.extend(risks)

        file_analyses.append({
            "path": filepath,
            "status": file_info["status"],
            "category": category,
            "priority_weight": weight,
            "additions": changes["additions"],
            "deletions": changes["deletions"],
            "risks": risks
        })

    # Sort by priority (highest first)
    file_analyses.sort(key=lambda x: (-x["priority_weight"], x["path"]))

    # Analyze commits
    commit_analysis = analyze_commit_messages(repo_path, base, head)

    # Calculate metrics
    complexity = calculate_complexity_score(file_analyses, all_risks)

    total_additions = sum(f["additions"] for f in file_analyses)
    total_deletions = sum(f["deletions"] for f in file_analyses)

    return {
        "status": "analyzed",
        "summary": {
            "files_changed": len(file_analyses),
            "total_additions": total_additions,
            "total_deletions": total_deletions,
            "complexity_score": complexity,
            "complexity_label": get_complexity_label(complexity),
            "commits": commit_analysis["commits"]
        },
        "risks": {
            "critical": [r for r in all_risks if r["severity"] == "critical"],
            "high": [r for r in all_risks if r["severity"] == "high"],
            "medium": [r for r in all_risks if r["severity"] == "medium"],
            "low": [r for r in all_risks if r["severity"] == "low"]
        },
        "files": file_analyses,
        "commit_issues": commit_analysis["issues"],
        "review_order": [f["path"] for f in file_analyses[:10]]  # Top 10 priority files
    }


def get_complexity_label(score: int) -> str:
    """Get human-readable complexity label."""
    if score <= 2:
        return "Simple"
    elif score <= 4:
        return "Moderate"
    elif score <= 6:
        return "Complex"
    elif score <= 8:
        return "Very Complex"
    else:
        return "Critical"


def print_report(analysis: Dict) -> None:
    """Print human-readable analysis report."""
    if analysis["status"] == "no_changes":
        print("No changes detected.")
        return

    summary = analysis["summary"]
    risks = analysis["risks"]

    print("=" * 60)
    print("PR ANALYSIS REPORT")
    print("=" * 60)

    print(f"\nComplexity: {summary['complexity_score']}/10 ({summary['complexity_label']})")
    print(f"Files Changed: {summary['files_changed']}")
    print(f"Lines: +{summary['total_additions']} / -{summary['total_deletions']}")
    print(f"Commits: {summary['commits']}")

    # Risk summary
    print("\n--- RISK SUMMARY ---")
    print(f"Critical: {len(risks['critical'])}")
    print(f"High: {len(risks['high'])}")
    print(f"Medium: {len(risks['medium'])}")
    print(f"Low: {len(risks['low'])}")

    # Critical and high risks details
    if risks["critical"]:
        print("\n--- CRITICAL RISKS ---")
        for risk in risks["critical"]:
            print(f"  [{risk['file']}] {risk['message']} (x{risk['count']})")

    if risks["high"]:
        print("\n--- HIGH RISKS ---")
        for risk in risks["high"]:
            print(f"  [{risk['file']}] {risk['message']} (x{risk['count']})")

    # Commit message issues
    if analysis["commit_issues"]:
        print("\n--- COMMIT MESSAGE ISSUES ---")
        for issue in analysis["commit_issues"][:5]:
            print(f"  {issue['commit']}: {issue['issue']}")

    # Review order
    print("\n--- SUGGESTED REVIEW ORDER ---")
    for i, filepath in enumerate(analysis["review_order"], 1):
        file_info = next(f for f in analysis["files"] if f["path"] == filepath)
        print(f"  {i}. [{file_info['category'].upper()}] {filepath}")

    print("\n" + "=" * 60)


def main():
    parser = argparse.ArgumentParser(
        description="Analyze pull request for review complexity and risks"
    )
    parser.add_argument(
        "repo_path",
        nargs="?",
        default=".",
        help="Path to git repository (default: current directory)"
    )
    parser.add_argument(
        "--base", "-b",
        default="main",
        help="Base branch for comparison (default: main)"
    )
    parser.add_argument(
        "--head",
        default="HEAD",
        help="Head branch/commit for comparison (default: HEAD)"
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output in JSON format"
    )
    parser.add_argument(
        "--output", "-o",
        help="Write output to file"
    )

    args = parser.parse_args()

    repo_path = Path(args.repo_path).resolve()

    if not (repo_path / ".git").exists():
        print(f"Error: {repo_path} is not a git repository", file=sys.stderr)
        sys.exit(1)

    analysis = analyze_pr(repo_path, args.base, args.head)

    if args.json:
        output = json.dumps(analysis, indent=2)
        if args.output:
            with open(args.output, "w") as f:
                f.write(output)
            print(f"Results written to {args.output}")
        else:
            print(output)
    else:
        print_report(analysis)


if __name__ == "__main__":
    main()
