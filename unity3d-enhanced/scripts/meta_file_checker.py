#!/usr/bin/env python3
"""
Meta File Synchronization Checker

Ensures meta files are properly synchronized with assets in version control.
Helps prevent common Unity git workflow issues.

Usage:
    python meta_file_checker.py <unity_project_path>
    python meta_file_checker.py <unity_project_path> --check-git
"""

import subprocess
import sys
from pathlib import Path


def run_git_command(cmd, cwd):
    """Run a git command and return output."""
    try:
        result = subprocess.run(
            cmd, cwd=cwd, capture_output=True, text=True, check=True
        )
        return result.stdout
    except subprocess.CalledProcessError:
        return None


def check_git_status(project_path):
    """Check git status for meta file sync issues."""
    # Check if git repo
    git_dir = Path(project_path) / ".git"
    if not git_dir.exists():
        print("⚠ Not a git repository")
        return []

    print("Checking git status for meta file issues...\n")

    # Get staged files
    staged = run_git_command(["git", "diff", "--cached", "--name-only"], project_path)
    if not staged:
        print("✓ No staged changes\n")
        return []

    staged_files = set(staged.strip().split("\n")) if staged.strip() else set()

    issues = []

    # Check for assets without meta files
    for file_path in staged_files:
        if file_path.startswith("Assets/") and not file_path.endswith(".meta"):
            full_path = Path(project_path) / file_path
            if full_path.exists() and full_path.is_file():
                meta_file = file_path + ".meta"
                if meta_file not in staged_files:
                    issues.append(
                        {
                            "type": "missing_meta_staged",
                            "file": file_path,
                            "meta": meta_file,
                        }
                    )

    # Check for meta files without assets
    for file_path in staged_files:
        if file_path.endswith(".meta"):
            asset_file = file_path[:-5]  # Remove .meta
            full_asset_path = Path(project_path) / asset_file

            if not full_asset_path.exists():
                issues.append(
                    {
                        "type": "orphaned_meta_staged",
                        "file": file_path,
                        "asset": asset_file,
                    }
                )
            elif asset_file not in staged_files:
                issues.append(
                    {
                        "type": "meta_without_asset_staged",
                        "file": file_path,
                        "asset": asset_file,
                    }
                )

    return issues


def check_deleted_files(project_path):
    """Check for deleted assets that still have meta files."""
    git_dir = Path(project_path) / ".git"
    if not git_dir.exists():
        return []

    # Get deleted files from git status
    status = run_git_command(["git", "status", "--short"], project_path)
    if not status:
        return []

    issues = []
    for line in status.split("\n"):
        if not line.strip():
            continue

        parts = line.strip().split(maxsplit=1)
        if len(parts) != 2:
            continue

        status_code, file_path = parts

        # Check for deleted assets
        if (
            "D" in status_code
            and file_path.startswith("Assets/")
            and not file_path.endswith(".meta")
        ):
            meta_file = Path(project_path) / (file_path + ".meta")
            if meta_file.exists():
                issues.append(
                    {
                        "type": "deleted_asset_has_meta",
                        "file": file_path,
                        "meta": str(meta_file.relative_to(project_path)),
                    }
                )

    return issues


def print_issues(issues, deleted_issues):
    """Print all detected issues."""
    if not issues and not deleted_issues:
        print("✓ No meta file synchronization issues found\n")
        return False

    has_errors = False

    if issues:
        print("❌ GIT STAGING ISSUES FOUND:\n")
        has_errors = True

        for issue in issues:
            if issue["type"] == "missing_meta_staged":
                print(f"  Asset staged without meta file:")
                print(f"    Asset: {issue['file']}")
                print(f"    Missing: {issue['meta']}")
                print(f"    Fix: git add {issue['meta']}\n")

            elif issue["type"] == "orphaned_meta_staged":
                print(f"  Meta file staged without asset:")
                print(f"    Meta: {issue['file']}")
                print(f"    Missing asset: {issue['asset']}")
                print(f"    Fix: git rm {issue['file']}\n")

            elif issue["type"] == "meta_without_asset_staged":
                print(f"  Meta file staged without corresponding asset:")
                print(f"    Meta: {issue['file']}")
                print(f"    Asset not staged: {issue['asset']}")
                print(f"    Fix: git add {issue['asset']}\n")

    if deleted_issues:
        print("❌ DELETED ASSET ISSUES:\n")
        has_errors = True

        for issue in deleted_issues:
            print(f"  Asset deleted but meta file remains:")
            print(f"    Deleted: {issue['file']}")
            print(f"    Orphaned meta: {issue['meta']}")
            print(f"    Fix: git rm {issue['meta']}\n")

    return has_errors


def check_meta_sync(project_path, check_git=False):
    """Check meta file synchronization."""
    project_path = Path(project_path)

    if not project_path.exists():
        raise ValueError(f"Project path not found: {project_path}")

    assets_path = project_path / "Assets"
    if not assets_path.exists():
        raise ValueError(f"Assets directory not found: {assets_path}")

    print(f"Checking meta file synchronization: {project_path}\n")

    issues = []
    deleted_issues = []

    if check_git:
        issues = check_git_status(project_path)
        deleted_issues = check_deleted_files(project_path)

    has_errors = print_issues(issues, deleted_issues)

    # Summary
    if has_errors:
        print("=" * 60)
        print("SYNCHRONIZATION ISSUES FOUND")
        print("=" * 60)
        print("\nRecommended actions:")
        print("  1. Always stage asset and meta file together")
        print("  2. Use: git add Assets/path/to/file.ext Assets/path/to/file.ext.meta")
        print("  3. Or: git add Assets/ (to stage all changes in Assets)")
        print("  4. When deleting, remove both files: git rm file.ext file.ext.meta")
        return 1
    else:
        print("=" * 60)
        print("✓ META FILES SYNCHRONIZED")
        print("=" * 60)
        return 0


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)

    project_path = sys.argv[1]
    check_git = "--check-git" in sys.argv

    try:
        exit_code = check_meta_sync(project_path, check_git=check_git)
        sys.exit(exit_code)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)
