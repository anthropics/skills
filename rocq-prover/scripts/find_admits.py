#!/usr/bin/env python3
"""
Find all admits, axioms, and incomplete proofs in Rocq/Coq files.

Usage:
    python find_admits.py file.v
    python find_admits.py directory/
    python find_admits.py . --recursive

This script searches for:
- Admitted (incomplete proofs)
- admit (holes in proofs)
- Axiom (assumed axioms)
- Parameter (unproven parameters)
- Abort (aborted proof attempts)
"""

import sys
import argparse
import re
from pathlib import Path


def find_issues_in_file(file_path):
    """
    Find all admits, axioms, and incomplete proofs in a single file.

    Returns:
        List of (line_number, issue_type, context) tuples
    """
    issues = []

    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()

        for i, line in enumerate(lines, start=1):
            line_stripped = line.strip()

            # Skip comments
            if line_stripped.startswith('(*'):
                continue

            # Check for various problematic patterns
            if re.search(r'\bAdmitted\b', line):
                issues.append((i, 'Admitted', line.strip()))
            elif re.search(r'\badmit\b', line):
                issues.append((i, 'admit', line.strip()))
            elif re.search(r'\bAxiom\b', line):
                issues.append((i, 'Axiom', line.strip()))
            elif re.search(r'\bParameter\b', line) and ':' in line:
                # Only flag Parameters with types (not just imports)
                issues.append((i, 'Parameter', line.strip()))
            elif re.search(r'\bAbort\b', line):
                issues.append((i, 'Abort', line.strip()))

    except Exception as e:
        print(f"Error reading {file_path}: {e}")
        return []

    return issues


def find_coq_files(path, recursive=False):
    """Find all .v files in the given path."""
    path_obj = Path(path)

    if path_obj.is_file():
        if path_obj.suffix == '.v':
            return [path_obj]
        else:
            return []

    if recursive:
        return list(path_obj.rglob('*.v'))
    else:
        return list(path_obj.glob('*.v'))


def main():
    parser = argparse.ArgumentParser(
        description="Find all admits, axioms, and incomplete proofs in Rocq/Coq files"
    )
    parser.add_argument('path', help='Path to .v file or directory')
    parser.add_argument('--recursive', '-r', action='store_true',
                        help='Search recursively in subdirectories')
    parser.add_argument('--summary', '-s', action='store_true',
                        help='Show only summary counts')

    args = parser.parse_args()

    # Find all Coq files
    coq_files = find_coq_files(args.path, args.recursive)

    if not coq_files:
        print(f"No .v files found in {args.path}")
        return 1

    # Track statistics
    total_issues = 0
    issue_counts = {
        'Admitted': 0,
        'admit': 0,
        'Axiom': 0,
        'Parameter': 0,
        'Abort': 0
    }
    files_with_issues = 0

    # Process each file
    for file_path in sorted(coq_files):
        issues = find_issues_in_file(file_path)

        if issues:
            files_with_issues += 1
            total_issues += len(issues)

            if not args.summary:
                print(f"\n{file_path}:")

            for line_num, issue_type, context in issues:
                issue_counts[issue_type] += 1

                if not args.summary:
                    print(f"  Line {line_num}: [{issue_type}] {context}")

    # Print summary
    print(f"\n{'='*60}")
    print("SUMMARY")
    print(f"{'='*60}")
    print(f"Files scanned: {len(coq_files)}")
    print(f"Files with issues: {files_with_issues}")
    print(f"Total issues found: {total_issues}")
    print()
    print("Breakdown by type:")
    for issue_type, count in issue_counts.items():
        if count > 0:
            print(f"  {issue_type}: {count}")

    # Return non-zero exit code if issues found
    if total_issues > 0:
        print()
        print("[WARNING] Found incomplete proofs or axioms!")
        print("All proofs should end with Qed, not Admitted.")
        return 1
    else:
        print()
        print("[SUCCESS] No admits or axioms found!")
        return 0


if __name__ == "__main__":
    sys.exit(main())
