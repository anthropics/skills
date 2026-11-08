#!/usr/bin/env python3
"""
Find files with zero imports in a codebase.

Usage:
    python find_unused_imports.py <directory> [--extensions .ts,.tsx,.js,.jsx]

Examples:
    python find_unused_imports.py lib/
    python find_unused_imports.py components/ --extensions .tsx,.ts
"""

import os
import sys
import argparse
import subprocess
from pathlib import Path
from typing import Set, List, Tuple


def find_files(directory: str, extensions: List[str]) -> List[Path]:
    """Find all files with given extensions in directory."""
    files = []
    for ext in extensions:
        # Use find command for efficiency
        result = subprocess.run(
            ['find', directory, '-name', f'*{ext}', '-type', 'f'],
            capture_output=True,
            text=True
        )
        if result.returncode == 0:
            files.extend([Path(p) for p in result.stdout.strip().split('\n') if p])
    return files


def check_file_usage(file_path: Path, search_root: str) -> int:
    """
    Count how many times a file is imported.
    Returns the number of import statements found.
    """
    # Generate search patterns for different import styles
    file_name = file_path.stem
    file_name_with_ext = file_path.name
    relative_path = str(file_path.relative_to(search_root))

    # Common import patterns to search for
    patterns = [
        f"from '{relative_path}'",
        f'from "{relative_path}"',
        f"from './{file_name}'",
        f'from "./{file_name}"',
        f"from '@/{relative_path}",
        f"import '{relative_path}'",
        f'import "{relative_path}"',
    ]

    total_imports = 0
    for pattern in patterns:
        # Use ripgrep (rg) if available, otherwise grep
        try:
            result = subprocess.run(
                ['rg', '-c', pattern, search_root],
                capture_output=True,
                text=True
            )
        except FileNotFoundError:
            result = subprocess.run(
                ['grep', '-r', '-c', pattern, search_root],
                capture_output=True,
                text=True
            )

        if result.returncode == 0:
            # Count non-zero counts
            for line in result.stdout.strip().split('\n'):
                if ':' in line:
                    count = int(line.split(':')[1])
                    total_imports += count

    return total_imports


def main():
    parser = argparse.ArgumentParser(
        description='Find files with zero imports in a codebase'
    )
    parser.add_argument(
        'directory',
        help='Directory to search for unused files'
    )
    parser.add_argument(
        '--extensions',
        default='.ts,.tsx,.js,.jsx',
        help='Comma-separated file extensions to check (default: .ts,.tsx,.js,.jsx)'
    )
    parser.add_argument(
        '--search-root',
        help='Root directory to search for imports (defaults to current directory)'
    )

    args = parser.parse_args()

    if not os.path.isdir(args.directory):
        print(f"Error: {args.directory} is not a valid directory")
        sys.exit(1)

    extensions = [ext.strip() for ext in args.extensions.split(',')]
    search_root = args.search_root or '.'

    print(f"Searching for unused files in: {args.directory}")
    print(f"Extensions: {', '.join(extensions)}")
    print(f"Search root: {search_root}\n")

    # Find all files
    files = find_files(args.directory, extensions)
    print(f"Found {len(files)} files to check\n")

    # Check each file
    unused_files = []
    for file_path in files:
        import_count = check_file_usage(file_path, search_root)
        if import_count == 0:
            unused_files.append(file_path)

    # Report results
    if unused_files:
        print(f"Found {len(unused_files)} unused files:\n")
        for file_path in sorted(unused_files):
            print(f"  - {file_path}")
    else:
        print("No unused files found!")

    return 0 if not unused_files else 1


if __name__ == '__main__':
    sys.exit(main())
