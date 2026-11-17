#!/usr/bin/env python3
"""
Find Prisma models with zero usage in the codebase.

This script:
1. Parses schema.prisma to find all model names
2. Searches codebase for usage patterns (prisma.modelName.*, etc.)
3. Reports models with zero usage

Usage:
    python find_orphaned_models.py <schema-path> [--search-root .]

Examples:
    python find_orphaned_models.py prisma/schema.prisma
    python find_orphaned_models.py prisma/schema.prisma --search-root .
"""

import os
import sys
import re
import argparse
import subprocess
from pathlib import Path
from typing import List, Dict, Set


def parse_prisma_schema(schema_path: str) -> List[str]:
    """Extract all model names from Prisma schema."""
    with open(schema_path, 'r') as f:
        content = f.read()

    # Find all model declarations
    # Pattern: model ModelName {
    pattern = r'model\s+(\w+)\s*\{'
    models = re.findall(pattern, content)

    return models


def search_model_usage(model_name: str, search_root: str) -> int:
    """
    Search for usage of a Prisma model in the codebase.

    Searches for patterns like:
    - prisma.modelName.
    - prisma["modelName"]
    - model references in queries

    Returns the number of usage instances found.
    """
    # Convert PascalCase to camelCase for Prisma client
    camel_case = model_name[0].lower() + model_name[1:]

    # Search patterns
    patterns = [
        f'prisma.{camel_case}.',
        f'prisma["{camel_case}"]',
        f"prisma['{camel_case}']",
        f'db.{camel_case}.',
        f'{model_name}:',  # In GraphQL or type definitions
    ]

    total_usage = 0

    for pattern in patterns:
        try:
            # Use ripgrep if available
            result = subprocess.run(
                ['rg', '-c', '--type', 'ts', '--type', 'js', pattern, search_root],
                capture_output=True,
                text=True
            )
        except FileNotFoundError:
            # Fallback to grep
            result = subprocess.run(
                ['grep', '-r', '-c', '--include=*.ts', '--include=*.tsx',
                 '--include=*.js', '--include=*.jsx', pattern, search_root],
                capture_output=True,
                text=True
            )

        if result.returncode == 0:
            # Count non-zero occurrences
            for line in result.stdout.strip().split('\n'):
                if ':' in line:
                    try:
                        count = int(line.split(':')[-1])
                        total_usage += count
                    except ValueError:
                        continue

    return total_usage


def main():
    parser = argparse.ArgumentParser(
        description='Find Prisma models with zero usage'
    )
    parser.add_argument(
        'schema_path',
        help='Path to Prisma schema file (e.g., prisma/schema.prisma)'
    )
    parser.add_argument(
        '--search-root',
        default='.',
        help='Root directory to search for model usage (default: current directory)'
    )

    args = parser.parse_args()

    if not os.path.isfile(args.schema_path):
        print(f"Error: {args.schema_path} is not a valid file")
        sys.exit(1)

    print(f"Parsing Prisma schema: {args.schema_path}")
    models = parse_prisma_schema(args.schema_path)
    print(f"Found {len(models)} models\n")

    print(f"Searching for model usage in: {args.search_root}\n")

    # Check each model
    orphaned_models = []
    used_models = []

    for model in models:
        usage_count = search_model_usage(model, args.search_root)

        if usage_count == 0:
            orphaned_models.append(model)
            print(f"❌ {model}: 0 uses (ORPHANED)")
        else:
            used_models.append((model, usage_count))
            print(f"✅ {model}: {usage_count} uses")

    # Summary
    print("\n" + "="*60)
    print(f"\nSummary:")
    print(f"  Total models: {len(models)}")
    print(f"  Used models: {len(used_models)}")
    print(f"  Orphaned models: {len(orphaned_models)}")

    if orphaned_models:
        print(f"\nOrphaned models (safe to remove):")
        for model in sorted(orphaned_models):
            print(f"  - {model}")
        return 1
    else:
        print("\nNo orphaned models found!")
        return 0


if __name__ == '__main__':
    sys.exit(main())
