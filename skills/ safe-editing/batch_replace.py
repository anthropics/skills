#!/usr/bin/env python3
"""
batch_replace.py - Safe batch string replacement with validation.

Applies multiple replacements to a file in a single pass with:
- Dry-run mode (preview changes without applying)
- Automatic backup before applying
- Uniqueness validation (warns if a search string matches multiple times)
- Unicode-aware comparison with diagnostics
- Detailed report of what changed and what failed

Usage:
    # From a JSON replacements file:
    python batch_replace.py target.js replacements.json
    python batch_replace.py target.js replacements.json --dry-run
    
    # The replacements.json format:
    [
        {"old": "original text", "new": "replacement text"},
        {"old": "another old", "new": "another new"}
    ]

    # Or from a simple TSV (tab-separated old→new):
    python batch_replace.py target.js replacements.tsv

    # With backup:
    python batch_replace.py target.js replacements.json --backup
"""

import argparse
import json
import sys
import shutil
from pathlib import Path
from datetime import datetime


def load_replacements(replacements_path):
    """Load replacements from JSON or TSV file."""
    path = Path(replacements_path)
    
    if path.suffix == '.json':
        with open(path, 'r') as f:
            data = json.load(f)
        if isinstance(data, list):
            return [(item['old'], item['new']) for item in data]
        elif isinstance(data, dict):
            return list(data.items())
    elif path.suffix in ('.tsv', '.txt'):
        replacements = []
        with open(path, 'r') as f:
            for line in f:
                line = line.rstrip('\n')
                if '\t' in line:
                    old, new = line.split('\t', 1)
                    replacements.append((old, new))
        return replacements
    else:
        # Try JSON first, then TSV
        try:
            with open(path, 'r') as f:
                data = json.load(f)
            return [(item['old'], item['new']) for item in data]
        except (json.JSONDecodeError, KeyError):
            replacements = []
            with open(path, 'r') as f:
                for line in f:
                    if '\t' in line:
                        old, new = line.rstrip('\n').split('\t', 1)
                        replacements.append((old, new))
            return replacements


def diagnose_unicode(search_str, content):
    """When a search fails, check for unicode lookalike issues."""
    issues = []
    
    # Check for common unicode confusables
    confusables = {
        '\u2018': "'",   # left single quote → apostrophe
        '\u2019': "'",   # right single quote → apostrophe
        '\u201C': '"',   # left double quote → straight quote
        '\u201D': '"',   # right double quote → straight quote
        '\u2014': '--',  # em dash → double hyphen
        '\u2013': '-',   # en dash → hyphen
        '\u00A0': ' ',   # non-breaking space → space
        '\u00E9': 'e',   # é → e (might be escaped as \u00E9 in source)
        '\u00EB': 'e',   # ë → e
        '\u00F6': 'o',   # ö → o
        '\u00FC': 'u',   # ü → u
        '\u00E0': 'a',   # à → a
    }
    
    for char in search_str:
        if char in confusables:
            # Check if the content has the ASCII equivalent instead
            ascii_version = search_str.replace(char, confusables[char])
            if ascii_version in content:
                issues.append(
                    f"  Unicode mismatch: '{char}' (U+{ord(char):04X}) "
                    f"in search, but '{confusables[char]}' in file"
                )
    
    # Check if the source file uses escaped unicode (e.g., \u00E9)
    for char in search_str:
        if ord(char) > 127:
            escaped = f"\\u{ord(char):04X}"
            if escaped in content:
                issues.append(
                    f"  File uses escape '{escaped}' but search has literal '{char}'"
                )
    
    # Check for whitespace issues
    if '  ' in search_str and '  ' not in content:
        issues.append("  Double space in search string not found in file")
    if '\t' in search_str and '\t' not in content:
        issues.append("  Tab in search string but file may use spaces")
    
    return issues


def batch_replace(target_path, replacements, dry_run=False, backup=False):
    """
    Apply multiple replacements to a file.
    
    Returns: (applied_count, skipped_count, errors)
    """
    target = Path(target_path)
    if not target.exists():
        print(f"Error: {target} not found")
        return 0, 0, [f"File not found: {target}"]

    with open(target, 'r', errors='replace') as f:
        original = f.read()
    
    content = original
    applied = []
    skipped = []
    errors = []

    # Validation pass: check all replacements first
    print(f"{'DRY RUN - ' if dry_run else ''}Validating {len(replacements)} replacements...\n")
    
    for i, (old, new) in enumerate(replacements, 1):
        count = content.count(old)
        
        if count == 0:
            # Try to diagnose why
            diagnostics = diagnose_unicode(old, content)
            if diagnostics:
                errors.append((i, old, "NOT FOUND (unicode issue)", diagnostics))
            else:
                errors.append((i, old, "NOT FOUND", []))
        elif count > 1:
            errors.append((i, old, f"AMBIGUOUS ({count} matches)", []))
        else:
            applied.append((i, old, new))

    # Report validation results
    if applied:
        print(f"  Ready to apply: {len(applied)} replacements")
    if errors:
        print(f"  Problems found: {len(errors)}\n")
        for num, old, issue, diagnostics in errors:
            preview = old[:60].replace('\n', '\\n')
            print(f"  #{num}: {issue}")
            print(f"    Search: \"{preview}{'...' if len(old) > 60 else ''}\"")
            for diag in diagnostics:
                print(f"    {diag}")
            print()

    if dry_run:
        print(f"\nDRY RUN complete. {len(applied)} would apply, {len(errors)} have issues.")
        if applied:
            print(f"\nChanges that would be made:")
            for num, old, new in applied:
                old_preview = old[:50].replace('\n', '\\n')
                new_preview = new[:50].replace('\n', '\\n')
                print(f"  #{num}: \"{old_preview}\" → \"{new_preview}\"")
        return len(applied), 0, errors

    if not applied:
        print("Nothing to apply.")
        return 0, len(errors), errors

    # Create backup if requested
    if backup:
        backup_path = target.with_suffix(target.suffix + '.bak')
        shutil.copy2(target, backup_path)
        print(f"\nBackup: {backup_path}")

    # Apply all valid replacements
    for num, old, new in applied:
        content = content.replace(old, new)

    # Write result
    with open(target, 'w') as f:
        f.write(content)

    print(f"\nApplied {len(applied)} replacements to {target.name}")
    if errors:
        print(f"Skipped {len(errors)} (see errors above)")

    return len(applied), len(errors), errors


def main():
    parser = argparse.ArgumentParser(
        description="Safe batch string replacement with validation"
    )
    parser.add_argument("target", help="File to edit")
    parser.add_argument("replacements", help="JSON or TSV file with replacements")
    parser.add_argument("--dry-run", action="store_true",
                        help="Preview changes without applying")
    parser.add_argument("--backup", action="store_true",
                        help="Create .bak backup before applying")
    args = parser.parse_args()

    replacements = load_replacements(args.replacements)
    if not replacements:
        print("No replacements loaded")
        sys.exit(1)

    applied, skipped, errors = batch_replace(
        args.target, replacements,
        dry_run=args.dry_run,
        backup=args.backup
    )

    sys.exit(0 if not errors else 1)


if __name__ == "__main__":
    main()
