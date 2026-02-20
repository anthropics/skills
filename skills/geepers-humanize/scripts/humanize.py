#!/usr/bin/env python3
"""
Humanize CLI - Remove AI writing indicators from documentation

Wrapper for the DocumentHumanizer library to provide Claude Code skill interface.

Author: Luke Steuber
"""

import sys
import argparse
from pathlib import Path

# Add shared library to path
sys.path.insert(0, '/home/coolhand/shared')

try:
    from doc_humanizer import DocumentHumanizer, format_scan_results
except ImportError:
    print("Error: doc_humanizer module not found in /home/coolhand/shared", file=sys.stderr)
    print("Make sure the shared library is installed.", file=sys.stderr)
    sys.exit(1)


def main():
    """CLI entry point for humanize skill."""
    parser = argparse.ArgumentParser(
        description='Remove AI writing indicators from documentation files',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s file.md                    # Fix with default threshold (0.8)
  %(prog)s file.md --preview          # Show diff without applying
  %(prog)s file.md --confidence 0.9   # Higher confidence threshold
  %(prog)s projects/wordblocks/       # Process directory recursively
  %(prog)s --batch file1.md file2.md  # Multiple files
  %(prog)s README.md --yes            # Auto-apply without confirmation

Exit codes:
  0 - Success
  1 - Error occurred
  2 - User canceled operation
        """
    )

    parser.add_argument(
        'paths',
        nargs='+',
        help='File(s) or directory to process'
    )

    parser.add_argument(
        '--preview',
        action='store_true',
        help='Show changes without applying (like --dry-run)'
    )

    parser.add_argument(
        '--confidence',
        type=float,
        default=0.8,
        metavar='LEVEL',
        help='Confidence threshold for applying fixes (0.0-1.0, default: 0.8)'
    )

    parser.add_argument(
        '--threshold',
        type=float,
        metavar='LEVEL',
        help='Alias for --confidence (for compatibility)'
    )

    parser.add_argument(
        '--batch',
        action='store_true',
        help='Process multiple files (auto-enabled if multiple paths given)'
    )

    parser.add_argument(
        '--yes', '-y',
        action='store_true',
        help='Auto-apply changes without confirmation'
    )

    parser.add_argument(
        '--parallel',
        type=int,
        metavar='N',
        default=4,
        help='Process N files in parallel (default: 4)'
    )

    parser.add_argument(
        '--diff-only',
        action='store_true',
        help='Generate diff file without modifying original'
    )

    parser.add_argument(
        '--no-backup',
        action='store_true',
        help='Do not create .backup files'
    )

    args = parser.parse_args()

    # Use --threshold as alias for --confidence
    if args.threshold is not None:
        args.confidence = args.threshold

    # Validate confidence
    if not 0.0 <= args.confidence <= 1.0:
        print("Error: Confidence must be between 0.0 and 1.0", file=sys.stderr)
        return 1

    # Collect all files to process
    files_to_process = []
    for path_str in args.paths:
        path = Path(path_str)

        if not path.exists():
            print(f"Error: Path not found: {path}", file=sys.stderr)
            return 1

        if path.is_file():
            # Check file extension
            if path.suffix not in ['.md', '.html', '.txt']:
                print(f"Warning: Skipping unsupported file type: {path}", file=sys.stderr)
                continue
            files_to_process.append(path)

        elif path.is_dir():
            # Recursively find markdown files
            for ext in ['.md', '.html', '.txt']:
                files_to_process.extend(path.rglob(f'*{ext}'))

    if not files_to_process:
        print("Error: No supported files found (.md, .html, .txt)", file=sys.stderr)
        return 1

    # Initialize humanizer
    humanizer = DocumentHumanizer()

    # Preview mode - just scan and show diff
    if args.preview or args.diff_only:
        for filepath in files_to_process:
            print(f"\n{'='*70}")
            print(f"Analyzing: {filepath}")
            print('='*70)

            try:
                # Scan for indicators
                results = humanizer.scan_file(str(filepath))

                # Filter by confidence
                filtered = {
                    pattern: [ind for ind in indicators if ind.confidence >= args.confidence]
                    for pattern, indicators in results.items()
                }
                filtered = {k: v for k, v in filtered.items() if v}

                if not filtered:
                    print("\n✓ No AI writing indicators detected above threshold")
                    continue

                print(format_scan_results(filtered))

                # Generate diff
                with open(filepath, 'r', encoding='utf-8') as f:
                    original = f.read()

                transformed = humanizer.apply_transforms(original, args.confidence)
                diff = humanizer.generate_diff(original, transformed)

                if diff:
                    print("\n" + "─"*70)
                    print("Preview of changes:")
                    print("─"*70)
                    print(diff)

                    if args.diff_only:
                        diff_path = filepath.with_suffix(filepath.suffix + '.diff')
                        with open(diff_path, 'w', encoding='utf-8') as f:
                            f.write(diff)
                        print(f"\n✓ Diff saved to: {diff_path}")
                else:
                    print("\n✓ No changes would be made at this confidence level")

            except Exception as e:
                print(f"✗ Error processing {filepath}: {e}", file=sys.stderr)
                continue

        return 0

    # Fix mode - apply transformations
    total_fixed = 0
    total_files = len(files_to_process)

    print(f"\nProcessing {total_files} file(s) with confidence threshold {args.confidence:.1%}...")

    # Ask for confirmation if not --yes
    if not args.yes and total_files > 0:
        print(f"\nThis will modify {total_files} file(s).")
        if not args.no_backup:
            print("Backups will be created with .backup extension.")
        response = input("\nProceed? [y/N]: ").strip().lower()
        if response not in ['y', 'yes']:
            print("Canceled.")
            return 2

    for filepath in files_to_process:
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                original = f.read()

            # Apply transformations
            transformed = humanizer.apply_transforms(original, args.confidence)

            # Check if anything changed
            if transformed == original:
                print(f"✓ {filepath} - No changes needed")
                continue

            # Create backup
            if not args.no_backup:
                backup_path = Path(f"{filepath}.backup")
                with open(backup_path, 'w', encoding='utf-8') as f:
                    f.write(original)

            # Write transformed content
            with open(filepath, 'w', encoding='utf-8') as f:
                f.write(transformed)

            # Count changes (rough estimate from diff)
            diff = humanizer.generate_diff(original, transformed)
            change_count = len([line for line in diff.split('\n') if line.startswith('+') or line.startswith('-')])

            total_fixed += 1
            backup_msg = f" (backup: {filepath}.backup)" if not args.no_backup else ""
            print(f"✓ {filepath} - Fixed (~{change_count // 2} changes){backup_msg}")

        except Exception as e:
            print(f"✗ Error processing {filepath}: {e}", file=sys.stderr)
            continue

    print(f"\n{'='*70}")
    print(f"Summary: Fixed {total_fixed} of {total_files} file(s)")
    print('='*70)

    return 0


if __name__ == '__main__':
    sys.exit(main())
