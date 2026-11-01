#!/usr/bin/env python3
"""
GUID Validator for Unity Projects

Validates GUIDs in Unity asset files and meta files, identifying common issues:
- Invalid GUID format (non-hexadecimal characters)
- Duplicate GUIDs across meta files
- Missing or orphaned meta files
- Broken asset references

Usage:
    python guid_validator.py <unity_project_path>
    python guid_validator.py <unity_project_path> --fix-orphaned
"""

import re
import sys
from pathlib import Path
from collections import defaultdict


def is_valid_guid(guid):
    """Check if GUID is valid 32-character hexadecimal string."""
    return bool(re.match(r"^[0-9a-f]{32}$", guid))


def find_meta_files(project_path):
    """Find all .meta files in the Assets directory."""
    assets_path = Path(project_path) / "Assets"
    if not assets_path.exists():
        raise ValueError(f"Assets directory not found: {assets_path}")
    return list(assets_path.rglob("*.meta"))


def extract_guid_from_meta(meta_path):
    """Extract GUID from a .meta file."""
    try:
        with open(meta_path, "r", encoding="utf-8") as f:
            for line in f:
                if line.startswith("guid:"):
                    guid = line.split(":", 1)[1].strip()
                    return guid
    except Exception as e:
        print(f"Error reading {meta_path}: {e}")
    return None


def find_asset_references(project_path, guid):
    """Find all references to a GUID in scene and prefab files."""
    assets_path = Path(project_path) / "Assets"
    references = []

    for ext in ["*.unity", "*.prefab", "*.asset", "*.mat"]:
        for file_path in assets_path.rglob(ext):
            try:
                with open(file_path, "r", encoding="utf-8") as f:
                    content = f.read()
                    if f"guid: {guid}" in content:
                        references.append(file_path)
            except Exception:
                pass

    return references


def check_orphaned_meta_files(meta_files):
    """Find meta files without corresponding assets."""
    orphaned = []
    for meta_path in meta_files:
        asset_path = Path(str(meta_path)[:-5])  # Remove .meta extension
        if not asset_path.exists():
            orphaned.append(meta_path)
    return orphaned


def check_missing_meta_files(project_path):
    """Find assets without corresponding meta files."""
    assets_path = Path(project_path) / "Assets"
    missing = []

    # Skip directories that shouldn't have meta files
    skip_dirs = {".git", ".vs", "Library", "Temp", "obj", "Logs"}

    for asset_path in assets_path.rglob("*"):
        if asset_path.is_file() and not asset_path.name.endswith(".meta"):
            # Skip files in excluded directories
            if any(skip_dir in asset_path.parts for skip_dir in skip_dirs):
                continue

            meta_path = Path(str(asset_path) + ".meta")
            if not meta_path.exists():
                missing.append(asset_path)

    return missing


def validate_guids(project_path, fix_orphaned=False):
    """Validate all GUIDs in a Unity project."""
    print(f"Validating Unity project: {project_path}\n")

    meta_files = find_meta_files(project_path)
    print(f"Found {len(meta_files)} meta files\n")

    # Track GUIDs
    guid_to_files = defaultdict(list)
    invalid_guids = []

    # Check each meta file
    for meta_path in meta_files:
        guid = extract_guid_from_meta(meta_path)
        if guid:
            if is_valid_guid(guid):
                guid_to_files[guid].append(meta_path)
            else:
                invalid_guids.append((meta_path, guid))

    # Report invalid GUIDs
    if invalid_guids:
        print("❌ INVALID GUIDs FOUND:")
        for meta_path, guid in invalid_guids:
            print(f"  {meta_path}")
            print(f"    Invalid GUID: {guid}")
            print(f"    Must be 32 hexadecimal characters (0-9, a-f)")
        print()
    else:
        print("✓ All GUIDs have valid format\n")

    # Report duplicate GUIDs
    duplicates = {
        guid: files for guid, files in guid_to_files.items() if len(files) > 1
    }
    if duplicates:
        print("❌ DUPLICATE GUIDs FOUND:")
        for guid, files in duplicates.items():
            print(f"  GUID: {guid}")
            for file_path in files:
                print(f"    - {file_path}")
        print()
    else:
        print("✓ No duplicate GUIDs\n")

    # Check for orphaned meta files
    orphaned = check_orphaned_meta_files(meta_files)
    if orphaned:
        print(f"⚠ ORPHANED META FILES ({len(orphaned)}):")
        for meta_path in orphaned:
            print(f"  {meta_path}")
            guid = extract_guid_from_meta(meta_path)
            if guid:
                refs = find_asset_references(project_path, guid)
                if refs:
                    print(f"    Referenced by: {len(refs)} file(s)")
        print()

        if fix_orphaned:
            print("Removing orphaned meta files...")
            for meta_path in orphaned:
                meta_path.unlink()
                print(f"  Deleted: {meta_path}")
            print()
    else:
        print("✓ No orphaned meta files\n")

    # Check for missing meta files
    missing = check_missing_meta_files(project_path)
    if missing:
        print(f"⚠ MISSING META FILES ({len(missing)}):")
        for asset_path in missing[:10]:  # Show first 10
            print(f"  {asset_path}")
        if len(missing) > 10:
            print(f"  ... and {len(missing) - 10} more")
        print("\nFix: Open project in Unity Editor to regenerate meta files\n")
    else:
        print("✓ No missing meta files\n")

    # Summary
    has_errors = bool(invalid_guids or duplicates or orphaned or missing)
    if has_errors:
        print("=" * 60)
        print("VALIDATION FAILED - Issues found")
        print("=" * 60)
        return 1
    else:
        print("=" * 60)
        print("✓ VALIDATION PASSED - No issues found")
        print("=" * 60)
        return 0


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)

    project_path = sys.argv[1]
    fix_orphaned = "--fix-orphaned" in sys.argv

    try:
        exit_code = validate_guids(project_path, fix_orphaned=fix_orphaned)
        sys.exit(exit_code)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)
