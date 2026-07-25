#!/usr/bin/env python3
"""
Skill Packager — creates a deployable .zip of a rootnode Skill folder.

Packages the rootnode Skill folder structure:
    {skill-name}/SKILL.md
    {skill-name}/references/*.md
    {skill-name}/scripts/*
    {skill-name}/agents/*.md
    {skill-name}/eval-viewer/*

Audit artifacts are NOT included — they ship separately per
root_SKILL_BUILD_DISCIPLINE.md §4.4.

Usage:
    python scripts/package_zip.py <path/to/skill-folder> [--output OUTPUT_PATH]

Example:
    python scripts/package_zip.py rootnode-skill-builder/
    python scripts/package_zip.py rootnode-skill-builder/ --output design/audit-artifacts/v3.0/rootnode-skill-builder.zip
"""

import argparse
import fnmatch
import sys
import zipfile
from pathlib import Path

from scripts.quick_validate import validate_skill

EXCLUDE_DIRS = {"__pycache__", "node_modules"}
EXCLUDE_GLOBS = {"*.pyc"}
EXCLUDE_FILES = {".DS_Store"}
# Directories excluded only at the skill root (not when nested deeper).
ROOT_EXCLUDE_DIRS = {"evals", "audit-artifacts"}


def should_exclude(rel_path: Path) -> bool:
    """Check whether a path should be excluded from packaging."""
    parts = rel_path.parts
    if any(part in EXCLUDE_DIRS for part in parts):
        return True
    # rel_path is relative to skill_path.parent, so parts[0] is the skill
    # folder name and parts[1] (if present) is the first subdir.
    if len(parts) > 1 and parts[1] in ROOT_EXCLUDE_DIRS:
        return True
    name = rel_path.name
    if name in EXCLUDE_FILES:
        return True
    return any(fnmatch.fnmatch(name, pat) for pat in EXCLUDE_GLOBS)


def package_zip(skill_path, output_path=None):
    """
    Package a Skill folder into a .zip file.

    Args:
        skill_path: Path to the Skill folder.
        output_path: Optional output .zip path. Defaults to {skill-name}.zip in cwd.

    Returns:
        Path to the created .zip file, or None on error.
    """
    skill_path = Path(skill_path).resolve()

    if not skill_path.exists():
        print(f"Error: Skill folder not found: {skill_path}")
        return None

    if not skill_path.is_dir():
        print(f"Error: Path is not a directory: {skill_path}")
        return None

    skill_md = skill_path / "SKILL.md"
    if not skill_md.exists():
        print(f"Error: SKILL.md not found in {skill_path}")
        return None

    print("Validating Skill...")
    valid, message = validate_skill(skill_path)
    if not valid:
        print(f"Validation failed: {message}")
        print("   Fix the validation errors before packaging.")
        return None
    print(f"OK: {message}\n")

    skill_name = skill_path.name
    if output_path:
        output_path = Path(output_path).resolve()
        output_path.parent.mkdir(parents=True, exist_ok=True)
        zip_filename = output_path
    else:
        zip_filename = Path.cwd() / f"{skill_name}.zip"

    try:
        with zipfile.ZipFile(zip_filename, 'w', zipfile.ZIP_DEFLATED) as zipf:
            for file_path in skill_path.rglob('*'):
                if not file_path.is_file():
                    continue
                arcname = file_path.relative_to(skill_path.parent)
                if should_exclude(arcname):
                    print(f"  Skipped: {arcname}")
                    continue
                zipf.write(file_path, arcname)
                print(f"  Added: {arcname}")

        print(f"\nSuccessfully packaged Skill to: {zip_filename}")
        return zip_filename

    except Exception as e:
        print(f"Error creating .zip: {e}")
        return None


def main():
    parser = argparse.ArgumentParser(
        description="Package a rootnode Skill folder into a deployable .zip"
    )
    parser.add_argument("skill_path", help="Path to the Skill folder")
    parser.add_argument(
        "--output",
        default=None,
        help="Output .zip path (default: {skill-name}.zip in current directory)",
    )
    args = parser.parse_args()

    print(f"Packaging Skill: {args.skill_path}")
    if args.output:
        print(f"   Output: {args.output}")
    print()

    result = package_zip(args.skill_path, args.output)
    sys.exit(0 if result else 1)


if __name__ == "__main__":
    main()
