#!/usr/bin/env python3
"""
Skill Packager - Creates a distributable zip file of a skill folder

Usage:
    python utils/package_skill.py <path/to/skill-folder> [output-directory]

Example:
    python utils/package_skill.py skills/public/my-skill
    python utils/package_skill.py skills/public/my-skill ./dist
"""

import sys
import zipfile
import json
import os
from pathlib import Path
from quick_validate import validate_skill


def find_marketplace_files(start_path):
    """
    Find all marketplace.json files in the directory tree starting from start_path.
    Searches current directory and up to 3 levels of parent directories.

    Args:
        start_path: Path to start searching from

    Returns:
        List of Path objects for found marketplace.json files
    """
    marketplace_files = []
    start_path = Path(start_path).resolve()

    # Search in current directory and subdirectories
    for marketplace in start_path.rglob('marketplace.json'):
        if marketplace.is_file():
            marketplace_files.append(marketplace)

    # Search upwards through parent directories (up to 3 levels)
    current = start_path.parent
    max_levels = 3
    level = 0

    while current != current.parent and level < max_levels:
        # Check current parent directory only (not recursive)
        marketplace = current / 'marketplace.json'
        if marketplace.is_file():
            marketplace_files.append(marketplace)

        # Check common subdirectories in parent
        for subdir in ['.claude-plugin', '.config', 'config']:
            marketplace = current / subdir / 'marketplace.json'
            if marketplace.is_file():
                marketplace_files.append(marketplace)

        current = current.parent
        level += 1

    return sorted(set(marketplace_files))


def add_skill_to_marketplace(marketplace_path, skill_path, skill_name):
    """
    Add a skill to the marketplace.json file.

    Args:
        marketplace_path: Path to the marketplace.json file
        skill_path: Path to the skill folder
        skill_name: Name of the skill

    Returns:
        True if successful, False otherwise
    """
    try:
        # Read existing marketplace.json
        with open(marketplace_path, 'r') as f:
            marketplace_data = json.load(f)

        # Calculate relative path from marketplace.json to skill
        # Resolve both paths to absolute before calculating relative path
        skill_path_abs = Path(skill_path).resolve()
        marketplace_dir_abs = marketplace_path.parent.resolve()

        try:
            # Use os.path.relpath to calculate relative path between any two paths
            relative_skill_path = os.path.relpath(skill_path_abs, marketplace_dir_abs)
            # Normalize the path for consistency
            if relative_skill_path.startswith('..'):
                skill_entry = f"./{relative_skill_path}"
            else:
                skill_entry = f"./{relative_skill_path}"
        except ValueError:
            # If paths are on different drives (Windows), use absolute path
            skill_entry = str(skill_path_abs)

        # Ask user which plugin to add the skill to
        plugins = marketplace_data.get('plugins', [])
        if not plugins:
            print("❌ No plugins found in marketplace.json")
            return False

        print("\nAvailable plugins in marketplace:")
        for idx, plugin in enumerate(plugins, 1):
            print(f"  {idx}. {plugin.get('name', 'Unnamed')} - {plugin.get('description', 'No description')}")

        try:
            choice = input(f"\nWhich plugin should this skill be added to? (1-{len(plugins)}): ").strip()
            plugin_idx = int(choice) - 1

            if plugin_idx < 0 or plugin_idx >= len(plugins):
                print("❌ Invalid plugin selection")
                return False

            # Add skill to selected plugin
            selected_plugin = plugins[plugin_idx]
            if 'skills' not in selected_plugin:
                selected_plugin['skills'] = []

            # Check if skill already exists
            if skill_entry in selected_plugin['skills']:
                print(f"ℹ️  Skill '{skill_entry}' already exists in plugin '{selected_plugin.get('name')}'")
                return True

            # Add the skill
            selected_plugin['skills'].append(skill_entry)

            # Write back to marketplace.json with proper formatting
            with open(marketplace_path, 'w') as f:
                json.dump(marketplace_data, f, indent=2)
                f.write('\n')  # Add trailing newline

            print(f"✅ Successfully added skill to '{selected_plugin.get('name')}' plugin in marketplace.json")
            return True

        except (ValueError, EOFError, KeyboardInterrupt):
            print("\n❌ Invalid input or cancelled")
            return False

    except json.JSONDecodeError as e:
        print(f"❌ Error parsing marketplace.json: {e}")
        return False
    except Exception as e:
        print(f"❌ Error updating marketplace.json: {e}")
        return False


def prompt_marketplace_submission(skill_name, skill_path):
    """
    Prompt the user about adding their skill to a local marketplace.json file.

    Args:
        skill_name: Name of the skill that was packaged
        skill_path: Path to the skill folder
    """
    print("\n" + "="*70)
    print("📢 Marketplace Registration")
    print("="*70)

    try:
        response = input("\nIs this skill part of a marketplace? (y/N): ").strip().lower()

        if response not in ['y', 'yes']:
            print("ℹ️  Skipping marketplace registration.")
            return

        # Search for marketplace.json files
        print("\n🔍 Searching for marketplace.json files...")
        marketplace_files = find_marketplace_files(Path(skill_path).parent)

        if not marketplace_files:
            print("❌ No marketplace.json files found in the current folder structure.")
            print("   Please create a marketplace.json file or manually add the skill.")
            return

        print(f"✅ Found {len(marketplace_files)} marketplace.json file(s)")

        # Iterate through found marketplace files
        for marketplace_path in marketplace_files:
            print(f"\n📄 Found: {marketplace_path}")

            confirm = input("   Is this the correct marketplace.json file to use? (y/N): ").strip().lower()

            if confirm in ['y', 'yes']:
                # Add skill to this marketplace
                if add_skill_to_marketplace(marketplace_path, skill_path, skill_name):
                    return  # Successfully added, we're done
                else:
                    # Failed to add, ask if they want to try another file
                    retry = input("\n   Would you like to try another marketplace.json file? (y/N): ").strip().lower()
                    if retry not in ['y', 'yes']:
                        return
            else:
                print("   Skipping this file...")

        # If we get here, we've gone through all files without success
        print("\n❌ No more marketplace.json files found in the current folder structure.")
        print("   Please manually add the skill to your marketplace.json file.")

    except (EOFError, KeyboardInterrupt):
        print("\n\nℹ️  Marketplace registration cancelled.")
    except Exception as e:
        print(f"\n❌ Unexpected error: {e}")


def package_skill(skill_path, output_dir=None):
    """
    Package a skill folder into a zip file.

    Args:
        skill_path: Path to the skill folder
        output_dir: Optional output directory for the zip file (defaults to current directory)

    Returns:
        Path to the created zip file, or None if error
    """
    skill_path = Path(skill_path).resolve()

    # Validate skill folder exists
    if not skill_path.exists():
        print(f"❌ Error: Skill folder not found: {skill_path}")
        return None

    if not skill_path.is_dir():
        print(f"❌ Error: Path is not a directory: {skill_path}")
        return None

    # Validate SKILL.md exists
    skill_md = skill_path / "SKILL.md"
    if not skill_md.exists():
        print(f"❌ Error: SKILL.md not found in {skill_path}")
        return None

    # Run validation before packaging
    print("🔍 Validating skill...")
    valid, message = validate_skill(skill_path)
    if not valid:
        print(f"❌ Validation failed: {message}")
        print("   Please fix the validation errors before packaging.")
        return None
    print(f"✅ {message}\n")

    # Determine output location
    skill_name = skill_path.name
    if output_dir:
        output_path = Path(output_dir).resolve()
        output_path.mkdir(parents=True, exist_ok=True)
    else:
        output_path = Path.cwd()

    zip_filename = output_path / f"{skill_name}.zip"

    # Create the zip file
    try:
        with zipfile.ZipFile(zip_filename, 'w', zipfile.ZIP_DEFLATED) as zipf:
            # Walk through the skill directory
            for file_path in skill_path.rglob('*'):
                if file_path.is_file():
                    # Calculate the relative path within the zip
                    arcname = file_path.relative_to(skill_path.parent)
                    zipf.write(file_path, arcname)
                    print(f"  Added: {arcname}")

        print(f"\n✅ Successfully packaged skill to: {zip_filename}")

        # Prompt about marketplace submission
        prompt_marketplace_submission(skill_name, skill_path)

        return zip_filename

    except Exception as e:
        print(f"❌ Error creating zip file: {e}")
        return None


def main():
    if len(sys.argv) < 2:
        print("Usage: python utils/package_skill.py <path/to/skill-folder> [output-directory]")
        print("\nExample:")
        print("  python utils/package_skill.py skills/public/my-skill")
        print("  python utils/package_skill.py skills/public/my-skill ./dist")
        sys.exit(1)

    skill_path = sys.argv[1]
    output_dir = sys.argv[2] if len(sys.argv) > 2 else None

    print(f"📦 Packaging skill: {skill_path}")
    if output_dir:
        print(f"   Output directory: {output_dir}")
    print()

    result = package_skill(skill_path, output_dir)

    if result:
        sys.exit(0)
    else:
        sys.exit(1)


if __name__ == "__main__":
    main()
