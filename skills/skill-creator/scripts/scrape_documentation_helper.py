#!/usr/bin/env python3
"""
Documentation Scraping Helper for Skill Creator

Interactive guide for using Skill_Seekers to populate skill references from online documentation.
"""

import os
import sys
from pathlib import Path


def print_header():
    """Print welcome header"""
    print("=" * 70)
    print("Documentation Scraping Helper for Skill Creator")
    print("=" * 70)
    print()
    print("This helper guides you through using Skill_Seekers to automatically")
    print("scrape and organize documentation into your skill's references/ directory.")
    print()


def check_skill_seekers():
    """Check if Skill_Seekers is available and guide setup if needed"""
    print("Step 1: Checking for Skill_Seekers...")
    print("-" * 70)

    # Common locations to check
    home = Path.home()
    common_paths = [
        home / "Skill_Seekers",
        home / "Projects" / "Skill_Seekers",
        home / "Documents" / "Skill_Seekers",
        Path("/Users/tomdimino/Desktop/Programming/Skill_Seekers"),  # Current cloned location
    ]

    # Check if Skill_Seekers exists in any common location
    found_path = None
    for path in common_paths:
        if path.exists() and (path / "cli" / "doc_scraper.py").exists():
            found_path = path
            break

    if found_path:
        print(f"✅ Found Skill_Seekers at: {found_path}")
        return str(found_path)

    # Not found, guide user to clone
    print("❌ Skill_Seekers not found in common locations")
    print()
    print("To install Skill_Seekers:")
    print()
    print("  cd ~")
    print("  git clone https://github.com/yusufkaraaslan/Skill_Seekers.git")
    print("  cd Skill_Seekers")
    print("  pip install requests beautifulsoup4")
    print()

    # Ask if they want to provide a custom path
    custom_path = input("If you've already cloned it, enter the path (or press Enter to exit): ").strip()

    if custom_path:
        custom_path = Path(custom_path).expanduser()
        if custom_path.exists() and (custom_path / "cli" / "doc_scraper.py").exists():
            print(f"✅ Found Skill_Seekers at: {custom_path}")
            return str(custom_path)
        else:
            print(f"❌ Invalid path: {custom_path}")
            print("Please clone Skill_Seekers and run this script again.")
            sys.exit(1)
    else:
        print("Please clone Skill_Seekers and run this script again.")
        sys.exit(0)


def show_presets():
    """Show available preset configurations"""
    print()
    print("Step 2: Choose Documentation Source")
    print("-" * 70)
    print()
    print("Available preset configurations (15+):")
    print()
    print("  Web Frameworks:")
    print("    - react      (React documentation)")
    print("    - vue        (Vue.js documentation)")
    print("    - django     (Django web framework)")
    print("    - fastapi    (FastAPI Python framework)")
    print("    - laravel    (Laravel PHP framework)")
    print("    - astro      (Astro web framework)")
    print()
    print("  Game Engines:")
    print("    - godot      (Godot game engine)")
    print()
    print("  CSS & Utilities:")
    print("    - tailwind   (Tailwind CSS)")
    print()
    print("  DevOps:")
    print("    - kubernetes (Kubernetes documentation)")
    print("    - ansible    (Ansible Core)")
    print()
    print("  Or enter a custom documentation URL")
    print()


def get_user_choice():
    """Get user's choice between preset or custom"""
    choice = input("Enter preset name or 'custom' for custom URL: ").strip().lower()
    return choice


def generate_commands(skill_seekers_path, choice, skill_path=None):
    """Generate the scraping commands"""
    print()
    print("Step 3: Commands to Run")
    print("-" * 70)
    print()

    if choice == "custom":
        # Custom documentation URL
        doc_url = input("Documentation URL: ").strip()
        skill_name = input("Skill name (e.g., 'myframework'): ").strip()

        if not doc_url or not skill_name:
            print("❌ Error: URL and skill name are required")
            sys.exit(1)

        print()
        print("Run these commands:")
        print()
        print(f"  cd {skill_seekers_path}")
        print(f"  python3 cli/doc_scraper.py --url {doc_url} --name {skill_name}")
        print()

        if skill_path:
            skill_path = Path(skill_path).expanduser().absolute()
            print(f"  # Then copy references to your skill:")
            print(f"  cp -r output/{skill_name}/references/* {skill_path}/references/")
        else:
            print(f"  # Then copy references to your skill:")
            print(f"  cp -r output/{skill_name}/references/* /path/to/your-skill/references/")

    else:
        # Preset configuration
        config_file = f"configs/{choice}.json"

        print("Run these commands:")
        print()
        print(f"  cd {skill_seekers_path}")
        print(f"  python3 cli/doc_scraper.py --config {config_file}")
        print()

        if skill_path:
            skill_path = Path(skill_path).expanduser().absolute()
            print(f"  # Then copy references to your skill:")
            print(f"  cp -r output/{choice}/references/* {skill_path}/references/")
        else:
            print(f"  # Then copy references to your skill:")
            print(f"  cp -r output/{choice}/references/* /path/to/your-skill/references/")

    print()
    print("=" * 70)
    print("Optional: AI Enhancement (Recommended)")
    print("=" * 70)
    print()
    print("For higher quality SKILL.md generation, run enhancement:")
    print()
    print("  # Using Claude Code Max (free, no API key)")
    if choice == "custom":
        skill_name = input("Enter skill name again: ").strip()
        print(f"  python3 cli/enhance_skill_local.py output/{skill_name}/")
    else:
        print(f"  python3 cli/enhance_skill_local.py output/{choice}/")
    print()


def main():
    """Main function"""
    print_header()

    # Check for Skill_Seekers
    skill_seekers_path = check_skill_seekers()

    # Show available presets
    show_presets()

    # Get user choice
    choice = get_user_choice()

    # Ask for skill path (optional)
    print()
    skill_path = input("Path to your skill directory (optional, press Enter to skip): ").strip()

    # Generate commands
    generate_commands(skill_seekers_path, choice, skill_path if skill_path else None)

    print()
    print("Next Steps:")
    print("1. Run the commands above")
    print("2. Verify references/ directory is populated")
    print("3. Continue with Step 4: Update SKILL.md")
    print()


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\n\nAborted by user.")
        sys.exit(0)
