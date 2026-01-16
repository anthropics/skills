#!/usr/bin/env python3
"""
Convert all Agent Skills to different platform formats

This is a master conversion tool that converts skills to all supported platforms.

Usage:
    python convert_all.py <skills_dir> <output_base_dir>
    
Example:
    python convert_all.py ../skills ../adapters-output
"""

import sys
from pathlib import Path

# Add adapter directories to path
sys.path.insert(0, str(Path(__file__).parent))

from cursor.convert_to_cursor import convert_all_skills as convert_cursor
from trae.convert_to_trae import convert_all_skills as convert_trae
from qoder.convert_to_qoder import convert_all_skills as convert_qoder
from codebuddy.convert_to_codebuddy import convert_all_skills as convert_codebuddy
from windsurf.convert_to_windsurf import convert_all_skills as convert_windsurf


def convert_to_all_platforms(skills_dir, output_base_dir):
    """
    Convert all skills to all supported platforms
    
    Args:
        skills_dir: Directory containing skills
        output_base_dir: Base output directory
    """
    output_base = Path(output_base_dir)
    output_base.mkdir(parents=True, exist_ok=True)
    
    print("🚀 Starting conversion to all platforms...\n")
    
    # Convert to Cursor
    print("📝 Converting to Cursor format...")
    try:
        convert_cursor(skills_dir, output_base / "cursor")
        print("✅ Cursor conversion completed\n")
    except Exception as e:
        print(f"❌ Cursor conversion failed: {e}\n")
    
    # Convert to Trae
    print("🔌 Converting to Trae format...")
    try:
        convert_trae(skills_dir, output_base / "trae")
        print("✅ Trae conversion completed\n")
    except Exception as e:
        print(f"❌ Trae conversion failed: {e}\n")
    
    # Convert to Qoder
    print("🤖 Converting to Qoder format...")
    try:
        convert_qoder(skills_dir, output_base / "qoder")
        print("✅ Qoder conversion completed\n")
    except Exception as e:
        print(f"❌ Qoder conversion failed: {e}\n")
    
    # Convert to CodeBuddy
    print("🔄 Converting to CodeBuddy format...")
    try:
        convert_codebuddy(skills_dir, output_base / "codebuddy")
        print("✅ CodeBuddy conversion completed\n")
    except Exception as e:
        print(f"❌ CodeBuddy conversion failed: {e}\n")
    
    # Convert to Windsurf
    print("🌊 Converting to Windsurf format...")
    try:
        convert_windsurf(skills_dir, output_base / "windsurf")
        print("✅ Windsurf conversion completed\n")
    except Exception as e:
        print(f"❌ Windsurf conversion failed: {e}\n")
    
    print("🎉 All conversions completed!")
    print(f"\nOutput directories:")
    print(f"  - Cursor: {output_base / 'cursor'}")
    print(f"  - Trae: {output_base / 'trae'}")
    print(f"  - Qoder: {output_base / 'qoder'}")
    print(f"  - CodeBuddy: {output_base / 'codebuddy'}")
    print(f"  - Windsurf: {output_base / 'windsurf'}")


if __name__ == "__main__":
    if len(sys.argv) < 3:
        print("Usage: python convert_all.py <skills_dir> <output_base_dir>")
        print("\nExample:")
        print("  python convert_all.py ../skills ../adapters-output")
        sys.exit(1)
    
    skills_dir = sys.argv[1]
    output_base_dir = sys.argv[2]
    
    convert_to_all_platforms(skills_dir, output_base_dir)
