#!/usr/bin/env python3
"""
Validate pixel art sprite sheet specifications.
Checks for common issues and inconsistencies.
"""

import re
import sys
from typing import List, Tuple


def validate_spec(spec_text: str) -> Tuple[bool, List[str]]:
    """
    Validate a sprite sheet specification.

    Returns:
        Tuple of (is_valid, list_of_issues)
    """
    issues = []

    # Check for required sections
    required_sections = [
        ("Canvas:", "Missing canvas dimensions"),
        ("Grid:", "Missing grid layout"),
        ("Cell Size:", "Missing cell size"),
        ("Palette:", "Missing color palette"),
    ]

    for section, error in required_sections:
        if section not in spec_text:
            issues.append(error)

    # Extract and validate dimensions
    canvas_match = re.search(r"Canvas:\s*(\d+)\s*x\s*(\d+)", spec_text, re.IGNORECASE)
    grid_match = re.search(r"Grid:\s*(\d+)\s*Rows?\s*x\s*(\d+)\s*Columns?", spec_text, re.IGNORECASE)
    cell_match = re.search(r"Cell Size:\s*(\d+)\s*x\s*(\d+)", spec_text, re.IGNORECASE)

    if canvas_match and grid_match and cell_match:
        canvas_w, canvas_h = int(canvas_match.group(1)), int(canvas_match.group(2))
        grid_rows, grid_cols = int(grid_match.group(1)), int(grid_match.group(2))
        cell_w, cell_h = int(cell_match.group(1)), int(cell_match.group(2))

        expected_w = grid_cols * cell_w
        expected_h = grid_rows * cell_h

        if canvas_w != expected_w:
            issues.append(f"Canvas width mismatch: {canvas_w} != {grid_cols} cols x {cell_w}px = {expected_w}")
        if canvas_h != expected_h:
            issues.append(f"Canvas height mismatch: {canvas_h} != {grid_rows} rows x {cell_h}px = {expected_h}")

    # Check palette color count
    palette_match = re.search(r"Palette:\s*(\d+)\s*colors?", spec_text, re.IGNORECASE)
    if palette_match:
        color_count = int(palette_match.group(1))
        valid_counts = [2, 4, 8, 16, 32, 64, 256]
        if color_count not in valid_counts:
            issues.append(f"Unusual palette size: {color_count}. Standard sizes: {valid_counts}")

    # Check for row descriptions
    row_matches = re.findall(r"Row\s*\d+:", spec_text)
    if grid_match:
        expected_rows = int(grid_match.group(1))
        if len(row_matches) != expected_rows:
            issues.append(f"Row count mismatch: found {len(row_matches)} row descriptions, expected {expected_rows}")

    # Check frame descriptions per row
    frame_pattern = r"Frame\s*\d+:"
    for i, row_match in enumerate(re.finditer(r"### Row \d+:.*?(?=### Row|\Z)", spec_text, re.DOTALL)):
        row_text = row_match.group(0)
        frame_count = len(re.findall(frame_pattern, row_text))
        if grid_match and frame_count > 0:
            expected_frames = int(grid_match.group(2))  # columns
            if frame_count != expected_frames:
                issues.append(f"Row {i+1}: found {frame_count} frames, expected {expected_frames}")

    # Check background color format
    bg_match = re.search(r"Background:.*?(#[0-9A-Fa-f]{6})", spec_text)
    if not bg_match:
        issues.append("Missing or invalid background hex color (should be #RRGGBB format)")

    return len(issues) == 0, issues


def main():
    if len(sys.argv) < 2:
        print("Usage: validate_spec.py <spec_file.md>")
        print("       validate_spec.py --stdin")
        sys.exit(1)

    if sys.argv[1] == "--stdin":
        spec_text = sys.stdin.read()
    else:
        with open(sys.argv[1], 'r') as f:
            spec_text = f.read()

    is_valid, issues = validate_spec(spec_text)

    if is_valid:
        print("Specification is valid.")
        sys.exit(0)
    else:
        print("Specification has issues:")
        for issue in issues:
            print(f"  - {issue}")
        sys.exit(1)


if __name__ == "__main__":
    main()
