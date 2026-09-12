#!/usr/bin/env python3
"""
pptx-v2 inventory extraction script - backward compatible with pptx-v1

Extract structured text content from PowerPoint presentations using the enhanced
pptx-v2 InventoryExtractor class.

Usage:
    python inventory.py input.pptx output.json [--issues-only]
"""

import argparse
import sys
from pathlib import Path

# Import from parent directory
sys.path.insert(0, str(Path(__file__).parent.parent))
from manager import InventoryExtractor, Presentation


def main():
    """Main entry point for command-line usage."""
    parser = argparse.ArgumentParser(
        description="Extract text inventory from PowerPoint using pptx-v2.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python inventory.py presentation.pptx inventory.json
    Extracts text inventory with enhanced shape and formatting analysis

  python inventory.py presentation.pptx inventory.json --issues-only
    Extracts only text shapes that have formatting issues

The output JSON includes all features from pptx-v1 plus enhancements:
  - Enhanced position accuracy
  - Improved formatting detection
  - Better placeholder type recognition
  - Compatible with pptx-v1 replacement workflow
        """,
    )

    parser.add_argument("input", help="Input PowerPoint file (.pptx)")
    parser.add_argument("output", help="Output JSON file for inventory")
    parser.add_argument(
        "--issues-only",
        action="store_true",
        help="Include only text shapes that have formatting issues",
    )

    args = parser.parse_args()

    input_path = Path(args.input)
    if not input_path.exists():
        print(f"Error: Input file not found: {args.input}")
        sys.exit(1)

    if not input_path.suffix.lower() == ".pptx":
        print("Error: Input must be a PowerPoint file (.pptx)")
        sys.exit(1)

    try:
        print(f"Extracting text inventory from: {args.input}")
        if args.issues_only:
            print("Filtering to include only text shapes with issues")
        
        # Load presentation and extract inventory
        prs = Presentation(str(input_path))
        extractor = InventoryExtractor(prs)
        inventory = extractor.extract_text_inventory(issues_only=args.issues_only)

        # Save inventory
        output_path = Path(args.output)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        extractor.save_inventory(inventory, str(output_path))

        print(f"Output saved to: {args.output}")

        # Report statistics
        total_slides = len(inventory)
        total_shapes = sum(len(shapes) for shapes in inventory.values())
        if args.issues_only:
            if total_shapes > 0:
                print(f"Found {total_shapes} text elements with issues in {total_slides} slides")
            else:
                print("No issues discovered")
        else:
            print(f"Found text in {total_slides} slides with {total_shapes} text elements")

    except Exception as e:
        print(f"Error processing presentation: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()