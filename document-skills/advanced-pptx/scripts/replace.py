#!/usr/bin/env python3
"""
pptx-v2 replacement script - backward compatible with pptx-v1

Apply text replacements to PowerPoint presentations using the enhanced
pptx-v2 ReplacementEngine class.

Usage:
    python replace.py input.pptx replacements.json output.pptx
"""

import json
import sys
from pathlib import Path

# Import from parent directory
sys.path.insert(0, str(Path(__file__).parent.parent))
from manager import ReplacementEngine, InventoryExtractor, Presentation


def apply_replacements(pptx_file: str, json_file: str, output_file: str):
    """Apply text replacements from JSON to PowerPoint presentation."""
    
    # Load presentation
    prs = Presentation(pptx_file)
    
    # Load replacement data
    with open(json_file, "r") as f:
        replacements = json.load(f)
    
    # Validate replacements against current inventory
    extractor = InventoryExtractor(prs)
    inventory = extractor.extract_text_inventory()
    
    # Validate that all shapes exist
    errors = []
    for slide_key, shapes_data in replacements.items():
        if not slide_key.startswith("slide-"):
            continue
        
        if slide_key not in inventory:
            errors.append(f"Slide '{slide_key}' not found in inventory")
            continue
        
        for shape_key in shapes_data.keys():
            if shape_key not in inventory[slide_key]:
                available_shapes = list(inventory[slide_key].keys())
                errors.append(
                    f"Shape '{shape_key}' not found on '{slide_key}'. "
                    f"Available shapes: {', '.join(available_shapes) if available_shapes else 'none'}"
                )
    
    if errors:
        print("ERROR: Invalid shapes in replacement JSON:")
        for error in errors:
            print(f"  - {error}")
        print("\nPlease check the inventory and update your replacement JSON.")
        raise ValueError(f"Found {len(errors)} validation error(s)")
    
    # Apply replacements using enhanced engine
    engine = ReplacementEngine(prs)
    success = engine.apply_replacements(replacements)
    
    if not success:
        raise ValueError("Failed to apply replacements")
    
    # Save the presentation
    prs.save(output_file)
    
    # Report results
    total_slides = len([k for k in replacements.keys() if k.startswith("slide-")])
    total_shapes = sum(
        len(shapes) for slide_key, shapes in replacements.items() 
        if slide_key.startswith("slide-")
    )
    
    print(f"Saved updated presentation to: {output_file}")
    print(f"Processed {total_slides} slides with {total_shapes} shape replacements")


def main():
    """Main entry point for command-line usage."""
    if len(sys.argv) != 4:
        print(__doc__)
        sys.exit(1)

    input_pptx = Path(sys.argv[1])
    replacements_json = Path(sys.argv[2])
    output_pptx = Path(sys.argv[3])

    if not input_pptx.exists():
        print(f"Error: Input file '{input_pptx}' not found")
        sys.exit(1)

    if not replacements_json.exists():
        print(f"Error: Replacements JSON file '{replacements_json}' not found")
        sys.exit(1)

    try:
        apply_replacements(str(input_pptx), str(replacements_json), str(output_pptx))
    except Exception as e:
        print(f"Error applying replacements: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()