#!/usr/bin/env python3
"""
Apple HIG Compliance Checker
Quantitative checks for tap targets, contrast, and typography.
"""

import sys
import argparse
import json
import math

def calculate_luminance(hex_color):
    """Calculates relative luminance for a given hex color."""
    hex_color = hex_color.lstrip('#')
    if len(hex_color) != 6:
        return 0
    
    r, g, b = [int(hex_color[i:i+2], 16) / 255.0 for i in (0, 2, 4)]
    
    def adjust(c):
        return c / 12.92 if c <= 0.03928 else ((c + 0.055) / 1.055) ** 2.4
    
    return 0.2126 * adjust(r) + 0.7152 * adjust(g) + 0.0722 * adjust(b)

def check_contrast(fg, bg):
    """Checks contrast ratio between foreground and background."""
    l1 = calculate_luminance(fg)
    l2 = calculate_luminance(bg)
    
    if l1 < l2:
        l1, l2 = l2, l1
        
    ratio = (l1 + 0.05) / (l2 + 0.05)
    return round(ratio, 2)

def main():
    parser = argparse.ArgumentParser(description="Apple HIG Compliance Checker")
    subparsers = parser.add_subparsers(dest="command", help="Compliance command")
    
    # Contrast command
    contrast_parser = subparsers.add_parser("contrast", help="Check contrast ratio")
    contrast_parser.add_argument("fg", help="Foreground Hex (e.g. #FFFFFF)")
    contrast_parser.add_argument("bg", help="Background Hex (e.g. #000000)")
    
    # Target command
    target_parser = subparsers.add_parser("target", help="Check tap target size")
    target_parser.add_argument("width", type=int, help="Width in points")
    target_parser.add_argument("height", type=int, help="Height in points")
    
    # Batch command
    batch_parser = subparsers.add_parser("batch", help="Batch check from JSON")
    batch_parser.add_argument("file", help="Path to JSON file")
    
    args = parser.parse_args()
    
    results = {"score": 100, "violations": []}
    
    if args.command == "contrast":
        ratio = check_contrast(args.fg, args.bg)
        status = "PASSED" if ratio >= 4.5 else "FAILED"
        print(f"Contrast Ratio: {ratio} [{status}]")
        if status == "FAILED":
            print("Recommendation: Increase contrast to at least 4.5:1 for accessibility.")
            
    elif args.command == "target":
        if args.width < 44 or args.height < 44:
            print(f"Tap Target: {args.width}x{args.height} [FAILED]")
            print("Recommendation: Minimum tap target size is 44x44 points per Apple HIG.")
        else:
            print(f"Tap Target: {args.width}x{args.height} [PASSED]")
            
    elif args.command == "batch":
        try:
            with open(args.file, 'r') as f:
                data = json.load(f)
                # Sample batch processing
                for item in data.get("checks", []):
                    if item['type'] == 'contrast':
                        r = check_contrast(item['fg'], item['bg'])
                        if r < 4.5:
                            results["violations"].append(f"Contrast {r} fails for {item.get('name', 'element')}")
                            results["score"] -= 10
                    elif item['type'] == 'target':
                        if item['w'] < 44 or item['h'] < 44:
                            results["violations"].append(f"Target {item['w']}x{item['h']} small for {item.get('name', 'element')}")
                            results["score"] -= 10
                            
            print(json.dumps(results, indent=2))
        except Exception as e:
            print(f"Error: {e}")
            sys.exit(1)
            
    else:
        parser.print_help()

if __name__ == "__main__":
    main()
