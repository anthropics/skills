#!/usr/bin/env python3
"""
Mark strings as shouldTranslate: false in Localizable.xcstrings.
Removes existing localizations for marked strings.

Usage: python mark_non_translatable.py <xcstrings_path> <key1> [key2] [key3] ...
Example: python mark_non_translatable.py ./Localizable.xcstrings "1:2" "16:9" "A4" "OK"
"""

import json
import sys
from pathlib import Path


def mark_non_translatable(xcstrings_path: str, keys: list) -> int:
    """
    Mark specified keys as shouldTranslate: false.
    Returns the number of keys updated.
    """
    with open(xcstrings_path, "r", encoding="utf-8") as f:
        data = json.load(f)

    strings = data.get("strings", {})
    updated = 0

    for key in keys:
        if key in strings:
            # Remove any existing localizations
            if "localizations" in strings[key]:
                del strings[key]["localizations"]
            strings[key]["shouldTranslate"] = False
            updated += 1
            print(f"Marked: {key}")
        else:
            print(f"Warning: Key not found: {key}", file=sys.stderr)

    # Write back to file preserving Xcode's formatting (" : " separator)
    with open(xcstrings_path, "w", encoding="utf-8") as f:
        content = json.dumps(data, ensure_ascii=False, indent=2)
        # Xcode uses " : " (space before colon) for key-value separators
        import re
        content = re.sub(r'": ', '" : ', content)
        f.write(content)
        f.write("\n")

    return updated


def main():
    if len(sys.argv) < 3:
        print("Usage: python mark_non_translatable.py <xcstrings_path> <key1> [key2] ...", file=sys.stderr)
        print('Example: python mark_non_translatable.py ./Localizable.xcstrings "1:2" "16:9"', file=sys.stderr)
        sys.exit(1)

    xcstrings_path = sys.argv[1]
    keys = sys.argv[2:]

    if not Path(xcstrings_path).exists():
        print(f"Error: File not found: {xcstrings_path}", file=sys.stderr)
        sys.exit(1)

    count = mark_non_translatable(xcstrings_path, keys)
    print(f"\nTotal: {count} strings marked as shouldTranslate: false")


if __name__ == "__main__":
    main()
