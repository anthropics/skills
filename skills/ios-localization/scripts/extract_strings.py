#!/usr/bin/env python3
"""
Extract translatable strings from Localizable.xcstrings for a specific language.
Outputs JSON with strings that need translation.

Usage: python extract_strings.py <xcstrings_path> <lang_code>
Example: python extract_strings.py ./Localizable.xcstrings fr
"""

import json
import sys
from pathlib import Path


def extract_strings(xcstrings_path: str, lang_code: str) -> dict:
    """Extract strings needing translation for the given language."""
    with open(xcstrings_path, "r", encoding="utf-8") as f:
        data = json.load(f)

    strings = data.get("strings", {})
    to_translate = {}

    for key, value in strings.items():
        # Skip strings marked as shouldTranslate: false
        if value.get("shouldTranslate") is False:
            continue

        # Check if already translated for this language
        localizations = value.get("localizations", {})
        if lang_code in localizations:
            lang_data = localizations[lang_code]
            if lang_data.get("stringUnit", {}).get("state") == "translated":
                continue

        # This string needs translation
        to_translate[key] = key

    return to_translate


def main():
    if len(sys.argv) != 3:
        print("Usage: python extract_strings.py <xcstrings_path> <lang_code>", file=sys.stderr)
        print("Example: python extract_strings.py ./Localizable.xcstrings fr", file=sys.stderr)
        sys.exit(1)

    xcstrings_path = sys.argv[1]
    lang_code = sys.argv[2]

    if not Path(xcstrings_path).exists():
        print(f"Error: File not found: {xcstrings_path}", file=sys.stderr)
        sys.exit(1)

    strings = extract_strings(xcstrings_path, lang_code)
    print(json.dumps(strings, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
