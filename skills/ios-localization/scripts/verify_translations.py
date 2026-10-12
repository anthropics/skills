#!/usr/bin/env python3
"""
Verify that all translations are complete in Localizable.xcstrings.
Reports completion percentage per language and lists missing translations.

Usage: python verify_translations.py <xcstrings_path> [lang1,lang2,...]
Example: python verify_translations.py ./Localizable.xcstrings
Example: python verify_translations.py ./Localizable.xcstrings fr,de,es
"""

import json
import sys
from pathlib import Path

# Common iOS app target languages
DEFAULT_LANGUAGES = [
    "ar", "ca", "zh-Hans", "zh-Hant", "hr", "cs", "da", "nl",
    "fr", "de", "id", "it", "ja", "ko", "ms", "pl",
    "pt-PT", "pt-BR", "sk", "es", "th", "tr", "vi", "ru",
    "uk", "he", "hi", "bn", "sv", "no", "fi", "el", "ro", "hu"
]

LANGUAGE_NAMES = {
    "ar": "Arabic", "ca": "Catalan", "zh-Hans": "Chinese (Simplified)",
    "zh-Hant": "Chinese (Traditional)", "hr": "Croatian", "cs": "Czech",
    "da": "Danish", "nl": "Dutch", "fr": "French", "de": "German",
    "id": "Indonesian", "it": "Italian", "ja": "Japanese", "ko": "Korean",
    "ms": "Malay", "pl": "Polish", "pt-PT": "Portuguese (Portugal)",
    "pt-BR": "Portuguese (Brazil)", "sk": "Slovak", "es": "Spanish",
    "th": "Thai", "tr": "Turkish", "vi": "Vietnamese", "ru": "Russian",
    "uk": "Ukrainian", "he": "Hebrew", "hi": "Hindi", "bn": "Bengali",
    "sv": "Swedish", "no": "Norwegian", "fi": "Finnish", "el": "Greek",
    "ro": "Romanian", "hu": "Hungarian"
}


def detect_languages(data: dict) -> list:
    """Detect languages that have at least one translation in the file."""
    languages = set()
    strings = data.get("strings", {})

    for key, value in strings.items():
        localizations = value.get("localizations", {})
        languages.update(localizations.keys())

    # Filter to known languages and sort
    known = [lang for lang in DEFAULT_LANGUAGES if lang in languages]
    unknown = sorted([lang for lang in languages if lang not in DEFAULT_LANGUAGES])
    return known + unknown


def verify_translations(xcstrings_path: str, target_languages: list = None) -> dict:
    """
    Verify translations and return stats.
    Returns dict with completion stats and missing translations per language.
    """
    with open(xcstrings_path, "r", encoding="utf-8") as f:
        data = json.load(f)

    strings = data.get("strings", {})

    # Auto-detect languages if not specified
    if not target_languages:
        target_languages = detect_languages(data)
        if not target_languages:
            print("No translations found. Specify target languages.", file=sys.stderr)
            sys.exit(1)

    # Get list of translatable strings
    translatable = []
    for key, value in strings.items():
        if value.get("shouldTranslate") is False:
            continue
        translatable.append(key)

    total = len(translatable)
    results = {}

    for lang in target_languages:
        missing = []
        translated = 0

        for key in translatable:
            localizations = strings.get(key, {}).get("localizations", {})
            lang_data = localizations.get(lang, {})

            if lang_data.get("stringUnit", {}).get("state") == "translated":
                translated += 1
            else:
                missing.append(key)

        percentage = (translated / total * 100) if total > 0 else 0
        results[lang] = {
            "translated": translated,
            "total": total,
            "percentage": percentage,
            "missing": missing
        }

    return results, target_languages


def main():
    if len(sys.argv) < 2:
        print("Usage: python verify_translations.py <xcstrings_path> [lang1,lang2,...]", file=sys.stderr)
        print("Example: python verify_translations.py ./Localizable.xcstrings", file=sys.stderr)
        print("Example: python verify_translations.py ./Localizable.xcstrings fr,de,es", file=sys.stderr)
        sys.exit(1)

    xcstrings_path = sys.argv[1]
    target_languages = None

    if len(sys.argv) >= 3:
        target_languages = sys.argv[2].split(",")

    if not Path(xcstrings_path).exists():
        print(f"Error: File not found: {xcstrings_path}", file=sys.stderr)
        sys.exit(1)

    results, languages = verify_translations(xcstrings_path, target_languages)
    all_complete = True

    print("=" * 60)
    print("TRANSLATION VERIFICATION REPORT")
    print("=" * 60)
    print()

    # Summary table
    print(f"{'Language':<25} {'Translated':<12} {'Percentage':<12}")
    print("-" * 49)

    for lang in languages:
        stats = results[lang]
        name = LANGUAGE_NAMES.get(lang, lang)
        translated = stats["translated"]
        total = stats["total"]
        pct = stats["percentage"]

        status = "COMPLETE" if pct == 100 else ""
        print(f"{name:<25} {translated:>4}/{total:<6} {pct:>6.1f}%  {status}")

        if pct < 100:
            all_complete = False

    print()

    # Missing translations detail
    if not all_complete:
        print("=" * 60)
        print("MISSING TRANSLATIONS")
        print("=" * 60)

        for lang in languages:
            stats = results[lang]
            if stats["missing"]:
                name = LANGUAGE_NAMES.get(lang, lang)
                print(f"\n{name} ({lang}) - {len(stats['missing'])} missing:")
                for key in stats["missing"][:10]:
                    print(f"  - {key}")
                if len(stats["missing"]) > 10:
                    print(f"  ... and {len(stats['missing']) - 10} more")

    print()
    if all_complete:
        print("All translations complete!")
        sys.exit(0)
    else:
        print("Some translations are missing.")
        sys.exit(1)


if __name__ == "__main__":
    main()
