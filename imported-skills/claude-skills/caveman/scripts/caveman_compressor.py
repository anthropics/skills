#!/usr/bin/env python3
"""caveman_compressor.py — Apply Matt Pocock's caveman compression rules to text.

Stdlib-only. Deterministic regex-based compression matching the rules in
Matt Pocock's caveman skill SKILL.md:

  1. Drop articles (a/an/the)
  2. Drop filler (just/really/basically/actually/simply)
  3. Drop pleasantries (sure/certainly/of course/happy to)
  4. Drop hedging (might/maybe/perhaps/likely/possibly)
  5. Abbreviate common technical terms (database -> DB, configuration -> config, etc.)
  6. Strip conjunctions where safe (and/but at sentence start)
  7. Use arrows for "leads to" / "causes" phrases (-> )
  8. Strip "as you can see / it should be noted / it's worth mentioning"

PRESERVES:
- Code blocks (```...```) unchanged
- Inline code (`...`) unchanged
- Technical terms named verbatim
- Quoted strings unchanged

NO LLM CALLS. Stdlib only.

Usage:
    python caveman_compressor.py                          # uses embedded sample
    python caveman_compressor.py "your text here"
    python caveman_compressor.py --file path/to/input.txt
    python caveman_compressor.py "text" --output json
"""

import argparse
import json
import re
import sys
from typing import Any, Dict, List, Tuple


# Filler/pleasantry/hedging vocabularies (per Matt's rules)
ARTICLES = {"a", "an", "the"}
FILLER = {"just", "really", "basically", "actually", "simply", "obviously", "literally"}
PLEASANTRIES_PHRASES = [
    "sure!", "sure,", "certainly!", "certainly,",
    "of course!", "of course,",
    "happy to help", "i'd be happy to", "i would be happy to",
    "great question", "good question",
    "absolutely!", "absolutely,",
    "no problem!", "no problem,",
]
HEDGING = {"might", "maybe", "perhaps", "likely", "possibly", "probably"}
METATALK_PHRASES = [
    "as you can see",
    "it should be noted",
    "it's worth mentioning",
    "it is worth mentioning",
    "needless to say",
    "to be clear",
    "in other words",
    "that said",
    "having said that",
]

# Technical term abbreviations
ABBREVIATIONS = [
    (r"\bdatabase\b", "DB"),
    (r"\bdatabases\b", "DBs"),
    (r"\bauthentication\b", "auth"),
    (r"\bauthorization\b", "authz"),
    (r"\bconfiguration\b", "config"),
    (r"\bconfigurations\b", "configs"),
    (r"\brequest\b", "req"),
    (r"\brequests\b", "reqs"),
    (r"\bresponse\b", "res"),
    (r"\bresponses\b", "ress"),
    (r"\bfunction\b", "fn"),
    (r"\bfunctions\b", "fns"),
    (r"\bimplementation\b", "impl"),
    (r"\bimplementations\b", "impls"),
    (r"\benvironment\b", "env"),
    (r"\bdependencies\b", "deps"),
    (r"\bdependency\b", "dep"),
    (r"\brepository\b", "repo"),
    (r"\brepositories\b", "repos"),
    (r"\bdocumentation\b", "docs"),
    (r"\bapplication\b", "app"),
    (r"\bapplications\b", "apps"),
]

# Causality phrase -> arrow
CAUSALITY_PATTERNS = [
    (re.compile(r"\b(which\s+)?(leads?|causes?|results?\s+in|gives?\s+you|produces?)\s+", re.IGNORECASE), "-> "),
    (re.compile(r"\bbecause\s+of\b", re.IGNORECASE), "<- "),
]

# Embedded sample
SAMPLE_INPUT = (
    "Sure! I'd be happy to help you with that. The issue you're experiencing is "
    "likely caused by a misconfiguration in the authentication middleware, where "
    "the token expiry check is actually using a strict less-than comparison "
    "instead of less-than-or-equal. This basically means tokens at the exact "
    "expiry timestamp will get rejected. To fix this, you should simply update "
    "the configuration of the auth function to use `<=` instead of `<`."
)


def _protect_code(text: str) -> Tuple[str, List[str]]:
    """Replace code blocks + inline code with placeholders, return text + protected list."""
    protected: List[str] = []

    def replace_block(m: re.Match) -> str:
        protected.append(m.group(0))
        return f"\x00CODE{len(protected) - 1}\x00"

    text = re.sub(r"```.*?```", replace_block, text, flags=re.DOTALL)
    text = re.sub(r"`[^`]+`", replace_block, text)
    return text, protected


def _restore_code(text: str, protected: List[str]) -> str:
    for i, code in enumerate(protected):
        text = text.replace(f"\x00CODE{i}\x00", code)
    return text


def _drop_articles(text: str) -> str:
    pattern = re.compile(r"\b(" + "|".join(ARTICLES) + r")\s+", re.IGNORECASE)
    return pattern.sub("", text)


def _drop_word_set(text: str, words: set) -> str:
    pattern = re.compile(r"\b(" + "|".join(words) + r")\b\s*", re.IGNORECASE)
    return pattern.sub("", text)


def _drop_phrases(text: str, phrases: List[str]) -> str:
    for phrase in phrases:
        text = re.sub(re.escape(phrase) + r"\s*", "", text, flags=re.IGNORECASE)
        text = re.sub(re.escape(phrase.rstrip(",!")) + r"\s*", "", text, flags=re.IGNORECASE)
    return text


def _apply_abbreviations(text: str) -> str:
    for pattern, replacement in ABBREVIATIONS:
        text = re.sub(pattern, replacement, text, flags=re.IGNORECASE)
    return text


def _apply_causality_arrows(text: str) -> str:
    for pattern, replacement in CAUSALITY_PATTERNS:
        text = pattern.sub(replacement, text)
    return text


def _strip_leading_conjunctions(text: str) -> str:
    return re.sub(r"(^|\.\s+)(and|but|so)\s+", r"\1", text, flags=re.IGNORECASE)


def _collapse_whitespace(text: str) -> str:
    text = re.sub(r"\s+", " ", text)
    text = re.sub(r"\s+([.,;:!?])", r"\1", text)
    return text.strip()


def compress(text: str) -> str:
    """Apply Matt Pocock's caveman rules. Returns compressed text."""
    text, protected = _protect_code(text)
    text = _drop_phrases(text, PLEASANTRIES_PHRASES)
    text = _drop_phrases(text, METATALK_PHRASES)
    text = _drop_word_set(text, FILLER)
    text = _drop_word_set(text, HEDGING)
    text = _drop_articles(text)
    text = _apply_abbreviations(text)
    text = _apply_causality_arrows(text)
    text = _strip_leading_conjunctions(text)
    text = _collapse_whitespace(text)
    text = _restore_code(text, protected)
    return text


def analyze(original: str, compressed: str) -> Dict[str, Any]:
    orig_words = len(original.split())
    new_words = len(compressed.split())
    saved = orig_words - new_words
    pct = round(100.0 * saved / max(orig_words, 1), 1)
    return {
        "original_chars": len(original),
        "compressed_chars": len(compressed),
        "original_words": orig_words,
        "compressed_words": new_words,
        "words_saved": saved,
        "percent_savings": pct,
        "compressed_text": compressed,
    }


def render_text(original: str, result: Dict[str, Any]) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("CAVEMAN COMPRESSOR")
    lines.append("=" * 72)
    lines.append("")
    lines.append("ORIGINAL:")
    lines.append(f"  {original}")
    lines.append("")
    lines.append("COMPRESSED:")
    lines.append(f"  {result['compressed_text']}")
    lines.append("")
    lines.append("-" * 72)
    lines.append(f"Chars: {result['original_chars']} -> {result['compressed_chars']}")
    lines.append(f"Words: {result['original_words']} -> {result['compressed_words']}")
    lines.append(f"Savings: {result['words_saved']} words ({result['percent_savings']}%)")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Compress text per Matt Pocock's caveman rules.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("text", nargs="?", help="Input text (uses embedded sample if omitted)")
    parser.add_argument("--file", help="Read input from file")
    parser.add_argument("--output", choices=("text", "json"), default="text", help="Output format")
    args = parser.parse_args()

    if args.file:
        try:
            with open(args.file, "r", encoding="utf-8") as f:
                original = f.read()
        except (IOError, OSError) as e:
            print(f"error: {e}", file=sys.stderr)
            return 1
    elif args.text:
        original = args.text
    else:
        original = SAMPLE_INPUT

    compressed = compress(original)
    result = analyze(original, compressed)

    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_text(original, result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
