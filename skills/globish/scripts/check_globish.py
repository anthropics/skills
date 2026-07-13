#!/usr/bin/env python3
"""
check_globish.py — Compliance checker for the Globish skill.

Scans a text or markdown draft and reports:
  1. Words not on the approved Globish vocabulary list (after stripping
     common inflections: plurals, -ed, -ing, -er, -est, -ly, possessives).
  2. Sentences longer than 15 words.
  3. Two tenses Globish does not use: past perfect continuous
     ("had been ...ing") and future perfect continuous
     ("will have been ...ing").
  4. Idioms / business clichés from idioms.txt.

Capitalized words that are NOT the first word of a sentence are treated as
likely proper nouns (names, places, products, companies) and are skipped —
Globish always permits proper nouns, technical terms defined on first use,
and numerals.

Usage:
    python3 check_globish.py path/to/draft.txt
    cat draft.txt | python3 check_globish.py -
    python3 check_globish.py path/to/draft.txt --extra-allowed my_terms.txt

Exit code is 0 whether or not issues are found — this is a report, not a
hard gate. Read the output and decide what to fix.
"""

import argparse
import re
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent

SUFFIX_RULES = [
    ("ies", "y"),
    ("ied", "y"),
    ("ing", ""),
    ("ing", "e"),
    ("ed", ""),
    ("ed", "e"),
    ("es", ""),
    ("es", "e"),
    ("s", ""),
    ("er", ""),
    ("er", "e"),
    ("est", ""),
    ("est", "e"),
    ("ly", ""),
    ("'s", ""),
    ("s'", ""),
]

SENTENCE_SPLIT_RE = re.compile(r"(?<=[.!?])\s+")
WORD_RE = re.compile(r"[A-Za-z]+(?:'[A-Za-z]+)?")

# Common irregular verbs: inflected form -> base form. Suffix stripping alone
# misses these (e.g. "sent" -> "send", "wrote" -> "write"), so they are
# checked as extra root candidates. Only the base form needs to be on the
# approved word list for the inflected form to pass.
IRREGULAR_VERBS = {
    "was": "be", "were": "be", "been": "be", "am": "be", "is": "be", "are": "be",
    "began": "begin", "begun": "begin",
    "bit": "bite", "bitten": "bite",
    "blew": "blow", "blown": "blow",
    "broke": "break", "broken": "break",
    "brought": "bring",
    "built": "build",
    "bought": "buy",
    "caught": "catch",
    "chose": "choose", "chosen": "choose",
    "came": "come",
    "cut": "cut",
    "dealt": "deal",
    "did": "do", "done": "do",
    "drew": "draw", "drawn": "draw",
    "drank": "drink", "drunk": "drink",
    "drove": "drive", "driven": "drive",
    "ate": "eat", "eaten": "eat",
    "fell": "fall", "fallen": "fall",
    "fed": "feed",
    "felt": "feel",
    "fought": "fight",
    "found": "find",
    "flew": "fly", "flown": "fly",
    "forbade": "forbid", "forbidden": "forbid",
    "forgave": "forgive", "forgiven": "forgive",
    "forgot": "forget", "forgotten": "forget",
    "froze": "freeze", "frozen": "freeze",
    "got": "get", "gotten": "get",
    "gave": "give", "given": "give",
    "went": "go", "gone": "go",
    "grew": "grow", "grown": "grow",
    "had": "have", "has": "have",
    "heard": "hear",
    "held": "hold",
    "hid": "hide", "hidden": "hide",
    "hit": "hit",
    "hurt": "hurt",
    "kept": "keep",
    "knew": "know", "known": "know",
    "laid": "lay",
    "led": "lead",
    "left": "leave",
    "lent": "lend",
    "let": "let",
    "lay": "lie", "lain": "lie",
    "lost": "lose",
    "made": "make",
    "meant": "mean",
    "met": "meet",
    "paid": "pay",
    "put": "put",
    "quit": "quit",
    "read": "read",
    "rode": "ride", "ridden": "ride",
    "rang": "ring", "rung": "ring",
    "rose": "rise", "risen": "rise",
    "ran": "run",
    "said": "say",
    "saw": "see", "seen": "see",
    "sold": "sell",
    "sent": "send",
    "set": "set",
    "shook": "shake", "shaken": "shake",
    "shone": "shine",
    "shot": "shoot",
    "shrank": "shrink", "shrunk": "shrink",
    "shut": "shut",
    "sang": "sing", "sung": "sing",
    "sank": "sink", "sunk": "sink",
    "sat": "sit",
    "slept": "sleep",
    "slid": "slide",
    "spoke": "speak", "spoken": "speak",
    "spent": "spend",
    "spread": "spread",
    "sprang": "spring", "sprung": "spring",
    "stood": "stand",
    "stole": "steal", "stolen": "steal",
    "stuck": "stick",
    "struck": "strike",
    "swore": "swear", "sworn": "swear",
    "swept": "sweep",
    "swam": "swim", "swum": "swim",
    "swung": "swing",
    "took": "take", "taken": "take",
    "taught": "teach",
    "tore": "tear", "torn": "tear",
    "told": "tell",
    "thought": "think",
    "threw": "throw", "thrown": "throw",
    "understood": "understand",
    "woke": "wake", "woken": "wake",
    "wore": "wear", "worn": "wear",
    "won": "win",
    "wound": "wind",
    "wrote": "write", "written": "write",
}

PAST_PERFECT_CONTINUOUS_RE = re.compile(
    r"\bhad\s+been\s+\w+ing\b", re.IGNORECASE
)
FUTURE_PERFECT_CONTINUOUS_RE = re.compile(
    r"\bwill\s+have\s+been\s+\w+ing\b", re.IGNORECASE
)


def load_wordlist(path: Path) -> set:
    words = set()
    for line in path.read_text(encoding="utf-8").splitlines():
        w = line.strip().lower()
        if w:
            words.add(w)
    return words


def load_idioms(path: Path) -> list:
    idioms = []
    for line in path.read_text(encoding="utf-8").splitlines():
        phrase = line.strip().lower()
        if phrase:
            idioms.append(phrase)
    return idioms


def root_forms(word: str):
    """Yield the word itself plus plausible root forms after stripping
    common English inflectional suffixes, and after checking the irregular
    verb table."""
    yield word
    if word in IRREGULAR_VERBS:
        yield IRREGULAR_VERBS[word]
    for suffix, replacement in SUFFIX_RULES:
        if word.endswith(suffix) and len(word) - len(suffix) + len(replacement) >= 2:
            yield word[: -len(suffix)] + replacement


def is_approved(word: str, approved: set) -> bool:
    return any(root in approved for root in root_forms(word))


def find_vocabulary_violations(text: str, approved: set, extra_allowed: set):
    violations = []
    seen = set()
    sentences = SENTENCE_SPLIT_RE.split(text)
    for sentence in sentences:
        tokens = WORD_RE.findall(sentence)
        for i, token in enumerate(tokens):
            lower = token.lower()
            # Skip pure numerals-as-words handled elsewhere; skip 1-letter "a"/"i"
            if lower in approved or lower in extra_allowed:
                continue
            if is_approved(lower, approved):
                continue
            # Treat capitalized, non-sentence-initial words as proper nouns.
            if token[0].isupper() and i != 0:
                continue
            # Sentence-initial capitalized word: check its lowercase form too
            # before flagging (already done above via `lower in approved`).
            if lower not in seen:
                seen.add(lower)
                violations.append(token)
    return violations


def find_long_sentences(text: str, max_words: int = 15):
    long_sentences = []
    for sentence in SENTENCE_SPLIT_RE.split(text):
        sentence = sentence.strip()
        if not sentence:
            continue
        word_count = len(WORD_RE.findall(sentence))
        if word_count > max_words:
            long_sentences.append((word_count, sentence))
    return long_sentences


def find_forbidden_tenses(text: str):
    hits = []
    for m in PAST_PERFECT_CONTINUOUS_RE.finditer(text):
        hits.append(("past perfect continuous", m.group(0)))
    for m in FUTURE_PERFECT_CONTINUOUS_RE.finditer(text):
        hits.append(("future perfect continuous", m.group(0)))
    return hits


def find_idioms(text: str, idioms: list):
    lower_text = text.lower()
    hits = [phrase for phrase in idioms if phrase in lower_text]
    return hits


def main():
    parser = argparse.ArgumentParser(description="Check a draft against the Globish framework.")
    parser.add_argument("input", help="Path to a text/markdown file, or '-' for stdin")
    parser.add_argument(
        "--wordlist",
        default=str(SCRIPT_DIR / "wordlist.txt"),
        help="Path to the approved word list (default: bundled wordlist.txt)",
    )
    parser.add_argument(
        "--idioms",
        default=str(SCRIPT_DIR / "idioms.txt"),
        help="Path to the idiom/cliche list (default: bundled idioms.txt)",
    )
    parser.add_argument(
        "--extra-allowed",
        help="Optional path to a file of extra approved terms (one per line), "
        "for domain-specific vocabulary agreed with the user.",
    )
    parser.add_argument("--max-sentence-words", type=int, default=15)
    args = parser.parse_args()

    text = sys.stdin.read() if args.input == "-" else Path(args.input).read_text(encoding="utf-8")

    approved = load_wordlist(Path(args.wordlist))
    idioms = load_idioms(Path(args.idioms))
    extra_allowed = set()
    if args.extra_allowed:
        extra_allowed = {w.strip().lower() for w in Path(args.extra_allowed).read_text(encoding="utf-8").splitlines() if w.strip()}

    vocab_violations = find_vocabulary_violations(text, approved, extra_allowed)
    long_sentences = find_long_sentences(text, args.max_sentence_words)
    tense_hits = find_forbidden_tenses(text)
    idiom_hits = find_idioms(text, idioms)

    print("=== Globish compliance report ===\n")

    print(f"Words not on the approved list ({len(vocab_violations)} unique):")
    if vocab_violations:
        for w in vocab_violations:
            print(f"  - {w}")
        print(
            "  Note: capitalized words after the start of a sentence were treated as\n"
            "  proper nouns and skipped. Review the words above: replace with an\n"
            "  approved synonym, or keep and define on first use if it's an essential\n"
            "  technical term."
        )
    else:
        print("  None found.")
    print()

    print(f"Sentences over {args.max_sentence_words} words ({len(long_sentences)}):")
    if long_sentences:
        for count, sentence in long_sentences:
            print(f"  - [{count} words] {sentence.strip()}")
    else:
        print("  None found.")
    print()

    print(f"Forbidden tenses ({len(tense_hits)}):")
    if tense_hits:
        for tense, phrase in tense_hits:
            print(f"  - {tense}: \"{phrase}\"")
    else:
        print("  None found.")
    print()

    print(f"Idioms / clichés ({len(idiom_hits)}):")
    if idiom_hits:
        for phrase in idiom_hits:
            print(f"  - {phrase}")
    else:
        print("  None found.")
    print()

    total_issues = len(vocab_violations) + len(long_sentences) + len(tense_hits) + len(idiom_hits)
    if total_issues == 0:
        print("Draft is clean. No revisions needed.")
    else:
        print(f"Total issues to review: {total_issues}")


if __name__ == "__main__":
    main()
