#!/usr/bin/env python3
"""
readability_scorer.py — Readability metrics for marketing copy
Usage:
  python3 readability_scorer.py --file copy.txt
  echo "Your text here" | python3 readability_scorer.py
  python3 readability_scorer.py          # demo mode
  python3 readability_scorer.py --json
"""

import argparse
import json
import math
import re
import sys


# ---------------------------------------------------------------------------
# Word lists
# ---------------------------------------------------------------------------

FILLER_WORDS = [
    "very", "really", "just", "actually", "basically", "literally",
    "honestly", "totally", "absolutely", "definitely", "certainly",
    "obviously", "clearly", "quite", "rather", "somewhat", "fairly",
    "pretty", "simply", "truly", "genuinely", "essentially",
]

# Simple passive voice detection: "was/were/is/are/been/being + past participle"
PASSIVE_PATTERN = re.compile(
    r"\b(was|were|is|are|been|being|be|am)\s+(\w+ed|known|written|built|made|done|seen|given|taken|brought|thought|found|put|set|cut|read|let|hit|hurt|cost|led|felt|kept|left|meant|sent|spent|stood|told|wore|won|beat|lost|broke|chose|drove|flew|froze|grew|hid|rang|rode|rose|ran|sank|sang|spoke|swore|swam|threw|woke|wrote)\b",
    re.IGNORECASE,
)

ADVERB_PATTERN = re.compile(r"\b\w+ly\b", re.IGNORECASE)

# Syllable estimation: count vowel groups
def count_syllables(word: str) -> int:
    word = word.lower().strip(".,!?;:\"'")
    if not word:
        return 0
    # Silent e
    if word.endswith("e") and len(word) > 2:
        word = word[:-1]
    count = len(re.findall(r"[aeiou]+", word))
    return max(1, count)


def split_sentences(text: str) -> list:
    # Split on sentence-ending punctuation
    parts = re.split(r"(?<=[.!?])\s+", text.strip())
    return [p.strip() for p in parts if p.strip()]


def split_words(text: str) -> list:
    return re.findall(r"\b[a-zA-Z]+\b", text)


# ---------------------------------------------------------------------------
# Metrics
# ---------------------------------------------------------------------------

def flesch_reading_ease(avg_sentence_len: float, avg_syllables: float) -> float:
    """Flesch Reading Ease formula."""
    score = 206.835 - (1.015 * avg_sentence_len) - (84.6 * avg_syllables)
    return round(max(0.0, min(100.0, score)), 1)


def flesch_kincaid_grade(avg_sentence_len: float, avg_syllables: float) -> float:
    """Flesch-Kincaid Grade Level formula."""
    grade = (0.39 * avg_sentence_len) + (11.8 * avg_syllables) - 15.59
    return round(max(0.0, grade), 1)


def ease_label(score: float) -> str:
    if score >= 90: return "Very Easy (5th grade)"
    if score >= 80: return "Easy (6th grade)"
    if score >= 70: return "Fairly Easy (7th grade)"
    if score >= 60: return "Standard (8-9th grade)"
    if score >= 50: return "Fairly Difficult (10-12th grade)"
    if score >= 30: return "Difficult (College)"
    return "Very Confusing (Professional)"


def analyze_text(text: str) -> dict:
    sentences = split_sentences(text)
    words = split_words(text)

    if not words:
        return {"error": "No readable text found."}

    num_sentences = max(1, len(sentences))
    num_words = len(words)

    # Syllables
    syllable_counts = [count_syllables(w) for w in words]
    total_syllables = sum(syllable_counts)

    avg_sentence_len = num_words / num_sentences
    avg_word_len = sum(len(w) for w in words) / num_words
    avg_syllables_per_word = total_syllables / num_words

    fre = flesch_reading_ease(avg_sentence_len, avg_syllables_per_word)
    fk_grade = flesch_kincaid_grade(avg_sentence_len, avg_syllables_per_word)

    # Passive voice
    passive_matches = PASSIVE_PATTERN.findall(text)
    passive_count = len(passive_matches)
    passive_pct = round(passive_count / num_sentences * 100, 1)

    # Adverbs
    adverb_matches = ADVERB_PATTERN.findall(text)
    # Filter obvious non-adverbs
    non_adverb = {"family", "early", "only", "likely", "nearly", "really",
                  "daily", "weekly", "monthly", "yearly", "friendly", "lovely",
                  "lonely", "lively", "elderly", "costly"}
    adverbs = [a for a in adverb_matches if a.lower() not in non_adverb]
    adverb_density = round(len(adverbs) / num_words * 100, 1)

    # Filler words
    text_lower = text.lower()
    word_tokens_lower = [w.lower() for w in words]
    filler_found = {fw: word_tokens_lower.count(fw) for fw in FILLER_WORDS if fw in word_tokens_lower}
    filler_total = sum(filler_found.values())

    # Scoring:
    # FRE already 0-100 (higher = easier = better for marketing copy)
    # Target for marketing: 60-80 range
    fre_score = fre  # use as-is

    return {
        "stats": {
            "word_count": num_words,
            "sentence_count": num_sentences,
            "avg_sentence_length": round(avg_sentence_len, 1),
            "avg_word_length": round(avg_word_len, 1),
            "avg_syllables_per_word": round(avg_syllables_per_word, 2),
        },
        "flesch_reading_ease": {
            "score": fre,
            "label": ease_label(fre),
            "target": "60-80 for most marketing copy",
        },
        "flesch_kincaid_grade": {
            "grade_level": fk_grade,
            "note": f"Equivalent to grade {fk_grade} reading level",
        },
        "passive_voice": {
            "count": passive_count,
            "percentage": passive_pct,
            "target": "<10%",
            "pass": passive_pct < 10,
        },
        "adverb_density": {
            "count": len(adverbs),
            "percentage": adverb_density,
            "examples": list(set(adverbs))[:8],
            "target": "<5%",
            "pass": adverb_density < 5,
        },
        "filler_words": {
            "total_count": filler_total,
            "breakdown": filler_found,
            "target": "0-3 per 100 words",
            "per_100_words": round(filler_total / num_words * 100, 1),
        },
        "overall_score": round(fre),
    }


# ---------------------------------------------------------------------------
# Demo text
# ---------------------------------------------------------------------------

DEMO_TEXT = """
Marketing copy needs to be clear, direct, and persuasive. When you write for your audience, 
you should always think about what they actually want to hear. Really good copy is basically 
about solving problems. It is very important to avoid using overly complicated language that 
might confuse the reader.

The best headlines are written by experts who truly understand their customers. A strong 
call-to-action is absolutely essential for any landing page. You need to make sure that 
every single word is earning its place on the page.

Studies show that shorter sentences improve comprehension. The average reader processes 
information faster when sentences contain fewer than 20 words. This is genuinely proven 
by research. Passive voice constructions are often used by writers who want to sound 
authoritative, but they can actually make copy feel distant and unclear.

Focus on benefits, not features. Tell the reader what they will gain. Use numbers when 
you can — "save 3 hours per week" beats "save time" every single time. Specificity 
builds trust. Vague promises are ignored.
"""


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Readability scorer for marketing copy — Flesch, passive voice, filler words."
    )
    parser.add_argument("--file", help="Path to text file")
    parser.add_argument("--json", action="store_true", help="Output as JSON")
    args = parser.parse_args()

    if args.file:
        with open(args.file, "r", encoding="utf-8", errors="replace") as f:
            text = f.read()
    elif not sys.stdin.isatty():
        text = sys.stdin.read()
        if not text.strip():
            text = DEMO_TEXT
            if not args.json:
                print("No input provided — running in demo mode.\n")
    else:
        text = DEMO_TEXT
        if not args.json:
            print("No input provided — running in demo mode.\n")

    result = analyze_text(text)

    if "error" in result:
        print(f"Error: {result['error']}", file=sys.stderr)
        sys.exit(1)

    if args.json:
        print(json.dumps(result, indent=2))
        return

    fre = result["flesch_reading_ease"]
    fk = result["flesch_kincaid_grade"]
    stats = result["stats"]
    passive = result["passive_voice"]
    adverbs = result["adverb_density"]
    fillers = result["filler_words"]
    score = result["overall_score"]

    PASS = "✅"
    FAIL = "❌"

    print("=" * 62)
    print(f"  READABILITY REPORT   Flesch Score: {fre['score']}/100")
    print("=" * 62)
    print(f"  {fre['label']}")
    print(f"  Target: {fre['target']}")
    print()
    print(f"  📊 Stats")
    print(f"     Words:              {stats['word_count']}")
    print(f"     Sentences:          {stats['sentence_count']}")
    print(f"     Avg sentence length:{stats['avg_sentence_length']} words")
    print(f"     Avg word length:    {stats['avg_word_length']} chars")
    print(f"     Syllables/word:     {stats['avg_syllables_per_word']}")
    print()
    print(f"  📐 Flesch-Kincaid Grade Level: {fk['grade_level']}")
    print(f"     {fk['note']}")
    print()

    pv_icon = PASS if passive["pass"] else FAIL
    print(f"  {pv_icon} Passive Voice: {passive['count']} instances ({passive['percentage']}%)")
    print(f"     Target: {passive['target']}")

    av_icon = PASS if adverbs["pass"] else FAIL
    print(f"  {av_icon} Adverb Density: {adverbs['count']} adverbs ({adverbs['percentage']}%)")
    if adverbs["examples"]:
        print(f"     Examples: {', '.join(adverbs['examples'][:5])}")

    filler_ok = fillers["per_100_words"] <= 3
    fw_icon = PASS if filler_ok else FAIL
    print(f"  {fw_icon} Filler Words: {fillers['total_count']} total ({fillers['per_100_words']} per 100 words)")
    if fillers["breakdown"]:
        top = sorted(fillers["breakdown"].items(), key=lambda x: -x[1])[:5]
        print(f"     Top: {', '.join(f'{w}({c})' for w,c in top)}")

    print()
    print("=" * 62)
    score_bar_len = round(score / 10)
    bar = "█" * score_bar_len + "░" * (10 - score_bar_len)
    print(f"  Readability Score:  [{bar}] {score}/100")
    print("=" * 62)


if __name__ == "__main__":
    main()
