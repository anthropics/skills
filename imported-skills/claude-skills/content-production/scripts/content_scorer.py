#!/usr/bin/env python3
"""content_scorer.py — scores content 0-100 on readability, SEO, structure, and engagement."""

import sys
import re
import json
import math
from collections import Counter

# ── Sample content for zero-config demo run ──────────────────────────────────
SAMPLE_CONTENT = """
Title: How to Reduce Churn in SaaS: 7 Proven Tactics That Actually Work

Introduction

Most SaaS companies discover their churn problem too late — after the customer has already left. By then, the damage is done. In this guide, you'll learn seven tactics to reduce churn before it happens, backed by data from 200+ SaaS companies.

## Why Customers Churn (It's Not What You Think)

Customers don't churn because your product is bad. They churn because they never saw value. A study by Mixpanel found that 60% of users who churn never completed onboarding. That's a product adoption problem, not a satisfaction problem.

Fix the adoption gap first. Everything else is downstream.

## Tactic 1: Instrument Your Activation Funnel

You can't fix what you can't see. Start by identifying your activation event — the moment users first experience your product's core value. For Slack, it's sending 2,000 messages. For Dropbox, it's saving a first file.

Map the funnel from signup to activation. Find where users drop off. That's your highest-leverage intervention point.

## Tactic 2: Segment Your Churn by Cohort

Not all churn is equal. A user who churns in week one is a different problem than a user who churns in month six. Cohort analysis breaks this apart.

Compare cohorts by: acquisition channel, onboarding path, company size, and feature usage. You'll find that certain cohorts churn 3-4x more than others. Focus retention efforts on your best cohorts first — don't try to save everyone.

## Tactic 3: Build a Customer Health Score

A health score is a composite signal that predicts churn before it happens. Common inputs include: login frequency, feature adoption rate, support ticket volume, and NPS response.

Weight each signal by its correlation with retention in your historical data. A score below 40 should trigger a customer success outreach. Don't wait for the cancellation request.

## Conclusion

Churn is a lagging indicator. By the time you see it, the problem happened weeks ago. Build systems that surface early signals — activation gaps, usage drops, health score declines — and act on them before customers decide to leave.

Start with one tactic. Instrument your activation funnel this week.
"""

SAMPLE_KEYWORD = "reduce churn"
SAMPLE_TITLE = "How to Reduce Churn in SaaS: 7 Proven Tactics That Actually Work"


# ── Scoring functions ─────────────────────────────────────────────────────────

def count_syllables(word: str) -> int:
    """Approximate syllable count using vowel-group heuristic."""
    word = word.lower().strip(".,!?;:")
    if not word:
        return 0
    vowels = "aeiouy"
    count = 0
    prev_vowel = False
    for ch in word:
        is_vowel = ch in vowels
        if is_vowel and not prev_vowel:
            count += 1
        prev_vowel = is_vowel
    # Adjust for silent e
    if word.endswith("e") and len(word) > 2:
        count = max(1, count - 1)
    return max(1, count)


def flesch_reading_ease(text: str) -> float:
    """
    Flesch Reading Ease score.
    206.835 - 1.015 * (words/sentences) - 84.6 * (syllables/words)
    Higher = easier. Target: 60-70 for professional content.
    """
    sentences = re.split(r'[.!?]+', text)
    sentences = [s.strip() for s in sentences if s.strip()]
    n_sentences = max(1, len(sentences))

    words = re.findall(r'\b[a-zA-Z]+\b', text)
    n_words = max(1, len(words))

    n_syllables = sum(count_syllables(w) for w in words)

    asl = n_words / n_sentences  # avg sentence length
    asw = n_syllables / n_words  # avg syllables per word

    score = 206.835 - (1.015 * asl) - (84.6 * asw)
    return round(max(0.0, min(100.0, score)), 1)


def score_readability(text: str) -> dict:
    """Score readability 0-25 (25% of total)."""
    fre = flesch_reading_ease(text)

    # FRE → points (target 60-70 for B2B)
    if fre >= 65:
        fre_points = 15
    elif fre >= 55:
        fre_points = 12
    elif fre >= 45:
        fre_points = 8
    elif fre >= 35:
        fre_points = 4
    else:
        fre_points = 0

    # Sentence length variance
    sentences = re.split(r'[.!?]+', text)
    sentences = [s.strip() for s in sentences if len(s.split()) > 2]
    lengths = [len(s.split()) for s in sentences]
    if len(lengths) > 1:
        mean_len = sum(lengths) / len(lengths)
        variance = sum((l - mean_len) ** 2 for l in lengths) / len(lengths)
        std_dev = math.sqrt(variance)
        variance_points = min(10, int(std_dev))  # good variance = high std dev
    else:
        variance_points = 0

    total = min(25, fre_points + variance_points)
    return {
        "score": total,
        "max": 25,
        "flesch_reading_ease": fre,
        "sentence_length_std_dev": round(math.sqrt(variance) if len(lengths) > 1 else 0, 1)
    }


def score_seo(text: str, title: str = "", keyword: str = "") -> dict:
    """Score SEO signals 0-25 (25% of total)."""
    text_lower = text.lower()
    title_lower = title.lower()
    keyword_lower = keyword.lower()

    points = 0
    signals = {}

    # Title contains keyword
    if keyword_lower and keyword_lower in title_lower:
        points += 7
        signals["keyword_in_title"] = True
    else:
        signals["keyword_in_title"] = False

    # Keyword in first 100 words
    first_100 = " ".join(re.findall(r'\b\w+\b', text_lower)[:100])
    if keyword_lower and keyword_lower in first_100:
        points += 5
        signals["keyword_in_intro"] = True
    else:
        signals["keyword_in_intro"] = False

    # Keyword density (target 0.5-2%)
    words = re.findall(r'\b\w+\b', text_lower)
    n_words = max(1, len(words))
    kw_words = keyword_lower.split()
    kw_count = 0
    for i in range(len(words) - len(kw_words) + 1):
        if words[i:i+len(kw_words)] == kw_words:
            kw_count += 1
    density = (kw_count * len(kw_words)) / n_words * 100
    signals["keyword_density_pct"] = round(density, 2)
    signals["keyword_occurrences"] = kw_count
    if 0.5 <= density <= 2.5:
        points += 5
    elif kw_count > 0:
        points += 2

    # H2 headings present
    h2_count = len(re.findall(r'^## .+', text, re.MULTILINE))
    signals["h2_count"] = h2_count
    if h2_count >= 3:
        points += 5
    elif h2_count >= 1:
        points += 2

    # Title length
    signals["title_length"] = len(title)
    if 30 <= len(title) <= 65:
        points += 3

    total = min(25, points)
    return {"score": total, "max": 25, **signals}


def score_structure(text: str) -> dict:
    """Score structure 0-25 (25% of total)."""
    points = 0
    signals = {}

    lines = text.strip().split('\n')

    # Intro: first non-empty paragraph
    paragraphs = [p.strip() for p in text.split('\n\n') if p.strip()]
    signals["paragraph_count"] = len(paragraphs)

    # Has intro (first paragraph isn't a heading)
    if paragraphs and not paragraphs[0].startswith('#'):
        intro_words = len(paragraphs[0].split())
        signals["intro_word_count"] = intro_words
        if 30 <= intro_words <= 200:
            points += 7
        elif intro_words > 0:
            points += 3
    else:
        signals["intro_word_count"] = 0

    # Has H2 sections
    h2s = [l for l in lines if l.startswith('## ')]
    signals["h2_count"] = len(h2s)
    if len(h2s) >= 4:
        points += 8
    elif len(h2s) >= 2:
        points += 5
    elif len(h2s) >= 1:
        points += 2

    # Has conclusion (last substantial paragraph)
    last_para = paragraphs[-1] if paragraphs else ""
    conclusion_words = len(last_para.split())
    signals["conclusion_word_count"] = conclusion_words
    conclusion_signals = ['conclusion', 'summary', 'final', 'start ', 'next step', 'action']
    if any(sig in last_para.lower() for sig in conclusion_signals) and conclusion_words >= 20:
        points += 7
    elif conclusion_words >= 30:
        points += 4

    # Average paragraph length (web = shorter is better)
    para_lengths = [len(p.split()) for p in paragraphs if not p.startswith('#')]
    if para_lengths:
        avg_para_len = sum(para_lengths) / len(para_lengths)
        signals["avg_paragraph_word_count"] = round(avg_para_len, 1)
        if avg_para_len <= 80:
            points += 3
    else:
        signals["avg_paragraph_word_count"] = 0

    total = min(25, points)
    return {"score": total, "max": 25, **signals}


def score_engagement(text: str) -> dict:
    """Score engagement signals 0-25 (25% of total)."""
    points = 0
    signals = {}
    text_lower = text.lower()

    # Questions (engage readers, prompt thought)
    question_count = len(re.findall(r'\?', text))
    signals["question_count"] = question_count
    if question_count >= 3:
        points += 6
    elif question_count >= 1:
        points += 3

    # Specific numbers / data points
    number_count = len(re.findall(r'\b\d+(?:\.\d+)?%?\b', text))
    signals["numbers_and_stats"] = number_count
    if number_count >= 5:
        points += 7
    elif number_count >= 2:
        points += 4
    elif number_count >= 1:
        points += 2

    # Example signals
    example_phrases = ['for example', 'for instance', 'such as', 'like ', 'e.g.', 'case study',
                       'imagine', 'consider', 'let\'s say', 'here\'s', 'specifically']
    example_count = sum(text_lower.count(p) for p in example_phrases)
    signals["example_signals"] = example_count
    if example_count >= 3:
        points += 6
    elif example_count >= 1:
        points += 3

    # Lists (bulleted or numbered)
    list_items = len(re.findall(r'^\s*[-*•]\s+.+|^\s*\d+\.\s+.+', text, re.MULTILINE))
    signals["list_items"] = list_items
    if list_items >= 5:
        points += 6
    elif list_items >= 2:
        points += 3

    total = min(25, points)
    return {"score": total, "max": 25, **signals}


# ── Main ──────────────────────────────────────────────────────────────────────

def score_content(text: str, title: str = "", keyword: str = "") -> dict:
    readability = score_readability(text)
    seo = score_seo(text, title, keyword)
    structure = score_structure(text)
    engagement = score_engagement(text)

    total = readability["score"] + seo["score"] + structure["score"] + engagement["score"]

    grade = "D"
    if total >= 90:
        grade = "A+"
    elif total >= 80:
        grade = "A"
    elif total >= 70:
        grade = "B"
    elif total >= 60:
        grade = "C"

    return {
        "total_score": total,
        "grade": grade,
        "sections": {
            "readability": readability,
            "seo": seo,
            "structure": structure,
            "engagement": engagement,
        }
    }


def print_report(result: dict, title: str, keyword: str) -> None:
    total = result["total_score"]
    grade = result["grade"]
    s = result["sections"]

    bar_filled = int(total / 5)
    bar = "█" * bar_filled + "░" * (20 - bar_filled)

    print()
    print("╔══════════════════════════════════════════╗")
    print("║         CONTENT SCORER — REPORT          ║")
    print("╚══════════════════════════════════════════╝")
    print(f"  Title:   {title[:55] or '(not provided)'}")
    print(f"  Keyword: {keyword or '(not provided)'}")
    print()
    print(f"  TOTAL SCORE:  {total}/100  [{grade}]")
    print(f"  [{bar}]")
    print()
    print("  ── Section Breakdown ──────────────────────")

    sections = [
        ("Readability", s["readability"]),
        ("SEO Signals", s["seo"]),
        ("Structure",   s["structure"]),
        ("Engagement",  s["engagement"]),
    ]
    for label, section in sections:
        sc = section["score"]
        mx = section["max"]
        bar2_filled = int(sc / mx * 10)
        bar2 = "█" * bar2_filled + "░" * (10 - bar2_filled)
        print(f"  {label:<14} {sc:>2}/{mx}  [{bar2}]")

    print()
    print("  ── Key Signals ────────────────────────────")

    r = s["readability"]
    print(f"  Flesch Reading Ease:   {r['flesch_reading_ease']} (target: 60-70)")
    print(f"  Sentence length StDev: {r['sentence_length_std_dev']} (higher = more varied)")

    seo_d = s["seo"]
    print(f"  Keyword in title:      {'✅' if seo_d.get('keyword_in_title') else '❌'}")
    print(f"  Keyword in intro:      {'✅' if seo_d.get('keyword_in_intro') else '❌'}")
    print(f"  Keyword density:       {seo_d.get('keyword_density_pct', 0)}% (target: 0.5-2.5%)")
    print(f"  H2 sections:           {seo_d.get('h2_count', 0)}")

    st = s["structure"]
    print(f"  Intro word count:      {st.get('intro_word_count', 0)} (target: 30-200)")
    print(f"  Avg paragraph length:  {st.get('avg_paragraph_word_count', 0)} words (target: ≤80)")

    en = s["engagement"]
    print(f"  Questions:             {en.get('question_count', 0)}")
    print(f"  Stats/numbers:         {en.get('numbers_and_stats', 0)}")
    print(f"  Examples:              {en.get('example_signals', 0)}")

    print()
    print("  ── Recommendations ────────────────────────")
    if r["flesch_reading_ease"] < 55:
        print("  ⚠ Readability is low — shorten sentences and use simpler words")
    if not seo_d.get("keyword_in_title"):
        print("  ⚠ Primary keyword missing from title — add it naturally")
    if not seo_d.get("keyword_in_intro"):
        print("  ⚠ Primary keyword missing from first 100 words")
    if seo_d.get("h2_count", 0) < 3:
        print("  ⚠ Add more H2 sections — aim for at least 4")
    if st.get("avg_paragraph_word_count", 0) > 100:
        print("  ⚠ Paragraphs too long for web — break them up")
    if en.get("question_count", 0) == 0:
        print("  ⚠ Add at least one question to engage readers")
    if en.get("numbers_and_stats", 0) < 2:
        print("  ⚠ Thin on data — add specific numbers or stats")
    if total >= 70:
        print("  ✅ Content is publish-ready (score ≥ 70)")
    else:
        print(f"  ❌ Score below 70 — address recommendations before publishing")

    print()


def main():
    import argparse

    parser = argparse.ArgumentParser(
        description="Scores content 0-100 on readability, SEO, structure, and engagement."
    )
    parser.add_argument(
        "file", nargs="?", default=None,
        help="Path to a text/markdown file to analyze. If omitted, runs demo "
             "with embedded sample content."
    )
    parser.add_argument(
        "keyword", nargs="?", default="",
        help="Target SEO keyword to check density and placement."
    )
    parser.add_argument(
        "--json", action="store_true",
        help="Also output results as JSON."
    )
    args = parser.parse_args()

    title = ""
    keyword = args.keyword
    text = ""

    if args.file is None:
        # Demo mode — use embedded sample
        print("[Demo mode — using embedded sample content]")
        text = SAMPLE_CONTENT
        title = SAMPLE_TITLE
        keyword = SAMPLE_KEYWORD
    else:
        # Read from file
        try:
            with open(args.file, 'r', encoding='utf-8') as f:
                text = f.read()
        except FileNotFoundError:
            print(f"Error: file not found: {args.file}", file=sys.stderr)
            sys.exit(1)

        # Extract title from first H1 or first line
        for line in text.split('\n'):
            line = line.strip()
            if line.startswith('# '):
                title = line[2:].strip()
                break
            elif line.startswith('Title:'):
                title = line[6:].strip()
                break
        if not title and text:
            title = text.split('\n')[0][:80]

    result = score_content(text, title, keyword)
    print_report(result, title, keyword)

    # JSON output for programmatic use
    if args.json:
        print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
