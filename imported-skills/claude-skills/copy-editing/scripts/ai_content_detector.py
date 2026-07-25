#!/usr/bin/env python3
"""
ai_content_detector.py — Detect AI-generated content patterns.

Three detection methods:
  1. Burstiness analysis — human writing has high variance in sentence length;
     AI writing has consistently medium-length sentences
  2. Vocabulary diversity (Type-Token Ratio) — AI reuses words more than humans
  3. Known AI phrases — specific phrases that appear disproportionately in
     AI-generated text

This is a heuristic tool, NOT a proof engine. False positives are expected.
The goal is to flag passages that FEEL AI-generated so a human editor can
inject voice, variance, and specificity.

Usage:
    python ai_content_detector.py article.md
    python ai_content_detector.py article.md --json
    python ai_content_detector.py --demo

Scoring:
    0-20   = likely human (high burstiness, diverse vocab, no AI phrases)
    21-50  = mixed signals (review flagged passages)
    51-100 = likely AI (flat burstiness, repetitive vocab, AI phrase density)
"""
from __future__ import annotations
import argparse
import json
import math
import re
import sys
from collections import Counter
from pathlib import Path

# --- Known AI phrases (commonly overrepresented in LLM output) ---

AI_PHRASES = [
    "in today's digital landscape",
    "in today's fast-paced",
    "it's worth noting that",
    "it is important to note",
    "delve into",
    "dive deep into",
    "leverage",
    "game-changer",
    "game changer",
    "unlock the potential",
    "unlock the power",
    "harness the power",
    "at the end of the day",
    "in conclusion",
    "in summary",
    "navigating the complexities",
    "a comprehensive guide",
    "seamlessly integrate",
    "robust solution",
    "cutting-edge",
    "state-of-the-art",
    "empower you to",
    "take your .* to the next level",
    "in the realm of",
    "tapestry of",
    "multifaceted",
    "it's crucial to",
    "paramount",
    "foster a .* environment",
    "elevate your",
]

AI_PHRASE_RES = [re.compile(p, re.IGNORECASE) for p in AI_PHRASES]

# --- Sentence splitting ---

SENTENCE_RE = re.compile(r"[^.!?]+[.!?]+", re.DOTALL)
WORD_RE = re.compile(r"[a-zA-Z]+")

DEMO_CONTENT = """In today's digital landscape, leveraging AI tools has become a game-changer for content creators. It's worth noting that the ability to harness the power of large language models can unlock the potential of your marketing efforts. This comprehensive guide will delve into the multifaceted world of AI-assisted content creation.

The integration of AI into content workflows is a robust solution that seamlessly integrates with existing processes. By navigating the complexities of modern content production, you can elevate your brand's voice and foster a creative environment that empowers your team to take their content to the next level.

At the end of the day, it's crucial to understand that AI is a tool, not a replacement. The cutting-edge capabilities of state-of-the-art models are paramount for staying competitive in the realm of digital marketing. In conclusion, the tapestry of modern content creation requires both human creativity and artificial intelligence working in harmony."""


def extract_sentences(text):
    body = re.sub(r"^---.*?---\s*", "", text, count=1, flags=re.DOTALL)
    body = re.sub(r"^#+\s+.*$", "", body, flags=re.MULTILINE)
    body = re.sub(r"```.*?```", "", body, flags=re.DOTALL)
    body = re.sub(r"`[^`]+`", "", body)
    body = re.sub(r"\[([^\]]+)\]\([^)]+\)", r"\1", body)
    sentences = SENTENCE_RE.findall(body)
    return [s.strip() for s in sentences if len(s.strip().split()) >= 3]


def burstiness_score(sentences):
    """Compute burstiness (sentence length variance). High = human, low = AI."""
    if len(sentences) < 5:
        return {"score": 50, "mean": 0, "std": 0, "cv": 0, "note": "too few sentences"}
    lengths = [len(s.split()) for s in sentences]
    mean = sum(lengths) / len(lengths)
    variance = sum((l - mean) ** 2 for l in lengths) / len(lengths)
    std = math.sqrt(variance)
    cv = std / mean if mean > 0 else 0  # coefficient of variation

    # Human writing: CV typically 0.4-0.8+ (high variance)
    # AI writing: CV typically 0.15-0.35 (consistently medium)
    if cv >= 0.5:
        ai_prob = max(0, 30 - (cv - 0.5) * 60)
    elif cv >= 0.35:
        ai_prob = 30 + (0.5 - cv) * 130
    else:
        ai_prob = 50 + (0.35 - cv) * 250

    ai_prob = max(0, min(100, ai_prob))
    return {
        "score": round(ai_prob, 1),
        "mean_sentence_length": round(mean, 1),
        "std_sentence_length": round(std, 1),
        "coefficient_of_variation": round(cv, 3),
        "note": "low CV = flat sentence lengths (AI-like)" if cv < 0.35 else "healthy variance",
    }


def vocabulary_diversity(text):
    """Type-Token Ratio. Low TTR = repetitive vocabulary (AI-like)."""
    body = re.sub(r"^---.*?---\s*", "", text, count=1, flags=re.DOTALL)
    words = [w.lower() for w in WORD_RE.findall(body) if len(w) > 2]
    if len(words) < 50:
        return {"score": 50, "ttr": 0, "unique": 0, "total": len(words), "note": "too few words"}
    # Use a sliding window TTR for length-independence
    window = min(200, len(words))
    ttrs = []
    for i in range(0, len(words) - window + 1, window // 2):
        chunk = words[i : i + window]
        ttrs.append(len(set(chunk)) / len(chunk))
    avg_ttr = sum(ttrs) / len(ttrs)

    # Human: TTR 0.55-0.75+ (varied vocabulary)
    # AI: TTR 0.35-0.50 (repetitive patterns)
    if avg_ttr >= 0.60:
        ai_prob = max(0, 25 - (avg_ttr - 0.60) * 150)
    elif avg_ttr >= 0.45:
        ai_prob = 25 + (0.60 - avg_ttr) * 330
    else:
        ai_prob = 75 + (0.45 - avg_ttr) * 250

    ai_prob = max(0, min(100, ai_prob))

    # Top repeated words (excluding stop words)
    stop = {"the", "and", "for", "that", "this", "with", "from", "are", "was", "were", "been",
            "have", "has", "had", "not", "but", "can", "will", "your", "you", "they", "their",
            "more", "than", "also", "into", "when", "how", "what", "which", "about", "each"}
    content_words = [w for w in words if w not in stop]
    top_repeated = Counter(content_words).most_common(5)

    return {
        "score": round(ai_prob, 1),
        "avg_ttr": round(avg_ttr, 3),
        "unique_words": len(set(words)),
        "total_words": len(words),
        "top_repeated": [{"word": w, "count": c} for w, c in top_repeated],
        "note": "low TTR = repetitive vocabulary (AI-like)" if avg_ttr < 0.45 else "healthy diversity",
    }


def phrase_detection(text):
    """Count known AI phrases."""
    found = []
    text_lower = text.lower()
    for i, pattern in enumerate(AI_PHRASE_RES):
        matches = pattern.findall(text_lower)
        if matches:
            found.append({"phrase": AI_PHRASES[i], "count": len(matches)})

    total_matches = sum(f["count"] for f in found)
    word_count = len(text.split())
    density = (total_matches / (word_count / 1000)) if word_count > 0 else 0

    # 0-2 per 1K words = normal; 3-5 = suspect; 6+ = likely AI
    if density <= 2:
        ai_prob = density * 15
    elif density <= 5:
        ai_prob = 30 + (density - 2) * 20
    else:
        ai_prob = min(100, 90 + (density - 5) * 5)

    return {
        "score": round(ai_prob, 1),
        "phrases_found": len(found),
        "total_matches": total_matches,
        "density_per_1k_words": round(density, 1),
        "matches": found[:10],
        "note": f"{density:.1f} AI phrases per 1K words" if found else "no known AI phrases",
    }


def analyze(text):
    sentences = extract_sentences(text)
    burst = burstiness_score(sentences)
    vocab = vocabulary_diversity(text)
    phrases = phrase_detection(text)

    # Weighted composite: burstiness 35%, vocab 30%, phrases 35%
    composite = burst["score"] * 0.35 + vocab["score"] * 0.30 + phrases["score"] * 0.35
    composite = round(min(100, max(0, composite)), 1)

    if composite <= 20:
        verdict = "LIKELY_HUMAN"
    elif composite <= 50:
        verdict = "MIXED"
    else:
        verdict = "LIKELY_AI"

    return {
        "status": "ok",
        "composite_score": composite,
        "verdict": verdict,
        "burstiness": burst,
        "vocabulary": vocab,
        "phrases": phrases,
        "sentences_analyzed": len(sentences),
        "recommendations": _recommendations(burst, vocab, phrases),
    }


def _recommendations(burst, vocab, phrases):
    recs = []
    if burst["score"] > 40:
        recs.append("Vary sentence lengths: mix short punchy sentences (5-8 words) with longer explanatory ones (20-30 words).")
    if vocab["score"] > 40:
        recs.append("Diversify vocabulary: replace repeated words with synonyms. Use domain-specific jargon where appropriate.")
    if phrases["total_matches"] > 0:
        top = phrases["matches"][:3]
        recs.append(f"Remove/replace AI phrases: {', '.join(p['phrase'] for p in top)}")
    if not recs:
        recs.append("Content reads naturally. No humanization needed.")
    return recs


def main():
    p = argparse.ArgumentParser(
        description="Detect AI-generated content via burstiness, vocabulary diversity, and phrase analysis.",
        epilog="Score 0-20 = likely human, 21-50 = mixed, 51-100 = likely AI. Run with --demo.",
    )
    p.add_argument("file", nargs="?", help="Markdown/text file to analyze")
    p.add_argument("--json", action="store_true", help="JSON output")
    p.add_argument("--demo", action="store_true", help="Run with AI-heavy demo text")
    args = p.parse_args()

    if args.demo:
        text = DEMO_CONTENT
    elif args.file:
        path = Path(args.file)
        if not path.exists():
            print(f"[error] {path} not found", file=sys.stderr)
            sys.exit(1)
        text = path.read_text(encoding="utf-8", errors="replace")
    else:
        p.print_help()
        sys.exit(0)

    result = analyze(text)

    if args.json:
        print(json.dumps(result, indent=2))
        return

    print(f"AI Content Detection — Composite: {result['composite_score']}/100 ({result['verdict']})")
    print()
    b = result["burstiness"]
    print(f"  Burstiness:  {b['score']}/100 — CV={b['coefficient_of_variation']} ({b['note']})")
    v = result["vocabulary"]
    print(f"  Vocabulary:  {v['score']}/100 — TTR={v['avg_ttr']} ({v['note']})")
    ph = result["phrases"]
    print(f"  AI Phrases:  {ph['score']}/100 — {ph['total_matches']} matches, {ph['density_per_1k_words']}/1K words")
    if ph["matches"]:
        for m in ph["matches"][:5]:
            print(f"    → \"{m['phrase']}\" (×{m['count']})")
    print()
    print("Recommendations:")
    for r in result["recommendations"]:
        print(f"  → {r}")


if __name__ == "__main__":
    main()
