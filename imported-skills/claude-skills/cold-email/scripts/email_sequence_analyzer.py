#!/usr/bin/env python3
"""
email_sequence_analyzer.py — Analyzes a cold email sequence for quality signals.

Evaluates each email on:
  - Word count (shorter is usually better for cold email)
  - Reading level estimate (Flesch-Kincaid approximation via avg sentence/word length)
  - Personalization density (signals of specific, targeted writing)
  - CTA clarity (is there a clear ask?)
  - Spam trigger words (words that hurt deliverability)
  - Subject line analysis (length, warning patterns)
  - Overall score: 0-100

Usage:
    python3 email_sequence_analyzer.py [sequence.json]
    cat sequence.json | python3 email_sequence_analyzer.py

If no file provided, runs on embedded sample sequence.

Input format (JSON):
    [
      {
        "email": 1,
        "subject": "...",
        "body": "..."
      },
      ...
    ]

Stdlib only — no external dependencies.
"""

import json
import re
import sys
import math
import select
from typing import List, Dict, Any


# ─── Spam trigger words ───────────────────────────────────────────────────────

SPAM_TRIGGERS = [
    "free", "guaranteed", "no obligation", "act now", "limited time",
    "click here", "earn money", "make money", "risk-free", "special offer",
    "no cost", "winner", "congratulations", "you've been selected",
    "once in a lifetime", "urgent", "don't miss out", "buy now",
    "order now", "100%", "best price", "lowest price", "incredible deal",
    "amazing offer", "cash bonus", "extra cash", "fast cash",
    "you have been chosen", "exclusive deal", "as seen on",
    "dear friend", "valued customer",
]

# ─── Personalization signals ──────────────────────────────────────────────────

PERSONALIZATION_SIGNALS = [
    # Direct references to "you"
    r'\byou(?:r|rs|\'re|\'ve|\'d|\'ll)?\b',
    # Trigger references
    r'\b(?:saw|noticed|read|heard|saw|found|noted)\b',
    # Named observation patterns
    r'\b(?:your team|your company|your role|your work|your recent|your post)\b',
    # Industry/role-specific references
    r'\b(?:as a|in your|at your|given your)\b',
    # Specific numbers or facts
    r'\b\d{4}\b',  # years — often a sign of specific research
    r'\$\d+|\d+%',  # numbers with $ or %
]

# ─── Dead opener phrases ──────────────────────────────────────────────────────

DEAD_OPENERS = [
    "i hope this email finds you well",
    "i hope this finds you",
    "i wanted to reach out",
    "i am reaching out",
    "my name is",
    "i'm writing to",
    "i am writing to",
    "hope you're doing well",
    "i hope you are doing well",
    "just following up",
    "just checking in",
    "circling back",
    "touching base",
    "per my last email",
    "as per my previous",
]

# ─── Weak CTA patterns ────────────────────────────────────────────────────────

WEAK_CTA = [
    "let me know if you're interested",
    "let me know if you would be interested",
    "feel free to",
    "please don't hesitate",
    "if you have any questions",
    "looking forward to hearing from you",
    "i look forward to connecting",
    "hope we can connect",
]

# ─── Strong CTA signals ───────────────────────────────────────────────────────

STRONG_CTA_PATTERNS = [
    r'\b(?:15|20|30|45|60)[\s-]?minute\b',   # time-specific meeting ask
    r'\b(?:call|chat|talk|speak|connect|meet)\b.*\?',  # question + meeting word
    r'worth\s+(?:a|an)\b',                   # "worth a call?"
    r'\?$',                                   # ends with question
    r'\buseful\b\s*\?',                       # "useful?"
    r'\b(?:reply|respond)\b',                 # explicit reply ask
]


# ─── Text utilities ───────────────────────────────────────────────────────────

def count_words(text: str) -> int:
    return len(text.split())


def count_sentences(text: str) -> int:
    """Rough sentence count by terminal punctuation."""
    sentences = re.split(r'[.!?]+', text)
    return max(1, len([s for s in sentences if s.strip()]))


def avg_words_per_sentence(text: str) -> float:
    words = count_words(text)
    sentences = count_sentences(text)
    return words / sentences if sentences else words


def avg_chars_per_word(text: str) -> float:
    words = text.split()
    if not words:
        return 0
    return sum(len(w.strip('.,!?;:')) for w in words) / len(words)


def flesch_reading_ease(text: str) -> float:
    """
    Approximate Flesch Reading Ease score.
    206.835 - 1.015 * (words/sentences) - 84.6 * (syllables/words)
    We approximate syllables as: max(1, len(word) * 0.4) for each word.
    """
    words = text.split()
    if not words:
        return 0
    sentences = count_sentences(text)
    syllables = sum(max(1, int(len(re.sub(r'[^aeiouAEIOU]', '', w)) * 1.2) or 1) for w in words)
    asl = len(words) / sentences  # avg sentence length
    asw = syllables / len(words)  # avg syllables per word
    score = 206.835 - (1.015 * asl) - (84.6 * asw)
    return max(0, min(100, score))


def grade_reading_level(fre_score: float) -> str:
    """Convert Flesch Reading Ease to a human label."""
    if fre_score >= 70:
        return "Easy (conversational)"
    if fre_score >= 60:
        return "Plain English"
    if fre_score >= 50:
        return "Fairly difficult"
    return "Difficult (too complex for cold email)"


# ─── Analysis functions ───────────────────────────────────────────────────────

def analyze_subject_line(subject: str) -> Dict:
    issues = []
    warnings = []

    if not subject:
        return {"length": 0, "issues": ["No subject line provided"], "score": 0}

    length = len(subject)

    if length > 60:
        issues.append(f"Too long ({length} chars) — aim for under 50")
    if length > 50:
        warnings.append("Subject is getting long — shorter subjects get more opens")

    if subject.isupper():
        issues.append("All caps subject lines trigger spam filters")

    if re.search(r'!!!|!{2,}', subject):
        issues.append("Multiple exclamation points look like spam")

    if subject.startswith("Re:") or subject.startswith("Fwd:"):
        lower = subject.lower()
        if lower.startswith("re:") or lower.startswith("fwd:"):
            warnings.append("Fake Re:/Fwd: subjects feel deceptive — people have learned this trick")

    if re.search(r'[A-Z]{4,}', subject) and not subject.isupper():
        warnings.append("SHOUTING words in subject lines look like spam")

    if re.search(r'[\U0001F600-\U0001FFFF]', subject):
        warnings.append("Emojis in subject lines are polarizing and often spam-filtered for B2B")

    if '?' in subject:
        warnings.append("Question mark in subject can feel like an ad — test without")

    # Spam trigger check in subject
    subject_lower = subject.lower()
    triggered = [w for w in SPAM_TRIGGERS if w in subject_lower]
    if triggered:
        issues.append(f"Spam trigger words in subject: {', '.join(triggered)}")

    # Score
    score = 100
    score -= len(issues) * 20
    score -= len(warnings) * 10
    score = max(0, min(100, score))

    return {
        "length": length,
        "issues": issues,
        "warnings": warnings,
        "score": score,
    }


def analyze_body(body: str) -> Dict:
    body_lower = body.lower()
    findings = []
    deductions = []

    word_count = count_words(body)
    fre = flesch_reading_ease(body)
    reading_level = grade_reading_level(fre)
    avg_wps = avg_words_per_sentence(body)

    # Word count scoring
    if word_count > 200:
        deductions.append(("word_count", 15, f"Too long ({word_count} words) — cold emails should be under 150"))
    elif word_count > 150:
        deductions.append(("word_count", 5, f"Getting long ({word_count} words) — aim for under 150"))
    elif word_count < 30:
        deductions.append(("word_count", 10, f"Very short ({word_count} words) — may lack enough context"))

    # Sentence length
    if avg_wps > 25:
        deductions.append(("readability", 10, f"Sentences average {avg_wps:.0f} words — too complex, aim for 15-20"))

    # Dead opener check
    for opener in DEAD_OPENERS:
        if opener in body_lower:
            deductions.append(("opener", 20, f"Dead opener detected: '{opener}' — rewrite the opening"))
            break

    # Personalization density
    pers_matches = 0
    for pattern in PERSONALIZATION_SIGNALS:
        matches = re.findall(pattern, body_lower)
        pers_matches += len(matches)

    pers_density = pers_matches / word_count * 100 if word_count else 0
    if pers_density < 5:
        deductions.append(("personalization", 10, "Low personalization signals — email may feel generic"))

    # Spam trigger words in body
    triggered = [w for w in SPAM_TRIGGERS if w in body_lower]
    if triggered:
        deductions.append(("spam", len(triggered) * 5, f"Spam trigger words: {', '.join(triggered[:5])}"))

    # Weak CTA check
    for weak in WEAK_CTA:
        if weak in body_lower:
            deductions.append(("cta", 10, f"Weak CTA: '{weak}' — be more direct"))
            break

    # Strong CTA check
    has_strong_cta = any(re.search(p, body_lower) for p in STRONG_CTA_PATTERNS)
    if not has_strong_cta:
        deductions.append(("cta", 15, "No clear CTA detected — every cold email needs a single, direct ask"))

    # HTML check
    if re.search(r'<html|<body|<table|<div|style="|font-family:', body_lower):
        deductions.append(("format", 20, "HTML detected — plain text emails get better deliverability for cold outreach"))

    # Multiple links
    links = re.findall(r'https?://', body)
    if len(links) > 2:
        deductions.append(("links", 10, f"{len(links)} links detected — keep to 1-2 max for cold email"))

    # Calculate score
    total_deduction = sum(d[1] for d in deductions)
    score = max(0, min(100, 100 - total_deduction))

    return {
        "word_count": word_count,
        "reading_ease_score": round(fre, 1),
        "reading_level": reading_level,
        "avg_words_per_sentence": round(avg_wps, 1),
        "personalization_density": round(pers_density, 1),
        "has_strong_cta": has_strong_cta,
        "spam_triggers": triggered,
        "deductions": [(d[2], d[1]) for d in deductions],
        "score": score,
    }


# ─── Report printer ───────────────────────────────────────────────────────────

def grade(score: int) -> str:
    if score >= 85:
        return "🟢 Strong"
    if score >= 65:
        return "🟡 Decent"
    if score >= 45:
        return "🟠 Needs work"
    return "🔴 Rewrite"


def print_report(results: List[Dict]) -> None:
    print("\n" + "═" * 64)
    print("  COLD EMAIL SEQUENCE ANALYSIS")
    print("═" * 64)

    scores = []
    for r in results:
        email_num = r["email"]
        subj = r["subject_analysis"]
        body = r["body_analysis"]
        overall = r["overall_score"]
        scores.append(overall)

        print(f"\n── Email {email_num}: \"{r['subject']}\" ──")
        print(f"   Overall: {overall}/100  {grade(overall)}")

        print(f"\n   Subject ({subj['length']} chars): {subj['score']}/100")
        for issue in subj.get("issues", []):
            print(f"   ❌ {issue}")
        for warn in subj.get("warnings", []):
            print(f"   ⚠️  {warn}")

        print(f"\n   Body Analysis:")
        print(f"   Words: {body['word_count']}  |  "
              f"Reading: {body['reading_level']}  |  "
              f"Avg sentence: {body['avg_words_per_sentence']} words  |  "
              f"Personalization density: {body['personalization_density']}%")
        print(f"   CTA: {'✅ Clear ask detected' if body['has_strong_cta'] else '❌ No clear CTA found'}")

        if body.get("spam_triggers"):
            print(f"   ⚠️  Spam triggers: {', '.join(body['spam_triggers'])}")

        if body.get("deductions"):
            print(f"\n   Issues found:")
            for desc, pts in body["deductions"]:
                print(f"   [-{pts:2d}] {desc}")

    avg = sum(scores) // len(scores) if scores else 0
    print(f"\n{'═' * 64}")
    print(f"  SEQUENCE OVERALL: {avg}/100  {grade(avg)}")
    print(f"  Emails analyzed: {len(results)}")

    # Sequence-level observations
    print("\n  Sequence observations:")
    word_counts = [r["body_analysis"]["word_count"] for r in results]
    if all(abs(word_counts[i] - word_counts[i-1]) < 20 for i in range(1, len(word_counts))):
        print("  ⚠️  All emails are similar length — vary length across sequence")

    if len(results) > 1:
        last_body = results[-1]["body_analysis"]
        if last_body["word_count"] > 100:
            print("  ⚠️  Final email (breakup) should be shorter — 3-5 sentences max")

    print("═" * 64 + "\n")


# ─── Sample data ──────────────────────────────────────────────────────────────

SAMPLE_SEQUENCE = [
    {
        "email": 1,
        "subject": "your SDR team expansion",
        "body": (
            "Saw you're hiring four SDRs simultaneously — that's a significant scale-up.\n\n"
            "The challenge most teams hit at this stage isn't recruiting — it's ramp time. "
            "When you're adding four people at once, the gaps in your onboarding process "
            "become very expensive very fast. The average ramp in your segment is around "
            "4.5 months; the fastest teams we've seen get it to 2.5.\n\n"
            "We've helped three similar-sized SaaS teams compress that gap. Happy to share "
            "what worked if it's useful.\n\n"
            "Worth 15 minutes to compare notes?"
        ),
    },
    {
        "email": 2,
        "subject": "re: your onboarding stack",
        "body": (
            "I hope this email finds you well. I wanted to follow up on my previous email.\n\n"
            "Just checking in to see if you had a chance to review what I sent. "
            "As mentioned, our platform offers a comprehensive suite of tools designed to "
            "help sales teams of all sizes achieve unprecedented growth through our "
            "revolutionary AI-powered onboarding solution.\n\n"
            "I'd love to schedule a 45-minute product demo at your earliest convenience. "
            "Please don't hesitate to reach out if you have any questions. "
            "I look forward to hearing from you!\n\n"
            "Click here to book a time: https://calendly.com/example"
        ),
    },
    {
        "email": 3,
        "subject": "SDR ramp benchmark",
        "body": (
            "One data point that might be useful: across the 40 SaaS teams we've benchmarked, "
            "the ones with the fastest SDR ramp time don't hire the most experienced reps — "
            "they invest more heavily in structured onboarding in the first 30 days.\n\n"
            "Happy to share the full breakdown. No catch — just thought it might be relevant "
            "given where you're headed.\n\n"
            "Useful?"
        ),
    },
    {
        "email": 4,
        "subject": "quick question",
        "body": (
            "Is SDR onboarding actually a priority right now, or is the timing just off?\n\n"
            "No judgment either way — just helps me know whether it's worth staying in touch."
        ),
    },
    {
        "email": 5,
        "subject": "last one",
        "body": (
            "I'll stop cluttering your inbox after this one.\n\n"
            "If scaling your SDR ramp time ever becomes a priority, happy to reconnect — "
            "just reply here.\n\n"
            "If there's someone else at your company who owns sales enablement, "
            "a name would go a long way.\n\n"
            "Either way, good luck with the expansion."
        ),
    },
]


# ─── Main ─────────────────────────────────────────────────────────────────────

def main():
    import argparse

    parser = argparse.ArgumentParser(
        description="Analyzes a cold email sequence for quality signals. "
                    "Evaluates word count, reading level, personalization, CTA clarity, "
                    "spam triggers, and subject lines. Scores each email 0-100."
    )
    parser.add_argument(
        "file", nargs="?", default=None,
        help="Path to a JSON file containing the email sequence. "
             "Use '-' to read from stdin. If omitted, runs embedded sample."
    )
    args = parser.parse_args()

    if args.file:
        if args.file == "-":
            sequence = json.load(sys.stdin)
        else:
            try:
                with open(args.file, "r", encoding="utf-8") as f:
                    sequence = json.load(f)
            except FileNotFoundError:
                print(f"Error: File not found: {args.file}", file=sys.stderr)
                sys.exit(1)
            except json.JSONDecodeError as e:
                print(f"Error: Invalid JSON: {e}", file=sys.stderr)
                sys.exit(1)
    else:
        print("No file provided — running on embedded sample sequence.\n")
        sequence = SAMPLE_SEQUENCE

    results = []
    for email in sequence:
        subject = email.get("subject", "")
        body = email.get("body", "")
        email_num = email.get("email", len(results) + 1)

        subject_analysis = analyze_subject_line(subject)
        body_analysis = analyze_body(body)

        # Overall score: 30% subject, 70% body
        overall = int(subject_analysis["score"] * 0.3 + body_analysis["score"] * 0.7)

        results.append({
            "email": email_num,
            "subject": subject,
            "subject_analysis": subject_analysis,
            "body_analysis": body_analysis,
            "overall_score": overall,
        })

    print_report(results)

    # JSON output for programmatic use
    summary = {
        "emails_analyzed": len(results),
        "average_score": sum(r["overall_score"] for r in results) // len(results) if results else 0,
        "results": [
            {
                "email": r["email"],
                "subject": r["subject"],
                "score": r["overall_score"],
                "word_count": r["body_analysis"]["word_count"],
                "has_strong_cta": r["body_analysis"]["has_strong_cta"],
                "spam_triggers": r["body_analysis"]["spam_triggers"],
                "subject_score": r["subject_analysis"]["score"],
            }
            for r in results
        ],
    }
    print("── JSON Output ──")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
