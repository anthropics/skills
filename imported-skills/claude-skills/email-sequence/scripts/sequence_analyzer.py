#!/usr/bin/env python3
"""
sequence_analyzer.py — Email sequence quality analyzer
Usage:
  python3 sequence_analyzer.py --file sequence.json
  python3 sequence_analyzer.py --json
  python3 sequence_analyzer.py          # demo mode

Input JSON format:
  [
    {"subject": "...", "body": "...", "delay_days": 0},
    {"subject": "...", "body": "...", "delay_days": 2},
    ...
  ]
"""

import argparse
import json
import re
import sys


# ---------------------------------------------------------------------------
# Word/pattern lists
# ---------------------------------------------------------------------------

SPAM_TRIGGER_WORDS = [
    "free", "guarantee", "guaranteed", "winner", "won", "prize",
    "congratulations", "cash", "earn money", "make money", "extra income",
    "100% free", "no cost", "risk free", "act now", "limited time",
    "click here", "buy now", "order now", "get it now",
    "as seen on", "dear friend", "you have been selected",
    "this isn't spam", "not spam", "no credit card required",
    "special promotion", "special offer", "amazing offer",
    "!!!", "!!!", "$$$", "£££",
    "increase your", "increase sales", "double your",
    "lose weight", "weight loss", "diet", "viagra", "casino",
]

CTA_PATTERNS = re.compile(
    r"\b(click|tap|reply|download|sign up|register|buy|purchase|get started|"
    r"learn more|read more|visit|go to|check out|schedule|book|claim|try|"
    r"subscribe|join|start|access|watch|see|grab|discover)\b",
    re.IGNORECASE,
)

PERSONALIZATION_TOKENS = re.compile(
    r"\{\{?\s*\w+\s*\}?\}|%\w+%|\[FIRST_NAME\]|\[NAME\]|\[COMPANY\]|\[FIRSTNAME\]",
    re.IGNORECASE,
)


# ---------------------------------------------------------------------------
# Per-email analysis
# ---------------------------------------------------------------------------

def analyze_email(email: dict, index: int) -> dict:
    subject = email.get("subject", "")
    body = email.get("body", "")
    delay = email.get("delay_days", 0)

    # Subject analysis
    subject_len = len(subject)
    subject_word_count = len(subject.split())
    subject_ok = 30 <= subject_len <= 60
    subject_has_number = bool(re.search(r"\d", subject))
    subject_question = subject.strip().endswith("?")
    subject_all_caps = subject == subject.upper() and len(subject) > 3

    # Body analysis
    body_words = re.findall(r"\b\w+\b", body)
    body_word_count = len(body_words)

    # CTA detection
    cta_matches = CTA_PATTERNS.findall(body)
    has_cta = len(cta_matches) > 0

    # Personalization tokens
    tokens_in_subject = PERSONALIZATION_TOKENS.findall(subject)
    tokens_in_body = PERSONALIZATION_TOKENS.findall(body)
    total_tokens = len(tokens_in_subject) + len(tokens_in_body)

    # Spam triggers
    combined = (subject + " " + body).lower()
    spam_found = [w for w in SPAM_TRIGGER_WORDS if w.lower() in combined]

    # Spam score (0-100, higher = more spammy)
    spam_score = min(100, len(spam_found) * 10)

    return {
        "email_index": index + 1,
        "delay_days": delay,
        "subject": {
            "text": subject,
            "length": subject_len,
            "word_count": subject_word_count,
            "length_ok": subject_ok,
            "has_number": subject_has_number,
            "is_question": subject_question,
            "all_caps_warning": subject_all_caps,
            "personalized": len(tokens_in_subject) > 0,
        },
        "body": {
            "word_count": body_word_count,
            "length_verdict": _body_length_verdict(body_word_count),
            "has_cta": has_cta,
            "cta_phrases": list(set(cta_matches))[:5],
            "personalization_tokens": total_tokens,
        },
        "spam": {
            "trigger_words_found": spam_found[:8],
            "trigger_count": len(spam_found),
            "spam_risk_score": spam_score,
            "risk_level": "High" if spam_score >= 40 else "Medium" if spam_score >= 20 else "Low",
        },
    }


def _body_length_verdict(word_count: int) -> str:
    if word_count < 50:
        return "Too short (<50 words)"
    if word_count <= 150:
        return "Short/punchy — good for re-engagement"
    if word_count <= 300:
        return "Optimal (150-300 words)"
    if word_count <= 500:
        return "Long — ensure high value throughout"
    return "Very long (500+ words) — consider trimming"


# ---------------------------------------------------------------------------
# Sequence-level analysis
# ---------------------------------------------------------------------------

def analyze_pacing(emails: list) -> dict:
    if len(emails) <= 1:
        return {"note": "Single email — no pacing to analyze"}

    delays = [e.get("delay_days", 0) for e in emails]
    gaps = [delays[i] - delays[i - 1] for i in range(1, len(delays))]

    issues = []
    for i, gap in enumerate(gaps):
        if gap <= 0:
            issues.append(f"Email {i+2}: same-day or before previous — check delay_days")
        elif gap == 1:
            issues.append(f"Email {i+2}: only 1-day gap — may feel aggressive")
        elif gap > 14:
            issues.append(f"Email {i+2}: {gap}-day gap — momentum may drop")

    # Assess overall cadence
    avg_gap = sum(gaps) / len(gaps) if gaps else 0
    if avg_gap <= 2:
        cadence = "Aggressive (avg <2 days)"
    elif avg_gap <= 5:
        cadence = "High-frequency (avg 2-5 days)"
    elif avg_gap <= 10:
        cadence = "Standard (avg 5-10 days)"
    else:
        cadence = "Low-frequency (avg 10+ days)"

    return {
        "email_count": len(emails),
        "total_duration_days": max(delays) - min(delays),
        "avg_gap_days": round(avg_gap, 1),
        "cadence_type": cadence,
        "gaps": gaps,
        "issues": issues,
    }


# ---------------------------------------------------------------------------
# Scoring
# ---------------------------------------------------------------------------

def compute_sequence_score(email_analyses: list, pacing: dict) -> dict:
    if not email_analyses:
        return {"overall": 0}

    # Subject score: avg subject length compliance
    subject_ok_count = sum(1 for e in email_analyses if e["subject"]["length_ok"])
    subject_score = round(subject_ok_count / len(email_analyses) * 100)

    # CTA score: % of emails with CTA
    cta_count = sum(1 for e in email_analyses if e["body"]["has_cta"])
    cta_score = round(cta_count / len(email_analyses) * 100)

    # Personalization score
    personalized_count = sum(1 for e in email_analyses if e["body"]["personalization_tokens"] > 0)
    personalization_score = round(personalized_count / len(email_analyses) * 100)

    # Spam score (inverted — low spam = high score)
    avg_spam = sum(e["spam"]["spam_risk_score"] for e in email_analyses) / len(email_analyses)
    spam_score = max(0, 100 - int(avg_spam))

    # Pacing score
    pacing_issues = len(pacing.get("issues", []))
    pacing_score = max(0, 100 - pacing_issues * 20)

    # Body length score
    length_ok_count = sum(
        1 for e in email_analyses
        if "Optimal" in e["body"]["length_verdict"] or "punchy" in e["body"]["length_verdict"]
    )
    length_score = round(length_ok_count / len(email_analyses) * 100)

    weights = {
        "subject_quality": 0.20,
        "cta_presence":    0.20,
        "spam_safety":     0.25,
        "personalization": 0.15,
        "pacing":          0.10,
        "body_length":     0.10,
    }
    scores = {
        "subject_quality": subject_score,
        "cta_presence":    cta_score,
        "spam_safety":     spam_score,
        "personalization": personalization_score,
        "pacing":          pacing_score,
        "body_length":     length_score,
    }
    overall = round(sum(scores[k] * weights[k] for k in weights))
    grade = "A" if overall >= 85 else "B" if overall >= 70 else "C" if overall >= 55 else "D" if overall >= 40 else "F"

    return {
        "overall": overall,
        "grade": grade,
        "breakdown": {k: {"score": v, "weight": f"{int(weights[k]*100)}%"} for k, v in scores.items()},
    }


# ---------------------------------------------------------------------------
# Demo data
# ---------------------------------------------------------------------------

DEMO_SEQUENCE = [
    {
        "subject": "{{first_name}}, your free marketing audit is ready",
        "body": "Hi {{first_name}},\n\nWe analyzed 500 campaigns like yours and found three quick wins that could double your ROAS in 30 days.\n\nI've put together a custom audit for {{company}}. It's free and takes 10 minutes to review.\n\n→ Click here to see your results: [LINK]\n\nBest,\nSarah",
        "delay_days": 0,
    },
    {
        "subject": "Did you see this, {{first_name}}?",
        "body": "Quick follow-up.\n\nMost marketers we talk to are sitting on 2-3 easy optimizations that could add 20-40% more revenue from the same ad spend.\n\nHere's the #1 thing we see: landing pages that don't match the ad promise.\n\nWorth 5 minutes? → [Review your audit]\n\nSarah",
        "delay_days": 3,
    },
    {
        "subject": "The $50,000 mistake (and how to avoid it)",
        "body": "True story.\n\nOne of our clients was spending $8,500/month on Google Ads with a 1.8x ROAS. Technically above break-even, but barely.\n\nWe found that 60% of their budget was going to one keyword that had zero purchase intent.\n\nAfter fixing it: same spend, 4.2x ROAS.\n\nThat's the kind of thing our audit catches. Have you looked at yours yet?\n\n→ [Open your free audit]\n\nSarah\n\nP.S. This offer expires Friday.",
        "delay_days": 5,
    },
    {
        "subject": "Last call — your audit expires tonight",
        "body": "{{first_name}}, this is the last reminder.\n\nYour personalized audit expires at midnight tonight.\n\nIf growing your ROAS is a priority this quarter, take 10 minutes now.\n\n→ [Claim your audit before it expires]\n\nSarah",
        "delay_days": 7,
    },
    {
        "subject": "New case study: {{company}}-style win",
        "body": "Since you didn't grab the audit, I wanted to send you something valuable anyway.\n\nHere's a 3-minute case study showing how we helped a B2B SaaS company go from 1.9x to 5.4x ROAS in 45 days.\n\nNo audit required — just solid tactics you can steal.\n\n→ [Read the case study]\n\nHope it helps,\nSarah",
        "delay_days": 14,
    },
]


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Email sequence analyzer — scores sequence quality 0-100."
    )
    parser.add_argument("--file", help="JSON file with email sequence array")
    parser.add_argument("--json", action="store_true", help="Output as JSON")
    args = parser.parse_args()

    if args.file:
        with open(args.file, "r", encoding="utf-8") as f:
            emails = json.load(f)
    else:
        emails = DEMO_SEQUENCE
        if not args.json:
            print("No input provided — running in demo mode (5-email nurture sequence).\n")

    email_analyses = [analyze_email(e, i) for i, e in enumerate(emails)]
    pacing = analyze_pacing(emails)
    scoring = compute_sequence_score(email_analyses, pacing)

    if args.json:
        output = {
            "sequence_score": scoring,
            "pacing": pacing,
            "emails": email_analyses,
        }
        print(json.dumps(output, indent=2))
        return

    # Human-readable
    overall = scoring["overall"]
    grade = scoring["grade"]

    print("=" * 64)
    print(f"  EMAIL SEQUENCE ANALYSIS   Score: {overall}/100  Grade: {grade}")
    print("=" * 64)

    # Pacing summary
    print(f"\n  📅 SEQUENCE PACING")
    print(f"     Emails:         {pacing['email_count']}")
    print(f"     Duration:       {pacing.get('total_duration_days', 0)} days")
    print(f"     Avg gap:        {pacing.get('avg_gap_days', 0)} days")
    print(f"     Cadence:        {pacing.get('cadence_type', 'N/A')}")
    if pacing.get("issues"):
        for issue in pacing["issues"]:
            print(f"     ⚠️  {issue}")

    print(f"\n  📧 PER-EMAIL BREAKDOWN")
    print(f"  {'#':<3} {'Subject':<40} {'Words':<6} {'CTA':<4} {'Tokens':<7} {'Spam'}")
    print("  " + "─" * 60)

    for e in email_analyses:
        subj = e["subject"]["text"][:38]
        if not e["subject"]["length_ok"]:
            subj += "⚠️"
        words = e["body"]["word_count"]
        cta = "✅" if e["body"]["has_cta"] else "❌"
        tokens = e["body"]["personalization_tokens"]
        spam_lvl = e["spam"]["risk_level"]
        spam_icon = "✅" if spam_lvl == "Low" else ("⚠️ " if spam_lvl == "Medium" else "❌")
        spam_str = f"{spam_icon}{spam_lvl}"
        print(f"  {e['email_index']:<3} {subj:<40} {words:<6} {cta:<4} {tokens:<7} {spam_str}")

    if any(e["spam"]["trigger_words_found"] for e in email_analyses):
        print(f"\n  ⚠️  SPAM TRIGGER WORDS DETECTED")
        for e in email_analyses:
            if e["spam"]["trigger_words_found"]:
                triggers = ", ".join(e["spam"]["trigger_words_found"])
                print(f"     Email {e['email_index']}: {triggers}")

    print(f"\n  SCORE BREAKDOWN")
    for k, v in scoring["breakdown"].items():
        label = k.replace("_", " ").title()
        bar_len = round(v["score"] / 10)
        bar = "█" * bar_len + "░" * (10 - bar_len)
        print(f"  {label:<22} [{bar}] {v['score']:>3}/100  (weight {v['weight']})")

    print()
    print("=" * 64)
    print(f"  Overall: {overall}/100   Grade: {grade}")
    print("=" * 64)


if __name__ == "__main__":
    main()
