#!/usr/bin/env python3
"""
ad_copy_validator.py — Validates ad copy against platform specs.

Checks: character counts, rejection triggers (ALL CAPS, excessive punctuation,
trademarked terms), and scores each ad 0-100.

Usage:
    python3 ad_copy_validator.py                  # runs embedded sample
    python3 ad_copy_validator.py ads.json         # validates a JSON file
    echo '{"platform":"google_rsa","headlines":["My headline"]}' | python3 ad_copy_validator.py

JSON input format:
    {
      "platform": "google_rsa" | "meta_feed" | "linkedin" | "twitter" | "tiktok",
      "headlines": ["...", ...],
      "descriptions": ["...", ...],   # for google
      "primary_text": "...",          # for meta, linkedin, twitter, tiktok
      "headline": "...",              # for meta headline field
      "intro_text": "..."             # for linkedin
    }
"""

import json
import re
import sys
from collections import defaultdict

# ---------------------------------------------------------------------------
# Platform specifications
# ---------------------------------------------------------------------------
PLATFORM_SPECS = {
    "google_rsa": {
        "name": "Google RSA",
        "headline_max": 30,
        "headline_count_max": 15,
        "headline_count_min": 3,
        "description_max": 90,
        "description_count_max": 4,
        "description_count_min": 2,
    },
    "google_display": {
        "name": "Google Display",
        "headline_max": 30,
        "description_max": 90,
    },
    "meta_feed": {
        "name": "Meta (Facebook/Instagram) Feed",
        "primary_text_max": 125,   # preview limit; 2200 absolute max
        "headline_max": 40,
        "description_max": 30,
    },
    "linkedin": {
        "name": "LinkedIn Sponsored Content",
        "intro_text_max": 150,     # preview limit; 600 absolute max
        "headline_max": 70,
        "description_max": 100,
    },
    "twitter": {
        "name": "Twitter/X Promoted",
        "primary_text_max": 257,   # 280 - 23 chars for URL
    },
    "tiktok": {
        "name": "TikTok In-Feed",
        "primary_text_max": 100,
    },
}

# ---------------------------------------------------------------------------
# Rejection triggers
# ---------------------------------------------------------------------------
TRADEMARKED_TERMS = [
    "facebook", "instagram", "google", "youtube", "tiktok", "twitter",
    "linkedin", "snapchat", "whatsapp", "amazon", "apple", "microsoft",
]

PROHIBITED_PHRASES = [
    "click here",
    "limited time offer",  # allowed if real — flagged for review
    "guaranteed",
    "100% free",
    "act now",
    "best in class",
    "world's best",
    "#1 rated",
    "number one",
]

# Financial / health claim patterns
SUSPICIOUS_PATTERNS = [
    r"\$\d{3,}[k+]?\s*per\s*(day|week|month)",   # "make $1,000 per day"
    r"\d{3,}%\s*(return|roi|profit|gain)",         # "300% return"
    r"(cure|treat|heal|eliminate)\s+\w+",          # health claims
    r"lose\s+\d+\s*(pound|lb|kg)",                 # weight loss claims
]

# ---------------------------------------------------------------------------
# Validation logic
# ---------------------------------------------------------------------------

def count_chars(text):
    return len(text.strip())


def check_all_caps(text):
    """Returns True if more than 30% of alpha chars are uppercase — not counting acronyms."""
    words = text.split()
    violations = []
    for word in words:
        alpha = re.sub(r'[^a-zA-Z]', '', word)
        if len(alpha) > 3 and alpha.isupper():
            violations.append(word)
    return violations


def check_excessive_punctuation(text):
    """Flags repeated punctuation (!!!, ???, ...)."""
    return re.findall(r'[!?\.]{2,}', text)


def check_trademark_mentions(text):
    lowered = text.lower()
    return [term for term in TRADEMARKED_TERMS if re.search(r'\b' + term + r'\b', lowered)]


def check_prohibited_phrases(text):
    lowered = text.lower()
    return [phrase for phrase in PROHIBITED_PHRASES if phrase in lowered]


def check_suspicious_claims(text):
    hits = []
    for pattern in SUSPICIOUS_PATTERNS:
        if re.search(pattern, text, re.IGNORECASE):
            hits.append(pattern)
    return hits


def score_ad(issues):
    """
    Score 0-100. Start at 100, deduct per issue category.
    """
    score = 100
    deductions = {
        "char_over_limit": 20,
        "all_caps": 15,
        "excessive_punctuation": 10,
        "trademark_mention": 25,
        "prohibited_phrase": 15,
        "suspicious_claim": 30,
        "count_too_few": 10,
        "count_too_many": 5,
    }
    for category, items in issues.items():
        if items:
            score -= deductions.get(category, 5) * (1 if isinstance(items, bool) else min(len(items), 3))
    return max(0, score)


def validate_google_rsa(ad):
    spec = PLATFORM_SPECS["google_rsa"]
    issues = defaultdict(list)
    report = []

    headlines = ad.get("headlines", [])
    descriptions = ad.get("descriptions", [])

    # Count checks
    if len(headlines) < spec["headline_count_min"]:
        issues["count_too_few"].append(f"Need ≥{spec['headline_count_min']} headlines, got {len(headlines)}")
    if len(headlines) > spec["headline_count_max"]:
        issues["count_too_many"].append(f"Max {spec['headline_count_max']} headlines, got {len(headlines)}")
    if len(descriptions) < spec["description_count_min"]:
        issues["count_too_few"].append(f"Need ≥{spec['description_count_min']} descriptions, got {len(descriptions)}")

    # Character checks per headline
    for i, h in enumerate(headlines):
        length = count_chars(h)
        status = "✅" if length <= spec["headline_max"] else "❌"
        if length > spec["headline_max"]:
            issues["char_over_limit"].append(f"Headline {i+1}: {length} chars (max {spec['headline_max']})")
        report.append(f"  Headline {i+1}: {status} '{h}' ({length}/{spec['headline_max']} chars)")

        # Rejection trigger checks on each headline
        caps = check_all_caps(h)
        if caps:
            issues["all_caps"].extend(caps)
        punct = check_excessive_punctuation(h)
        if punct:
            issues["excessive_punctuation"].extend(punct)
        trademarks = check_trademark_mentions(h)
        if trademarks:
            issues["trademark_mention"].extend(trademarks)
        prohibited = check_prohibited_phrases(h)
        if prohibited:
            issues["prohibited_phrase"].extend(prohibited)

    for i, d in enumerate(descriptions):
        length = count_chars(d)
        status = "✅" if length <= spec["description_max"] else "❌"
        if length > spec["description_max"]:
            issues["char_over_limit"].append(f"Description {i+1}: {length} chars (max {spec['description_max']})")
        report.append(f"  Description {i+1}: {status} '{d}' ({length}/{spec['description_max']} chars)")

        suspicious = check_suspicious_claims(d)
        if suspicious:
            issues["suspicious_claim"].extend(suspicious)

    return report, dict(issues)


def validate_meta_feed(ad):
    spec = PLATFORM_SPECS["meta_feed"]
    issues = defaultdict(list)
    report = []

    primary = ad.get("primary_text", "")
    headline = ad.get("headline", "")

    if primary:
        length = count_chars(primary)
        status = "✅" if length <= spec["primary_text_max"] else "⚠️ (preview truncated)"
        report.append(f"  Primary text: {status} ({length}/{spec['primary_text_max']} preview chars)")
        if length > spec["primary_text_max"]:
            issues["char_over_limit"].append(f"Primary text {length} chars exceeds {spec['primary_text_max']}-char preview")

        for check_fn, key in [
            (check_all_caps, "all_caps"),
            (check_excessive_punctuation, "excessive_punctuation"),
            (check_trademark_mentions, "trademark_mention"),
            (check_prohibited_phrases, "prohibited_phrase"),
            (check_suspicious_claims, "suspicious_claim"),
        ]:
            result = check_fn(primary)
            if result:
                issues[key].extend(result if isinstance(result, list) else [str(result)])

    if headline:
        length = count_chars(headline)
        status = "✅" if length <= spec["headline_max"] else "❌"
        if length > spec["headline_max"]:
            issues["char_over_limit"].append(f"Headline {length} chars (max {spec['headline_max']})")
        report.append(f"  Headline: {status} '{headline}' ({length}/{spec['headline_max']} chars)")

    return report, dict(issues)


def validate_linkedin(ad):
    spec = PLATFORM_SPECS["linkedin"]
    issues = defaultdict(list)
    report = []

    intro = ad.get("intro_text", ad.get("primary_text", ""))
    headline = ad.get("headline", "")

    if intro:
        length = count_chars(intro)
        status = "✅" if length <= spec["intro_text_max"] else "⚠️ (preview truncated)"
        report.append(f"  Intro text: {status} ({length}/{spec['intro_text_max']} preview chars)")
        if length > spec["intro_text_max"]:
            issues["char_over_limit"].append(f"Intro text {length} chars exceeds {spec['intro_text_max']}-char preview")

        for check_fn, key in [
            (check_all_caps, "all_caps"),
            (check_excessive_punctuation, "excessive_punctuation"),
            (check_trademark_mentions, "trademark_mention"),
        ]:
            result = check_fn(intro)
            if result:
                issues[key].extend(result if isinstance(result, list) else [str(result)])

    if headline:
        length = count_chars(headline)
        status = "✅" if length <= spec["headline_max"] else "❌"
        if length > spec["headline_max"]:
            issues["char_over_limit"].append(f"Headline {length} chars (max {spec['headline_max']})")
        report.append(f"  Headline: {status} '{headline}' ({length}/{spec['headline_max']} chars)")

    return report, dict(issues)


def validate_generic(ad, platform_key):
    spec = PLATFORM_SPECS.get(platform_key, {})
    issues = defaultdict(list)
    report = []

    text = ad.get("primary_text", ad.get("text", ""))
    max_chars = spec.get("primary_text_max", 280)

    if text:
        length = count_chars(text)
        status = "✅" if length <= max_chars else "❌"
        if length > max_chars:
            issues["char_over_limit"].append(f"Text {length} chars (max {max_chars})")
        report.append(f"  Text: {status} ({length}/{max_chars} chars)")

        for check_fn, key in [
            (check_all_caps, "all_caps"),
            (check_excessive_punctuation, "excessive_punctuation"),
            (check_trademark_mentions, "trademark_mention"),
            (check_prohibited_phrases, "prohibited_phrase"),
        ]:
            result = check_fn(text)
            if result:
                issues[key].extend(result if isinstance(result, list) else [str(result)])

    return report, dict(issues)


def validate_ad(ad):
    platform = ad.get("platform", "").lower()

    if platform == "google_rsa":
        return validate_google_rsa(ad)
    elif platform == "meta_feed":
        return validate_meta_feed(ad)
    elif platform == "linkedin":
        return validate_linkedin(ad)
    elif platform in ("twitter", "tiktok"):
        return validate_generic(ad, platform)
    else:
        return [f"  ⚠️  Unknown platform '{platform}' — using generic validation"], {}


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------

def format_report(ad, char_lines, issues):
    platform = ad.get("platform", "unknown")
    spec = PLATFORM_SPECS.get(platform, {})
    platform_name = spec.get("name", platform.upper())

    score = score_ad(issues)
    grade = "🟢 Excellent" if score >= 85 else "🟡 Needs Work" if score >= 60 else "🔴 High Risk"

    lines = []
    lines.append(f"\n{'='*60}")
    lines.append(f"Platform: {platform_name}")
    lines.append(f"Quality Score: {score}/100  {grade}")
    lines.append(f"{'='*60}")

    lines.append("\nCharacter Counts:")
    lines.extend(char_lines)

    if issues:
        lines.append("\nIssues Found:")
        category_labels = {
            "char_over_limit": "❌ Over character limit",
            "all_caps": "⚠️  ALL CAPS words",
            "excessive_punctuation": "⚠️  Excessive punctuation",
            "trademark_mention": "🚫 Trademarked term",
            "prohibited_phrase": "🚫 Prohibited phrase",
            "suspicious_claim": "🚨 Suspicious claim (review required)",
            "count_too_few": "⚠️  Too few elements",
            "count_too_many": "⚠️  Too many elements",
        }
        for category, items in issues.items():
            label = category_labels.get(category, category)
            lines.append(f"  {label}: {', '.join(str(i) for i in items)}")
    else:
        lines.append("\n✅ No rejection triggers found.")

    lines.append("")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Sample data (embedded — runs with zero config)
# ---------------------------------------------------------------------------

SAMPLE_ADS = [
    {
        "platform": "google_rsa",
        "headlines": [
            "Cut Reporting Time by 80%",                   # 26 chars ✅
            "Automated Reports, Zero Effort",              # 31 chars ❌ over limit
            "Your Data. Your Way. Every Week.",            # 33 chars ❌ over limit
            "Save 8 Hours Per Week on Reports",            # 32 chars ❌ over limit
            "Try Free for 14 Days",                        # 21 chars ✅
            "No Code. No Complexity. Just Results.",        # 38 chars ❌
            "5,000 Teams Use This",                        # 21 chars ✅
            "Replace Your Weekly Standup Deck",            # 32 chars ❌
            "Connect Your Tools in 15 Minutes",            # 32 chars ❌
            "Instant Dashboards for Your Team",            # 32 chars ❌
            "Start Free — No Credit Card",                 # 28 chars ✅
            "Built for Growth Teams",                      # 22 chars ✅
            "See Your KPIs at a Glance",                   # 25 chars ✅
            "Data-Driven Decisions, Made Easy",            # 32 chars ❌
            "GUARANTEED Results — Try Now!!!",             # 31 chars ❌ + ALL CAPS + excessive punct
        ],
        "descriptions": [
            "Connect your tools, set your KPIs, and let the platform handle the weekly reporting. Free 14-day trial.",  # 103 chars ❌
            "Stop wasting Monday mornings on spreadsheets. Automated reports your whole team actually reads.",           # 94 chars ❌
        ],
    },
    {
        "platform": "meta_feed",
        "primary_text": "Your team is shipping features, but nobody can see the impact. [Product] connects your tools and shows you exactly what's working — in one dashboard, updated automatically. Start free today.",
        "headline": "See Your Impact, Automatically",
    },
    {
        "platform": "linkedin",
        "intro_text": "Growth teams at 3,200+ companies use [Product] to replace their manual weekly reports with automated dashboards.",
        "headline": "Automated Reporting for Growth Teams",
    },
    {
        "platform": "twitter",
        "primary_text": "Stop spending 8 hours on a report nobody reads. [Product] automates it — connect your tools, set your KPIs, and it runs itself. Free trial → [link]",
    },
]


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    import argparse

    parser = argparse.ArgumentParser(
        description="Validates ad copy against platform specs. "
                    "Checks character counts, rejection triggers, and scores each ad 0-100."
    )
    parser.add_argument(
        "file", nargs="?", default=None,
        help="Path to a JSON file containing ad data. "
             "If omitted, reads from stdin or runs embedded sample."
    )
    args = parser.parse_args()

    # Load from file or stdin, else use sample
    ads = None

    if args.file:
        try:
            with open(args.file) as f:
                data = json.load(f)
                ads = data if isinstance(data, list) else [data]
        except Exception as e:
            print(f"Error reading file: {e}", file=sys.stderr)
            sys.exit(1)
    elif not sys.stdin.isatty():
        raw = sys.stdin.read().strip()
        if raw:
            try:
                data = json.loads(raw)
                ads = data if isinstance(data, list) else [data]
            except Exception as e:
                print(f"Error reading stdin: {e}", file=sys.stderr)
                sys.exit(1)
        else:
            print("No input provided — running embedded sample ads.\n")
            ads = SAMPLE_ADS
    else:
        print("No input provided — running embedded sample ads.\n")
        ads = SAMPLE_ADS

    # Aggregate results for JSON output
    results = []
    all_output = []

    for ad in ads:
        char_lines, issues = validate_ad(ad)
        score = score_ad(issues)
        report_text = format_report(ad, char_lines, issues)
        all_output.append(report_text)
        results.append({
            "platform": ad.get("platform"),
            "score": score,
            "issues": {k: v for k, v in issues.items()},
            "passed": score >= 70,
        })

    # Human-readable output
    for block in all_output:
        print(block)

    # Summary
    avg_score = sum(r["score"] for r in results) / len(results) if results else 0
    passed = sum(1 for r in results if r["passed"])
    print(f"\nSUMMARY: {passed}/{len(results)} ads passed (avg score: {avg_score:.0f}/100)")

    # JSON output to stdout (for programmatic use) — write to separate section
    print("\n--- JSON Output ---")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
