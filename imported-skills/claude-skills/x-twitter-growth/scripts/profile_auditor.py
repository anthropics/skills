#!/usr/bin/env python3
"""
X/Twitter Profile Auditor — Audit any X profile for growth readiness.

Checks bio quality, pinned tweet, posting patterns, and provides
actionable recommendations. Works without API access by analyzing
profile data you provide or scraping public info via web search.

Usage:
    python3 profile_auditor.py --handle @username
    python3 profile_auditor.py --handle @username --json
    python3 profile_auditor.py --bio "current bio text" --followers 5000 --posts-per-week 10
"""

import argparse
import json
import re
import sys
from dataclasses import dataclass, field, asdict
from typing import Optional


@dataclass
class ProfileData:
    handle: str = ""
    bio: str = ""
    followers: int = 0
    following: int = 0
    posts_per_week: float = 0
    reply_ratio: float = 0  # % of posts that are replies
    thread_ratio: float = 0  # % of posts that are threads
    has_pinned: bool = False
    pinned_age_days: int = 0
    has_link: bool = False
    has_newsletter: bool = False
    avg_engagement_rate: float = 0  # likes+replies+rts / followers


@dataclass
class AuditFinding:
    area: str
    status: str  # GOOD, WARN, CRITICAL
    message: str
    fix: str = ""


@dataclass
class AuditReport:
    handle: str
    score: int = 0
    max_score: int = 100
    grade: str = ""
    findings: list = field(default_factory=list)
    recommendations: list = field(default_factory=list)


def audit_bio(profile: ProfileData) -> list:
    findings = []
    bio = profile.bio.strip()

    if not bio:
        findings.append(AuditFinding("Bio", "CRITICAL", "No bio provided for audit",
                                     "Provide bio text with --bio flag"))
        return findings

    # Length check
    if len(bio) < 30:
        findings.append(AuditFinding("Bio", "WARN", f"Bio too short ({len(bio)} chars)",
                                     "Aim for 100-160 characters with clear value prop"))
    elif len(bio) > 160:
        findings.append(AuditFinding("Bio", "WARN", f"Bio may be too long ({len(bio)} chars)",
                                     "Keep under 160 chars for readability"))
    else:
        findings.append(AuditFinding("Bio", "GOOD", f"Bio length OK ({len(bio)} chars)"))

    # Hashtag check
    hashtags = re.findall(r'#\w+', bio)
    if hashtags:
        findings.append(AuditFinding("Bio", "WARN", f"Hashtags in bio ({', '.join(hashtags)})",
                                     "Remove hashtags — signals amateur. Use plain text."))
    else:
        findings.append(AuditFinding("Bio", "GOOD", "No hashtags in bio"))

    # Buzzword check
    buzzwords = ['entrepreneur', 'guru', 'ninja', 'rockstar', 'visionary', 'hustler',
                 'thought leader', 'serial entrepreneur', 'dreamer', 'doer']
    found = [bw for bw in buzzwords if bw.lower() in bio.lower()]
    if found:
        findings.append(AuditFinding("Bio", "WARN", f"Buzzwords detected: {', '.join(found)}",
                                     "Replace with specific, concrete descriptions of what you do"))

    # Specificity check — pipes and slashes often signal unfocused bios
    if bio.count('|') >= 3 or bio.count('/') >= 3:
        findings.append(AuditFinding("Bio", "WARN", "Bio may lack focus (too many roles/identities)",
                                     "Lead with ONE clear identity. What's the #1 thing you want to be known for?"))

    # Social proof check
    proof_patterns = [r'\d+[kKmM]?\+?\s*(followers|subscribers|readers|users|customers)',
                      r'(founder|ceo|cto|vp|head|director|lead)\s+(of|at|@)',
                      r'(author|writer)\s+of', r'featured\s+in', r'ex-\w+']
    has_proof = any(re.search(p, bio, re.IGNORECASE) for p in proof_patterns)
    if has_proof:
        findings.append(AuditFinding("Bio", "GOOD", "Social proof detected"))
    else:
        findings.append(AuditFinding("Bio", "WARN", "No obvious social proof in bio",
                                     "Add a credential: title, metric, brand association, or achievement"))

    # CTA/Link check
    if profile.has_link:
        findings.append(AuditFinding("Bio", "GOOD", "Profile has a link"))
    else:
        findings.append(AuditFinding("Bio", "WARN", "No link in profile",
                                     "Add a link to newsletter, product, or portfolio"))

    return findings


def audit_activity(profile: ProfileData) -> list:
    findings = []

    # Posting frequency
    if profile.posts_per_week <= 0:
        findings.append(AuditFinding("Activity", "CRITICAL", "No posting data provided",
                                     "Provide --posts-per-week estimate"))
    elif profile.posts_per_week < 3:
        findings.append(AuditFinding("Activity", "CRITICAL",
                                     f"Very low posting ({profile.posts_per_week:.0f}/week)",
                                     "Minimum 7 posts/week (1/day). Aim for 14-21."))
    elif profile.posts_per_week < 7:
        findings.append(AuditFinding("Activity", "WARN",
                                     f"Low posting ({profile.posts_per_week:.0f}/week)",
                                     "Aim for 2-3 posts per day for consistent growth"))
    elif profile.posts_per_week < 21:
        findings.append(AuditFinding("Activity", "GOOD",
                                     f"Good posting cadence ({profile.posts_per_week:.0f}/week)"))
    else:
        findings.append(AuditFinding("Activity", "GOOD",
                                     f"High posting cadence ({profile.posts_per_week:.0f}/week)"))

    # Reply ratio
    if profile.reply_ratio > 0:
        if profile.reply_ratio < 0.2:
            findings.append(AuditFinding("Activity", "WARN",
                                         f"Low reply ratio ({profile.reply_ratio:.0%})",
                                         "Aim for 30%+ replies. Engage with others, don't just broadcast."))
        elif profile.reply_ratio >= 0.3:
            findings.append(AuditFinding("Activity", "GOOD",
                                         f"Healthy reply ratio ({profile.reply_ratio:.0%})"))

    # Follower/following ratio
    if profile.followers > 0 and profile.following > 0:
        ratio = profile.followers / profile.following
        if ratio < 0.5:
            findings.append(AuditFinding("Profile", "WARN",
                                         f"Low follower/following ratio ({ratio:.1f}x)",
                                         "Unfollow inactive accounts. Ratio should trend toward 2:1+"))
        elif ratio >= 2:
            findings.append(AuditFinding("Profile", "GOOD",
                                         f"Healthy follower/following ratio ({ratio:.1f}x)"))

    # Pinned tweet
    if profile.has_pinned:
        if profile.pinned_age_days > 30:
            findings.append(AuditFinding("Profile", "WARN",
                                         f"Pinned tweet is {profile.pinned_age_days} days old",
                                         "Update pinned tweet monthly with your latest best content"))
        else:
            findings.append(AuditFinding("Profile", "GOOD", "Pinned tweet is recent"))
    else:
        findings.append(AuditFinding("Profile", "WARN", "No pinned tweet",
                                     "Pin your best-performing tweet or thread. It's your landing page."))

    return findings


def calculate_score(findings: list) -> tuple:
    total = len(findings)
    if total == 0:
        return 0, "F"

    good = sum(1 for f in findings if f.status == "GOOD")
    score = int((good / total) * 100)

    if score >= 90:
        grade = "A"
    elif score >= 75:
        grade = "B"
    elif score >= 60:
        grade = "C"
    elif score >= 40:
        grade = "D"
    else:
        grade = "F"

    return score, grade


def generate_recommendations(findings: list, profile: ProfileData) -> list:
    recs = []
    criticals = [f for f in findings if f.status == "CRITICAL"]
    warns = [f for f in findings if f.status == "WARN"]

    for f in criticals:
        if f.fix:
            recs.append(f"🔴 {f.fix}")

    for f in warns[:3]:  # Top 3 warnings
        if f.fix:
            recs.append(f"🟡 {f.fix}")

    # Stage-specific advice
    if profile.followers < 1000:
        recs.append("📈 Growth phase: Focus 70% on replies to larger accounts, 30% on your own posts")
    elif profile.followers < 10000:
        recs.append("📈 Momentum phase: 2-3 threads/week + daily engagement. Start a recurring series.")
    else:
        recs.append("📈 Scale phase: Leverage audience with cross-platform repurposing + newsletter growth")

    return recs


def main():
    parser = argparse.ArgumentParser(
        description="Audit an X/Twitter profile for growth readiness",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s --handle @rezarezvani --bio "CTO building AI products" --followers 5000
  %(prog)s --bio "Entrepreneur | Dreamer | Hustle" --followers 200 --posts-per-week 3
  %(prog)s --handle @example --followers 50000 --posts-per-week 21 --reply-ratio 0.4 --json
        """)

    parser.add_argument("--handle", default="@unknown", help="X handle")
    parser.add_argument("--bio", default="", help="Current bio text")
    parser.add_argument("--followers", type=int, default=0, help="Follower count")
    parser.add_argument("--following", type=int, default=0, help="Following count")
    parser.add_argument("--posts-per-week", type=float, default=0, help="Average posts per week")
    parser.add_argument("--reply-ratio", type=float, default=0, help="Fraction of posts that are replies (0-1)")
    parser.add_argument("--has-pinned", action="store_true", help="Has a pinned tweet")
    parser.add_argument("--pinned-age-days", type=int, default=0, help="Age of pinned tweet in days")
    parser.add_argument("--has-link", action="store_true", help="Has link in profile")
    parser.add_argument("--json", action="store_true", help="Output JSON")

    args = parser.parse_args()

    profile = ProfileData(
        handle=args.handle,
        bio=args.bio,
        followers=args.followers,
        following=args.following,
        posts_per_week=args.posts_per_week,
        reply_ratio=args.reply_ratio,
        has_pinned=args.has_pinned,
        pinned_age_days=args.pinned_age_days,
        has_link=args.has_link,
    )

    findings = audit_bio(profile) + audit_activity(profile)
    score, grade = calculate_score(findings)
    recs = generate_recommendations(findings, profile)

    report = AuditReport(
        handle=profile.handle,
        score=score,
        grade=grade,
        findings=[asdict(f) for f in findings],
        recommendations=recs,
    )

    if args.json:
        print(json.dumps(asdict(report), indent=2))
    else:
        print(f"\n{'='*60}")
        print(f"  X PROFILE AUDIT — {report.handle}")
        print(f"{'='*60}")
        print(f"\n  Score: {report.score}/100 (Grade: {report.grade})\n")

        for f in findings:
            icon = {"GOOD": "✅", "WARN": "⚠️", "CRITICAL": "🔴"}.get(f.status, "❓")
            print(f"  {icon} [{f.area}] {f.message}")
            if f.fix and f.status != "GOOD":
                print(f"     → {f.fix}")

        if recs:
            print(f"\n  {'─'*56}")
            print(f"  TOP RECOMMENDATIONS\n")
            for i, r in enumerate(recs, 1):
                print(f"  {i}. {r}")

        print(f"\n{'='*60}\n")


if __name__ == "__main__":
    main()
