#!/usr/bin/env python3
"""
X/Twitter Competitor Analyzer — Analyze competitor profiles for content strategy insights.

Takes competitor handles and available data, produces a competitive
intelligence report with content patterns, engagement strategies, and gaps.

Usage:
    python3 competitor_analyzer.py --handles @user1 @user2 @user3
    python3 competitor_analyzer.py --handles @user1 --followers 50000 --niche "AI"
    python3 competitor_analyzer.py --import data.json
"""

import argparse
import json
import sys
from dataclasses import dataclass, field, asdict
from typing import Optional


@dataclass
class CompetitorProfile:
    handle: str
    followers: int = 0
    following: int = 0
    posts_per_week: float = 0
    avg_likes: float = 0
    avg_replies: float = 0
    avg_retweets: float = 0
    thread_frequency: str = ""  # daily, weekly, rarely
    top_topics: list = field(default_factory=list)
    content_mix: dict = field(default_factory=dict)  # format: percentage
    posting_times: list = field(default_factory=list)
    bio: str = ""
    notes: str = ""


@dataclass
class CompetitiveInsight:
    category: str
    finding: str
    opportunity: str
    priority: str  # HIGH, MEDIUM, LOW


def calculate_engagement_rate(profile: CompetitorProfile) -> float:
    if profile.followers <= 0:
        return 0
    total_engagement = profile.avg_likes + profile.avg_replies + profile.avg_retweets
    return (total_engagement / profile.followers) * 100


def analyze_competitors(competitors: list) -> list:
    insights = []

    # Engagement comparison
    engagement_rates = []
    for c in competitors:
        er = calculate_engagement_rate(c)
        engagement_rates.append((c.handle, er))

    if engagement_rates:
        top = max(engagement_rates, key=lambda x: x[1])
        if top[1] > 0:
            insights.append(CompetitiveInsight(
                "Engagement", f"Highest engagement: {top[0]} ({top[1]:.2f}%)",
                "Study their top posts — what format and topics drive replies?",
                "HIGH"
            ))

    # Posting frequency
    frequencies = [(c.handle, c.posts_per_week) for c in competitors if c.posts_per_week > 0]
    if frequencies:
        avg_freq = sum(f for _, f in frequencies) / len(frequencies)
        insights.append(CompetitiveInsight(
            "Frequency", f"Average posting: {avg_freq:.0f}/week across competitors",
            f"Match or exceed {avg_freq:.0f} posts/week to compete for mindshare",
            "HIGH"
        ))

    # Thread usage
    thread_users = [c.handle for c in competitors if c.thread_frequency in ("daily", "weekly")]
    if thread_users:
        insights.append(CompetitiveInsight(
            "Format", f"Active thread users: {', '.join(thread_users)}",
            "Threads are a proven growth lever in your niche. Publish 2-3/week minimum.",
            "HIGH"
        ))

    # Reply engagement
    reply_heavy = [(c.handle, c.avg_replies) for c in competitors if c.avg_replies > c.avg_likes * 0.3]
    if reply_heavy:
        names = [h for h, _ in reply_heavy]
        insights.append(CompetitiveInsight(
            "Community", f"High reply ratios: {', '.join(names)}",
            "These accounts build community through conversation. Ask more questions in your tweets.",
            "MEDIUM"
        ))

    # Follower/following ratio
    for c in competitors:
        if c.followers > 0 and c.following > 0:
            ratio = c.followers / c.following
            if ratio > 10:
                insights.append(CompetitiveInsight(
                    "Authority", f"{c.handle} has {ratio:.0f}x follower/following ratio",
                    "Strong authority signal — they attract followers without follow-backs",
                    "LOW"
                ))

    # Topic gaps
    all_topics = []
    for c in competitors:
        all_topics.extend(c.top_topics)

    if all_topics:
        from collections import Counter
        common = Counter(all_topics).most_common(5)
        insights.append(CompetitiveInsight(
            "Topics", f"Most covered topics: {', '.join(t for t, _ in common)}",
            "Cover these topics to compete, but find unique angles. What are they NOT covering?",
            "MEDIUM"
        ))

    return insights


def print_report(competitors: list, insights: list):
    print(f"\n{'='*70}")
    print(f"  COMPETITIVE ANALYSIS REPORT")
    print(f"{'='*70}")

    # Profile summary table
    print(f"\n  {'Handle':<20} {'Followers':>10} {'Posts/wk':>10} {'Eng Rate':>10}")
    print(f"  {'─'*20} {'─'*10} {'─'*10} {'─'*10}")
    for c in competitors:
        er = calculate_engagement_rate(c)
        print(f"  {c.handle:<20} {c.followers:>10,} {c.posts_per_week:>10.0f} {er:>9.2f}%")

    # Insights
    if insights:
        print(f"\n  {'─'*66}")
        print(f"  KEY INSIGHTS\n")

        priority_order = {"HIGH": 0, "MEDIUM": 1, "LOW": 2}
        sorted_insights = sorted(insights, key=lambda x: priority_order.get(x.priority, 3))

        for i in sorted_insights:
            icon = {"HIGH": "🔴", "MEDIUM": "🟡", "LOW": "⚪"}.get(i.priority, "❓")
            print(f"  {icon} [{i.category}] {i.finding}")
            print(f"     → {i.opportunity}")
            print()

    # Action items
    print(f"  {'─'*66}")
    print(f"  NEXT STEPS\n")
    print(f"  1. Search each competitor's profile on X — note their pinned tweet and bio")
    print(f"  2. Read their last 20 posts — categorize by format and topic")
    print(f"  3. Identify their top 3 performing posts — what made them work?")
    print(f"  4. Find gaps — what topics do they NOT cover that you can own?")
    print(f"  5. Set engagement targets based on their metrics as benchmarks")
    print(f"\n{'='*70}\n")


def main():
    parser = argparse.ArgumentParser(
        description="Analyze X/Twitter competitors for content strategy insights",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s --handles @user1 @user2
  %(prog)s --import competitors.json
  
  JSON format for --import:
  [{"handle": "@user1", "followers": 50000, "posts_per_week": 14, ...}]
        """)

    parser.add_argument("--handles", nargs="+", default=[], help="Competitor handles")
    parser.add_argument("--import", dest="import_file", help="Import from JSON file")
    parser.add_argument("--json", action="store_true", help="Output JSON")

    args = parser.parse_args()

    competitors = []

    if args.import_file:
        with open(args.import_file) as f:
            data = json.load(f)
            for item in data:
                competitors.append(CompetitorProfile(**item))
    elif args.handles:
        for handle in args.handles:
            if not handle.startswith("@"):
                handle = f"@{handle}"
            competitors.append(CompetitorProfile(handle=handle))

        if all(c.followers == 0 for c in competitors):
            print(f"\n  ℹ️  Handles registered: {', '.join(c.handle for c in competitors)}")
            print(f"  To get full analysis, provide data via JSON import:")
            print(f"  1. Research each profile on X")
            print(f"  2. Create a JSON file with follower counts, posting frequency, etc.")
            print(f"  3. Run: {sys.argv[0]} --import data.json")
            print(f"\n  Example JSON:")
            example = [asdict(CompetitorProfile(
                handle="@example",
                followers=25000,
                following=1200,
                posts_per_week=14,
                avg_likes=150,
                avg_replies=30,
                avg_retweets=20,
                thread_frequency="weekly",
                top_topics=["AI", "startups", "engineering"],
            ))]
            print(f"  {json.dumps(example, indent=2)}")
            print()
            return

    if not competitors:
        print("Error: provide --handles or --import", file=sys.stderr)
        sys.exit(1)

    insights = analyze_competitors(competitors)

    if args.json:
        print(json.dumps({
            "competitors": [asdict(c) for c in competitors],
            "insights": [asdict(i) for i in insights],
        }, indent=2))
    else:
        print_report(competitors, insights)


if __name__ == "__main__":
    main()
