#!/usr/bin/env python3
"""
X/Twitter Growth Tracker — Track and analyze account growth over time.

Stores periodic snapshots of account metrics and calculates growth trends,
engagement patterns, and milestone projections.

Usage:
    python3 growth_tracker.py --record --handle @user --followers 5200 --eng-rate 2.1
    python3 growth_tracker.py --report --handle @user
    python3 growth_tracker.py --report --handle @user --period 30d --json
    python3 growth_tracker.py --milestone --handle @user --target 10000
"""

import argparse
import json
import os
import sys
from datetime import datetime, timedelta
from pathlib import Path

DATA_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".growth-data")


def get_data_file(handle: str) -> str:
    clean = handle.lstrip("@").lower()
    os.makedirs(DATA_DIR, exist_ok=True)
    return os.path.join(DATA_DIR, f"{clean}.jsonl")


def record_snapshot(handle: str, followers: int, following: int = 0,
                    eng_rate: float = 0, posts_week: float = 0, notes: str = ""):
    entry = {
        "timestamp": datetime.now().isoformat(),
        "handle": handle,
        "followers": followers,
        "following": following,
        "engagement_rate": eng_rate,
        "posts_per_week": posts_week,
        "notes": notes,
    }

    filepath = get_data_file(handle)
    with open(filepath, "a") as f:
        f.write(json.dumps(entry) + "\n")

    return entry


def load_snapshots(handle: str, period_days: int = 0) -> list:
    filepath = get_data_file(handle)
    if not os.path.exists(filepath):
        return []

    entries = []
    cutoff = None
    if period_days > 0:
        cutoff = datetime.now() - timedelta(days=period_days)

    with open(filepath) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            entry = json.loads(line)
            if cutoff:
                ts = datetime.fromisoformat(entry["timestamp"])
                if ts < cutoff:
                    continue
            entries.append(entry)

    return entries


def generate_report(handle: str, entries: list) -> dict:
    if not entries:
        return {"handle": handle, "error": "No data found"}

    report = {
        "handle": handle,
        "data_points": len(entries),
        "first_record": entries[0]["timestamp"],
        "last_record": entries[-1]["timestamp"],
        "current_followers": entries[-1]["followers"],
    }

    if len(entries) >= 2:
        first = entries[0]
        last = entries[-1]

        follower_change = last["followers"] - first["followers"]
        days_span = (datetime.fromisoformat(last["timestamp"]) -
                     datetime.fromisoformat(first["timestamp"])).days
        days_span = max(days_span, 1)

        report["follower_change"] = follower_change
        report["days_tracked"] = days_span
        report["daily_growth"] = round(follower_change / days_span, 1)
        report["weekly_growth"] = round((follower_change / days_span) * 7, 1)
        report["monthly_projection"] = round((follower_change / days_span) * 30)

        if first["followers"] > 0:
            pct_change = ((last["followers"] - first["followers"]) / first["followers"]) * 100
            report["growth_percent"] = round(pct_change, 1)

        # Engagement trend
        eng_rates = [e["engagement_rate"] for e in entries if e.get("engagement_rate", 0) > 0]
        if len(eng_rates) >= 2:
            mid = len(eng_rates) // 2
            first_half_avg = sum(eng_rates[:mid]) / mid
            second_half_avg = sum(eng_rates[mid:]) / (len(eng_rates) - mid)
            report["engagement_trend"] = "improving" if second_half_avg > first_half_avg else "declining"
            report["avg_engagement_rate"] = round(sum(eng_rates) / len(eng_rates), 2)

    return report


def project_milestone(handle: str, entries: list, target: int) -> dict:
    if len(entries) < 2:
        return {"error": "Need at least 2 data points for projection"}

    current = entries[-1]["followers"]
    if current >= target:
        return {"handle": handle, "target": target, "status": "Already reached!"}

    first = entries[0]
    last = entries[-1]
    days_span = (datetime.fromisoformat(last["timestamp"]) -
                 datetime.fromisoformat(first["timestamp"])).days
    days_span = max(days_span, 1)

    daily_growth = (last["followers"] - first["followers"]) / days_span

    if daily_growth <= 0:
        return {"handle": handle, "target": target, "status": "Not growing — can't project",
                "daily_growth": round(daily_growth, 1)}

    remaining = target - current
    days_needed = remaining / daily_growth
    target_date = datetime.now() + timedelta(days=days_needed)

    return {
        "handle": handle,
        "current": current,
        "target": target,
        "remaining": remaining,
        "daily_growth": round(daily_growth, 1),
        "days_needed": round(days_needed),
        "projected_date": target_date.strftime("%Y-%m-%d"),
    }


def print_report(report: dict):
    print(f"\n{'='*60}")
    print(f"  GROWTH REPORT — {report['handle']}")
    print(f"{'='*60}")

    if "error" in report:
        print(f"\n  ⚠️  {report['error']}")
        print(f"  Record data first: python3 growth_tracker.py --record --handle {report['handle']} --followers N")
        print()
        return

    print(f"\n  Current followers:    {report['current_followers']:,}")
    print(f"  Data points:         {report['data_points']}")
    print(f"  Tracking since:      {report['first_record'][:10]}")

    if "follower_change" in report:
        change_icon = "📈" if report["follower_change"] > 0 else "📉" if report["follower_change"] < 0 else "➡️"
        print(f"\n  {change_icon} Change:  {report['follower_change']:+,} followers over {report['days_tracked']} days")
        print(f"  Daily avg:           {report.get('daily_growth', 0):+.1f}/day")
        print(f"  Weekly avg:          {report.get('weekly_growth', 0):+.1f}/week")
        print(f"  30-day projection:   {report.get('monthly_projection', 0):+,}")

        if "growth_percent" in report:
            print(f"  Growth rate:         {report['growth_percent']:+.1f}%")

        if "engagement_trend" in report:
            trend_icon = "📈" if report["engagement_trend"] == "improving" else "📉"
            print(f"  Engagement:          {trend_icon} {report['engagement_trend']} (avg {report['avg_engagement_rate']}%)")

    print(f"\n{'='*60}\n")


def main():
    parser = argparse.ArgumentParser(
        description="Track X/Twitter account growth over time",
        formatter_class=argparse.RawDescriptionHelpFormatter)

    parser.add_argument("--record", action="store_true", help="Record a new snapshot")
    parser.add_argument("--report", action="store_true", help="Generate growth report")
    parser.add_argument("--milestone", action="store_true", help="Project when target will be reached")

    parser.add_argument("--handle", required=True, help="X handle")
    parser.add_argument("--followers", type=int, default=0, help="Current follower count")
    parser.add_argument("--following", type=int, default=0, help="Current following count")
    parser.add_argument("--eng-rate", type=float, default=0, help="Current engagement rate (pct)")
    parser.add_argument("--posts-week", type=float, default=0, help="Posts per week")
    parser.add_argument("--notes", default="", help="Notes for this snapshot")
    parser.add_argument("--period", default="all", help="Report period: 7d, 30d, 90d, all")
    parser.add_argument("--target", type=int, default=0, help="Follower milestone target")
    parser.add_argument("--json", action="store_true", help="Output JSON")

    args = parser.parse_args()

    if not args.handle.startswith("@"):
        args.handle = f"@{args.handle}"

    if args.record:
        if args.followers <= 0:
            print("Error: --followers required for recording", file=sys.stderr)
            sys.exit(1)
        entry = record_snapshot(args.handle, args.followers, args.following,
                                args.eng_rate, args.posts_week, args.notes)
        if args.json:
            print(json.dumps(entry, indent=2))
        else:
            print(f"  ✅ Recorded: {args.handle} — {args.followers:,} followers")
            print(f"     File: {get_data_file(args.handle)}")

    elif args.report:
        period_days = 0
        if args.period != "all":
            period_days = int(args.period.rstrip("d"))
        entries = load_snapshots(args.handle, period_days)
        report = generate_report(args.handle, entries)
        if args.json:
            print(json.dumps(report, indent=2))
        else:
            print_report(report)

    elif args.milestone:
        if args.target <= 0:
            print("Error: --target required for milestone projection", file=sys.stderr)
            sys.exit(1)
        entries = load_snapshots(args.handle)
        result = project_milestone(args.handle, entries, args.target)
        if args.json:
            print(json.dumps(result, indent=2))
        else:
            if "error" in result:
                print(f"  ⚠️  {result['error']}")
            elif "status" in result and "days_needed" not in result:
                print(f"  🎉 {result['status']}")
            else:
                print(f"\n  🎯 Milestone Projection: {result['handle']}")
                print(f"  Current:  {result['current']:,}")
                print(f"  Target:   {result['target']:,}")
                print(f"  Gap:      {result['remaining']:,}")
                print(f"  Growth:   {result['daily_growth']:+.1f}/day")
                print(f"  ETA:      {result['projected_date']} (~{result['days_needed']} days)")
                print()

    else:
        parser.print_help()


if __name__ == "__main__":
    main()
