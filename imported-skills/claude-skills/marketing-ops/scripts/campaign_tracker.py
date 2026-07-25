#!/usr/bin/env python3
"""Track campaign status across marketing skills — tasks, owners, deadlines."""

import json
import sys
from datetime import datetime, timedelta
from pathlib import Path

SAMPLE_CAMPAIGN = {
    "name": "Q1 Product Launch",
    "created": "2026-03-01",
    "status": "in_progress",
    "skills_used": [],
    "tasks": [
        {"skill": "marketing-context", "task": "Update context for new feature", "owner": "Marketing", "deadline": "2026-03-03", "status": "complete"},
        {"skill": "launch-strategy", "task": "Plan launch phases", "owner": "PMM", "deadline": "2026-03-05", "status": "complete"},
        {"skill": "content-strategy", "task": "Plan content calendar", "owner": "Content", "deadline": "2026-03-07", "status": "in_progress"},
        {"skill": "copywriting", "task": "Write landing page copy", "owner": "Copywriter", "deadline": "2026-03-10", "status": "not_started"},
        {"skill": "email-sequence", "task": "Write launch email sequence", "owner": "Email", "deadline": "2026-03-10", "status": "not_started"},
        {"skill": "social-content", "task": "Create social media posts", "owner": "Social", "deadline": "2026-03-12", "status": "not_started"},
        {"skill": "paid-ads", "task": "Set up ad campaigns", "owner": "Paid", "deadline": "2026-03-12", "status": "not_started"},
        {"skill": "ad-creative", "task": "Generate ad variations", "owner": "Creative", "deadline": "2026-03-11", "status": "not_started"},
        {"skill": "analytics-tracking", "task": "Set up conversion tracking", "owner": "Analytics", "deadline": "2026-03-08", "status": "in_progress"},
        {"skill": "seo-audit", "task": "Optimize landing page SEO", "owner": "SEO", "deadline": "2026-03-09", "status": "not_started"},
    ]
}


def analyze_campaign(campaign: dict) -> dict:
    """Analyze campaign status and generate report."""
    tasks = campaign["tasks"]
    today = datetime.now().strftime("%Y-%m-%d")

    complete = [t for t in tasks if t["status"] == "complete"]
    in_progress = [t for t in tasks if t["status"] == "in_progress"]
    not_started = [t for t in tasks if t["status"] == "not_started"]
    overdue = [t for t in tasks if t["deadline"] < today and t["status"] != "complete"]
    due_soon = [t for t in tasks if today <= t["deadline"] <= (datetime.now() + timedelta(days=3)).strftime("%Y-%m-%d") and t["status"] != "complete"]

    total = len(tasks)
    progress = round((len(complete) / total) * 100) if total > 0 else 0

    # Skills coverage
    skills_used = list(set(t["skill"] for t in tasks))
    pods_covered = set()
    pod_map = {
        "content": ["content-strategy", "copywriting", "copy-editing", "social-content", "marketing-ideas", "content-production", "content-humanizer", "content-creator"],
        "seo": ["seo-audit", "programmatic-seo", "aeo", "schema-markup", "site-architecture"],
        "cro": ["page-cro", "form-cro", "signup-flow-cro", "onboarding-cro", "popup-cro", "paywall-upgrade-cro"],
        "channels": ["email-sequence", "cold-email", "paid-ads", "ad-creative", "social-media-manager"],
        "growth": ["ab-test-setup", "referral-program", "free-tool-strategy", "churn-prevention"],
        "intelligence": ["campaign-analytics", "analytics-tracking", "competitor-alternatives", "marketing-psychology"],
        "gtm": ["launch-strategy", "pricing-strategy"]
    }
    for pod, skills in pod_map.items():
        if any(s in skills_used for s in skills):
            pods_covered.add(pod)

    # Blockers
    blockers = []
    for t in tasks:
        if t["status"] == "not_started":
            # Check if any dependency is incomplete
            deps = [d for d in tasks if d["deadline"] < t["deadline"] and d["status"] != "complete"]
            if deps:
                blocker_names = [d["task"] for d in deps if d["status"] != "complete"]
                if blocker_names:
                    blockers.append({"task": t["task"], "blocked_by": blocker_names[0]})

    return {
        "campaign": campaign["name"],
        "progress": progress,
        "total_tasks": total,
        "complete": len(complete),
        "in_progress": len(in_progress),
        "not_started": len(not_started),
        "overdue": [{"task": t["task"], "deadline": t["deadline"], "owner": t["owner"]} for t in overdue],
        "due_soon": [{"task": t["task"], "deadline": t["deadline"], "owner": t["owner"]} for t in due_soon],
        "pods_covered": sorted(pods_covered),
        "pods_missing": sorted(set(pod_map.keys()) - pods_covered),
        "skills_used": sorted(skills_used),
        "blockers": blockers
    }


def print_report(analysis: dict):
    """Print human-readable campaign status."""
    print(f"\n{'='*55}")
    print(f"CAMPAIGN: {analysis['campaign']}")
    print(f"{'='*55}")

    bar_len = 30
    filled = round(bar_len * analysis["progress"] / 100)
    bar = "█" * filled + "░" * (bar_len - filled)
    print(f"\nProgress: [{bar}] {analysis['progress']}%")
    print(f"Tasks: {analysis['complete']} done / {analysis['in_progress']} active / {analysis['not_started']} pending")

    if analysis["overdue"]:
        print(f"\n🔴 OVERDUE ({len(analysis['overdue'])}):")
        for t in analysis["overdue"]:
            print(f"   → {t['task']} (due {t['deadline']}, owner: {t['owner']})")

    if analysis["due_soon"]:
        print(f"\n🟡 DUE SOON ({len(analysis['due_soon'])}):")
        for t in analysis["due_soon"]:
            print(f"   → {t['task']} (due {t['deadline']}, owner: {t['owner']})")

    if analysis["blockers"]:
        print(f"\n⚠️  BLOCKERS:")
        for b in analysis["blockers"]:
            print(f"   → {b['task']} blocked by: {b['blocked_by']}")

    print(f"\n📦 Pods covered: {', '.join(analysis['pods_covered'])}")
    if analysis["pods_missing"]:
        print(f"   Missing: {', '.join(analysis['pods_missing'])}")

    print(f"\n🔧 Skills used: {', '.join(analysis['skills_used'])}")
    print(f"{'='*55}")


def main():
    import argparse

    parser = argparse.ArgumentParser(
        description="Track campaign status across marketing skills — tasks, owners, deadlines."
    )
    parser.add_argument(
        "input_file", nargs="?", default=None,
        help="JSON file with campaign data (default: run with sample data)"
    )
    parser.add_argument(
        "--json", action="store_true",
        help="Also output results as JSON"
    )
    args = parser.parse_args()

    if args.input_file:
        filepath = Path(args.input_file)
        if filepath.exists():
            campaign = json.loads(filepath.read_text())
        else:
            print(f"Error: {filepath} not found", file=sys.stderr)
            sys.exit(1)
    else:
        campaign = SAMPLE_CAMPAIGN
        print("[Using sample campaign data — pass a JSON file for real tracking]")

    analysis = analyze_campaign(campaign)
    print_report(analysis)

    if args.json:
        print(f"\n{json.dumps(analysis, indent=2)}")


if __name__ == "__main__":
    main()
