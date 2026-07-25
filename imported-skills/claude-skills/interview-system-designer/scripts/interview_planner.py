#!/usr/bin/env python3
"""Generate an interview loop plan by role and level."""

from __future__ import annotations

import argparse
import json
from typing import Dict, List

BASE_ROUNDS = {
    "junior": [
        ("Screen", 45, "Fundamentals and communication"),
        ("Coding", 60, "Problem solving and code quality"),
        ("Behavioral", 45, "Collaboration and growth mindset"),
    ],
    "mid": [
        ("Screen", 45, "Fundamentals and ownership"),
        ("Coding", 60, "Implementation quality"),
        ("System Design", 60, "Service/component design"),
        ("Behavioral", 45, "Stakeholder collaboration"),
    ],
    "senior": [
        ("Screen", 45, "Depth and tradeoff reasoning"),
        ("Coding", 60, "Code quality and testing"),
        ("System Design", 75, "Scalability and reliability"),
        ("Leadership", 60, "Mentoring and decision making"),
        ("Behavioral", 45, "Cross-functional influence"),
    ],
    "staff": [
        ("Screen", 45, "Strategic and technical depth"),
        ("Architecture", 90, "Org-level design decisions"),
        ("Technical Strategy", 60, "Long-term tradeoffs"),
        ("Influence", 60, "Cross-team leadership"),
        ("Behavioral", 45, "Values and executive communication"),
    ],
}

QUESTION_BANK = {
    "coding": [
        "Walk through your approach before coding and identify tradeoffs.",
        "How would you test this implementation for edge cases?",
        "What would you refactor if this code became a shared library?",
    ],
    "system": [
        "Design this system for 10x traffic growth in 12 months.",
        "Where are the main failure modes and how would you detect them?",
        "What components would you scale first and why?",
    ],
    "leadership": [
        "Describe a time you changed technical direction with incomplete information.",
        "How do you raise the bar for code quality across a team?",
        "How do you handle disagreement between product and engineering priorities?",
    ],
    "behavioral": [
        "Tell me about a high-stakes mistake and what changed afterward.",
        "Describe a conflict where you had to influence without authority.",
        "How do you support underperforming teammates?",
    ],
}


def normalize_level(level: str) -> str:
    level = level.strip().lower()
    if level in {"staff+", "principal", "lead"}:
        return "staff"
    if level not in BASE_ROUNDS:
        raise ValueError(f"Unsupported level: {level}")
    return level


def suggested_questions(round_name: str) -> List[str]:
    name = round_name.lower()
    if "coding" in name:
        return QUESTION_BANK["coding"]
    if "system" in name or "architecture" in name:
        return QUESTION_BANK["system"]
    if "lead" in name or "influence" in name or "strategy" in name:
        return QUESTION_BANK["leadership"]
    return QUESTION_BANK["behavioral"]


def generate_plan(role: str, level: str) -> Dict[str, object]:
    normalized = normalize_level(level)
    rounds = []
    for idx, (name, minutes, focus) in enumerate(BASE_ROUNDS[normalized], start=1):
        rounds.append(
            {
                "round": idx,
                "name": name,
                "duration_minutes": minutes,
                "focus": focus,
                "suggested_questions": suggested_questions(name),
            }
        )
    return {
        "role": role,
        "level": normalized,
        "total_rounds": len(rounds),
        "total_minutes": sum(r["duration_minutes"] for r in rounds),
        "rounds": rounds,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate an interview loop plan for a role and level.")
    parser.add_argument("--role", required=True, help="Role name (e.g., Senior Software Engineer)")
    parser.add_argument("--level", required=True, help="Level: junior|mid|senior|staff")
    parser.add_argument("--json", action="store_true", help="Output as JSON")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    plan = generate_plan(args.role, args.level)

    if args.json:
        print(json.dumps(plan, indent=2))
    else:
        print(f"Interview Plan: {plan['role']} ({plan['level']})")
        print(f"Total rounds: {plan['total_rounds']} | Total time: {plan['total_minutes']} minutes")
        print("")
        for r in plan["rounds"]:
            print(f"Round {r['round']}: {r['name']} ({r['duration_minutes']} min)")
            print(f"Focus: {r['focus']}")
            for q in r["suggested_questions"]:
                print(f"- {q}")
            print("")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
