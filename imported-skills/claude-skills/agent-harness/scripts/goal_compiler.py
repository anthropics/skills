#!/usr/bin/env python3
"""Compile a goal into a verifiable task plan against a domain harness manifest.

Deterministic keyword scoring (no LLM calls): the goal is tokenized, each skill
in the manifest is scored on name/description overlap, and the top matches
become ordered tasks — each with the verification checks the manifest recorded
for that skill and a done_when contract loop_controller.py can enforce.

Refusal gates (the harness never runs on fuzz):
  exit 3 — goal too vague (< 4 content tokens): emits forcing questions.
  exit 4 — no skill scores above --min-score: emits nearest candidates.

Usage:
  python3 goal_compiler.py --goal "audit our API design and ship an SLO" \
      --manifest assets/harnesses/engineering.json --out plan.json
  python3 goal_compiler.py --sample
"""

import argparse
import datetime
import json
import re
import sys

SCHEMA = "agent-harness/plan.v1"

STOPWORDS = {
    "a", "an", "and", "are", "as", "at", "be", "by", "can", "do", "for",
    "from", "get", "have", "how", "i", "in", "is", "it", "make", "me", "my",
    "of", "on", "or", "our", "please", "set", "should", "so", "that", "the",
    "then", "this", "to", "up", "us", "want", "we", "what", "when", "will",
    "with", "you", "your", "need", "needs", "into", "using", "use",
}

FORCING_QUESTIONS = [
    "What is the single observable outcome that means this goal is DONE "
    "(a file, a passing check, a published artifact)?",
    "Which system, repo, or artifact does the work act on?",
    "What must NOT change (constraints, no-touch zones, budgets)?",
    "Who reviews the result, and what evidence do they need to accept it?",
    "What is the deadline or iteration budget before a human takes over?",
]


def tokenize(text):
    words = re.findall(r"[a-z0-9][a-z0-9\-]+", text.lower())
    out = []
    for w in words:
        out.extend(w.split("-"))
    return [w for w in out if len(w) > 2 and w not in STOPWORDS]


def score_skill(goal_tokens, skill):
    name_tokens = set(tokenize(skill.get("name", "")))
    desc_tokens = set(tokenize(skill.get("description", "")))
    score = 0
    hits = []
    for t in set(goal_tokens):
        if t in name_tokens:
            score += 3
            hits.append(t)
        elif t in desc_tokens:
            score += 1
            hits.append(t)
    return score, sorted(hits)


def build_task(idx, skill, goal, defaults):
    checks = []
    tool_cmds = []
    for tool in skill.get("tools", []):
        tool_cmds.append("python3 %s --help  # discover flags first" % tool["script"])
        checks.extend(tool.get("verification", []))
    if not checks:
        checks.append({
            "cmd": "MANUAL: state the observable evidence that this task met "
                   "its objective; a task with no check cannot be closed, only "
                   "escalated.",
            "expect_exit": 0,
            "kind": "manual-evidence",
        })
    return {
        "id": "T%d" % idx,
        "skill": skill["name"],
        "skill_path": skill["path"],
        "objective": "Apply skill '%s' toward goal: %s" % (skill["name"], goal),
        "suggested_tools": tool_cmds,
        "verification": checks,
        "done_when": "every verification check meets expect_exit AND the "
                     "output is consistent with the task objective",
        "max_attempts": defaults.get("max_attempts_per_task", 3),
        "status": "pending",
    }


SAMPLE_PLAN = {
    "schema": SCHEMA,
    "goal": "design an SLO and error budget for the payments API",
    "domain": "engineering",
    "tasks": [{
        "id": "T1",
        "skill": "slo-architect",
        "skill_path": "engineering/slo-architect/skills/slo-architect",
        "objective": "Apply skill 'slo-architect' toward goal: design an SLO "
                     "and error budget for the payments API",
        "suggested_tools": [
            "python3 .../scripts/error_budget_calculator.py --help  # discover flags first",
        ],
        "verification": [
            {"cmd": "python3 .../error_budget_calculator.py --target 99.9 "
                    "--window-days 30", "expect_exit": 0, "kind": "sample"},
        ],
        "done_when": "every verification check meets expect_exit AND the "
                     "output is consistent with the task objective",
        "max_attempts": 3,
        "status": "pending",
    }],
    "loop": {
        "order": "sequential",
        "max_loop_iterations": 12,
        "escalate_on": ["attempts_exhausted", "no_verification_available"],
    },
    "close": {
        "requires": "all tasks verified (or explicitly waived with a reason)",
        "handoff": "loop_controller.py close emits the evidence log + summary",
    },
}


def main():
    ap = argparse.ArgumentParser(
        description="Compile a goal into a verifiable task plan from a domain "
                    "harness manifest.")
    ap.add_argument("--goal", help="The goal statement to compile.")
    ap.add_argument("--manifest", help="Path to a harness manifest JSON.")
    ap.add_argument("--max-tasks", type=int, default=5)
    ap.add_argument("--min-score", type=int, default=2,
                    help="Minimum match score for a skill to become a task.")
    ap.add_argument("--out", help="Write the plan JSON here.")
    ap.add_argument("--json", action="store_true", help="Print plan to stdout.")
    ap.add_argument("--sample", action="store_true",
                    help="Print an example plan and exit 0.")
    args = ap.parse_args()

    if args.sample:
        print(json.dumps(SAMPLE_PLAN, indent=2))
        return 0
    if not args.goal or not args.manifest:
        ap.error("--goal and --manifest are required (or use --sample)")

    goal_tokens = tokenize(args.goal)
    if len(goal_tokens) < 4:
        print(json.dumps({
            "verdict": "REFUSED-VAGUE-GOAL",
            "reason": "goal has %d content tokens (< 4); the harness never "
                      "runs on fuzz" % len(goal_tokens),
            "forcing_questions": FORCING_QUESTIONS,
        }, indent=2))
        return 3

    with open(args.manifest, encoding="utf-8") as f:
        manifest = json.load(f)
    defaults = manifest.get("loop_defaults", {})

    scored = []
    for skill in manifest.get("skills", []):
        s, hits = score_skill(goal_tokens, skill)
        if s > 0:
            scored.append((s, skill["name"], hits, skill))
    scored.sort(key=lambda x: (-x[0], x[1]))

    eligible = [x for x in scored if x[0] >= args.min_score]
    if not eligible:
        print(json.dumps({
            "verdict": "REFUSED-NO-MATCH",
            "reason": "no skill in domain '%s' scored >= %d for this goal"
                      % (manifest.get("domain"), args.min_score),
            "nearest_candidates": [
                {"skill": n, "score": s, "matched": h}
                for s, n, h, _ in scored[:5]
            ],
            "forcing_questions": FORCING_QUESTIONS[:2],
        }, indent=2))
        return 4

    tasks = [build_task(i + 1, sk, args.goal, defaults)
             for i, (_, _, _, sk) in enumerate(eligible[: args.max_tasks])]

    plan = {
        "schema": SCHEMA,
        "goal": args.goal,
        "domain": manifest.get("domain"),
        "compiled_at": datetime.datetime.now(datetime.timezone.utc)
        .strftime("%Y-%m-%dT%H:%M:%SZ"),
        "skill_match_report": [
            {"skill": n, "score": s, "matched": h} for s, n, h, _ in scored[:10]
        ],
        "tasks": tasks,
        "loop": {
            "order": "sequential",
            "max_loop_iterations": defaults.get("max_loop_iterations", 12),
            "escalate_on": defaults.get("escalate_on", ["attempts_exhausted"]),
        },
        "close": {
            "requires": "all tasks verified (or explicitly waived with a reason)",
            "handoff": "loop_controller.py close emits the evidence log + summary",
        },
    }

    out = json.dumps(plan, indent=2)
    if args.out:
        with open(args.out, "w", encoding="utf-8") as f:
            f.write(out + "\n")
        print("wrote %s (%d tasks)" % (args.out, len(tasks)), file=sys.stderr)
    if args.json or not args.out:
        print(out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
