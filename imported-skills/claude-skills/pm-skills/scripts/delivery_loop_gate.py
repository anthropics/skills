#!/usr/bin/env python3
"""delivery_loop_gate.py — governance gate for agent-executed delivery loops.

Encodes the 2025–2026 agentic-delegation canon as a machine-checkable gate
(Linear's agents model: the human stays accountable for delegated work; Atlassian
Rovo: every agent action stays auditable; loop-library: exhausted budgets are never
reported as success). Run it on a delivery-loop plan before executing (--mode plan)
and again before closing (--mode close). Pairs with the repo-wide
engineering/agent-harness loop_controller.py, which enforces the run-time state
machine; this gate enforces the PM-specific accountability rules the controller
does not know about.

Plan JSON shape (see --sample):
  {"goal": str,
   "budgets": {"max_attempts_per_task": int, "max_loop_iterations": int},
   "iteration": int,
   "tasks": [{"id","title","owner","executor":"human|agent","reviewer",
              "acceptance": {"cmd": str} | {"criterion": str},
              "status":"todo|in_progress|done|blocked|waived",
              "evidence": str, "attempts": int, "waive_reason": str}]}

Rules enforced:
  G1 every task has a named human owner (agents are contributors, never owners)
  G2 agent-executed tasks name a human reviewer distinct from nobody
  G3 acceptance is machine-checkable: a cmd, or a criterion containing a measurable
     threshold (a digit) — "looks good" is not a gate
  G4 done requires non-empty evidence; waived requires a waive_reason
  G5 close is refused while any task is neither done nor waived
  G6 close is refused when budgets are exhausted with work remaining — that is an
     escalation, not a success
Exit codes: 0 pass · 2 plan violations · 3 unreadable input · 4 close refused.
Stdlib only, deterministic.
"""

import argparse
import json
import re
import sys

SAMPLE_PLAN = {
    "goal": "Get sprint 14 to a verified close with a health score >= 70",
    "budgets": {"max_attempts_per_task": 3, "max_loop_iterations": 12},
    "iteration": 4,
    "tasks": [
        {"id": "T1", "title": "Pull sprint snapshot via searchJiraIssuesUsingJql",
         "owner": "Sarah Chen", "executor": "agent", "reviewer": "Sarah Chen",
         "acceptance": {"cmd": "python3 scripts/jira_snapshot_bridge.py --input snapshot.json --to sprint"},
         "status": "done", "evidence": "sprint_data.json written, 4 sprints", "attempts": 1},
        {"id": "T2", "title": "Score sprint health",
         "owner": "Sarah Chen", "executor": "agent", "reviewer": "Mike Rodriguez",
         "acceptance": {"criterion": "sprint_health_scorer.py composite >= 70"},
         "status": "in_progress", "evidence": "", "attempts": 1},
    ],
}


def check_plan(plan):
    violations, warnings = [], []
    tasks = plan.get("tasks", [])
    if not tasks:
        violations.append({"rule": "G1", "task": "-", "problem": "plan has no tasks"})
    for t in tasks:
        tid = t.get("id", "?")
        if not str(t.get("owner", "")).strip():
            violations.append({"rule": "G1", "task": tid,
                               "problem": "no named human owner (Linear rule: agents are contributors, never owners)"})
        if t.get("executor") == "agent" and not str(t.get("reviewer", "")).strip():
            violations.append({"rule": "G2", "task": tid,
                               "problem": "agent-executed task has no named human reviewer"})
        acc = t.get("acceptance") or {}
        cmd = str(acc.get("cmd", "")).strip()
        criterion = str(acc.get("criterion", "")).strip()
        if not cmd and not (criterion and re.search(r"\d", criterion)):
            violations.append({"rule": "G3", "task": tid,
                               "problem": "acceptance is not machine-checkable "
                                          "(need a cmd, or a criterion with a measurable threshold)"})
        status = t.get("status", "todo")
        if status == "done" and not str(t.get("evidence", "")).strip():
            violations.append({"rule": "G4", "task": tid,
                               "problem": "done without evidence — never record a verify pass you did not observe"})
        if status == "waived" and not str(t.get("waive_reason", "")).strip():
            violations.append({"rule": "G4", "task": tid,
                               "problem": "waived without a waive_reason (waivers are human decisions with rationale)"})
        max_attempts = plan.get("budgets", {}).get("max_attempts_per_task")
        if max_attempts and t.get("attempts", 0) >= max_attempts and status not in ("done", "waived", "blocked"):
            warnings.append({"rule": "G6", "task": tid,
                             "note": f"attempts exhausted ({t.get('attempts')}/{max_attempts}) — escalate, do not retry"})
    return violations, warnings


def check_close(plan):
    refusals = []
    for t in plan.get("tasks", []):
        if t.get("status") not in ("done", "waived"):
            refusals.append({"rule": "G5", "task": t.get("id", "?"),
                             "problem": f"status is '{t.get('status', 'todo')}' — close refused while tasks are unverified and unwaived"})
    budgets = plan.get("budgets", {})
    max_iter = budgets.get("max_loop_iterations")
    if max_iter and plan.get("iteration", 0) > max_iter and refusals:
        refusals.append({"rule": "G6", "task": "-",
                         "problem": f"iteration {plan['iteration']} > cap {max_iter} with open tasks — "
                                    "this is an ESCALATION, never a success report"})
    return refusals


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Accountability gate for agent-executed PM delivery loops.")
    ap.add_argument("--plan", help="Path to the loop plan JSON ('-' for stdin).")
    ap.add_argument("--mode", choices=["plan", "close"], default="plan")
    ap.add_argument("--output", choices=["json", "human"], default="json")
    ap.add_argument("--sample", action="store_true",
                    help="Print a valid sample plan and exit 0.")
    args = ap.parse_args()

    if args.sample:
        print(json.dumps(SAMPLE_PLAN, indent=2))
        return 0
    if not args.plan:
        ap.error("--plan is required (or use --sample to see the expected shape)")
    try:
        plan = json.load(sys.stdin if args.plan == "-" else open(args.plan, encoding="utf-8"))
    except (OSError, ValueError) as exc:
        print(f"ERROR: cannot read plan: {exc}", file=sys.stderr)
        return 3

    violations, warnings = check_plan(plan)
    result = {"mode": args.mode, "goal": plan.get("goal", ""),
              "violations": violations, "warnings": warnings}
    exit_code = 0
    if args.mode == "close":
        refusals = check_close(plan)
        result["close_refusals"] = refusals
        result["verdict"] = "CLOSE-REFUSED" if (refusals or violations) else "CLOSE-OK"
        exit_code = 4 if (refusals or violations) else 0
    else:
        result["verdict"] = "PLAN-BLOCKED" if violations else "PLAN-OK"
        exit_code = 2 if violations else 0

    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(f"Verdict: {result['verdict']}")
        for v in violations + result.get("close_refusals", []):
            print(f"  [{v['rule']}] {v['task']}: {v['problem']}")
        for w in warnings:
            print(f"  (warn {w['rule']}) {w['task']}: {w['note']}")
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
