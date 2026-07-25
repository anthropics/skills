#!/usr/bin/env python3
"""JSON-backed loop state machine: the harness's execute→verify→close enforcer.

Takes the plan from goal_compiler.py and drives a bounded loop. The agent asks
`next` for a directive, does the work, then `record`s the outcome with an exit
code. The controller enforces the discipline the agent must not be trusted to
enforce on itself:

  * a task is only VERIFIED by recording a passing verify phase — never by
    recording execution success alone (no verification theater);
  * failed attempts increment a counter; at max_attempts the task ESCALATES
    to a human instead of retrying forever;
  * a global iteration cap bounds the whole loop;
  * `close` refuses (exit 4) while any task is unverified and unwaived.

Task states: pending → in_progress → verifying → verified
                    ↘ (failure at cap) escalated        ↘ waived (close-time, with reason)

Exit codes: 0 ok · 2 escalation required · 4 close refused · 5 iteration cap ·
6 invalid transition/state.

Usage:
  python3 loop_controller.py init --plan plan.json --state state.json
  python3 loop_controller.py next --state state.json
  python3 loop_controller.py record --state state.json --task T1 --phase execute --exit-code 0
  python3 loop_controller.py record --state state.json --task T1 --phase verify --exit-code 0 --evidence "error_budget_calculator exit 0; 43.2min budget"
  python3 loop_controller.py close --state state.json
  python3 loop_controller.py --sample   # in-memory demo of a full loop
"""

import argparse
import datetime
import json
import os
import subprocess
import sys
import tempfile

STATE_SCHEMA = "agent-harness/state.v1"
CHECK_TIMEOUT_S = 120


def now():
    return datetime.datetime.now(datetime.timezone.utc).strftime(
        "%Y-%m-%dT%H:%M:%SZ")


def load(path):
    with open(path, encoding="utf-8") as f:
        return json.load(f)


def save(state, path):
    """Atomic write (temp file + os.replace) so a crashed run never leaves a
    half-written state file."""
    d = os.path.dirname(os.path.abspath(path)) or "."
    fd, tmp = tempfile.mkstemp(dir=d, prefix=".harness-state-")
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            json.dump(state, f, indent=2)
            f.write("\n")
        os.replace(tmp, path)
    except BaseException:
        if os.path.exists(tmp):
            os.unlink(tmp)
        raise


def emit(obj, code=0):
    print(json.dumps(obj, indent=2))
    return code


def cmd_init(args):
    plan = load(args.plan)
    state = {
        "schema": STATE_SCHEMA,
        "goal": plan.get("goal"),
        "domain": plan.get("domain"),
        "plan_file": args.plan,
        "created_at": now(),
        "iteration": 0,
        "max_loop_iterations": plan.get("loop", {}).get("max_loop_iterations", 12),
        "status": "open",
        "tasks": [{
            "id": t["id"],
            "skill": t.get("skill"),
            "objective": t.get("objective"),
            "verification": t.get("verification", []),
            "max_attempts": t.get("max_attempts", 3),
            "attempts": 0,
            "status": "pending",
            "evidence": [],
        } for t in plan.get("tasks", [])],
    }
    if not state["tasks"]:
        return emit({"error": "plan has no tasks"}, 6)
    save(state, args.state)
    return emit({"initialized": args.state, "tasks": len(state["tasks"]),
                 "max_loop_iterations": state["max_loop_iterations"]})


def directive(state):
    if state["status"] == "closed":
        return {"action": "done", "detail": "loop already closed"}, 0
    if state["iteration"] >= state["max_loop_iterations"]:
        return {"action": "escalate",
                "detail": "global iteration cap (%d) reached — hand the loop "
                          "to a human with the evidence log"
                          % state["max_loop_iterations"]}, 5
    for t in state["tasks"]:
        if t["status"] == "escalated":
            return {"action": "escalate", "task": t["id"],
                    "detail": "task %s exhausted %d attempts; a human must "
                              "review the evidence log before the loop may "
                              "continue" % (t["id"], t["max_attempts"])}, 2
    for t in state["tasks"]:
        if t["status"] in ("pending", "in_progress"):
            return {"action": "execute", "task": t["id"],
                    "objective": t["objective"],
                    "attempt": t["attempts"] + 1,
                    "max_attempts": t["max_attempts"],
                    "then": "record --phase execute --exit-code <code>"}, 0
        if t["status"] == "verifying":
            return {"action": "verify", "task": t["id"],
                    "checks": t["verification"],
                    "rule": "run every check; ALL must meet expect_exit; then "
                            "record --phase verify with the worst exit code "
                            "and an --evidence line naming what you observed"}, 0
    return {"action": "close",
            "detail": "all tasks verified — run `close` to emit the handoff"}, 0


def cmd_next(args):
    state = load(args.state)
    d, code = directive(state)
    return emit(d, code)


def cmd_record(args):
    state = load(args.state)
    if state["status"] == "closed":
        return emit({"error": "loop is closed; no further records accepted"}, 6)
    task = next((t for t in state["tasks"] if t["id"] == args.task), None)
    if task is None:
        return emit({"error": "unknown task %s" % args.task}, 6)
    if task["status"] in ("verified", "escalated"):
        return emit({"error": "task %s is %s; recording on it is invalid"
                     % (task["id"], task["status"])}, 6)

    state["iteration"] += 1
    entry = {"at": now(), "phase": args.phase, "exit_code": args.exit_code,
             "attempt": task["attempts"] + 1}
    if args.evidence:
        entry["evidence"] = args.evidence
    task["evidence"].append(entry)

    ok = args.exit_code == 0
    if args.phase == "execute":
        if ok:
            task["status"] = "verifying"
            result = {"task": task["id"], "status": "verifying",
                      "next": "run the verification checks, then record "
                              "--phase verify"}
            code = 0
        else:
            code, result = _fail(task)
    else:  # verify
        if task["status"] != "verifying":
            return emit({"error": "task %s is not awaiting verification "
                                  "(status=%s); execute must succeed first"
                         % (task["id"], task["status"])}, 6)
        if ok:
            if not args.evidence:
                return emit({"error": "a passing verify record requires "
                                      "--evidence naming what was observed "
                                      "(no verification theater)"}, 6)
            task["status"] = "verified"
            result = {"task": task["id"], "status": "verified"}
            code = 0
        else:
            code, result = _fail(task)

    save(state, args.state)
    d, dcode = directive(state)
    result["directive"] = d
    return emit(result, code if code != 0 else dcode)


def _fail(task):
    task["attempts"] += 1
    if task["attempts"] >= task["max_attempts"]:
        task["status"] = "escalated"
        return 2, {"task": task["id"], "status": "escalated",
                   "detail": "attempts exhausted (%d/%d) — escalate to a human"
                             % (task["attempts"], task["max_attempts"])}
    task["status"] = "pending"
    return 0, {"task": task["id"], "status": "pending",
               "detail": "attempt %d/%d failed — change the approach before "
                         "retrying (same command + same input = same failure)"
                         % (task["attempts"], task["max_attempts"])}


def cmd_verify(args):
    """Run the task's executable verification checks via subprocess — the
    controller adjudicates pass/fail itself instead of trusting a recorded
    exit code (reward-hacking guard)."""
    state = load(args.state)
    task = next((t for t in state["tasks"] if t["id"] == args.task), None)
    if task is None:
        return emit({"error": "unknown task %s" % args.task}, 6)
    if task["status"] != "verifying":
        return emit({"error": "task %s is not awaiting verification "
                              "(status=%s); execute must succeed first"
                     % (task["id"], task["status"])}, 6)

    runnable = [c for c in task["verification"]
                if c.get("kind") != "manual-evidence"]
    results = []
    worst = 0
    for chk in runnable:
        try:
            proc = subprocess.run(
                chk["cmd"], shell=True, cwd=args.cwd,
                capture_output=True, text=True, timeout=CHECK_TIMEOUT_S)
            rc = proc.returncode
            tail = (proc.stdout + proc.stderr).strip().splitlines()[-3:]
        except subprocess.TimeoutExpired:
            rc, tail = 124, ["TIMEOUT after %ss" % CHECK_TIMEOUT_S]
        passed = rc == chk.get("expect_exit", 0)
        results.append({"cmd": chk["cmd"], "exit": rc, "passed": passed,
                        "tail": tail})
        if not passed:
            worst = 1

    state["iteration"] += 1
    task["evidence"].append({"at": now(), "phase": "verify-run",
                             "checks": results, "attempt": task["attempts"] + 1})

    manual = [c for c in task["verification"]
              if c.get("kind") == "manual-evidence"]
    if worst == 0 and runnable and not manual:
        task["status"] = "verified"
        result = {"task": task["id"], "status": "verified",
                  "checks_run": len(results)}
        code = 0
    elif worst == 0 and manual:
        result = {"task": task["id"], "status": "verifying",
                  "checks_run": len(results),
                  "detail": "executable checks pass; a manual-evidence check "
                            "remains — record --phase verify --exit-code 0 "
                            "--evidence '<what you observed>' to finish"}
        code = 0
    elif not runnable:
        result = {"task": task["id"], "status": "verifying",
                  "detail": "no executable checks; record --phase verify "
                            "with --evidence instead"}
        code = 0
    else:
        code, result = _fail(task)
        result["failed_checks"] = [r for r in results if not r["passed"]]

    save(state, args.state)
    d, dcode = directive(state)
    result["directive"] = d
    return emit(result, code if code != 0 else dcode)


def cmd_close(args):
    state = load(args.state)
    waivers = dict(zip(args.waive or [], args.reason or []))
    if (args.waive or []) and len(args.waive) != len(args.reason or []):
        return emit({"error": "every --waive needs a matching --reason"}, 6)
    blocking = []
    for t in state["tasks"]:
        if t["status"] == "verified":
            continue
        if t["id"] in waivers:
            t["status"] = "waived"
            t["waive_reason"] = waivers[t["id"]]
            continue
        blocking.append({"task": t["id"], "status": t["status"]})
    if blocking:
        return emit({"verdict": "CLOSE-REFUSED",
                     "blocking": blocking,
                     "rule": "close requires every task verified, or waived "
                             "with --waive <id> --reason <why>"}, 4)
    state["status"] = "closed"
    state["closed_at"] = now()
    save(state, args.state)
    return emit({
        "verdict": "CLOSED",
        "goal": state["goal"],
        "iterations_used": state["iteration"],
        "handoff": {
            "tasks": [{"id": t["id"], "skill": t["skill"],
                       "status": t["status"],
                       "evidence": t["evidence"][-1] if t["evidence"] else None,
                       "waive_reason": t.get("waive_reason")}
                      for t in state["tasks"]],
        },
    })


def cmd_status(args):
    state = load(args.state)
    return emit({
        "goal": state["goal"], "status": state["status"],
        "iteration": "%d/%d" % (state["iteration"],
                                state["max_loop_iterations"]),
        "tasks": [{"id": t["id"], "status": t["status"],
                   "attempts": "%d/%d" % (t["attempts"], t["max_attempts"])}
                  for t in state["tasks"]],
    })


def run_sample():
    """In-memory demo: two tasks, one verify failure, retry, verified close."""
    import tempfile, os  # noqa: E401
    tmp = tempfile.mkdtemp(prefix="harness-demo-")
    plan_path = os.path.join(tmp, "plan.json")
    state_path = os.path.join(tmp, "state.json")
    plan = {
        "schema": "agent-harness/plan.v1",
        "goal": "demo: ship a verified change",
        "domain": "engineering",
        "tasks": [
            {"id": "T1", "skill": "demo-skill",
             "objective": "make the change",
             "verification": [{"cmd": "true", "expect_exit": 0,
                               "kind": "smoke"}], "max_attempts": 3},
        ],
        "loop": {"max_loop_iterations": 12},
    }
    with open(plan_path, "w") as f:
        json.dump(plan, f)
    steps = [
        ["init", "--plan", plan_path, "--state", state_path],
        ["next", "--state", state_path],
        ["record", "--state", state_path, "--task", "T1",
         "--phase", "execute", "--exit-code", "0"],
        ["record", "--state", state_path, "--task", "T1",
         "--phase", "verify", "--exit-code", "1",
         "--evidence", "check failed: unexpected output"],
        ["record", "--state", state_path, "--task", "T1",
         "--phase", "execute", "--exit-code", "0"],
        ["record", "--state", state_path, "--task", "T1",
         "--phase", "verify", "--exit-code", "0",
         "--evidence", "smoke check exit 0, output matches objective"],
        ["close", "--state", state_path],
    ]
    for s in steps:
        print("\n$ loop_controller.py " + " ".join(s))
        code = main(s)
        print("(exit %d)" % code)
    return 0


def build_parser():
    ap = argparse.ArgumentParser(
        description="Bounded execute→verify→close loop state machine for the "
                    "agent-harness skill.")
    ap.add_argument("--sample", action="store_true",
                    help="Run an in-memory demo loop and exit 0.")
    sub = ap.add_subparsers(dest="cmd")
    p = sub.add_parser("init", help="Create a state file from a plan.")
    p.add_argument("--plan", required=True)
    p.add_argument("--state", required=True)
    p = sub.add_parser("next", help="Emit the next directive.")
    p.add_argument("--state", required=True)
    p = sub.add_parser("record", help="Record an execute/verify outcome.")
    p.add_argument("--state", required=True)
    p.add_argument("--task", required=True)
    p.add_argument("--phase", required=True, choices=["execute", "verify"])
    p.add_argument("--exit-code", required=True, type=int)
    p.add_argument("--evidence", help="What was observed (required to pass verify).")
    p = sub.add_parser("verify", help="Run the task's executable checks via "
                                      "subprocess and adjudicate them.")
    p.add_argument("--state", required=True)
    p.add_argument("--task", required=True)
    p.add_argument("--cwd", default=".",
                   help="Working directory for check commands (repo root).")
    p = sub.add_parser("close", help="Close the loop (refuses if unverified).")
    p.add_argument("--state", required=True)
    p.add_argument("--waive", action="append",
                   help="Task id to waive (repeatable; requires --reason).")
    p.add_argument("--reason", action="append",
                   help="Reason for the matching --waive (repeatable).")
    p = sub.add_parser("status", help="Summarize loop state.")
    p.add_argument("--state", required=True)
    return ap


def main(argv=None):
    ap = build_parser()
    args = ap.parse_args(argv)
    if args.sample:
        return run_sample()
    if not args.cmd:
        ap.print_help()
        return 0
    return {"init": cmd_init, "next": cmd_next, "record": cmd_record,
            "verify": cmd_verify, "close": cmd_close,
            "status": cmd_status}[args.cmd](args)


if __name__ == "__main__":
    sys.exit(main())
