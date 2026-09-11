"""Command-line interface.

    python3 -m chairman --db org.db init
    python3 -m chairman --db org.db request --by chairman --name analyst ...
    python3 -m chairman --db org.db approve <request-id> --by chairman
    python3 -m chairman --db org.db chart
    python3 -m chairman --db org.db verify
"""

from __future__ import annotations

import argparse
import sys
from typing import List, Optional

from .errors import ChairmanError
from .models import (
    Classification,
    Escalation,
    Level,
    RequestStatus,
    TaskStatus,
    Tool,
)
from .registry import Registry
from .store import Store


def _fmt_tools(tools) -> str:
    return ",".join(sorted(t.value for t in tools)) or "-"


def cmd_init(registry: Registry, args) -> int:
    chairman = registry.install_chairman(name=args.name)
    print(f"Chairman ready: {chairman.name} ({chairman.agent_id})")
    print(f"  level          {int(chairman.level)} ({chairman.level.name})")
    print(f"  tools          {len(chairman.tools)} categories")
    print(f"  clearance      {chairman.max_classification.name}")
    return 0


def cmd_request(registry: Registry, args) -> int:
    request = registry.request_agent(
        requested_by=args.by,
        name=args.name,
        level=Level[args.level.upper()],
        tools=[Tool(t.strip()) for t in args.tools.split(",") if t.strip()],
        max_classification=Classification[args.classification.upper()],
        purpose=args.purpose,
        objectives=args.objective,
        reporting=args.reporting,
        risks=args.risks,
        budget_usd=args.budget,
    )
    print(f"Filed {request.request_id} — status {request.status.value}")
    print(f"  awaiting approval; no agent exists yet")
    return 0


def cmd_approve(registry: Registry, args) -> int:
    agent = registry.approve_request(args.request_id, approver=args.by, reason=args.reason)
    print(f"Approved. Created {agent.name} ({agent.agent_id})")
    print(f"  level {int(agent.level)}  tools {_fmt_tools(agent.tools)}")
    return 0


def cmd_reject(registry: Registry, args) -> int:
    request = registry.reject_request(args.request_id, approver=args.by, reason=args.reason)
    print(f"Rejected {request.request_id}: {request.decision_reason}")
    return 0


def cmd_requests(registry: Registry, args) -> int:
    status = RequestStatus[args.status.upper()] if args.status else None
    rows = registry.store.list_requests(status)
    if not rows:
        print("(none)")
        return 0
    for r in rows:
        print(f"{r.request_id}  {r.status.value:9}  {r.name:20} L{int(r.level)}  {_fmt_tools(r.tools)}")
    return 0


def cmd_chart(registry: Registry, args) -> int:
    rows = registry.org_chart(root=args.root)
    if not rows:
        print("(no agents)")
        return 0
    for depth, agent in rows:
        marker = "" if agent.status.value == "active" else f" [{agent.status.value}]"
        indent = "  " * depth
        print(f"{indent}{agent.name}{marker}")
        print(f"{indent}  L{int(agent.level)} {agent.max_classification.name} {_fmt_tools(agent.tools)}")
    return 0


def cmd_check(registry: Registry, args) -> int:
    decision = registry.authorize(
        args.agent,
        Tool(args.tool),
        Classification[args.classification.upper()],
        write=args.write,
        resource=args.resource,
    )
    print(f"{'ALLOW' if decision.allowed else 'DENY '}  {decision.reason}")
    return 0 if decision.allowed else 1


def cmd_assign(registry: Registry, args) -> int:
    task = registry.assign_task(
        title=args.title,
        assigned_by=args.by,
        assigned_to=args.to,
        tool=Tool(args.tool),
        classification=Classification[args.classification.upper()],
        note=args.note,
    )
    print(f"Assigned {task.task_id} to {args.to}")
    return 0


def cmd_task(registry: Registry, args) -> int:
    task = registry.update_task(
        args.task_id,
        by=args.by,
        status=TaskStatus[args.status.upper()] if args.status else None,
        escalation=Escalation[args.escalation.upper()] if args.escalation else None,
        note=args.note,
    )
    print(f"{task.task_id}  {task.status.value}  E{int(task.escalation)} "
          f"({task.escalation.name})")
    if task.note:
        print(f"  {task.note}")
    return 0


def cmd_tasks(registry: Registry, args) -> int:
    rows = registry.store.list_tasks()
    if not rows:
        print("(none)")
        return 0
    for t in rows:
        assignee = registry.store.get_agent(t.assigned_to)
        name = assignee.name if assignee else t.assigned_to
        print(f"{t.task_id}  {t.status.value:12} E{int(t.escalation)}  {name:20} {t.title}")
    return 0


def cmd_escalations(registry: Registry, args) -> int:
    rows = registry.open_escalations(Escalation[args.minimum.upper()])
    if not rows:
        print("(no open escalations)")
        return 0
    for t in rows:
        assignee = registry.store.get_agent(t.assigned_to)
        name = assignee.name if assignee else t.assigned_to
        print(f"E{int(t.escalation)} {t.escalation.name:14} {name:20} {t.title}")
        if t.note:
            print(f"     {t.note}")
    return 1


def cmd_suspend(registry: Registry, args) -> int:
    agent = registry.suspend(args.agent, by=args.by, reason=args.reason)
    print(f"Suspended {agent.name}: {args.reason}")
    return 0


def cmd_terminate(registry: Registry, args) -> int:
    killed = registry.terminate(args.agent, by=args.by, reason=args.reason)
    print(f"Terminated {len(killed)} agent(s): {', '.join(a.name for a in killed)}")
    return 0


def cmd_log(registry: Registry, args) -> int:
    for e in registry.audit_log(limit=args.limit):
        print(f"{e.seq:5}  {e.timestamp}  {e.actor:16} {e.action:20} {e.outcome:9} {e.resource}")
    return 0


def cmd_verify(registry: Registry, args) -> int:
    ok, problems = registry.verify_audit()
    count = len(registry.audit_log())
    if ok:
        print(f"Audit chain intact across {count} entries.")
        return 0
    print(f"AUDIT CHAIN COMPROMISED — {len(problems)} problem(s) across {count} entries:")
    for p in problems:
        print(f"  {p}")
    return 1


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="chairman", description=__doc__)
    parser.add_argument("--db", default="chairman.db", help="SQLite path (default: chairman.db)")
    sub = parser.add_subparsers(dest="command", required=True)

    p = sub.add_parser("init", help="create the root Chairman agent")
    p.add_argument("--name", default="chairman")
    p.set_defaults(func=cmd_init)

    p = sub.add_parser("request", help="file an agent creation proposal")
    p.add_argument("--by", required=True, help="requesting agent")
    p.add_argument("--name", required=True)
    p.add_argument("--level", required=True,
                   choices=[l.name.lower() for l in Level])
    p.add_argument("--tools", required=True, help="comma-separated tool categories")
    p.add_argument("--classification", required=True,
                   choices=[c.name.lower() for c in Classification])
    p.add_argument("--purpose", required=True)
    p.add_argument("--objective", action="append", default=[],
                   help="repeatable; at least one required")
    p.add_argument("--reporting", required=True)
    p.add_argument("--risks", required=True)
    p.add_argument("--budget", type=float, default=0.0)
    p.set_defaults(func=cmd_request)

    p = sub.add_parser("approve", help="approve a pending proposal")
    p.add_argument("request_id")
    p.add_argument("--by", required=True)
    p.add_argument("--reason", default="")
    p.set_defaults(func=cmd_approve)

    p = sub.add_parser("reject", help="reject a pending proposal")
    p.add_argument("request_id")
    p.add_argument("--by", required=True)
    p.add_argument("--reason", required=True)
    p.set_defaults(func=cmd_reject)

    p = sub.add_parser("requests", help="list proposals")
    p.add_argument("--status", choices=[s.name.lower() for s in RequestStatus])
    p.set_defaults(func=cmd_requests)

    p = sub.add_parser("chart", help="print the org chart")
    p.add_argument("--root")
    p.set_defaults(func=cmd_chart)

    p = sub.add_parser("check", help="test whether an agent may act")
    p.add_argument("agent")
    p.add_argument("--tool", required=True, choices=[t.value for t in Tool])
    p.add_argument("--classification", required=True,
                   choices=[c.name.lower() for c in Classification])
    p.add_argument("--write", action="store_true")
    p.add_argument("--resource", default="-")
    p.set_defaults(func=cmd_check)

    p = sub.add_parser("assign", help="delegate a task")
    p.add_argument("title")
    p.add_argument("--by", required=True)
    p.add_argument("--to", required=True)
    p.add_argument("--tool", required=True, choices=[t.value for t in Tool])
    p.add_argument("--classification", required=True,
                   choices=[c.name.lower() for c in Classification])
    p.add_argument("--note", default="")
    p.set_defaults(func=cmd_assign)

    p = sub.add_parser("task", help="update a task's status, escalation, or note")
    p.add_argument("task_id")
    p.add_argument("--by", required=True)
    p.add_argument("--status", choices=[s.name.lower() for s in TaskStatus])
    p.add_argument("--escalation", choices=[e.name.lower() for e in Escalation])
    p.add_argument("--note", default="")
    p.set_defaults(func=cmd_task)

    p = sub.add_parser("tasks", help="list tasks")
    p.set_defaults(func=cmd_tasks)

    p = sub.add_parser("escalations", help="list open escalations")
    p.add_argument("--minimum", default="urgent",
                   choices=[e.name.lower() for e in Escalation])
    p.set_defaults(func=cmd_escalations)

    p = sub.add_parser("suspend", help="suspend an agent")
    p.add_argument("agent")
    p.add_argument("--by", required=True)
    p.add_argument("--reason", required=True)
    p.set_defaults(func=cmd_suspend)

    p = sub.add_parser("terminate", help="terminate an agent and its reports")
    p.add_argument("agent")
    p.add_argument("--by", required=True)
    p.add_argument("--reason", required=True)
    p.set_defaults(func=cmd_terminate)

    p = sub.add_parser("log", help="print the audit log")
    p.add_argument("--limit", type=int)
    p.set_defaults(func=cmd_log)

    p = sub.add_parser("verify", help="verify audit chain integrity")
    p.set_defaults(func=cmd_verify)

    return parser


def main(argv: Optional[List[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        with Store(args.db) as store:
            return args.func(Registry(store), args)
    except ChairmanError as exc:
        print(f"REFUSED: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
