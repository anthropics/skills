"""Agent lifecycle: request, approve, act, delegate, suspend, terminate.

This is the only module that mutates state, and every mutation writes an
audit record — including refusals. A denied request that leaves no trace is
how a system loses the ability to answer "who tried what, and when".
"""

from __future__ import annotations

from dataclasses import replace
from typing import Iterable, List, Optional, Sequence, Tuple

from . import permissions
from .audit import verify_chain
from .errors import (
    ChairmanError,
    IncompleteRequest,
    NotFound,
    PermissionDenied,
    StateError,
)
from .models import (
    Agent,
    AgentRequest,
    AgentStatus,
    AuditEntry,
    Classification,
    Decision,
    Escalation,
    Level,
    RequestStatus,
    Task,
    TaskStatus,
    Tool,
    new_id,
    utcnow,
)
from .store import Store

CHAIRMAN_NAME = "chairman"

# An agent proposal must answer all of these before it can be filed. This is
# the enforced form of "provide full information about what you want and why".
REQUIRED_JUSTIFICATION = ("purpose", "reporting", "risks")


class Registry:
    """The governance surface. Construct with a :class:`Store`."""

    def __init__(self, store: Store) -> None:
        self.store = store

    # ------------------------------------------------------------ bootstrap

    def install_chairman(
        self,
        name: str = CHAIRMAN_NAME,
        purpose: str = "Supreme authority over all agents",
    ) -> Agent:
        """Create the root agent. Idempotent; refuses to make a second one."""
        existing = self.store.get_agent_by_name(name)
        if existing is not None:
            return existing

        for agent in self.store.list_agents():
            if agent.level is Level.CHAIRMAN:
                raise StateError(
                    f"a Chairman already exists: {agent.name}; there is exactly one root"
                )

        chairman = Agent(
            agent_id=new_id("agent"),
            name=name,
            level=Level.CHAIRMAN,
            tools=frozenset(Tool),
            max_classification=Classification.RESTRICTED,
            purpose=purpose,
            parent_id=None,
            status=AgentStatus.ACTIVE,
        )
        self.store.put_agent(chairman)
        self.store.append_audit(
            actor=name,
            action="install_chairman",
            resource=chairman.agent_id,
            outcome="allowed",
            details={"level": int(Level.CHAIRMAN), "tools": len(Tool)},
        )
        return chairman

    # -------------------------------------------------------------- lookups

    def require_agent(self, ident: str) -> Agent:
        """Resolve by name or id, raising :class:`NotFound` if absent."""
        agent = self.store.get_agent_by_name(ident) or self.store.get_agent(ident)
        if agent is None:
            raise NotFound(f"no such agent: {ident}")
        return agent

    def list_agents(self, parent: Optional[str] = None) -> List[Agent]:
        parent_id = self.require_agent(parent).agent_id if parent else None
        return self.store.list_agents(parent_id)

    def org_chart(self, root: Optional[str] = None) -> List[Tuple[int, Agent]]:
        """Depth-first walk returning ``(depth, agent)`` pairs for display."""
        agents = self.store.list_agents()
        by_parent: dict[Optional[str], List[Agent]] = {}
        for agent in agents:
            by_parent.setdefault(agent.parent_id, []).append(agent)

        if root is not None:
            start = [self.require_agent(root)]
        else:
            start = by_parent.get(None, [])

        out: List[Tuple[int, Agent]] = []

        def walk(node: Agent, depth: int) -> None:
            out.append((depth, node))
            for child in by_parent.get(node.agent_id, []):
                walk(child, depth + 1)

        for node in start:
            walk(node, 0)
        return out

    # ------------------------------------------------------- agent creation

    def request_agent(
        self,
        requested_by: str,
        name: str,
        level: Level,
        tools: Iterable[Tool],
        max_classification: Classification,
        purpose: str,
        objectives: Sequence[str],
        reporting: str,
        risks: str,
        budget_usd: float = 0.0,
    ) -> AgentRequest:
        """File a proposal. Validates completeness and the parent's authority.

        Nothing is created here — the proposal sits in PENDING until an
        agent with approval authority signs it off.
        """
        parent = self.require_agent(requested_by)

        missing = [
            field
            for field, value in (
                ("purpose", purpose),
                ("reporting", reporting),
                ("risks", risks),
            )
            if not (value or "").strip()
        ]
        if not objectives or not any((o or "").strip() for o in objectives):
            missing.append("objectives")
        if not (name or "").strip():
            missing.append("name")

        if missing:
            self.store.append_audit(
                actor=parent.name,
                action="request_agent",
                resource=name or "<unnamed>",
                outcome="rejected",
                details={"missing": missing},
            )
            raise IncompleteRequest(
                "agent proposal is missing required justification: "
                + ", ".join(sorted(missing))
            )

        if self.store.get_agent_by_name(name) is not None:
            raise StateError(f"an agent named {name!r} already exists")

        tools = frozenset(tools)
        decision = permissions.can_create_subagent(
            parent=parent,
            child_level=level,
            child_tools=tools,
            child_classification=max_classification,
            current_report_count=self.store.count_active_reports(parent.agent_id),
        )
        if not decision.allowed:
            self.store.append_audit(
                actor=parent.name,
                action="request_agent",
                resource=name,
                outcome="denied",
                details={"reason": decision.reason},
            )
            raise PermissionDenied(decision.reason)

        request = AgentRequest(
            request_id=new_id("req"),
            requested_by=parent.agent_id,
            name=name,
            level=level,
            tools=tools,
            max_classification=max_classification,
            purpose=purpose,
            objectives=list(objectives),
            reporting=reporting,
            risks=risks,
            budget_usd=budget_usd,
        )
        self.store.put_request(request)
        self.store.append_audit(
            actor=parent.name,
            action="request_agent",
            resource=request.request_id,
            outcome="pending",
            details={
                "name": name,
                "level": int(level),
                "tools": sorted(t.value for t in tools),
                "classification": max_classification.name,
                "budget_usd": budget_usd,
            },
        )
        return request

    def approve_request(self, request_id: str, approver: str, reason: str = "") -> Agent:
        """Approve a pending proposal and bring the agent into existence."""
        request = self.store.get_request(request_id)
        if request is None:
            raise NotFound(f"no such request: {request_id}")
        if request.status is not RequestStatus.PENDING:
            raise StateError(f"request is already {request.status.value}")

        approver_agent = self.require_agent(approver)
        decision = permissions.can_approve(approver_agent, request.level)
        if not decision.allowed:
            self.store.append_audit(
                actor=approver_agent.name,
                action="approve_request",
                resource=request_id,
                outcome="denied",
                details={"reason": decision.reason},
            )
            raise PermissionDenied(decision.reason)

        parent = self.store.get_agent(request.requested_by)
        if parent is None:
            raise NotFound(f"requesting agent {request.requested_by} no longer exists")

        # Re-check at approval time: the parent may have been suspended, or
        # filled its report slots, since the proposal was filed.
        recheck = permissions.can_create_subagent(
            parent=parent,
            child_level=request.level,
            child_tools=request.tools,
            child_classification=request.max_classification,
            current_report_count=self.store.count_active_reports(parent.agent_id),
        )
        if not recheck.allowed:
            self.store.append_audit(
                actor=approver_agent.name,
                action="approve_request",
                resource=request_id,
                outcome="denied",
                details={"reason": f"revalidation failed: {recheck.reason}"},
            )
            raise PermissionDenied(f"conditions changed since filing: {recheck.reason}")

        agent = Agent(
            agent_id=new_id("agent"),
            name=request.name,
            level=request.level,
            tools=request.tools,
            max_classification=request.max_classification,
            purpose=request.purpose,
            parent_id=parent.agent_id,
            status=AgentStatus.ACTIVE,
        )
        self.store.put_agent(agent)
        self.store.put_request(
            replace(
                request,
                status=RequestStatus.APPROVED,
                decided_by=approver_agent.agent_id,
                decided_at=utcnow(),
                decision_reason=reason or decision.reason,
            )
        )
        self.store.append_audit(
            actor=approver_agent.name,
            action="approve_request",
            resource=agent.agent_id,
            outcome="allowed",
            details={"request_id": request_id, "name": agent.name, "parent": parent.name},
        )
        return agent

    def reject_request(self, request_id: str, approver: str, reason: str) -> AgentRequest:
        if not (reason or "").strip():
            raise IncompleteRequest("a rejection must state a reason")

        request = self.store.get_request(request_id)
        if request is None:
            raise NotFound(f"no such request: {request_id}")
        if request.status is not RequestStatus.PENDING:
            raise StateError(f"request is already {request.status.value}")

        approver_agent = self.require_agent(approver)
        rejected = replace(
            request,
            status=RequestStatus.REJECTED,
            decided_by=approver_agent.agent_id,
            decided_at=utcnow(),
            decision_reason=reason,
        )
        self.store.put_request(rejected)
        self.store.append_audit(
            actor=approver_agent.name,
            action="reject_request",
            resource=request_id,
            outcome="rejected",
            details={"reason": reason},
        )
        return rejected

    # --------------------------------------------------------------- acting

    def authorize(
        self,
        agent_name: str,
        tool: Tool,
        classification: Classification,
        write: bool = False,
        resource: str = "-",
    ) -> Decision:
        """Check an action and record the outcome either way."""
        agent = self.require_agent(agent_name)
        decision = permissions.authorize_action(agent, tool, classification, write)
        self.store.append_audit(
            actor=agent.name,
            action=f"{'write' if write else 'read'}:{tool.value}",
            resource=resource,
            outcome="allowed" if decision.allowed else "denied",
            details={
                "classification": classification.name,
                "reason": decision.reason,
            },
        )
        return decision

    # ------------------------------------------------------------ lifecycle

    def suspend(self, agent_name: str, by: str, reason: str) -> Agent:
        """Suspend an agent. Its reports keep their slots but it cannot act."""
        if not (reason or "").strip():
            raise IncompleteRequest("a suspension must state a reason")
        actor = self.require_agent(by)
        agent = self.require_agent(agent_name)

        if agent.is_chairman:
            raise PermissionDenied("the Chairman cannot be suspended")
        if actor.level <= agent.level and not actor.is_chairman:
            raise PermissionDenied(
                f"{actor.name} (level {int(actor.level)}) cannot suspend "
                f"{agent.name} (level {int(agent.level)})"
            )

        updated = replace(agent, status=AgentStatus.SUSPENDED)
        self.store.put_agent(updated)
        self.store.append_audit(
            actor=actor.name,
            action="suspend",
            resource=agent.agent_id,
            outcome="allowed",
            details={"agent": agent.name, "reason": reason},
        )
        return updated

    def reinstate(self, agent_name: str, by: str, reason: str) -> Agent:
        actor = self.require_agent(by)
        agent = self.require_agent(agent_name)
        if agent.status is AgentStatus.TERMINATED:
            raise StateError("a terminated agent cannot be reinstated")

        updated = replace(agent, status=AgentStatus.ACTIVE)
        self.store.put_agent(updated)
        self.store.append_audit(
            actor=actor.name,
            action="reinstate",
            resource=agent.agent_id,
            outcome="allowed",
            details={"agent": agent.name, "reason": reason},
        )
        return updated

    def terminate(self, agent_name: str, by: str, reason: str) -> List[Agent]:
        """Terminate an agent and everything beneath it.

        Termination cascades because an orphaned sub-agent would keep the
        authority its parent granted while nobody remains accountable for it.
        """
        if not (reason or "").strip():
            raise IncompleteRequest("a termination must state a reason")
        actor = self.require_agent(by)
        agent = self.require_agent(agent_name)

        if agent.is_chairman:
            raise PermissionDenied("the Chairman cannot be terminated")
        if actor.level <= agent.level and not actor.is_chairman:
            raise PermissionDenied(
                f"{actor.name} (level {int(actor.level)}) cannot terminate "
                f"{agent.name} (level {int(agent.level)})"
            )

        doomed = [node for _, node in self.org_chart(root=agent.name)]
        stamp = utcnow()
        out: List[Agent] = []
        for node in doomed:
            if node.status is AgentStatus.TERMINATED:
                continue
            updated = replace(
                node,
                status=AgentStatus.TERMINATED,
                terminated_at=stamp,
                termination_reason=reason,
            )
            self.store.put_agent(updated)
            out.append(updated)

        self.store.append_audit(
            actor=actor.name,
            action="terminate",
            resource=agent.agent_id,
            outcome="allowed",
            details={
                "agent": agent.name,
                "reason": reason,
                "cascaded": [a.name for a in out if a.agent_id != agent.agent_id],
            },
        )
        return out

    # ----------------------------------------------------------------- work

    def assign_task(
        self,
        title: str,
        assigned_by: str,
        assigned_to: str,
        tool: Tool,
        classification: Classification,
        note: str = "",
    ) -> Task:
        """Delegate work, but only work the assignee is cleared to perform."""
        assigner = self.require_agent(assigned_by)
        assignee = self.require_agent(assigned_to)

        if assigner.status is not AgentStatus.ACTIVE:
            raise PermissionDenied(f"{assigner.name} is {assigner.status.value}")

        decision = permissions.authorize_action(assignee, tool, classification)
        if not decision.allowed:
            self.store.append_audit(
                actor=assigner.name,
                action="assign_task",
                resource=assignee.agent_id,
                outcome="denied",
                details={"title": title, "reason": decision.reason},
            )
            raise PermissionDenied(
                f"cannot assign to {assignee.name}: {decision.reason}"
            )

        task = Task(
            task_id=new_id("task"),
            title=title,
            assigned_to=assignee.agent_id,
            assigned_by=assigner.agent_id,
            tool=tool,
            classification=classification,
            note=note,
        )
        self.store.put_task(task)
        self.store.append_audit(
            actor=assigner.name,
            action="assign_task",
            resource=task.task_id,
            outcome="allowed",
            details={"title": title, "to": assignee.name, "tool": tool.value},
        )
        return task

    def update_task(
        self,
        task_id: str,
        by: str,
        status: Optional[TaskStatus] = None,
        escalation: Optional[Escalation] = None,
        note: str = "",
    ) -> Task:
        task = self.store.get_task(task_id)
        if task is None:
            raise NotFound(f"no such task: {task_id}")
        actor = self.require_agent(by)

        updated = replace(
            task,
            status=status or task.status,
            escalation=escalation or task.escalation,
            note=note or task.note,
            updated_at=utcnow(),
        )
        self.store.put_task(updated)
        self.store.append_audit(
            actor=actor.name,
            action="update_task",
            resource=task_id,
            outcome="allowed",
            details={
                "status": updated.status.value,
                "escalation": int(updated.escalation),
                "note": note,
            },
        )
        return updated

    def open_escalations(
        self, minimum: Escalation = Escalation.URGENT
    ) -> List[Task]:
        """Tasks at or above ``minimum`` that are not yet resolved."""
        closed = {TaskStatus.DONE, TaskStatus.FAILED}
        return [
            t
            for t in self.store.list_tasks()
            if t.escalation >= minimum and t.status not in closed
        ]

    # ---------------------------------------------------------------- audit

    def record(
        self,
        actor: str,
        action: str,
        resource: str,
        outcome: str,
        details: Optional[dict] = None,
    ) -> AuditEntry:
        """Append an entry for work performed outside the registry itself.

        Used by :mod:`chairman.enforcement` to log execution outcomes, which
        are a separate fact from the permission decision that preceded them:
        a call can be permitted and still fail.
        """
        return self.store.append_audit(actor, action, resource, outcome, details or {})

    def audit_log(self, limit: Optional[int] = None) -> List[AuditEntry]:
        return self.store.list_audit(limit)

    def verify_audit(self) -> Tuple[bool, List[str]]:
        """Recompute the whole hash chain. Returns ``(ok, problems)``."""
        return verify_chain(self.store.list_audit())


__all__ = ["Registry", "ChairmanError", "CHAIRMAN_NAME"]
