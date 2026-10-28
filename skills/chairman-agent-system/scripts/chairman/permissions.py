"""The permission rules. Pure functions over :mod:`chairman.models`.

The single invariant this module exists to protect: **authority can only
narrow as you move down the tree**. An agent can never hand a child a level,
a tool, or a clearance it does not itself hold. Without that, delegation
becomes a privilege-escalation path — an agent could mint a more powerful
child and act through it.
"""

from __future__ import annotations

from typing import FrozenSet, Iterable

from .models import (
    Agent,
    AgentStatus,
    Classification,
    Decision,
    Level,
    Tool,
)

# Ceiling on the data an agent may touch, independent of what its charter
# nominally granted. The stricter of (level cap, charter grant) always wins.
LEVEL_CLASSIFICATION_CAP: dict[Level, Classification] = {
    Level.READ_ONLY: Classification.PUBLIC,
    Level.INTERNAL: Classification.INTERNAL,
    Level.OPERATOR: Classification.CONFIDENTIAL,
    Level.CROSS_AGENT: Classification.CONFIDENTIAL,
    Level.EXECUTIVE: Classification.RESTRICTED,
    Level.CHAIRMAN: Classification.RESTRICTED,
}

# How many direct reports each level may hold. Level 1 cannot delegate at all.
MAX_DIRECT_REPORTS: dict[Level, int] = {
    Level.READ_ONLY: 0,
    Level.INTERNAL: 5,
    Level.OPERATOR: 10,
    Level.CROSS_AGENT: 25,
    Level.EXECUTIVE: 100,
    Level.CHAIRMAN: 1000,
}

# Writing requires level 3+; levels 1-2 are read postures by definition.
MIN_WRITE_LEVEL = Level.OPERATOR


def effective_classification(agent: Agent) -> Classification:
    """The strictest of the agent's charter grant and its level cap."""
    return min(agent.max_classification, LEVEL_CLASSIFICATION_CAP[agent.level])


def authorize_action(
    agent: Agent,
    tool: Tool,
    classification: Classification,
    write: bool = False,
) -> Decision:
    """Decide whether ``agent`` may use ``tool`` against data of the given
    sensitivity. Every branch returns a reason suitable for the audit log.
    """
    if agent.status is not AgentStatus.ACTIVE:
        return Decision(False, f"agent status is {agent.status.value}, not active")

    if tool not in agent.tools:
        return Decision(False, f"tool {tool.value} not granted to {agent.name}")

    cap = effective_classification(agent)
    if classification > cap:
        return Decision(
            False,
            f"{classification.name} exceeds clearance {cap.name} for {agent.name}",
        )

    if write and agent.level < MIN_WRITE_LEVEL:
        return Decision(
            False,
            f"write requires level {MIN_WRITE_LEVEL} ({MIN_WRITE_LEVEL.name}), "
            f"{agent.name} is level {int(agent.level)}",
        )

    verb = "write" if write else "read"
    return Decision(
        True, f"{agent.name} may {verb} {classification.name} via {tool.value}"
    )


def can_create_subagent(
    parent: Agent,
    child_level: Level,
    child_tools: Iterable[Tool],
    child_classification: Classification,
    current_report_count: int,
) -> Decision:
    """Decide whether ``parent`` may create the proposed child.

    Enforces, in order: parent is active, parent's level permits delegation,
    the child is strictly weaker, tools are a subset, clearance does not
    exceed the parent's effective clearance, and the span-of-control limit
    is not already met.
    """
    if parent.status is not AgentStatus.ACTIVE:
        return Decision(False, f"parent status is {parent.status.value}, not active")

    limit = MAX_DIRECT_REPORTS[parent.level]
    if limit == 0:
        return Decision(
            False, f"level {int(parent.level)} agents may not create sub-agents"
        )

    if child_level >= parent.level:
        return Decision(
            False,
            f"child level {int(child_level)} must be below parent level "
            f"{int(parent.level)}",
        )

    requested: FrozenSet[Tool] = frozenset(child_tools)
    if not requested:
        return Decision(False, "child must be granted at least one tool")

    ungranted = requested - parent.tools
    if ungranted:
        names = ", ".join(sorted(t.value for t in ungranted))
        return Decision(False, f"parent cannot grant tools it lacks: {names}")

    parent_cap = effective_classification(parent)
    if child_classification > parent_cap:
        return Decision(
            False,
            f"child clearance {child_classification.name} exceeds parent "
            f"clearance {parent_cap.name}",
        )

    if current_report_count >= limit:
        return Decision(
            False,
            f"{parent.name} already holds {current_report_count} of "
            f"{limit} permitted direct reports",
        )

    return Decision(
        True,
        f"{parent.name} may create a level {int(child_level)} agent "
        f"({current_report_count + 1}/{limit} reports)",
    )


def can_approve(approver: Agent, requested_level: Level) -> Decision:
    """Approval authority is separate from creation authority.

    Creating a level 3+ agent is a structural change, so it needs an
    executive or the Chairman signing off even when the requesting parent
    is technically permitted to hold that report.
    """
    if approver.status is not AgentStatus.ACTIVE:
        return Decision(False, f"approver status is {approver.status.value}")

    if approver.is_chairman:
        return Decision(True, "Chairman holds unconditional approval authority")

    if requested_level >= Level.OPERATOR and approver.level < Level.EXECUTIVE:
        return Decision(
            False,
            f"level {int(requested_level)} agents require an executive "
            f"(level {int(Level.EXECUTIVE)}) or Chairman approver",
        )

    if approver.level <= requested_level:
        return Decision(
            False,
            f"approver level {int(approver.level)} must exceed requested "
            f"level {int(requested_level)}",
        )

    return Decision(True, f"{approver.name} may approve level {int(requested_level)}")
