"""Core domain types for the Chairman agent governance system.

Everything here is a plain dataclass or enum with no I/O, so the rules that
matter can be reasoned about and tested in isolation from storage.
"""

from __future__ import annotations

import datetime as dt
import uuid
from dataclasses import dataclass, field
from enum import Enum, IntEnum
from typing import FrozenSet, Optional, Sequence


def utcnow() -> str:
    """Timestamps are UTC ISO-8601 with explicit offset, never local time."""
    return dt.datetime.now(dt.timezone.utc).isoformat()


def new_id(prefix: str) -> str:
    return f"{prefix}-{uuid.uuid4()}"


class Level(IntEnum):
    """Authority levels. Higher grants strictly more than lower.

    CHAIRMAN sits above the documented 1-5 range so ordinary comparisons
    (``agent.level > other.level``) work without special-casing the root.
    """

    READ_ONLY = 1
    INTERNAL = 2
    OPERATOR = 3
    CROSS_AGENT = 4
    EXECUTIVE = 5
    CHAIRMAN = 6


class Classification(IntEnum):
    """Data sensitivity. Ordered so ``<=`` means "no more sensitive than"."""

    PUBLIC = 0
    INTERNAL = 1
    CONFIDENTIAL = 2
    RESTRICTED = 3


class Tool(str, Enum):
    """The tool ecosystems an agent can be granted access to."""

    FEATURED = "featured"
    PRODUCTIVE = "productive"
    CREATIVITY = "creativity"
    DEVELOPER = "developer"
    BUSINESS_OPS = "business_ops"
    DATA_ANALYSIS = "data_analysis"
    COMMUNICATION = "communication"
    EDUCATION = "education"
    RESEARCH = "research"
    SECURITY = "security"
    FINANCE = "finance"
    HEALTHCARE = "healthcare"
    ENTERTAINMENT = "entertainment"


class AgentStatus(str, Enum):
    PENDING = "pending"
    ACTIVE = "active"
    SUSPENDED = "suspended"
    TERMINATED = "terminated"


class RequestStatus(str, Enum):
    PENDING = "pending"
    APPROVED = "approved"
    REJECTED = "rejected"


class TaskStatus(str, Enum):
    ASSIGNED = "assigned"
    IN_PROGRESS = "in_progress"
    BLOCKED = "blocked"
    DONE = "done"
    FAILED = "failed"


class Escalation(IntEnum):
    """Escalation severity, mirroring references/escalation-procedures.md."""

    LOG_ONLY = 1
    INFORMATIONAL = 2
    ROUTINE = 3
    URGENT = 4
    IMMEDIATE = 5


@dataclass(frozen=True)
class Decision:
    """The result of a permission check. Always carries a reason.

    A denial without a reason is useless to the operator reading the audit
    log later, so ``reason`` is required in both directions.
    """

    allowed: bool
    reason: str

    def __bool__(self) -> bool:
        return self.allowed


@dataclass(frozen=True)
class Agent:
    agent_id: str
    name: str
    level: Level
    tools: FrozenSet[Tool]
    max_classification: Classification
    purpose: str
    parent_id: Optional[str] = None
    status: AgentStatus = AgentStatus.ACTIVE
    created_at: str = field(default_factory=utcnow)
    terminated_at: Optional[str] = None
    termination_reason: Optional[str] = None

    @property
    def is_chairman(self) -> bool:
        return self.level is Level.CHAIRMAN


@dataclass(frozen=True)
class AgentRequest:
    """A proposal to create an agent, pending approval.

    No agent comes into existence without one of these being approved. The
    justification fields are validated as non-empty at construction time in
    :mod:`chairman.registry`, which is what makes "provide full information
    before creating" an enforced rule rather than a convention.
    """

    request_id: str
    requested_by: str
    name: str
    level: Level
    tools: FrozenSet[Tool]
    max_classification: Classification
    purpose: str
    objectives: Sequence[str]
    reporting: str
    risks: str
    budget_usd: float
    status: RequestStatus = RequestStatus.PENDING
    created_at: str = field(default_factory=utcnow)
    decided_by: Optional[str] = None
    decided_at: Optional[str] = None
    decision_reason: Optional[str] = None


@dataclass(frozen=True)
class Task:
    task_id: str
    title: str
    assigned_to: str
    assigned_by: str
    tool: Tool
    classification: Classification
    status: TaskStatus = TaskStatus.ASSIGNED
    escalation: Escalation = Escalation.LOG_ONLY
    note: str = ""
    created_at: str = field(default_factory=utcnow)
    updated_at: str = field(default_factory=utcnow)


@dataclass(frozen=True)
class AuditEntry:
    """One tamper-evident record. ``entry_hash`` chains to ``prev_hash``."""

    seq: int
    timestamp: str
    actor: str
    action: str
    resource: str
    outcome: str
    details: dict
    prev_hash: str
    entry_hash: str
