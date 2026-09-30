"""Chairman — enforced governance for hierarchical agent systems.

A small, dependency-free library that makes delegation rules executable:
agents are created only through an approved proposal carrying full
justification, authority narrows strictly as it moves down the tree, and
every decision — allowed or denied — lands in a hash-chained audit log.

    from chairman import Registry, Store, Level, Tool, Classification

    registry = Registry(Store("org.db"))
    chairman = registry.install_chairman()

    request = registry.request_agent(
        requested_by="chairman",
        name="finance-analyst",
        level=Level.OPERATOR,
        tools=[Tool.FINANCE, Tool.DATA_ANALYSIS],
        max_classification=Classification.CONFIDENTIAL,
        purpose="Daily financial metrics analysis and anomaly detection",
        objectives=["Flag anomalies within 24h", "Publish a daily briefing"],
        reporting="Daily briefing, weekly deep dive",
        risks="Handles confidential ledger data; mis-flagging wastes analyst time",
    )
    agent = registry.approve_request(request.request_id, approver="chairman")
"""

from .audit import GENESIS_HASH, head_hash, verify_chain
from .enforcement import Classifier, Session, ToolBox, ToolSpec, active_tools
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
)
from .permissions import (
    LEVEL_CLASSIFICATION_CAP,
    MAX_DIRECT_REPORTS,
    authorize_action,
    can_approve,
    can_create_subagent,
    effective_classification,
)
from .registry import CHAIRMAN_NAME, Registry
from .store import Store

__version__ = "1.0.0"

__all__ = [
    "Agent",
    "AgentRequest",
    "AgentStatus",
    "AuditEntry",
    "CHAIRMAN_NAME",
    "ChairmanError",
    "Classifier",
    "Classification",
    "Decision",
    "Escalation",
    "GENESIS_HASH",
    "IncompleteRequest",
    "LEVEL_CLASSIFICATION_CAP",
    "Level",
    "MAX_DIRECT_REPORTS",
    "NotFound",
    "PermissionDenied",
    "Registry",
    "RequestStatus",
    "Session",
    "StateError",
    "Store",
    "Task",
    "TaskStatus",
    "Tool",
    "ToolBox",
    "ToolSpec",
    "active_tools",
    "authorize_action",
    "can_approve",
    "can_create_subagent",
    "effective_classification",
    "head_hash",
    "verify_chain",
]
