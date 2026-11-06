"""SQLite persistence. Stdlib only, so the package runs with no install step.

The store is deliberately dumb: it reads and writes rows and appends audit
entries. All rule enforcement lives in :mod:`chairman.permissions` and
:mod:`chairman.registry` so the rules stay testable without a database.
"""

from __future__ import annotations

import json
import sqlite3
from pathlib import Path
from typing import List, Optional, Sequence

from .audit import GENESIS_HASH, compute_hash
from .models import (
    Agent,
    AgentRequest,
    AgentStatus,
    AuditEntry,
    Classification,
    Escalation,
    Level,
    RequestStatus,
    Task,
    TaskStatus,
    Tool,
    utcnow,
)

SCHEMA = """
CREATE TABLE IF NOT EXISTS agents (
    agent_id TEXT PRIMARY KEY,
    name TEXT NOT NULL UNIQUE,
    level INTEGER NOT NULL,
    tools TEXT NOT NULL,
    max_classification INTEGER NOT NULL,
    purpose TEXT NOT NULL,
    parent_id TEXT,
    status TEXT NOT NULL,
    created_at TEXT NOT NULL,
    terminated_at TEXT,
    termination_reason TEXT
);

CREATE TABLE IF NOT EXISTS requests (
    request_id TEXT PRIMARY KEY,
    requested_by TEXT NOT NULL,
    name TEXT NOT NULL,
    level INTEGER NOT NULL,
    tools TEXT NOT NULL,
    max_classification INTEGER NOT NULL,
    purpose TEXT NOT NULL,
    objectives TEXT NOT NULL,
    reporting TEXT NOT NULL,
    risks TEXT NOT NULL,
    budget_usd REAL NOT NULL,
    status TEXT NOT NULL,
    created_at TEXT NOT NULL,
    decided_by TEXT,
    decided_at TEXT,
    decision_reason TEXT
);

CREATE TABLE IF NOT EXISTS tasks (
    task_id TEXT PRIMARY KEY,
    title TEXT NOT NULL,
    assigned_to TEXT NOT NULL,
    assigned_by TEXT NOT NULL,
    tool TEXT NOT NULL,
    classification INTEGER NOT NULL,
    status TEXT NOT NULL,
    escalation INTEGER NOT NULL,
    note TEXT NOT NULL,
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS audit (
    seq INTEGER PRIMARY KEY AUTOINCREMENT,
    timestamp TEXT NOT NULL,
    actor TEXT NOT NULL,
    action TEXT NOT NULL,
    resource TEXT NOT NULL,
    outcome TEXT NOT NULL,
    details TEXT NOT NULL,
    prev_hash TEXT NOT NULL,
    entry_hash TEXT NOT NULL
);

CREATE INDEX IF NOT EXISTS idx_agents_parent ON agents(parent_id);
CREATE INDEX IF NOT EXISTS idx_tasks_assignee ON tasks(assigned_to);
"""


def _tools_to_text(tools) -> str:
    return ",".join(sorted(t.value for t in tools))


def _tools_from_text(text: str) -> frozenset:
    if not text:
        return frozenset()
    return frozenset(Tool(v) for v in text.split(","))


class Store:
    """Owns the database connection and row/object translation."""

    def __init__(self, path: str | Path = ":memory:") -> None:
        self.path = str(path)
        if self.path != ":memory:":
            Path(self.path).parent.mkdir(parents=True, exist_ok=True)
        self._conn = sqlite3.connect(self.path)
        self._conn.row_factory = sqlite3.Row
        self._conn.execute("PRAGMA foreign_keys = ON")
        self._conn.executescript(SCHEMA)
        self._conn.commit()

    def close(self) -> None:
        self._conn.close()

    def __enter__(self) -> "Store":
        return self

    def __exit__(self, *exc) -> None:
        self.close()

    # ---------------------------------------------------------------- agents

    def put_agent(self, agent: Agent) -> None:
        self._conn.execute(
            """INSERT OR REPLACE INTO agents
               (agent_id, name, level, tools, max_classification, purpose,
                parent_id, status, created_at, terminated_at, termination_reason)
               VALUES (?,?,?,?,?,?,?,?,?,?,?)""",
            (
                agent.agent_id,
                agent.name,
                int(agent.level),
                _tools_to_text(agent.tools),
                int(agent.max_classification),
                agent.purpose,
                agent.parent_id,
                agent.status.value,
                agent.created_at,
                agent.terminated_at,
                agent.termination_reason,
            ),
        )
        self._conn.commit()

    def _row_to_agent(self, row: sqlite3.Row) -> Agent:
        return Agent(
            agent_id=row["agent_id"],
            name=row["name"],
            level=Level(row["level"]),
            tools=_tools_from_text(row["tools"]),
            max_classification=Classification(row["max_classification"]),
            purpose=row["purpose"],
            parent_id=row["parent_id"],
            status=AgentStatus(row["status"]),
            created_at=row["created_at"],
            terminated_at=row["terminated_at"],
            termination_reason=row["termination_reason"],
        )

    def get_agent(self, agent_id: str) -> Optional[Agent]:
        row = self._conn.execute(
            "SELECT * FROM agents WHERE agent_id = ?", (agent_id,)
        ).fetchone()
        return self._row_to_agent(row) if row else None

    def get_agent_by_name(self, name: str) -> Optional[Agent]:
        row = self._conn.execute(
            "SELECT * FROM agents WHERE name = ?", (name,)
        ).fetchone()
        return self._row_to_agent(row) if row else None

    def list_agents(self, parent_id: Optional[str] = None) -> List[Agent]:
        if parent_id is None:
            rows = self._conn.execute(
                "SELECT * FROM agents ORDER BY created_at"
            ).fetchall()
        else:
            rows = self._conn.execute(
                "SELECT * FROM agents WHERE parent_id = ? ORDER BY created_at",
                (parent_id,),
            ).fetchall()
        return [self._row_to_agent(r) for r in rows]

    def count_active_reports(self, parent_id: str) -> int:
        """Terminated agents free up a slot; suspended ones do not."""
        row = self._conn.execute(
            "SELECT COUNT(*) AS n FROM agents WHERE parent_id = ? AND status != ?",
            (parent_id, AgentStatus.TERMINATED.value),
        ).fetchone()
        return int(row["n"])

    # -------------------------------------------------------------- requests

    def put_request(self, request: AgentRequest) -> None:
        self._conn.execute(
            """INSERT OR REPLACE INTO requests
               (request_id, requested_by, name, level, tools, max_classification,
                purpose, objectives, reporting, risks, budget_usd, status,
                created_at, decided_by, decided_at, decision_reason)
               VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
            (
                request.request_id,
                request.requested_by,
                request.name,
                int(request.level),
                _tools_to_text(request.tools),
                int(request.max_classification),
                request.purpose,
                json.dumps(list(request.objectives)),
                request.reporting,
                request.risks,
                request.budget_usd,
                request.status.value,
                request.created_at,
                request.decided_by,
                request.decided_at,
                request.decision_reason,
            ),
        )
        self._conn.commit()

    def _row_to_request(self, row: sqlite3.Row) -> AgentRequest:
        return AgentRequest(
            request_id=row["request_id"],
            requested_by=row["requested_by"],
            name=row["name"],
            level=Level(row["level"]),
            tools=_tools_from_text(row["tools"]),
            max_classification=Classification(row["max_classification"]),
            purpose=row["purpose"],
            objectives=json.loads(row["objectives"]),
            reporting=row["reporting"],
            risks=row["risks"],
            budget_usd=row["budget_usd"],
            status=RequestStatus(row["status"]),
            created_at=row["created_at"],
            decided_by=row["decided_by"],
            decided_at=row["decided_at"],
            decision_reason=row["decision_reason"],
        )

    def get_request(self, request_id: str) -> Optional[AgentRequest]:
        row = self._conn.execute(
            "SELECT * FROM requests WHERE request_id = ?", (request_id,)
        ).fetchone()
        return self._row_to_request(row) if row else None

    def list_requests(
        self, status: Optional[RequestStatus] = None
    ) -> List[AgentRequest]:
        if status is None:
            rows = self._conn.execute(
                "SELECT * FROM requests ORDER BY created_at"
            ).fetchall()
        else:
            rows = self._conn.execute(
                "SELECT * FROM requests WHERE status = ? ORDER BY created_at",
                (status.value,),
            ).fetchall()
        return [self._row_to_request(r) for r in rows]

    # ----------------------------------------------------------------- tasks

    def put_task(self, task: Task) -> None:
        self._conn.execute(
            """INSERT OR REPLACE INTO tasks
               (task_id, title, assigned_to, assigned_by, tool, classification,
                status, escalation, note, created_at, updated_at)
               VALUES (?,?,?,?,?,?,?,?,?,?,?)""",
            (
                task.task_id,
                task.title,
                task.assigned_to,
                task.assigned_by,
                task.tool.value,
                int(task.classification),
                task.status.value,
                int(task.escalation),
                task.note,
                task.created_at,
                task.updated_at,
            ),
        )
        self._conn.commit()

    def _row_to_task(self, row: sqlite3.Row) -> Task:
        return Task(
            task_id=row["task_id"],
            title=row["title"],
            assigned_to=row["assigned_to"],
            assigned_by=row["assigned_by"],
            tool=Tool(row["tool"]),
            classification=Classification(row["classification"]),
            status=TaskStatus(row["status"]),
            escalation=Escalation(row["escalation"]),
            note=row["note"],
            created_at=row["created_at"],
            updated_at=row["updated_at"],
        )

    def get_task(self, task_id: str) -> Optional[Task]:
        row = self._conn.execute(
            "SELECT * FROM tasks WHERE task_id = ?", (task_id,)
        ).fetchone()
        return self._row_to_task(row) if row else None

    def list_tasks(self, assigned_to: Optional[str] = None) -> List[Task]:
        if assigned_to is None:
            rows = self._conn.execute(
                "SELECT * FROM tasks ORDER BY created_at"
            ).fetchall()
        else:
            rows = self._conn.execute(
                "SELECT * FROM tasks WHERE assigned_to = ? ORDER BY created_at",
                (assigned_to,),
            ).fetchall()
        return [self._row_to_task(r) for r in rows]

    # ----------------------------------------------------------------- audit

    def append_audit(
        self,
        actor: str,
        action: str,
        resource: str,
        outcome: str,
        details: Optional[dict] = None,
    ) -> AuditEntry:
        """Append one chained record. Called for every state change."""
        details = details or {}
        row = self._conn.execute(
            "SELECT entry_hash FROM audit ORDER BY seq DESC LIMIT 1"
        ).fetchone()
        prev_hash = row["entry_hash"] if row else GENESIS_HASH

        row = self._conn.execute("SELECT COALESCE(MAX(seq), 0) AS m FROM audit").fetchone()
        seq = int(row["m"]) + 1
        timestamp = utcnow()

        entry_hash = compute_hash(
            prev_hash, seq, timestamp, actor, action, resource, outcome, details
        )

        self._conn.execute(
            """INSERT INTO audit
               (seq, timestamp, actor, action, resource, outcome, details,
                prev_hash, entry_hash)
               VALUES (?,?,?,?,?,?,?,?,?)""",
            (
                seq,
                timestamp,
                actor,
                action,
                resource,
                outcome,
                json.dumps(details, sort_keys=True, default=str),
                prev_hash,
                entry_hash,
            ),
        )
        self._conn.commit()

        return AuditEntry(
            seq=seq,
            timestamp=timestamp,
            actor=actor,
            action=action,
            resource=resource,
            outcome=outcome,
            details=details,
            prev_hash=prev_hash,
            entry_hash=entry_hash,
        )

    def list_audit(self, limit: Optional[int] = None) -> List[AuditEntry]:
        sql = "SELECT * FROM audit ORDER BY seq"
        rows = self._conn.execute(sql).fetchall()
        entries = [
            AuditEntry(
                seq=r["seq"],
                timestamp=r["timestamp"],
                actor=r["actor"],
                action=r["action"],
                resource=r["resource"],
                outcome=r["outcome"],
                details=json.loads(r["details"]),
                prev_hash=r["prev_hash"],
                entry_hash=r["entry_hash"],
            )
            for r in rows
        ]
        if limit is not None:
            return entries[-limit:]
        return entries

    def _raw_execute(self, sql: str, params: Sequence = ()) -> None:
        """Escape hatch used by the tests to simulate tampering."""
        self._conn.execute(sql, params)
        self._conn.commit()
