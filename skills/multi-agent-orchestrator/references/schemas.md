# Orchestrator Shared State Schemas

## context.json
```json
{
  "project": "string — one-line project description",
  "chat_context": "string — compacted summary of original conversation context and user preferences",
  "requirements": ["string — each requirement"],
  "constraints": ["string — each constraint"],
  "created_at": "ISO 8601 timestamp",
  "tasks": {
    "agent-name": "string — task description (added during decomposition)"
  }
}
```

## decisions.json
```json
[
  {
    "request_id": "string",
    "decision": "string — what was decided",
    "reason": "string — why",
    "resolved_at": "ISO 8601 timestamp"
  }
]
```

## requests.json
```json
[
  {
    "request_id": "string — unique ID",
    "agent": "string — name of agent",
    "type": "question | change | conflict | review_request",
    "priority": "low | medium | high",
    "content": "string — detailed request",
    "status": "pending | resolved | rejected",
    "created_at": "ISO 8601 timestamp"
  }
]
```

## agents.json
```json
{
  "agent-frontend": {
    "task": "string — current task description",
    "status": "running | completed | terminated | errored",
    "worktree": ".kilocode/worktrees/agent-frontend",
    "kilo_mode": "code | architect | debug | ask",
    "pid": "integer — the process ID of the running Kilo CLI",
    "started_at": "ISO 8601 timestamp",
    "last_heartbeat": "ISO 8601 timestamp"
  }
}
```
