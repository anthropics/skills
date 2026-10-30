# Audit Trail Reference

## Why SHA-256 Merkle Chain?

A simple JSONL log can be tampered with — entries can be deleted or
modified without detection. A Merkle chain makes tampering detectable:
each entry includes the hash of the previous entry. Changing any entry
changes its hash, which breaks all subsequent hashes.

This is what compliance teams (SOX, HIPAA, EU AI Act) require:
not just a log, but a **verifiable** log.

## Entry Schema

```json
{
  "timestamp": "2026-06-13T10:00:00.000000+00:00",
  "agent_id": "researcher-1",
  "tool_name": "web_search",
  "tool_args_hash": "sha256-of-tool-args",
  "verdict": "allowed",
  "reason": "Matched allow-search rule",
  "prev_hash": "sha256-of-previous-entry",
  "entry_hash": "sha256-of-this-entry"
}
```

## Compliance Framework Mapping

| Requirement | Implementation |
|------------|----------------|
| SOX — complete activity log | Every tool call recorded, no deletions |
| SOX — tamper evidence | SHA-256 Merkle chain |
| HIPAA — access audit | agent_id field per entry |
| EU AI Act Art. 12 — record keeping | Append-only JSONL with integrity verification |
| EU AI Act Art. 14 — oversight | `verdict: "pending"` for human approval flows |

## Querying the Audit Log

```python
import json
from pathlib import Path

def query_audit_log(
    log_path: str,
    agent_id: str | None = None,
    verdict: str | None = None,
    tool_name: str | None = None,
) -> list[dict]:
    """Query audit log entries by field values."""
    results = []
    with open(log_path) as f:
        for line in f:
            if not line.strip():
                continue
            entry = json.loads(line)
            if agent_id and entry.get("agent_id") != agent_id:
                continue
            if verdict and entry.get("verdict") != verdict:
                continue
            if tool_name and entry.get("tool_name") != tool_name:
                continue
            results.append(entry)
    return results

# Find all denied calls for agent researcher-1
denied = query_audit_log(
    "governance_audit.jsonl",
    agent_id="researcher-1",
    verdict="denied",
)
print(f"{len(denied)} denied calls for researcher-1")
```

## Rotating Logs Without Breaking the Chain

```python
def rotate_audit_log(log_path: str, archive_path: str) -> str:
    """
    Rotate the audit log while preserving chain continuity.
    The new log starts with a 'rotation' entry that includes
    the last hash from the old log, maintaining chain linkage.
    """
    # Get last hash from current log
    last_hash = "0" * 64
    with open(log_path) as f:
        for line in f:
            if line.strip():
                last_hash = json.loads(line)["entry_hash"]

    # Archive current log
    Path(log_path).rename(archive_path)

    # Start new log with rotation marker entry
    new_audit = AuditTrail(log_path)
    new_audit._last_hash = last_hash  # continue chain
    new_audit.record(
        tool_name="__rotation__",
        tool_args={"archived_to": archive_path},
        verdict="system",
        reason=f"Log rotated. Previous log: {archive_path}",
    )
    return new_audit._last_hash