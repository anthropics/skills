# TC Record Schema

A TC record is a JSON object stored at `docs/TC/records/<TC-ID>/tc_record.json`. Every record is validated against this schema and a state machine on every write.

## Top-Level Fields

| Field | Type | Required | Notes |
|-------|------|----------|-------|
| `tc_id` | string | yes | Pattern: `TC-NNN-MM-DD-YY-slug` |
| `parent_tc` | string \| null | no | For sub-TCs only |
| `title` | string | yes | 5-120 characters |
| `status` | enum | yes | One of: `planned`, `in_progress`, `blocked`, `implemented`, `tested`, `deployed` |
| `priority` | enum | yes | `critical`, `high`, `medium`, `low` |
| `created` | ISO 8601 | yes | UTC timestamp |
| `updated` | ISO 8601 | yes | UTC timestamp, refreshed on every write |
| `created_by` | string | yes | Author identifier (e.g., `user:micha`, `ai:claude-opus`) |
| `project` | string | yes | Project name (denormalized from registry) |
| `description` | object | yes | See below |
| `files_affected` | array | yes | See below |
| `revision_history` | array | yes | Append-only, sequential `R<n>` IDs |
| `sub_tcs` | array | no | Child TCs |
| `test_cases` | array | yes | Sequential `T<n>` IDs |
| `approval` | object | yes | See below |
| `session_context` | object | yes | See below |
| `tags` | array<string> | yes | Freeform tags |
| `related_tcs` | array<string> | yes | Cross-references |
| `notes` | string | yes | Freeform notes |
| `metadata` | object | yes | See below |

## description

```json
{
  "summary": "string (10+ chars)",
  "motivation": "string (1+ chars)",
  "scope": "feature|bugfix|refactor|infrastructure|documentation|hotfix|enhancement",
  "detailed_design": "string|null",
  "breaking_changes": ["string", "..."],
  "dependencies": ["string", "..."]
}
```

## files_affected (array of objects)

```json
{
  "path": "src/auth.py",
  "action": "created|modified|deleted|renamed",
  "description": "string|null",
  "lines_added": "integer|null",
  "lines_removed": "integer|null"
}
```

## revision_history (array of objects, append-only)

```json
{
  "revision_id": "R1",
  "timestamp": "2026-04-05T12:34:56+00:00",
  "author": "ai:claude-opus",
  "summary": "Created TC record",
  "field_changes": [
    {
      "field": "status",
      "action": "set|changed|added|removed",
      "old_value": "planned",
      "new_value": "in_progress",
      "reason": "Starting implementation"
    }
  ]
}
```

**Rules:**
- IDs are sequential: R1, R2, R3, ... no gaps allowed.
- The first entry is always the creation event.
- Existing entries are NEVER modified or deleted.

## test_cases (array of objects)

```json
{
  "test_id": "T1",
  "title": "Login returns JWT for valid credentials",
  "procedure": ["POST /login", "with valid creds"],
  "expected_result": "200 + token in body",
  "actual_result": "string|null",
  "status": "pending|pass|fail|skip|blocked",
  "evidence": [
    {
      "type": "log_snippet|screenshot|file_reference|command_output",
      "description": "string",
      "content": "string|null",
      "path": "string|null",
      "timestamp": "ISO|null"
    }
  ],
  "tested_by": "string|null",
  "tested_date": "ISO|null"
}
```

## approval

```json
{
  "approved": false,
  "approved_by": "string|null",
  "approved_date": "ISO|null",
  "approval_notes": "string",
  "test_coverage_status": "none|partial|full"
}
```

**Consistency rule:** if `approved=true`, both `approved_by` and `approved_date` MUST be set.

## session_context

```json
{
  "current_session": {
    "session_id": "string",
    "platform": "claude_code|claude_web|api|other",
    "model": "string",
    "started": "ISO",
    "last_active": "ISO|null"
  },
  "handoff": {
    "progress_summary": "string",
    "next_steps": ["string", "..."],
    "blockers": ["string", "..."],
    "key_context": ["string", "..."],
    "files_in_progress": [
      {
        "path": "src/foo.py",
        "state": "editing|needs_review|partially_done|ready",
        "notes": "string|null"
      }
    ],
    "decisions_made": [
      {
        "decision": "string",
        "rationale": "string",
        "timestamp": "ISO"
      }
    ]
  },
  "session_history": [
    {
      "session_id": "string",
      "platform": "string",
      "model": "string",
      "started": "ISO",
      "ended": "ISO",
      "summary": "string",
      "changes_made": ["string", "..."]
    }
  ]
}
```

## metadata

```json
{
  "project": "string",
  "created_by": "string",
  "last_modified_by": "string",
  "last_modified": "ISO",
  "estimated_effort": "trivial|small|medium|large|epic|null"
}
```

## Registry Schema (`tc_registry.json`)

```json
{
  "project_name": "string",
  "created": "ISO",
  "updated": "ISO",
  "next_tc_number": 1,
  "records": [
    {
      "tc_id": "TC-001-...",
      "title": "string",
      "status": "enum",
      "scope": "enum",
      "priority": "enum",
      "created": "ISO",
      "updated": "ISO",
      "path": "records/TC-001-.../tc_record.json"
    }
  ],
  "statistics": {
    "total": 0,
    "by_status": { "planned": 0, "in_progress": 0, "blocked": 0, "implemented": 0, "tested": 0, "deployed": 0 },
    "by_scope": { "feature": 0, "bugfix": 0, "refactor": 0, "infrastructure": 0, "documentation": 0, "hotfix": 0, "enhancement": 0 },
    "by_priority": { "critical": 0, "high": 0, "medium": 0, "low": 0 }
  }
}
```

Statistics are recomputed on every registry write. Never edit them by hand.
