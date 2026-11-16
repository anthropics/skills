# GOG Audit Logging

This document defines the audit logging format and practices for GOG skills.

## Overview

GOG skills maintain an audit log of all actions taken, especially those that modify data (sending emails, creating tasks, scheduling events). This log serves several purposes:

1. **Accountability**: Track what actions were performed
2. **Debugging**: Diagnose issues when things go wrong
3. **Compliance**: Provide an audit trail for sensitive operations
4. **User transparency**: Let users review what GOG has done on their behalf

## Log Location

The audit log is stored at:

```
~/.gog-assistant/audit.log
```

The directory `~/.gog-assistant/` is created automatically if it doesn't exist.

**Permissions**: The log file should be created with mode `0600` (read/write for owner only).

## Log Format

Each log entry is a single line of JSON, making it easy to parse with tools like `jq`.

### Standard Fields

Every log entry must include these fields:

```json
{
  "timestamp": "ISO8601 datetime (required)",
  "skill": "skill-name (required)",
  "action": "action-type (required)",
  "status": "success | failure | pending (required)",
  "entity_id": "ID of affected entity (optional)",
  "details": {}
}
```

### Field Descriptions

- **timestamp**: When the action was performed (ISO8601 with timezone, prefer UTC)
- **skill**: Name of the skill that performed the action (must match SKILL.md frontmatter name)
- **action**: Type of action taken (see Action Types below)
- **status**: Outcome of the action
  - `success`: Action completed successfully
  - `failure`: Action failed
  - `pending`: Action initiated but not yet complete
- **entity_id**: Identifier of the entity affected (message ID, task ID, event ID, etc.)
- **details**: Action-specific additional information (object)

### Action Types

Common action types across GOG skills:

**Email Actions:**
- `email-send`: Send an email
- `email-draft`: Create/update a draft
- `email-archive`: Archive message(s)
- `email-delete`: Delete message(s)
- `email-label`: Add/remove labels

**Task Actions:**
- `task-create`: Create a new task
- `task-update`: Update task properties
- `task-complete`: Mark task as complete
- `task-delete`: Delete a task

**Calendar Actions:**
- `event-create`: Create calendar event
- `event-update`: Update event properties
- `event-delete`: Delete event
- `event-invite`: Send meeting invitation

**Follow-up Actions:**
- `followup-create`: Add follow-up tracking
- `followup-update`: Update follow-up status
- `followup-nudge`: Generate follow-up message

## Detail Field Schemas

### Email Send Details

```json
{
  "details": {
    "to": ["array of recipient emails"],
    "cc": ["array of CC emails"],
    "subject": "email subject",
    "draft_id": "draft ID if sending from draft",
    "reply_to_id": "original message ID if replying",
    "user_confirmation": true,
    "confirmation_string": "YES, SEND"
  }
}
```

### Email Draft Details

```json
{
  "details": {
    "draft_id": "draft identifier",
    "to": ["recipient emails"],
    "subject": "subject line",
    "body_length": 1234,
    "reply_to_id": "original message ID if replying"
  }
}
```

### Task Create Details

```json
{
  "details": {
    "title": "task title",
    "priority": "P0-P3",
    "category": "Work|Personal|Errands|Admin",
    "due_date": "YYYY-MM-DD",
    "source": "email | manual | calendar",
    "source_id": "email_id or event_id if applicable"
  }
}
```

### Event Create Details

```json
{
  "details": {
    "title": "event title",
    "start": "ISO8601 datetime",
    "duration_minutes": 60,
    "attendees": ["attendee emails"],
    "location": "event location",
    "user_confirmation": true
  }
}
```

### Follow-up Create Details

```json
{
  "details": {
    "person": "email or name",
    "topic": "follow-up topic",
    "next_nudge_date": "YYYY-MM-DD",
    "priority": "high|medium|low",
    "source_email_id": "message ID"
  }
}
```

## Privacy Considerations

**DO NOT log:**
- Full email bodies
- Passwords or credentials
- Sensitive personal information
- Full meeting notes or descriptions

**DO log:**
- Email subject lines (usually safe)
- Snippets (first ~50 chars)
- Metadata (IDs, timestamps, counts)
- Actions taken and their outcomes

If logging email subjects or snippets, consider:
- Truncating long content
- Redacting obvious sensitive terms (SSN, credit card patterns)
- Providing a config option to disable subject logging

## Example Log Entries

### Successful Email Send

```json
{"timestamp":"2026-01-28T15:30:00Z","skill":"gog-email-send","action":"email-send","status":"success","entity_id":"msg_sent789","details":{"to":["recipient@example.com"],"subject":"Follow-up on proposal","user_confirmation":true,"confirmation_string":"YES, SEND"}}
```

### Task Creation from Email

```json
{"timestamp":"2026-01-28T10:15:00Z","skill":"gog-tasks","action":"task-create","status":"success","entity_id":"task_abc123","details":{"title":"Review contract","priority":"P1","category":"Work","source":"email","source_id":"msg_contract456"}}
```

### Calendar Event Creation

```json
{"timestamp":"2026-01-28T14:00:00Z","skill":"gog-calendar","action":"event-create","status":"success","entity_id":"event_meeting789","details":{"title":"Q2 Planning","start":"2026-02-01T14:00:00Z","duration_minutes":60,"attendees":["alice@example.com","bob@example.com"],"user_confirmation":true}}
```

### Failed Email Send

```json
{"timestamp":"2026-01-28T16:00:00Z","skill":"gog-email-send","action":"email-send","status":"failure","details":{"to":["invalid@"],"subject":"Test","error":"Invalid recipient email address","user_confirmation":false}}
```

### Follow-up Nudge

```json
{"timestamp":"2026-01-30T09:00:00Z","skill":"gog-followups","action":"followup-nudge","status":"success","entity_id":"followup_xyz","details":{"person":"vendor@example.com","topic":"Pricing proposal","nudge_count":1,"draft_created":"draft_followup123"}}
```

## Using the Log

### View Recent Actions

```bash
tail -n 20 ~/.gog-assistant/audit.log | jq .
```

### Find All Email Sends

```bash
jq -r 'select(.action == "email-send")' ~/.gog-assistant/audit.log
```

### Check Actions by Skill

```bash
jq -r 'select(.skill == "gog-email-send")' ~/.gog-assistant/audit.log
```

### Find Failed Actions

```bash
jq -r 'select(.status == "failure")' ~/.gog-assistant/audit.log
```

### Actions in Last 24 Hours

```bash
# Requires date parsing (more complex)
jq -r --arg since "$(date -u -v-1d +%Y-%m-%dT%H:%M:%SZ)" \
  'select(.timestamp > $since)' ~/.gog-assistant/audit.log
```

## Log Rotation

The audit log can grow large over time. Consider implementing log rotation:

**Manual rotation:**
```bash
cd ~/.gog-assistant
mv audit.log audit.log.$(date +%Y%m%d)
gzip audit.log.*[0-9]
# Keep last 30 days
find . -name "audit.log.*.gz" -mtime +30 -delete
```

**Using logrotate (Linux):**

Create `/etc/logrotate.d/gog-assistant`:
```
/home/*/.gog-assistant/audit.log {
    daily
    rotate 30
    compress
    missingok
    notifempty
    create 0600
}
```

## Implementation Guidelines

### For Skill Authors

When implementing a skill that takes actions:

1. **Import the logging utility**: Use `scripts/log.sh` or implement equivalent
2. **Log before and after**: Log when action starts (status: pending) and when it completes (success/failure)
3. **Include confirmation status**: Always log whether user explicitly confirmed
4. **Keep details minimal**: Only essential metadata, no full content
5. **Handle errors gracefully**: Log failures with error details

### Example Bash Usage

```bash
# Source the logging script
source "$(dirname "$0")/../../_shared/scripts/log.sh"

# Log an action
log_action "gog-email-send" "email-send" "success" "msg_123" \
  '{"to":["user@example.com"],"subject":"Test","user_confirmation":true}'
```

### Example Python Usage

```python
import json
from pathlib import Path
from datetime import datetime

def log_action(skill, action, status, entity_id=None, details=None):
    log_dir = Path.home() / ".gog-assistant"
    log_dir.mkdir(mode=0o700, exist_ok=True)

    log_file = log_dir / "audit.log"

    entry = {
        "timestamp": datetime.utcnow().isoformat() + "Z",
        "skill": skill,
        "action": action,
        "status": status
    }

    if entity_id:
        entry["entity_id"] = entity_id
    if details:
        entry["details"] = details

    with open(log_file, "a") as f:
        json.dump(entry, f)
        f.write("\n")

# Usage
log_action("gog-tasks", "task-create", "success", "task_123",
          {"title": "Review contract", "priority": "P1"})
```

## Security Considerations

1. **Protect the log file**: Set restrictive permissions (0600)
2. **Don't log secrets**: Never log passwords, tokens, or API keys
3. **Validate inputs**: Sanitize data before logging to prevent log injection
4. **Limit log size**: Implement rotation to prevent disk exhaustion
5. **Secure transmission**: If logs are sent elsewhere, use encryption

## Future Enhancements

Potential improvements for the logging system:

- **Structured storage**: SQLite database instead of flat file
- **Web UI**: Dashboard to view and search logs
- **Alerting**: Notify on repeated failures
- **Analytics**: Track usage patterns and performance
- **Export**: Generate reports for specific time ranges
