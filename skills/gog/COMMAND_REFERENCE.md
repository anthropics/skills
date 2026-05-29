# GOG Skills - Quick Command Reference

This is a quick reference for GOG CLI v0.9.0 commands used by the skills.

## Gmail Commands

### Search Emails
```bash
# Unread emails
gog gmail search "is:unread" --max 25 --json

# From specific sender
gog gmail search "from:user@example.com" --max 10 --json

# To yourself
gog gmail search "to:me OR cc:me" --max 20 --json

# Complex query
gog gmail search "is:unread from:boss@company.com has:attachment" --max 5 --json
```

### Get Message/Thread
```bash
# Get a single message
gog gmail get <messageId> --json

# Get entire thread
gog gmail thread get <threadId> --json
```

### Create and Send Drafts
```bash
# Create draft
gog gmail drafts create \
  --to "recipient@example.com" \
  --subject "Subject here" \
  --body "Email body here" \
  --json

# Create draft reply
gog gmail drafts create \
  --to "recipient@example.com" \
  --subject "Re: Original Subject" \
  --body "Reply text" \
  --reply-to-message-id msg_abc123 \
  --json

# Send draft
gog gmail drafts send <draftId> --json

# Send directly (no draft)
gog gmail send \
  --to "recipient@example.com" \
  --subject "Quick note" \
  --body "Message text" \
  --json
```

## Calendar Commands

### View Events
```bash
# Today's events
gog calendar events --today --json

# This week
gog calendar events --week --json

# Next 7 days
gog calendar events --days 7 --json

# Date range
gog calendar events --from "2026-01-28" --to "2026-02-04" --json
```

### Find Available Time
```bash
# Check free/busy for tomorrow
gog calendar freebusy primary \
  --from "2026-01-29T00:00:00Z" \
  --to "2026-01-29T23:59:59Z" \
  --json

# Parse output to find gaps between busy periods
```

### Create Event
```bash
gog calendar create primary \
  --summary "Meeting Title" \
  --from "2026-01-29T14:00:00-08:00" \
  --to "2026-01-29T15:00:00-08:00" \
  --attendees "alice@example.com,bob@example.com" \
  --location "Conference Room A" \
  --description "Meeting agenda here" \
  --with-meet \
  --json
```

## Tasks Commands

### Get Task List ID (Required First Step)
```bash
# Get your first/default task list
TASKLIST_ID=$(gog tasks lists --json | jq -r '.tasklists[0].id')

# Or list all task lists
gog tasks lists --json
```

### List Tasks
```bash
# List open tasks
gog tasks list "$TASKLIST_ID" --json

# Include completed
gog tasks list "$TASKLIST_ID" --completed --json
```

### Create Task
```bash
gog tasks add "$TASKLIST_ID" \
  --title "Task title here" \
  --notes "Task description and details" \
  --due "2026-01-31" \
  --json
```

### Update Task
```bash
# Update title/notes/due date
gog tasks update "$TASKLIST_ID" <taskId> \
  --title "New title" \
  --notes "Updated notes" \
  --due "2026-02-05" \
  --json

# Mark as done
gog tasks done "$TASKLIST_ID" <taskId>

# Delete task
gog tasks delete "$TASKLIST_ID" <taskId>
```

## Common Patterns

### Email Triage Flow
```bash
# 1. Get unread emails
THREADS=$(gog gmail search "is:unread" --max 25 --json)

# 2. Get first thread
THREAD_ID=$(echo "$THREADS" | jq -r '.threads[0].id')

# 3. Read thread
gog gmail thread get "$THREAD_ID" --json
```

### Calendar Check Flow
```bash
# 1. Today's agenda
gog calendar events --today --json

# 2. Tomorrow's schedule
gog calendar events --tomorrow --json

# 3. Find free time tomorrow
gog calendar freebusy primary \
  --from "$(date -v+1d +%Y-%m-%dT00:00:00Z)" \
  --to "$(date -v+1d +%Y-%m-%dT23:59:59Z)" \
  --json
```

### Task Management Flow
```bash
# 1. Get task list ID
TASKLIST_ID=$(gog tasks lists --json | jq -r '.tasklists[0].id')

# 2. List open tasks
gog tasks list "$TASKLIST_ID" --json

# 3. Create task from email
gog tasks add "$TASKLIST_ID" \
  --title "Review proposal from Alice" \
  --notes "From email msg_abc123: Check section 3.2" \
  --due "2026-01-31" \
  --json

# 4. Complete task
gog tasks done "$TASKLIST_ID" task_xyz789
```

## Gmail Query Syntax

Essential operators for `gog gmail search`:

| Operator | Example | Description |
|----------|---------|-------------|
| `is:unread` | `is:unread` | Unread messages only |
| `is:starred` | `is:starred` | Starred messages |
| `from:` | `from:alice@example.com` | From specific sender |
| `to:` | `to:me` | To specific recipient |
| `cc:` | `cc:bob@example.com` | CC'd to someone |
| `subject:` | `subject:"budget"` | Subject contains text |
| `has:attachment` | `has:attachment` | Has attachments |
| `after:` | `after:2026/01/20` | After date |
| `before:` | `before:2026/02/01` | Before date |
| `newer_than:` | `newer_than:2d` | Last 2 days |
| `older_than:` | `older_than:7d` | Older than 7 days |
| `OR` | `to:me OR cc:me` | Either condition |
| `AND` | `from:alice is:unread` | Both conditions (implicit AND) |
| `-` | `-from:automated@` | Exclude (NOT) |

**Combine operators:**
```bash
gog gmail search "is:unread from:client@example.com after:2026/01/20 has:attachment" --max 10 --json
```

## Date/Time Formats

### RFC3339 (Preferred)
```
2026-01-29T14:00:00-08:00    # With timezone
2026-01-29T14:00:00Z         # UTC
```

### Simple Date (Tasks, All-day Events)
```
2026-01-29
```

### Relative (Calendar)
```
today
tomorrow
monday
```

## JSON Output Parsing

### Extract Thread ID
```bash
THREAD_ID=$(gog gmail search "is:unread" --max 1 --json | jq -r '.threads[0].id')
```

### Extract Subject from Thread
```bash
SUBJECT=$(gog gmail thread get "$THREAD_ID" --json | \
  jq -r '.thread.messages[0].payload.headers[] | select(.name == "Subject") | .value')
```

### Extract Task List ID
```bash
TASKLIST_ID=$(gog tasks lists --json | jq -r '.tasklists[0].id')
```

### Count Today's Events
```bash
EVENT_COUNT=$(gog calendar events --today --json | jq '.events | length')
```

### Get Free Time Slots
```bash
# Get busy periods
BUSY=$(gog calendar freebusy primary --from "2026-01-29T09:00:00Z" --to "2026-01-29T17:00:00Z" --json)

# Parse gaps (requires custom script to find spaces between busy periods)
echo "$BUSY" | jq -r '.calendars.primary.busy[] | "\(.start) - \(.end)"'
```

## Common Errors & Solutions

| Error | Solution |
|-------|----------|
| `gog: command not found` | Install: `brew install gog` or see https://github.com/rylio/gog |
| `unexpected argument` | Check command syntax - positional args changed |
| `Authentication failed` | Run: `gog auth login` |
| `Calendar not found` | Use `primary` as calendar ID |
| `Task list not found` | Get ID first: `gog tasks lists --json` |
| `Invalid time format` | Use RFC3339: `2026-01-29T14:00:00-08:00` |

## Helper Scripts

### Get Tasklist ID (use in scripts)
```bash
get_tasklist_id() {
  gog tasks lists --json 2>/dev/null | jq -r '.tasklists[0].id' 2>/dev/null || echo ""
}

TASKLIST_ID=$(get_tasklist_id)
if [ -z "$TASKLIST_ID" ]; then
  echo "Error: Could not get task list ID"
  exit 1
fi
```

### Calculate End Time from Duration
```bash
# Start time + duration → end time
START="2026-01-29T14:00:00-08:00"
DURATION_MIN=60

# macOS
END=$(date -j -f "%Y-%m-%dT%H:%M:%S%z" "$START" -v+${DURATION_MIN}M "+%Y-%m-%dT%H:%M:%S%z")

# Linux
END=$(date -d "$START + $DURATION_MIN minutes" -Iseconds)
```

### Parse Gmail Thread Subject
```bash
get_thread_subject() {
  local thread_id="$1"
  gog gmail thread get "$thread_id" --json 2>/dev/null | \
    jq -r '.thread.messages[0].payload.headers[] | select(.name == "Subject") | .value' 2>/dev/null
}

SUBJECT=$(get_thread_subject "19c0518f3b66efe2")
```

## Testing Commands

### Safe Read-Only Tests
```bash
# Email
gog gmail search "to:user@example.com" --max 5 --json

# Calendar
gog calendar events --today --json

# Tasks
TASKLIST_ID=$(gog tasks lists --json | jq -r '.tasklists[0].id')
gog tasks list "$TASKLIST_ID" --json
```

### Safe Write Test (Draft to Self)
```bash
# Create draft to yourself only
gog gmail drafts create \
  --to "user@example.com" \
  --subject "[TEST] Draft to Self" \
  --body "This is a test draft. Do not send." \
  --json

# Get draft ID from output, then delete
gog gmail drafts delete <draftId>
```

## Quick Reference Card

Print this or keep handy:

```
EMAIL:    gog gmail search "<query>" --max N --json
          gog gmail thread get <threadId> --json
          gog gmail drafts create --to --subject --body --json
          gog gmail drafts send <draftId>

CALENDAR: gog calendar events --today --json
          gog calendar events --week --json
          gog calendar freebusy primary --from --to --json
          gog calendar create primary --summary --from --to --attendees --json

TASKS:    TASKLIST_ID=$(gog tasks lists --json | jq -r '.tasklists[0].id')
          gog tasks list "$TASKLIST_ID" --json
          gog tasks add "$TASKLIST_ID" --title --notes --due --json
          gog tasks done "$TASKLIST_ID" <taskId>

AUTH:     gog auth login
VERSION:  gog --version
```
