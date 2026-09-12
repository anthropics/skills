# GOG Interface Documentation

This document describes the actual interface for the `gog` CLI tool (v0.9.0).

## Overview

GOG (Google CLI) is a command-line tool for managing Gmail, Google Calendar, Google Tasks, and other Google Workspace services through a unified interface. It provides structured JSON output for programmatic access and human-readable output for direct use.

**Official repository**: https://github.com/rylio/gog

## Installation & Configuration

### Step 1: Install GOG CLI

**Official repository**: https://github.com/steipete/gogcli

**Install options:**

```bash
# macOS with Homebrew (if available)
brew install gog

# Or download from releases
# https://github.com/steipete/gogcli/releases
```

Verify installation:
```bash
gog --version
# Should show: v0.9.0 or later
```

### Step 2: Set Up Google Cloud OAuth2 Credentials

**⚠️  CRITICAL STEP: You MUST create OAuth2 credentials before GOG can access your Google data.**

GOG requires OAuth2 credentials from Google Cloud Console. Without these, authentication will fail.

**Follow the complete guide here:**
👉 https://github.com/steipete/gogcli?tab=readme-ov-file#1-get-oauth2-credentials

**Summary of steps:**

1. **Create a Google Cloud Project**:
   - Go to: https://console.cloud.google.com/
   - Create a new project (or use existing)

2. **Enable Required APIs**:
   - Gmail API: https://console.cloud.google.com/apis/library/gmail.googleapis.com
   - Google Calendar API: https://console.cloud.google.com/apis/library/calendar-json.googleapis.com
   - Google Tasks API: https://console.cloud.google.com/apis/library/tasks.googleapis.com

3. **Create OAuth2 Credentials**:
   - Navigate to: APIs & Services → Credentials
   - Click: Create Credentials → OAuth client ID
   - Application type: **Desktop app**
   - Name: "GOG CLI" (or your choice)
   - Click: Create
   - Download the JSON file (client_secret_xxx.json)

4. **Configure OAuth Consent Screen** (if prompted):
   - User Type: External (for personal) or Internal (for workspace)
   - Add scopes: Gmail, Calendar, Tasks
   - Add test users if needed

### Step 3: Authenticate GOG

Once you have OAuth2 credentials, authenticate GOG:

```bash
gog auth login
```

**What happens:**
1. GOG prompts for OAuth2 credentials (if first time):
   - Client ID: (from your credentials JSON)
   - Client Secret: (from your credentials JSON)
   - Or it will find them automatically if you place the JSON file in config directory

2. GOG opens browser for OAuth consent:
   - Review permissions (Gmail, Calendar, Tasks)
   - Click "Allow"
   - Grant access

3. GOG stores tokens:
   - Location: `~/Library/Application Support/gogcli/` (macOS)
   - Or: `~/.config/gogcli/` (Linux)

**Verify authentication:**
```bash
# Check version
gog --version

# Test email access
gog gmail search "is:inbox" --max 1 --json

# Test calendar access
gog calendar events --today --json

# Test tasks access
gog tasks lists --json
```

### Configuration Files

GOG stores configuration and credentials in:

```
~/Library/Application Support/gogcli/          # macOS
├── config.json          # Main configuration
├── credentials.json     # OAuth2 credentials
└── tokens.json          # OAuth2 tokens

~/.config/gogcli/                               # Linux
├── config.json
├── credentials.json
└── tokens.json
```

## Command Reference

### Global Flags

- `--json` : Output structured JSON (recommended for programmatic use)
- `--plain` : Output stable, parseable text (TSV format)
- `--account <email>` : Specify which account to use
- `--help` : Show help for any command

### Gmail Commands

#### `gog gmail search`

Search emails/threads using Gmail query syntax.

**Usage:**
```bash
gog gmail search <query> [flags]
```

**Flags:**
- `--max <int>` : Maximum number of results (default: 10)
- `--json` : Output as JSON
- `--page <token>` : Page token for pagination
- `--oldest` : Show first message date instead of last

**Gmail Query Syntax:**
- `is:unread` : Unread messages only
- `from:user@example.com` : From specific sender
- `to:user@example.com` : To specific recipient
- `subject:"text"` : Subject contains text
- `has:attachment` : Has attachments
- `after:2026/01/01` : After date
- `before:2026/02/01` : Before date
- Combine with `OR` and `AND`: `to:me OR cc:me`

**Example:**
```bash
gog gmail search "is:unread to:user@example.com" --max 25 --json
```

**JSON Output Schema:**
```json
{
  "nextPageToken": "string",
  "threads": [
    {
      "id": "thread_id_string",
      "date": "2026-01-28 14:32",
      "from": "Sender Name <sender@example.com>",
      "subject": "Meeting Tomorrow",
      "labels": ["INBOX", "UNREAD"],
      "messageCount": 3
    }
  ]
}
```

#### `gog gmail get`

Get a single message by ID.

**Usage:**
```bash
gog gmail get <messageId> [flags]
```

**Flags:**
- `--json` : Output as JSON
- `--format <full|metadata|raw>` : Output format (default: full)

**Example:**
```bash
gog gmail get msg_abc123 --json
```

**JSON Output Schema:**
```json
{
  "historyId": "string",
  "id": "msg_abc123",
  "threadId": "thread_xyz",
  "labelIds": ["INBOX", "UNREAD"],
  "snippet": "Email preview text...",
  "payload": {
    "headers": [
      {"name": "From", "value": "sender@example.com"},
      {"name": "To", "value": "you@example.com"},
      {"name": "Subject", "value": "Meeting Tomorrow"},
      {"name": "Date", "value": "Tue, 28 Jan 2026 14:32:00 -0800"}
    ],
    "body": {
      "data": "base64_encoded_body"
    },
    "parts": [...]
  }
}
```

#### `gog gmail thread get`

Get an entire thread with all messages.

**Usage:**
```bash
gog gmail thread get <threadId> [flags]
```

**Flags:**
- `--json` : Output as JSON
- `--download-attachments <dir>` : Download attachments to directory

**Example:**
```bash
gog gmail thread get 19c0518f3b66efe2 --json
```

**JSON Output:**
```json
{
  "thread": {
    "id": "thread_id",
    "historyId": "string",
    "messages": [
      {
        "id": "msg_id",
        "threadId": "thread_id",
        "labelIds": ["INBOX"],
        "payload": {
          "headers": [...],
          "body": {...}
        }
      }
    ]
  }
}
```

#### `gog gmail drafts create`

Create a draft email.

**Usage:**
```bash
gog gmail drafts create [flags]
```

**Flags:**
- `--to <emails>` : Recipients (comma-separated)
- `--cc <emails>` : CC recipients
- `--bcc <emails>` : BCC recipients
- `--subject <string>` : Subject (required)
- `--body <string>` : Body text (required unless --body-html)
- `--body-file <path>` : Read body from file (use `-` for stdin)
- `--body-html <string>` : HTML body
- `--reply-to-message-id <id>` : Mark as reply to message
- `--attach <paths>` : Attachment file paths (repeatable)
- `--json` : Output draft ID as JSON

**Example:**
```bash
gog gmail drafts create \
  --to "recipient@example.com" \
  --subject "Re: Meeting Tomorrow" \
  --body-file draft.txt \
  --reply-to-message-id msg_abc123 \
  --json
```

**JSON Output:**
```json
{
  "id": "draft_id_string",
  "message": {
    "id": "msg_id",
    "threadId": "thread_id",
    "labelIds": ["DRAFT"]
  }
}
```

#### `gog gmail drafts send`

Send an existing draft.

**Usage:**
```bash
gog gmail drafts send <draftId>
```

**Flags:**
- `--json` : Output confirmation as JSON

**Example:**
```bash
gog gmail drafts send draft_abc123 --json
```

#### `gog gmail send`

Send an email directly (without creating draft first).

**Usage:**
```bash
gog gmail send [flags]
```

**Flags:** Same as `drafts create`, plus:
- `--reply-all` : Auto-populate recipients from original message
- `--thread-id <id>` : Reply within a thread

**Example:**
```bash
gog gmail send \
  --to "recipient@example.com" \
  --subject "Quick Update" \
  --body "All systems operational." \
  --json
```

### Calendar Commands

#### `gog calendar events`

List calendar events.

**Usage:**
```bash
gog calendar events [<calendarId>] [flags]
```

**Arguments:**
- `<calendarId>` : Calendar ID (default: `primary`)

**Flags:**
- `--from <time>` : Start time (RFC3339, date, or relative: `today`, `tomorrow`, `monday`)
- `--to <time>` : End time
- `--today` : Today only (timezone-aware)
- `--tomorrow` : Tomorrow only
- `--week` : This week
- `--days <N>` : Next N days
- `--max <int>` : Max results (default: 10)
- `--json` : Output as JSON
- `--query <string>` : Free text search
- `--all` : Fetch from all calendars

**Examples:**
```bash
# Today's events
gog calendar events --today --json

# This week
gog calendar events --week --json

# Date range
gog calendar events --from "2026-01-28" --to "2026-02-04" --json

# Next 7 days
gog calendar events --days 7 --json
```

**JSON Output Schema:**
```json
{
  "events": [
    {
      "id": "event_id",
      "summary": "Team Standup",
      "start": {
        "dateTime": "2026-01-28T09:00:00-08:00",
        "timeZone": "America/Los_Angeles"
      },
      "end": {
        "dateTime": "2026-01-28T09:30:00-08:00",
        "timeZone": "America/Los_Angeles"
      },
      "location": "Zoom",
      "attendees": [
        {
          "email": "alice@example.com",
          "responseStatus": "accepted"
        }
      ],
      "status": "confirmed",
      "htmlLink": "https://calendar.google.com/..."
    }
  ],
  "nextPageToken": ""
}
```

#### `gog calendar freebusy`

Get free/busy information for calendars.

**Usage:**
```bash
gog calendar freebusy <calendarIds> --from <time> --to <time> [flags]
```

**Arguments:**
- `<calendarIds>` : Comma-separated calendar IDs (use `primary` for your calendar)

**Flags:**
- `--from <time>` : Start time (RFC3339, required)
- `--to <time>` : End time (RFC3339, required)
- `--json` : Output as JSON

**Example:**
```bash
gog calendar freebusy primary --from "2026-01-29T00:00:00Z" --to "2026-01-31T23:59:59Z" --json
```

**JSON Output:**
```json
{
  "calendars": {
    "primary": {
      "busy": [
        {
          "start": "2026-01-29T14:00:00Z",
          "end": "2026-01-29T15:00:00Z"
        },
        {
          "start": "2026-01-29T16:00:00Z",
          "end": "2026-01-29T17:30:00Z"
        }
      ]
    }
  }
}
```

**Use this to find available meeting slots**: Parse busy periods and identify gaps.

#### `gog calendar create`

Create a calendar event.

**Usage:**
```bash
gog calendar create <calendarId> [flags]
```

**Arguments:**
- `<calendarId>` : Calendar ID (use `primary` for your main calendar)

**Flags:**
- `--summary <string>` : Event title (required)
- `--from <time>` : Start time (RFC3339, required)
- `--to <time>` : End time (RFC3339, required)
- `--description <string>` : Event description
- `--location <string>` : Event location
- `--attendees <emails>` : Comma-separated attendee emails
- `--with-meet` : Create Google Meet video conference
- `--all-day` : All-day event
- `--reminder <method:duration>` : Custom reminders (e.g., `popup:30m`, `email:1d`)
- `--json` : Output event details as JSON

**Example:**
```bash
gog calendar create primary \
  --summary "Project Review" \
  --from "2026-01-29T14:00:00-08:00" \
  --to "2026-01-29T15:00:00-08:00" \
  --attendees "alice@example.com,bob@example.com" \
  --location "Conference Room A" \
  --with-meet \
  --json
```

**JSON Output:**
```json
{
  "id": "event_id",
  "summary": "Project Review",
  "start": {...},
  "end": {...},
  "attendees": [...],
  "hangoutLink": "https://meet.google.com/..."
}
```

### Tasks Commands

**Note**: Google Tasks requires a task list ID for most operations. Get your lists first.

#### `gog tasks lists`

List all task lists.

**Usage:**
```bash
gog tasks lists [flags]
```

**Flags:**
- `--json` : Output as JSON

**Example:**
```bash
gog tasks lists --json
```

**JSON Output:**
```json
{
  "tasklists": [
    {
      "id": "tasklistId",
      "title": "My Tasks",
      "updated": "2026-01-28T12:00:00.000Z"
    }
  ]
}
```

#### `gog tasks list`

List tasks from a specific task list.

**Usage:**
```bash
gog tasks list <tasklistId> [flags]
```

**Arguments:**
- `<tasklistId>` : Task list ID (get from `gog tasks lists`)

**Flags:**
- `--json` : Output as JSON
- `--max <int>` : Max results
- `--completed` : Show completed tasks
- `--hidden` : Show hidden tasks
- `--deleted` : Show deleted tasks

**Example:**
```bash
# Get first tasklist
TASKLIST_ID=$(gog tasks lists --json | jq -r '.tasklists[0].id')

# List tasks
gog tasks list "$TASKLIST_ID" --json
```

**JSON Output:**
```json
{
  "tasks": [
    {
      "id": "task_id",
      "etag": "string",
      "title": "Review Q1 budget",
      "updated": "2026-01-28T10:00:00.000Z",
      "status": "needsAction",
      "due": "2026-02-01T00:00:00.000Z",
      "notes": "Check all department allocations"
    }
  ]
}
```

**Status values:**
- `needsAction` : Task is open
- `completed` : Task is done

#### `gog tasks add`

Create a new task.

**Usage:**
```bash
gog tasks add <tasklistId> [flags]
```

**Arguments:**
- `<tasklistId>` : Task list ID

**Flags:**
- `--title <string>` : Task title (required)
- `--notes <string>` : Task notes/description
- `--due <date>` : Due date (RFC3339 or YYYY-MM-DD)
- `--parent <taskId>` : Parent task ID (create as subtask)
- `--json` : Output task details as JSON

**Example:**
```bash
gog tasks add "$TASKLIST_ID" \
  --title "Prepare presentation" \
  --notes "Slides for stakeholder meeting" \
  --due "2026-02-05" \
  --json
```

**JSON Output:**
```json
{
  "id": "new_task_id",
  "title": "Prepare presentation",
  "status": "needsAction",
  "notes": "Slides for stakeholder meeting",
  "due": "2026-02-05T00:00:00.000Z"
}
```

#### `gog tasks update`

Update an existing task.

**Usage:**
```bash
gog tasks update <tasklistId> <taskId> [flags]
```

**Arguments:**
- `<tasklistId>` : Task list ID
- `<taskId>` : Task ID to update

**Flags:**
- `--title <string>` : New title
- `--notes <string>` : New notes
- `--due <date>` : New due date
- `--json` : Output updated task as JSON

**Example:**
```bash
gog tasks update "$TASKLIST_ID" task_abc123 \
  --notes "Updated description" \
  --json
```

#### `gog tasks done`

Mark a task as completed.

**Usage:**
```bash
gog tasks done <tasklistId> <taskId>
```

**Example:**
```bash
gog tasks done "$TASKLIST_ID" task_abc123
```

#### `gog tasks delete`

Delete a task.

**Usage:**
```bash
gog tasks delete <tasklistId> <taskId>
```

**Example:**
```bash
gog tasks delete "$TASKLIST_ID" task_abc123
```

### Utility Commands

#### `gog --version`

Display version information.

**Example:**
```bash
gog --version
```

**Output:**
```
v0.9.0 (99d9575 2026-01-22T04:15:12Z)
```

#### `gog auth login`

Authenticate with Google.

**Example:**
```bash
gog auth login
# Opens browser for OAuth flow
```

## Common Workflows

### Email Workflow

```bash
# 1. Search unread emails
gog gmail search "is:unread" --max 25 --json

# 2. Get a specific thread
THREAD_ID=$(gog gmail search "is:unread" --max 1 --json | jq -r '.threads[0].id')
gog gmail thread get "$THREAD_ID" --json

# 3. Create a draft reply
gog gmail drafts create \
  --to "recipient@example.com" \
  --subject "Re: Topic" \
  --body "Reply text" \
  --reply-to-message-id msg_abc123 \
  --json

# 4. Send the draft
DRAFT_ID=$(gog gmail drafts list --max 1 --json | jq -r '.drafts[0].id')
gog gmail drafts send "$DRAFT_ID"
```

### Calendar Workflow

```bash
# 1. Check today's agenda
gog calendar events --today --json

# 2. Find free time tomorrow
gog calendar freebusy primary \
  --from "$(date -v+1d -u +%Y-%m-%dT00:00:00Z)" \
  --to "$(date -v+1d -u +%Y-%m-%dT23:59:59Z)" \
  --json

# 3. Create a meeting
gog calendar create primary \
  --summary "Team Sync" \
  --from "2026-01-29T14:00:00-08:00" \
  --to "2026-01-29T15:00:00-08:00" \
  --attendees "alice@example.com,bob@example.com" \
  --with-meet \
  --json
```

### Tasks Workflow

```bash
# 1. Get task list ID
TASKLIST_ID=$(gog tasks lists --json | jq -r '.tasklists[0].id')

# 2. List open tasks
gog tasks list "$TASKLIST_ID" --json

# 3. Create a task
gog tasks add "$TASKLIST_ID" \
  --title "Review contract" \
  --notes "Legal team needs feedback" \
  --due "2026-01-31" \
  --json

# 4. Complete a task
gog tasks done "$TASKLIST_ID" task_abc123
```

## Error Handling

When a command fails, GOG returns:

- Exit code: non-zero
- stderr: human-readable error message

**Common errors:**

```
Authentication failed
→ Run: gog auth login

Calendar not found
→ Use "primary" for your main calendar

Task list not found
→ Run: gog tasks lists --json to get valid IDs

Invalid date format
→ Use RFC3339: 2026-01-29T14:00:00-08:00
→ Or simple date: 2026-01-29
```

## Important Notes

### Calendar IDs

- Use `primary` for your main calendar
- Get other calendar IDs with: `gog calendar calendars --json`

### Task List IDs

- Always get tasklist ID first: `gog tasks lists --json | jq -r '.tasklists[0].id'`
- Store the ID in a variable for reuse in a session

### Date/Time Formats

GOG accepts:
- **RFC3339**: `2026-01-29T14:00:00-08:00` (preferred for API)
- **Date only**: `2026-01-29` (for all-day or tasks)
- **Relative**: `today`, `tomorrow`, `monday`

### Gmail Query Operators

Common operators for `gog gmail search`:
- `is:unread`, `is:read`, `is:starred`
- `from:email`, `to:email`, `cc:email`
- `subject:"text"`, `has:attachment`
- `after:YYYY/MM/DD`, `before:YYYY/MM/DD`
- `newer_than:2d` (2 days), `older_than:1m` (1 month)
- Combine with `OR`, `AND`, `-` (NOT)

## Troubleshooting

### "gog: command not found"

Install GOG: https://github.com/rylio/gog

Or via Homebrew:
```bash
brew install gog
```

### "Authentication failed" or "No credentials found"

Run authentication:
```bash
gog auth login
# Follow browser prompts
```

Ensure scopes include:
- `https://www.googleapis.com/auth/gmail.modify`
- `https://www.googleapis.com/auth/calendar.events`
- `https://www.googleapis.com/auth/tasks`

### "Permission denied" on calendar/tasks

Check that you've granted the necessary scopes during `gog auth login`.

### Invalid JSON output

Ensure you're using `--json` flag. Without it, GOG outputs human-readable tables.

## Additional Resources

- **GOG Repository**: https://github.com/rylio/gog
- **Gmail Query Syntax**: https://support.google.com/mail/answer/7190
- **RFC3339 Date Format**: https://www.rfc-editor.org/rfc/rfc3339
- **Google Calendar API**: https://developers.google.com/calendar
- **Google Tasks API**: https://developers.google.com/tasks
