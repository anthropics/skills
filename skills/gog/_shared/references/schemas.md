# GOG Data Schemas

This document defines the JSON schemas for data objects used across GOG skills.

## Email Message Object

Represents an email message.

```json
{
  "id": "string (required) - Unique message identifier",
  "thread_id": "string - Thread/conversation identifier",
  "from": "string (required) - Sender email address",
  "from_name": "string - Sender display name",
  "to": ["string array (required) - Recipient email addresses"],
  "cc": ["string array - CC recipients"],
  "bcc": ["string array - BCC recipients"],
  "subject": "string (required) - Email subject line",
  "snippet": "string - First ~200 chars of body",
  "body_text": "string - Plain text body",
  "body_html": "string - HTML body",
  "date": "string (ISO8601) (required) - Message timestamp",
  "unread": "boolean - Whether message is unread",
  "labels": ["string array - Message labels/folders"],
  "attachments": [{
    "id": "string - Attachment identifier",
    "filename": "string - Original filename",
    "mime_type": "string - MIME type",
    "size_bytes": "integer - File size"
  }]
}
```

**Example:**
```json
{
  "id": "msg_abc123",
  "thread_id": "thread_xyz",
  "from": "alice@example.com",
  "from_name": "Alice Johnson",
  "to": ["you@example.com"],
  "cc": [],
  "subject": "Q1 Planning Session",
  "snippet": "Hi team, I wanted to schedule our Q1 planning...",
  "body_text": "Full email content here...",
  "date": "2026-01-28T14:30:00Z",
  "unread": true,
  "labels": ["INBOX", "IMPORTANT"],
  "attachments": []
}
```

## Task Object

Represents a task or todo item.

```json
{
  "id": "string (required) - Unique task identifier",
  "title": "string (required) - Task title",
  "description": "string - Detailed task description",
  "status": "string (required) - One of: open, completed, blocked, waiting",
  "priority": "string - One of: P0, P1, P2, P3 (P0 = most urgent)",
  "category": "string - One of: Work, Personal, Errands, Admin",
  "due_date": "string (YYYY-MM-DD) - Due date",
  "created_at": "string (ISO8601) (required) - Creation timestamp",
  "updated_at": "string (ISO8601) - Last update timestamp",
  "completed_at": "string (ISO8601) - Completion timestamp",
  "tags": ["string array - Custom tags"],
  "related_email_id": "string - Associated email message ID",
  "notes": "string - Additional notes"
}
```

**Priority Levels:**
- **P0**: Critical, must be done immediately
- **P1**: High priority, should be done soon
- **P2**: Medium priority, do when possible
- **P3**: Low priority, nice to have

**Categories:**
- **Work**: Professional/job-related tasks
- **Personal**: Personal life tasks
- **Errands**: Shopping, appointments, calls
- **Admin**: Bureaucratic/administrative tasks

**Example:**
```json
{
  "id": "task_def456",
  "title": "Review contract proposal",
  "description": "Legal team needs feedback by Friday",
  "status": "open",
  "priority": "P1",
  "category": "Work",
  "due_date": "2026-01-31",
  "created_at": "2026-01-28T09:00:00Z",
  "tags": ["legal", "contracts"],
  "related_email_id": "msg_contract123"
}
```

## Calendar Event Object

Represents a calendar event.

```json
{
  "id": "string (required) - Unique event identifier",
  "title": "string (required) - Event title",
  "description": "string - Event description",
  "start": "string (ISO8601) (required) - Start date/time",
  "end": "string (ISO8601) (required) - End date/time",
  "location": "string - Event location (physical or virtual)",
  "attendees": [{
    "email": "string (required)",
    "name": "string",
    "status": "string - accepted, declined, tentative, needs-action"
  }],
  "organizer": {
    "email": "string",
    "name": "string"
  },
  "status": "string - confirmed, tentative, cancelled",
  "all_day": "boolean - Whether this is an all-day event",
  "recurrence": "string - Recurrence rule (RFC5545)",
  "reminders": [{
    "minutes_before": "integer",
    "method": "string - email, popup, sms"
  }],
  "conference_link": "string - Video conference URL"
}
```

**Example:**
```json
{
  "id": "event_ghi789",
  "title": "Team Standup",
  "description": "Daily team sync",
  "start": "2026-01-28T09:00:00Z",
  "end": "2026-01-28T09:30:00Z",
  "location": "Zoom",
  "attendees": [
    {
      "email": "alice@example.com",
      "name": "Alice Johnson",
      "status": "accepted"
    },
    {
      "email": "bob@example.com",
      "name": "Bob Smith",
      "status": "tentative"
    }
  ],
  "organizer": {
    "email": "you@example.com",
    "name": "You"
  },
  "status": "confirmed",
  "all_day": false,
  "conference_link": "https://zoom.us/j/123456789"
}
```

## Follow-up Item Object

Represents a follow-up tracking item.

```json
{
  "id": "string (required) - Unique follow-up identifier",
  "email_id": "string - Associated email message ID",
  "thread_id": "string - Associated thread ID",
  "person": "string (required) - Person to follow up with (email or name)",
  "topic": "string (required) - What the follow-up is about",
  "context": "string - Additional context/notes",
  "last_touch": "string (ISO8601) (required) - Last interaction timestamp",
  "next_nudge_date": "string (YYYY-MM-DD) (required) - When to send follow-up",
  "nudge_count": "integer - Number of times followed up",
  "status": "string (required) - One of: pending, contacted, responded, closed",
  "priority": "string - One of: high, medium, low",
  "created_at": "string (ISO8601) (required) - Creation timestamp",
  "closed_at": "string (ISO8601) - When follow-up was closed"
}
```

**Status Values:**
- **pending**: Awaiting initial follow-up
- **contacted**: Follow-up sent, awaiting response
- **responded**: They responded, may need further action
- **closed**: Follow-up complete/no longer needed

**Example:**
```json
{
  "id": "followup_jkl012",
  "email_id": "msg_sent456",
  "thread_id": "thread_abc",
  "person": "charlie@vendor.com",
  "topic": "Pricing proposal for Q2",
  "context": "Sent proposal on Jan 20, they said they'd review by end of week",
  "last_touch": "2026-01-20T16:00:00Z",
  "next_nudge_date": "2026-01-30",
  "nudge_count": 0,
  "status": "pending",
  "priority": "high",
  "created_at": "2026-01-20T16:05:00Z"
}
```

## Email Triage Classification

Categories used for email triage:

```json
{
  "urgency": "string (required) - One of: urgent, high, medium, low",
  "category": "string (required) - One of: action-required, fyi, meeting, social, newsletter, spam",
  "suggested_action": "string (required) - One of: reply, reply-all, forward, archive, create-task, schedule-meeting, block-sender, delete"
}
```

**Urgency Levels:**
- **urgent**: Immediate attention required (< 2 hours)
- **high**: Should respond today
- **medium**: Can respond within 2-3 days
- **low**: No time pressure

**Categories:**
- **action-required**: Needs a decision or action from you
- **fyi**: Informational only, no action needed
- **meeting**: Meeting invitation or scheduling
- **social**: Personal correspondence
- **newsletter**: Automated newsletters/updates
- **spam**: Likely spam or unwanted

**Example:**
```json
{
  "urgency": "high",
  "category": "action-required",
  "suggested_action": "reply"
}
```

## Draft Email Object

Represents a draft email in preparation.

```json
{
  "draft_id": "string - Draft identifier (if saved)",
  "to": ["string array (required) - Recipients"],
  "cc": ["string array - CC recipients"],
  "subject": "string (required) - Email subject",
  "body": "string (required) - Email body text",
  "reply_to_id": "string - Original message ID if this is a reply",
  "assumptions": ["string array - Assumptions made while drafting"],
  "questions": ["string array - Questions to confirm before sending"],
  "tone": "string - professional, friendly, concise, detailed, etc."
}
```

**Example:**
```json
{
  "to": ["vendor@example.com"],
  "cc": ["manager@example.com"],
  "subject": "Re: Q2 Pricing Proposal",
  "body": "Hi [Name],\n\nThank you for the proposal...",
  "reply_to_id": "msg_abc123",
  "assumptions": [
    "Budget approved for Q2",
    "3-year contract term is acceptable"
  ],
  "questions": [
    "Should we negotiate payment terms?",
    "Do we need legal review first?"
  ],
  "tone": "professional"
}
```

## Time Slot Object

Represents an available calendar time slot.

```json
{
  "start": "string (ISO8601) (required) - Slot start time",
  "end": "string (ISO8601) (required) - Slot end time",
  "duration_minutes": "integer - Duration in minutes"
}
```

**Example:**
```json
{
  "start": "2026-01-29T14:00:00Z",
  "end": "2026-01-29T15:00:00Z",
  "duration_minutes": 60
}
```

## Audit Log Entry

Represents an audit log entry for actions taken by GOG skills.

```json
{
  "timestamp": "string (ISO8601) (required) - When action occurred",
  "skill": "string (required) - Skill that performed action",
  "action": "string (required) - Action type (send-email, create-task, etc.)",
  "entity_id": "string - ID of affected entity",
  "details": {
    "arbitrary fields specific to action type"
  },
  "user_confirmation": "boolean - Whether user explicitly confirmed"
}
```

**Example:**
```json
{
  "timestamp": "2026-01-28T15:30:00Z",
  "skill": "gog-email-send",
  "action": "send-email",
  "entity_id": "msg_sent789",
  "details": {
    "to": ["recipient@example.com"],
    "subject": "Follow-up on proposal",
    "draft_id": "draft_abc"
  },
  "user_confirmation": true
}
```

## Notes

- All timestamps use ISO8601 format with timezone (prefer UTC)
- All date-only fields use YYYY-MM-DD format
- Email addresses should be validated as RFC5322 compliant
- All IDs are strings to accommodate various backend systems
- Arrays may be empty but should not be null
- Optional string fields may be empty string or omitted entirely
