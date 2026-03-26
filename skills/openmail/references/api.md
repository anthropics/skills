# OpenMail CLI & API Reference

Base URL: `https://api.openmail.sh`  
Authentication: `Authorization: Bearer <OPENMAIL_API_KEY>`  
All responses are JSON.

---

## CLI commands

### Send email

```bash
openmail send \
  --to "recipient@example.com" \
  --subject "Subject" \
  --body "Plain text body."

# Reply in thread (subject ignored)
openmail send \
  --to "recipient@example.com" \
  --thread-id "thr_..." \
  --body "Reply body."

# With HTML and attachments
openmail send \
  --to "recipient@example.com" \
  --subject "Report" \
  --body "See attached." \
  --body-html "<p>See attached.</p>" \
  --attach ./report.pdf \
  --attach ./data.csv
```

Flags:
- `--to` (required) — recipient address
- `--subject` (required unless `--thread-id` is set) — email subject
- `--body` (required) — plain text body
- `--body-html` — optional HTML body
- `--thread-id` — reply in an existing thread
- `--attach` — file path to attach (repeatable)
- `--inbox-id` — override default inbox

Response:

```json
{
  "id": "msg_...",
  "threadId": "thr_...",
  "inboxId": "inb_...",
  "direction": "outbound",
  "createdAt": "2024-01-01T00:00:00.000Z"
}
```

### Threads

```bash
# List unread threads (preferred for checking new mail)
openmail threads list --is-read false

# List all threads
openmail threads list

# List with pagination
openmail threads list --limit 20 --offset 0

# Get messages in a thread (oldest-first)
openmail threads get --thread-id "thr_..."

# Mark thread as read
openmail threads read --thread-id "thr_..."

# Mark thread as unread
openmail threads unread --thread-id "thr_..."
```

Thread object:

```json
{
  "id": "thr_...",
  "inboxId": "inb_...",
  "subject": "Re: Hello",
  "lastMessageAt": "2024-01-01T00:00:00.000Z",
  "isRead": false,
  "messageCount": 3
}
```

### Messages

```bash
# List inbound messages
openmail messages list --direction inbound --limit 20

# List outbound messages
openmail messages list --direction outbound

# With pagination
openmail messages list --direction inbound --limit 50 --offset 100
```

Message object:

```json
{
  "id": "msg_...",
  "threadId": "thr_...",
  "inboxId": "inb_...",
  "fromAddr": "Alice <alice@example.com>",
  "toAddr": "agent@openmail.sh",
  "subject": "Hello",
  "bodyText": "Plain text content",
  "bodyHtml": "<p>HTML content</p>",
  "direction": "inbound",
  "attachments": [
    {
      "filename": "report.pdf",
      "url": "https://...",
      "sizeBytes": 12345
    }
  ],
  "createdAt": "2024-01-01T00:00:00.000Z"
}
```

### Inboxes

```bash
# List all inboxes
openmail inbox list

# Create an inbox
openmail inbox create --mailbox-name "support" --display-name "Support"

# Get inbox details
openmail inbox get --id "inb_..."

# Delete an inbox
openmail inbox delete --id "inb_..."
```

Inbox object:

```json
{
  "id": "inb_...",
  "address": "support@example.openmail.sh",
  "displayName": "Support",
  "createdAt": "2024-01-01T00:00:00.000Z"
}
```

### Status & diagnostics

```bash
openmail status
```

Shows API connection, default inbox, and bridge status.

---

## REST API

All endpoints require `Authorization: Bearer <OPENMAIL_API_KEY>`.

### POST /v1/inboxes/{id}/send

Send an email. Requires `Idempotency-Key` header (UUID).

```http
POST /v1/inboxes/{id}/send
Authorization: Bearer om_live_...
Content-Type: application/json
Idempotency-Key: <uuid>

{
  "to": "recipient@example.com",
  "subject": "Hello",
  "body": "Plain text body.",
  "bodyHtml": "<p>HTML body.</p>",
  "threadId": "thr_...",
  "attachments": [
    {
      "filename": "file.pdf",
      "contentType": "application/pdf",
      "data": "<base64>"
    }
  ]
}
```

### GET /v1/inboxes/{id}/threads

```
GET /v1/inboxes/{id}/threads?is_read=false&limit=20&offset=0
```

### PATCH /v1/threads/{id}

```http
PATCH /v1/threads/{id}
Content-Type: application/json

{ "is_read": true }
```

### GET /v1/threads/{id}/messages

Returns messages in a thread, sorted oldest-first.

### GET /v1/inboxes/{id}/messages

```
GET /v1/inboxes/{id}/messages?direction=inbound&limit=20&offset=0
```

### GET /v1/attachments/{messageId}/{filename}

Returns attachment data. Signed URL included in message payload — fetch promptly, URLs expire.

---

## Rate limits

| Resource | Limit |
|---|---|
| Inbox creation | 100 per day |
| Send per inbox | 10 per minute, 200 per day |
| API requests | 1,000 per minute |

---

## Idempotency

The send endpoint requires an `Idempotency-Key` header. Use a unique UUID per send attempt. Retrying with the same key within 24 hours returns the original response without resending.

The CLI generates idempotency keys automatically. For direct API calls, generate a UUID:

```bash
python3 -c "import uuid; print(uuid.uuid4())"
```
