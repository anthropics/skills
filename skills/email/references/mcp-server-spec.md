# MCP Server Spec: Microsoft Graph API Email Connector

This document specifies a future MCP server for full read/write email access via the Microsoft Graph API. Use this when the built-in M365 connectors are unavailable or when you need a self-hosted, standalone solution.

---

## Overview

A Model Context Protocol (MCP) server that wraps the Microsoft Graph API `/me/messages` endpoints, providing Claude with full email CRUD operations authenticated via OAuth 2.0.

---

## Authentication: OAuth 2.0 with PKCE

### App Registration (Microsoft Entra)

1. Register an app in Microsoft Entra ID (Azure AD)
2. Set platform to "Mobile and desktop applications" with redirect URI `http://localhost:<port>/callback`
3. Request these **delegated** permissions:
   - `Mail.Read` -- Read emails
   - `Mail.ReadWrite` -- Modify emails (flag, move, categorize, create drafts)
   - `Mail.Send` -- Send emails on behalf of user
   - `MailboxSettings.Read` -- Read mailbox settings (timezone, auto-replies)
   - `Calendars.Read` -- (Optional) Check calendar for meeting context

### Token Flow

```
1. Generate code_verifier (random 43-128 char string)
2. Create code_challenge = BASE64URL(SHA256(code_verifier))
3. Open browser to: https://login.microsoftonline.com/{tenant}/oauth2/v2.0/authorize
   ?client_id={app_id}&response_type=code&redirect_uri={redirect}
   &scope=Mail.Read Mail.ReadWrite Mail.Send MailboxSettings.Read
   &code_challenge={code_challenge}&code_challenge_method=S256
4. User consents, receives authorization_code at redirect URI
5. Exchange code for tokens at: POST https://login.microsoftonline.com/{tenant}/oauth2/v2.0/token
   body: client_id, code, redirect_uri, code_verifier, grant_type=authorization_code
6. Store access_token (valid ~1 hour) and refresh_token (encrypted)
7. Use access_token as: Authorization: Bearer {token}
8. Refresh when expired using refresh_token
```

---

## MCP Tool Definitions

### `search_emails`
Search and filter emails from the user's mailbox.

| Parameter | Type | Required | Description |
|---|---|---|---|
| query | string | no | Search text (searches subject, body, sender) |
| folder | string | no | Folder name (default: "Inbox") |
| is_read | boolean | no | Filter by read status |
| from | string | no | Filter by sender email |
| received_after | string | no | ISO 8601 datetime -- emails after this date |
| received_before | string | no | ISO 8601 datetime -- emails before this date |
| importance | string | no | "low", "normal", "high" |
| has_attachments | boolean | no | Filter for emails with attachments |
| top | integer | no | Max results (default: 25, max: 50) |

**Graph endpoint**: `GET /me/mailFolders('{folder}')/messages?$filter=...&$search="..."`

### `read_email`
Read the full content of a specific email.

| Parameter | Type | Required | Description |
|---|---|---|---|
| message_id | string | yes | The email message ID |

**Graph endpoint**: `GET /me/messages/{id}`

### `create_draft`
Create a draft email (does NOT send).

| Parameter | Type | Required | Description |
|---|---|---|---|
| subject | string | yes | Email subject line |
| body | string | yes | Email body (HTML supported) |
| to | string[] | yes | Recipient email addresses |
| cc | string[] | no | CC recipients |
| importance | string | no | "low", "normal", "high" |

**Graph endpoint**: `POST /me/messages` (creates draft without sending)

### `create_draft_reply`
Create a draft reply to an existing email (does NOT send).

| Parameter | Type | Required | Description |
|---|---|---|---|
| message_id | string | yes | Original message ID to reply to |
| body | string | yes | Reply body text |
| reply_all | boolean | no | Reply to all recipients (default: false) |

**Graph endpoint**: `POST /me/messages/{id}/createReply` then `PATCH` with body content

### `send_draft`
Send a previously created draft email.

| Parameter | Type | Required | Description |
|---|---|---|---|
| message_id | string | yes | Draft message ID |

**Graph endpoint**: `POST /me/messages/{id}/send`

### `forward_email`
Forward an email to specified recipients.

| Parameter | Type | Required | Description |
|---|---|---|---|
| message_id | string | yes | Message ID to forward |
| to | string[] | yes | Forward recipient emails |
| comment | string | no | Comment to add above forwarded content |

**Graph endpoint**: `POST /me/messages/{id}/forward`

### `move_email`
Move an email to a different folder.

| Parameter | Type | Required | Description |
|---|---|---|---|
| message_id | string | yes | Message ID to move |
| destination_folder | string | yes | Target folder name or ID |

**Graph endpoint**: `POST /me/messages/{id}/move`

### `flag_email`
Set or clear a follow-up flag on an email.

| Parameter | Type | Required | Description |
|---|---|---|---|
| message_id | string | yes | Message ID |
| flag_status | string | yes | "flagged", "complete", "notFlagged" |

**Graph endpoint**: `PATCH /me/messages/{id}` with `{"flag": {"flagStatus": "..."}}`

### `categorize_email`
Apply categories (color tags) to an email.

| Parameter | Type | Required | Description |
|---|---|---|---|
| message_id | string | yes | Message ID |
| categories | string[] | yes | Category names to apply |

**Graph endpoint**: `PATCH /me/messages/{id}` with `{"categories": [...]}`

### `mark_read`
Mark an email as read or unread.

| Parameter | Type | Required | Description |
|---|---|---|---|
| message_id | string | yes | Message ID |
| is_read | boolean | yes | true = read, false = unread |

**Graph endpoint**: `PATCH /me/messages/{id}` with `{"isRead": true/false}`

---

## Reference Implementations

These open-source projects implement similar functionality and serve as implementation references:

- **Softeria ms-365-mcp-server** (github.com/softeria/ms-365-mcp-server) -- Full M365 MCP server with read-only mode support and tool filtering
- **XenoXilus outlook-mcp** (github.com/XenoXilus/outlook-mcp) -- Email, calendar, and SharePoint via Graph API
- **mcp-outlook on PyPI** (pypi.org/project/mcp-outlook/) -- Python-based MCP server for Outlook

---

## Rate Limiting

Microsoft Graph API enforces per-app and per-user throttling. Key limits:
- 10,000 API requests per 10 minutes per app per tenant
- Respect HTTP 429 responses with `Retry-After` header
- Batch related operations where possible (`POST /$batch` for up to 20 requests)
- Use delta queries (`/me/mailFolders('Inbox')/messages/delta`) for efficient synchronization of inbox changes
