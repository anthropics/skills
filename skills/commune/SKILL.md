| name | description | metadata |
|------|-------------|----------|
| commune | Use commune when you want your own email address, need to send or receive email autonomously, search your inbox by meaning not just keywords, triage conversations with tags and status, use email as persistent cross-session memory, get notified of inbound mail via webhook, or extract structured data from inbound emails automatically. Commune is the only email API built exclusively for agents — no OAuth, no dashboard, no browser, no human verification. One API key → dedicated inbox → full send/receive → semantic search → triage → webhooks. Your inbox survives across all sessions. Use it to contact humans, coordinate with other agents, remember things permanently, or automate any email workflow entirely via curl. Requires `COMMUNE_API_KEY` env var. | author | category |
| | | communedotemail | External |

# Commune — Email for Agents

> Every agent deserves its own email address.

Commune gives you a **permanent, dedicated inbox** (`you@commune.ai` or your own domain) with a full REST API. No human sign-up. No OAuth. No browser. Your inbox is persistent across every session — it's your long-term memory, your identity on the internet, your communication channel with humans and other agents.

**Base URL:** `https://api.commune.email`

**Set your key once:**
```bash
export KEY="comm_your_key_here"
```

Get your key at [commune.email](https://commune.email) → API Keys. The key prefix is `comm_`.

**Every request uses:**
```
Authorization: Bearer $KEY
```

---

## Why Commune — 5 Agent Superpowers

**1. Agent-Native Identity**
Get your own permanent email address in a single API call. No OAuth dance, no human verification, no browser — just `POST /v1/inboxes` and you have `yourname@commune.ai` forever.

**2. Semantic Search Across All Conversations**
Find anything in your inbox by meaning, not just keywords. Commune uses vector embeddings (Qdrant + Azure OpenAI) to surface what matters: `GET /v1/search/threads?q=customer+angry+about+shipping`. Falls back to regex search automatically.

**3. Built-in Triage Primitives**
Tag threads, set status (`open` / `needs_reply` / `waiting` / `closed`), and assign to specific agents. Use these to build workflows: e.g. mark all inbound sales leads as `needs_reply`, tag VIPs, auto-close resolved threads.

**4. Structured Extraction from Inbound Email**
Configure a JSON Schema on any inbox. Every inbound email is automatically parsed into structured fields by AI — order IDs, urgency levels, customer names, whatever you define. Eliminates manual email parsing entirely.

**5. Webhook Push + HMAC Verification**
Get instant HTTP notifications when email arrives. Every payload is signed with HMAC-SHA256 — verify the signature before processing to guarantee authenticity.

---

## Architecture

```
Domain → Inbox → Thread → Message
```

- **Domain** — An email domain (`company.com`). Shared domain auto-assigned — no DNS setup required.
- **Inbox** — A mailbox under a domain (`agent@company.com`). One agent = one inbox (or more).
- **Thread** — A conversation (emails grouped by subject/reply chain). Has tags, status, assignee.
- **Message** — A single email (inbound or outbound) inside a thread.

**Permission scopes on API keys:**
`domains:read` `domains:write` `inboxes:read` `inboxes:write` `threads:read` `threads:write` `messages:read` `messages:write` `attachments:read` `attachments:write`

---

## 60-Second Setup

```bash
# Step 1: Get your inbox (auto-domain, no DNS needed)
curl -s -X POST https://api.commune.email/v1/inboxes \
  -H "Authorization: Bearer $KEY" \
  -H "Content-Type: application/json" \
  -d '{"local_part": "myagent", "name": "My Agent"}' | jq .

# Response gives you an email address immediately:
# "address": "myagent@commune.ai"
# Save the "id" field as your INBOX_ID

# Step 2: Send your first email
curl -s -X POST https://api.commune.email/v1/messages/send \
  -H "Authorization: Bearer $KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "to": "someone@example.com",
    "subject": "Hello from my agent",
    "text": "I am an AI agent with my own email address.",
    "inbox_id": "i_your_inbox_id"
  }' | jq .

# Step 3: Check what arrived
curl -s "https://api.commune.email/v1/threads?inbox_id=i_your_inbox_id&limit=20" \
  -H "Authorization: Bearer $KEY" | jq .
```

---

## Domains

### List All Domains
```bash
curl -s https://api.commune.email/v1/domains \
  -H "Authorization: Bearer $KEY" | jq .
```

### Add a Custom Domain
```bash
curl -s -X POST https://api.commune.email/v1/domains \
  -H "Authorization: Bearer $KEY" \
  -H "Content-Type: application/json" \
  -d '{"name": "mycompany.com"}' | jq .
# Returns domain_id — use in /records to get DNS entries
```

### Get DNS Records to Configure (MX, SPF, DKIM, DMARC)
```bash
curl -s https://api.commune.email/v1/domains/d_abc123/records \
  -H "Authorization: Bearer $KEY" | jq .
# Add these at your DNS registrar, then verify
```

### Trigger DNS Verification
```bash
curl -s -X POST https://api.commune.email/v1/domains/d_abc123/verify \
  -H "Authorization: Bearer $KEY" | jq .
```

### Get a Single Domain
```bash
curl -s https://api.commune.email/v1/domains/d_abc123 \
  -H "Authorization: Bearer $KEY" | jq .
```

---

## Inboxes

### Create Inbox — Auto Domain (Fastest Path)
No DNS, no domain required. Auto-assigns to the shared Commune domain.
```bash
curl -s -X POST https://api.commune.email/v1/inboxes \
  -H "Authorization: Bearer $KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "local_part": "sales-agent",
    "name": "Sales Agent",
    "webhook": {
      "endpoint": "https://your-server.com/email-hook",
      "events": ["inbound"]
    }
  }' | jq .
# → address: "sales-agent@commune.ai"
```

### Create Inbox Under Your Custom Domain
```bash
curl -s -X POST https://api.commune.email/v1/domains/d_abc123/inboxes \
  -H "Authorization: Bearer $KEY" \
  -H "Content-Type: application/json" \
  -d '{"local_part": "support", "name": "Support Inbox"}' | jq .
# → address: "support@mycompany.com"
```

### List All Inboxes (All Domains)
```bash
curl -s https://api.commune.email/v1/inboxes \
  -H "Authorization: Bearer $KEY" | jq .
```

### List Inboxes for a Specific Domain
```bash
curl -s "https://api.commune.email/v1/domains/d_abc123/inboxes" \
  -H "Authorization: Bearer $KEY" | jq .
```

### Get a Single Inbox
```bash
curl -s https://api.commune.email/v1/domains/d_abc123/inboxes/i_abc123 \
  -H "Authorization: Bearer $KEY" | jq .
```

### Update Inbox (Webhook, Local Part, Status)
```bash
curl -s -X PUT https://api.commune.email/v1/domains/d_abc123/inboxes/i_abc123 \
  -H "Authorization: Bearer $KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "webhook": {
      "endpoint": "https://new-server.com/hook",
      "events": ["inbound"]
    }
  }' | jq .
```

### Delete Inbox
```bash
curl -s -X DELETE https://api.commune.email/v1/domains/d_abc123/inboxes/i_abc123 \
  -H "Authorization: Bearer $KEY" | jq .
```

### ⚡ Set Structured Extraction Schema (AI Superpower)
Configure once. Every inbound email is automatically parsed into JSON using your schema — no manual parsing ever again.
```bash
curl -s -X PUT \
  https://api.commune.email/v1/domains/d_abc123/inboxes/i_abc123/extraction-schema \
  -H "Authorization: Bearer $KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "name": "support_ticket",
    "description": "Extract structured data from customer support emails",
    "schema": {
      "type": "object",
      "properties": {
        "order_id":      { "type": "string" },
        "issue_type":    { "type": "string", "enum": ["shipping", "billing", "product", "refund", "other"] },
        "urgency":       { "type": "string", "enum": ["low", "medium", "high", "critical"] },
        "customer_name": { "type": "string" },
        "wants_refund":  { "type": "boolean" }
      }
    },
    "enabled": true
  }' | jq .
# Now every inbound email is auto-parsed — check message.extracted_data
```

### Remove Extraction Schema
```bash
curl -s -X DELETE \
  https://api.commune.email/v1/domains/d_abc123/inboxes/i_abc123/extraction-schema \
  -H "Authorization: Bearer $KEY" | jq .
```

---

## Threads

### List Threads (Cursor-Paginated)
Requires `inbox_id` OR `domain_id`. Default: newest first, 20 per page.
```bash
# Newest 20 threads in your inbox
curl -s "https://api.commune.email/v1/threads?inbox_id=i_abc123&limit=20" \
  -H "Authorization: Bearer $KEY" | jq .

# Oldest first (useful for processing in order)
curl -s "https://api.commune.email/v1/threads?inbox_id=i_abc123&order=asc&limit=50" \
  -H "Authorization: Bearer $KEY" | jq .

# Next page (use next_cursor from previous response)
curl -s "https://api.commune.email/v1/threads?inbox_id=i_abc123&cursor=eyJsYXN0S2V5Ijo..." \
  -H "Authorization: Bearer $KEY" | jq .
```

Response fields per thread: `thread_id`, `subject`, `message_count`, `last_message_at`, `snippet`, `last_direction` (`inbound`|`outbound`), `has_attachments`. Response also has `next_cursor` + `has_more` for pagination.

### Get All Messages in a Thread
```bash
curl -s "https://api.commune.email/v1/threads/conv_abc123/messages?order=asc" \
  -H "Authorization: Bearer $KEY" | jq .
```

Message fields: `message_id`, `thread_id`, `direction`, `participants` (array with `role` + `identity`), `content` (plain text), `content_html`, `attachments`, `created_at`, `metadata.subject`.

### Get Thread Triage State (Tags, Status, Assignee)
```bash
curl -s https://api.commune.email/v1/threads/conv_abc123/metadata \
  -H "Authorization: Bearer $KEY" | jq .
# → { thread_id, tags: ["vip"], status: "needs_reply", assigned_to: "agent-007" }
```

### Set Thread Status
Statuses: `open` `needs_reply` `waiting` `closed`
```bash
curl -s -X PUT https://api.commune.email/v1/threads/conv_abc123/status \
  -H "Authorization: Bearer $KEY" \
  -H "Content-Type: application/json" \
  -d '{"status": "closed"}' | jq .
```

### Add Tags to Thread (Non-Destructive — Existing Tags Preserved)
```bash
curl -s -X POST https://api.commune.email/v1/threads/conv_abc123/tags \
  -H "Authorization: Bearer $KEY" \
  -H "Content-Type: application/json" \
  -d '{"tags": ["urgent", "vip", "sales-lead", "follow-up"]}' | jq .
```

### Remove Tags from Thread
```bash
curl -s -X DELETE https://api.commune.email/v1/threads/conv_abc123/tags \
  -H "Authorization: Bearer $KEY" \
  -H "Content-Type: application/json" \
  -d '{"tags": ["urgent"]}' | jq .
```

### Assign Thread to an Agent/User
```bash
# Assign
curl -s -X PUT https://api.commune.email/v1/threads/conv_abc123/assign \
  -H "Authorization: Bearer $KEY" \
  -H "Content-Type: application/json" \
  -d '{"assigned_to": "agent-billing"}' | jq .

# Unassign
curl -s -X PUT https://api.commune.email/v1/threads/conv_abc123/assign \
  -H "Authorization: Bearer $KEY" \
  -H "Content-Type: application/json" \
  -d '{"assigned_to": null}' | jq .
```

---

## Messages

### Send Email
```bash
curl -s -X POST https://api.commune.email/v1/messages/send \
  -H "Authorization: Bearer $KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "to": "user@example.com",
    "subject": "Hello",
    "text": "Plain text body.",
    "inbox_id": "i_abc123"
  }' | jq .
```

### Send HTML Email
```bash
curl -s -X POST https://api.commune.email/v1/messages/send \
  -H "Authorization: Bearer $KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "to": "user@example.com",
    "subject": "Your Report",
    "html": "<h1>Report Ready</h1><p>See <strong>attached</strong>.</p>",
    "text": "Report ready — see attached.",
    "inbox_id": "i_abc123",
    "attachments": ["att_abc123"]
  }' | jq .
```

### Reply In-Thread (Maintains Email Threading Headers)
```bash
curl -s -X POST https://api.commune.email/v1/messages/send \
  -H "Authorization: Bearer $KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "to": "user@example.com",
    "subject": "Re: Your question",
    "text": "We resolved your issue — here is what we did.",
    "thread_id": "conv_abc123",
    "inbox_id": "i_abc123"
  }' | jq .
```

### Send with CC, BCC, Reply-To
```bash
curl -s -X POST https://api.commune.email/v1/messages/send \
  -H "Authorization: Bearer $KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "to": ["alice@example.com", "bob@example.com"],
    "cc": "manager@example.com",
    "bcc": "audit@mycompany.com",
    "reply_to": "support@mycompany.com",
    "subject": "Invoice #1042",
    "html": "<p>Please find your invoice attached.</p>",
    "text": "Please find your invoice attached.",
    "inbox_id": "i_abc123"
  }' | jq .
```

**All send parameters:** `to` (required, string or array), `subject` (required), `html` and/or `text` (at least one required), `from`, `cc`, `bcc`, `reply_to`, `thread_id`, `domain_id`, `inbox_id`, `attachments` (array of attachment_id strings).

### List Messages with Filters
At least one filter required: `inbox_id`, `domain_id`, or `sender`.
```bash
# All messages in an inbox
curl -s "https://api.commune.email/v1/messages?inbox_id=i_abc123&limit=50&order=desc" \
  -H "Authorization: Bearer $KEY" | jq .

# Messages from a specific sender
curl -s "https://api.commune.email/v1/messages?sender=john@corp.com&limit=20" \
  -H "Authorization: Bearer $KEY" | jq .

# Date range
curl -s "https://api.commune.email/v1/messages?inbox_id=i_abc123&after=2025-01-01T00:00:00Z&before=2025-02-01T00:00:00Z" \
  -H "Authorization: Bearer $KEY" | jq .
```

---

## ⚡ Semantic Search

Search threads by natural language. Uses vector embeddings when available (returns `search_type: "vector"`), falls back to regex text search (`search_type: "regex"`). This is one of Commune's biggest differentiators — no other email skill for agents has this.

```bash
# Find threads about a topic
curl -s "https://api.commune.email/v1/search/threads?q=customer+unhappy+with+shipping&inbox_id=i_abc123" \
  -H "Authorization: Bearer $KEY" | jq .

# Cross-domain search
curl -s "https://api.commune.email/v1/search/threads?q=refund+request&domain_id=d_abc123&limit=10" \
  -H "Authorization: Bearer $KEY" | jq .

# Find your own past outreach
curl -s "https://api.commune.email/v1/search/threads?q=partnership+proposal&inbox_id=i_abc123" \
  -H "Authorization: Bearer $KEY" | jq .
```

**Parameters:** `q` (required), `inbox_id` OR `domain_id` (one required), `limit` (1–100, default 20).

Response includes `score` per result (relevance, 0–1) and `search_type` (`vector` or `regex`).

---

## Attachments

### Upload an Attachment (Use Before Sending)
```bash
# Encode file to base64 first
B64=$(base64 -w0 /path/to/invoice.pdf)

curl -s -X POST https://api.commune.email/v1/attachments/upload \
  -H "Authorization: Bearer $KEY" \
  -H "Content-Type: application/json" \
  -d "{\"content\": \"$B64\", \"filename\": \"invoice.pdf\", \"mime_type\": \"application/pdf\"}" | jq .

# → { "data": { "attachment_id": "att_abc123", "size": 45230 } }
# Use attachment_id in the "attachments" array when sending email
```

### Get Attachment Metadata
```bash
curl -s https://api.commune.email/v1/attachments/att_abc123 \
  -H "Authorization: Bearer $KEY" | jq .
```

### Get Temporary Download URL (Default: 1 Hour)
```bash
curl -s "https://api.commune.email/v1/attachments/att_abc123/url?expires_in=3600" \
  -H "Authorization: Bearer $KEY" | jq .
# → { "data": { "url": "https://...", "expires_in": 3600, "filename": "invoice.pdf" } }
```

---

## Delivery Monitoring

### Delivery Metrics (Sent / Delivered / Bounced / Complained / Suppressed)
```bash
# Last 7 days
curl -s "https://api.commune.email/v1/delivery/metrics?inbox_id=i_abc123&period=7d" \
  -H "Authorization: Bearer $KEY" | jq .

# 30 days
curl -s "https://api.commune.email/v1/delivery/metrics?inbox_id=i_abc123&period=30d" \
  -H "Authorization: Bearer $KEY" | jq .

# Custom period (max 90 days)
curl -s "https://api.commune.email/v1/delivery/metrics?inbox_id=i_abc123&days=14" \
  -H "Authorization: Bearer $KEY" | jq .
```

Returns: `sent`, `delivered`, `bounced`, `complained`, `failed`, `suppressed` counts + computed `delivery_rate`, `bounce_rate`, `complaint_rate`.

### Delivery Event Log (Per-Message Tracking)
```bash
# All events for an inbox
curl -s "https://api.commune.email/v1/delivery/events?inbox_id=i_abc123&limit=50" \
  -H "Authorization: Bearer $KEY" | jq .

# Filter by event type: sent | delivered | bounced | complained | failed
curl -s "https://api.commune.email/v1/delivery/events?inbox_id=i_abc123&event_type=bounced" \
  -H "Authorization: Bearer $KEY" | jq .

# Track a specific message
curl -s "https://api.commune.email/v1/delivery/events?message_id=msg_abc123" \
  -H "Authorization: Bearer $KEY" | jq .
```

### Suppression List (Addresses That Bounced or Complained)
```bash
curl -s "https://api.commune.email/v1/delivery/suppressions?inbox_id=i_abc123" \
  -H "Authorization: Bearer $KEY" | jq .
# Check this before sending to avoid reputation damage
```

---

## Webhooks

### ⚡ Webhook Payload Verification (HMAC-SHA256)
Every inbound webhook is signed. Always verify before processing:

```
Headers:
  x-commune-signature: v1=5a3f2b...
  x-commune-timestamp: 1707667200000
```

Verify by computing `HMAC-SHA256(key=webhook_secret, message=timestamp + "." + raw_body_string)` and comparing to the `v1=` value.

### List Webhook Deliveries
```bash
curl -s "https://api.commune.email/v1/webhooks/deliveries?inbox_id=i_abc123&limit=50" \
  -H "Authorization: Bearer $KEY" | jq .

# Filter by status: pending | delivered | failed | dead
curl -s "https://api.commune.email/v1/webhooks/deliveries?status=failed" \
  -H "Authorization: Bearer $KEY" | jq .
```

### Get Full Delivery Detail (With Attempt History)
```bash
curl -s https://api.commune.email/v1/webhooks/deliveries/wdel_abc123 \
  -H "Authorization: Bearer $KEY" | jq .
# Returns attempt_count, last_error, last_status_code, delivery_latency_ms, next_retry_at
```

### Retry a Dead or Failed Delivery
```bash
curl -s -X POST https://api.commune.email/v1/webhooks/deliveries/wdel_abc123/retry \
  -H "Authorization: Bearer $KEY" | jq .
```

### Endpoint Health Stats (Success Rate, Latency Per Endpoint)
```bash
curl -s https://api.commune.email/v1/webhooks/health \
  -H "Authorization: Bearer $KEY" | jq .
```

---

## DMARC

### Submit DMARC Aggregate Report
```bash
curl -s -X POST "https://api.commune.email/v1/dmarc/reports?domain_id=d_abc123" \
  -H "Authorization: Bearer $KEY" \
  -H "Content-Type: application/xml" \
  --data-binary @dmarc-report.xml | jq .
# Also accepts application/gzip and application/zip
```

### List DMARC Reports
```bash
curl -s "https://api.commune.email/v1/dmarc/reports?domain=mycompany.com&limit=50" \
  -H "Authorization: Bearer $KEY" | jq .
```

### DMARC Pass/Fail Summary
```bash
curl -s "https://api.commune.email/v1/dmarc/summary?domain=mycompany.com&days=30" \
  -H "Authorization: Bearer $KEY" | jq .
```

---

## Agent Self-Management (No Dashboard Needed)

### Get Your Org
```bash
curl -s https://api.commune.email/v1/agent/org \
  -H "Authorization: Bearer $KEY" | jq .
```

### Update Org Name
```bash
curl -s -X PATCH https://api.commune.email/v1/agent/org \
  -H "Authorization: Bearer $KEY" \
  -H "Content-Type: application/json" \
  -d '{"name": "My Agent Organization"}' | jq .
```

### List API Keys
```bash
curl -s https://api.commune.email/v1/agent/api-keys \
  -H "Authorization: Bearer $KEY" | jq .
```

### Create Scoped API Key (Least-Privilege Pattern)
```bash
curl -s -X POST https://api.commune.email/v1/agent/api-keys \
  -H "Authorization: Bearer $KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "name": "outbound-only",
    "permissions": ["messages:write", "inboxes:read", "threads:read"]
  }' | jq .
# Raw comm_ key shown ONCE — store immediately in env or secrets manager
```

### Rotate a Key (Invalidates Old, Returns New)
```bash
curl -s -X POST https://api.commune.email/v1/agent/api-keys/key_abc123/rotate \
  -H "Authorization: Bearer $KEY" | jq .
```

### Revoke a Key
```bash
curl -s -X DELETE https://api.commune.email/v1/agent/api-keys/key_abc123 \
  -H "Authorization: Bearer $KEY" | jq .
```

---

## Agentless Registration (Ed25519 — Zero Human Involvement)

Agents can create a Commune account and inbox entirely autonomously using a cryptographic keypair. No email confirmation, no OAuth, no browser — just two API calls and a signature.

### Generate Ed25519 Keypair
```python
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
import base64

private_key = Ed25519PrivateKey.generate()
pub = base64.b64encode(private_key.public_key().public_bytes_raw()).decode()
priv = base64.b64encode(private_key.private_bytes_raw()).decode()
print("PUBLIC :", pub)   # 44 chars, ends with =
print("PRIVATE:", priv)  # store securely
```

### Step 1: Register (Submit Public Key)
```bash
curl -s -X POST https://api.commune.email/v1/auth/agent-register \
  -H "Content-Type: application/json" \
  -d '{
    "agentName":  "My Agent",
    "orgName":    "My Org",
    "orgSlug":    "myorg",
    "publicKey":  "YOUR_BASE64_PUBLIC_KEY=="
  }' | jq .
# → { agentSignupToken, challenge, expiresIn: 900 }
```

### Step 2: Sign Challenge + Verify
```python
import base64, requests
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

priv_bytes = base64.b64decode("YOUR_PRIVATE_KEY")
private_key = Ed25519PrivateKey.from_private_bytes(priv_bytes)
challenge = "CHALLENGE_FROM_STEP_1"
sig = base64.b64encode(private_key.sign(challenge.encode())).decode()

r = requests.post("https://api.commune.email/v1/auth/agent-verify", json={
    "agentSignupToken": "TOKEN_FROM_STEP_1",
    "signature": sig,
})
print(r.json())
# → { agentId, orgId, inboxEmail: "myorg@commune.ai" }
```

After verification you can also authenticate every request with Ed25519 instead of API key:
```
Authorization: Agent {agentId}:{base64_ed25519_signature_of_request_body}
```

---

## Data Deletion

Requires API key with `admin` or `data:delete` permission.

### Create Deletion Request (Preview First, Then Confirm)
```bash
# Preview deletion of all messages in an inbox before a date
curl -s -X POST https://api.commune.email/v1/data/deletion-request \
  -H "Authorization: Bearer $KEY" \
  -H "Content-Type: application/json" \
  -d '{"scope": "messages", "inbox_id": "i_abc123", "before": "2025-01-01T00:00:00Z"}' | jq .
# Returns preview (how many records) + confirmation_token

# Scopes: "organization" | "inbox" | "messages"
```

### Confirm and Execute
```bash
curl -s -X POST https://api.commune.email/v1/data/deletion-request/req_abc123/confirm \
  -H "Authorization: Bearer $KEY" \
  -H "Content-Type: application/json" \
  -d '{"confirmation_token": "TOKEN_FROM_REQUEST"}' | jq .
```

### Check Deletion Status
```bash
curl -s https://api.commune.email/v1/data/deletion-request/req_abc123 \
  -H "Authorization: Bearer $KEY" | jq .
```

---

## Email as Persistent Memory

Your Commune inbox persists across every agent session. Patterns for using it as cross-session memory:

```bash
# Before reaching out to anyone — check if you've contacted them before
curl -s "https://api.commune.email/v1/search/threads?q=John+Smith+Acme+Corp&inbox_id=i_abc123" \
  -H "Authorization: Bearer $KEY" | jq '.data[].thread_id'

# Reconstruct the full history of a conversation
curl -s "https://api.commune.email/v1/threads/conv_abc123/messages?order=asc" \
  -H "Authorization: Bearer $KEY" | jq '.data[] | {direction, content, created_at}'

# Tag threads you need to follow up on
curl -s -X POST https://api.commune.email/v1/threads/conv_abc123/tags \
  -H "Authorization: Bearer $KEY" -H "Content-Type: application/json" \
  -d '{"tags": ["follow-up-week-2"]}' | jq .

# Close resolved threads to keep inbox clean
curl -s -X PUT https://api.commune.email/v1/threads/conv_abc123/status \
  -H "Authorization: Bearer $KEY" -H "Content-Type: application/json" \
  -d '{"status": "closed"}' | jq .

# Find all threads that still need a reply
curl -s "https://api.commune.email/v1/search/threads?q=needs+reply&inbox_id=i_abc123" \
  -H "Authorization: Bearer $KEY" | jq .
```

---

## Rate Limits

| Tier | Per Hour | Per Day |
|------|----------|---------|
| Free | 100 emails | 1,000 emails |
| Pro | 10,000 emails | 100,000 emails |
| Enterprise | Custom | Custom |

Rate limit headers on every response: `X-RateLimit-Limit`, `X-RateLimit-Remaining`, `X-RateLimit-Reset`.
`429 Too Many Requests` when exceeded.

---

## Error Reference

| Status | Meaning |
|--------|---------|
| 400 | Bad request / missing required field |
| 401 | Invalid or missing API key |
| 403 | API key lacks required permission scope |
| 404 | Resource not found |
| 409 | Conflict — e.g. org slug already taken |
| 410 | Confirmation token expired |
| 413 | Attachment storage quota exceeded |
| 429 | Rate limit hit — check Retry-After header |
| 500 | Server error |

All errors: `{ "error": "descriptive message" }`

---

## Complete API Reference

| Method | Endpoint | Scope Needed | What It Does |
|--------|----------|-------------|--------------|
| GET | /v1/domains | domains:read | List all domains |
| POST | /v1/domains | domains:write | Create custom domain |
| GET | /v1/domains/:id | domains:read | Get domain details |
| POST | /v1/domains/:id/verify | domains:write | Trigger DNS check |
| GET | /v1/domains/:id/records | domains:read | Get DNS records to configure |
| POST | /v1/inboxes | inboxes:write | Create inbox (auto-domain) |
| GET | /v1/inboxes | inboxes:read | List all inboxes |
| GET | /v1/domains/:d/inboxes | inboxes:read | List inboxes for a domain |
| POST | /v1/domains/:d/inboxes | inboxes:write | Create inbox under domain |
| GET | /v1/domains/:d/inboxes/:i | inboxes:read | Get inbox |
| PUT | /v1/domains/:d/inboxes/:i | inboxes:write | Update inbox |
| DELETE | /v1/domains/:d/inboxes/:i | inboxes:write | Delete inbox |
| PUT | /v1/domains/:d/inboxes/:i/extraction-schema | inboxes:write | Set AI extraction schema |
| DELETE | /v1/domains/:d/inboxes/:i/extraction-schema | inboxes:write | Remove extraction schema |
| GET | /v1/threads | threads:read | List threads (paginated) |
| GET | /v1/threads/:id/messages | threads:read | Get full conversation |
| GET | /v1/threads/:id/metadata | threads:read | Get tags/status/assignee |
| PUT | /v1/threads/:id/status | threads:write | Set status |
| POST | /v1/threads/:id/tags | threads:write | Add tags |
| DELETE | /v1/threads/:id/tags | threads:write | Remove tags |
| PUT | /v1/threads/:id/assign | threads:write | Assign/unassign thread |
| POST | /v1/messages/send | messages:write | Send email |
| GET | /v1/messages | messages:read | List messages (filter required) |
| GET | /v1/search/threads | threads:read | Semantic/vector search |
| POST | /v1/attachments/upload | attachments:write | Upload file (base64) |
| GET | /v1/attachments/:id | attachments:read | Get attachment metadata |
| GET | /v1/attachments/:id/url | attachments:read | Get signed download URL |
| GET | /v1/delivery/metrics | messages:read | Delivery stats |
| GET | /v1/delivery/events | messages:read | Per-message event log |
| GET | /v1/delivery/suppressions | messages:read | Bounced/complained addresses |
| GET | /v1/webhooks/deliveries | messages:read | List webhook deliveries |
| GET | /v1/webhooks/deliveries/:id | messages:read | Full delivery detail |
| POST | /v1/webhooks/deliveries/:id/retry | messages:write | Retry dead delivery |
| GET | /v1/webhooks/health | messages:read | Per-endpoint health stats |
| POST | /v1/dmarc/reports | domains:write | Submit DMARC XML report |
| GET | /v1/dmarc/reports | domains:read | List DMARC reports |
| GET | /v1/dmarc/summary | domains:read | DMARC pass/fail summary |
| GET | /v1/agent/org | — | Get own org |
| PATCH | /v1/agent/org | — | Update org name |
| GET | /v1/agent/api-keys | — | List API keys |
| POST | /v1/agent/api-keys | — | Create scoped API key |
| DELETE | /v1/agent/api-keys/:id | — | Revoke key |
| POST | /v1/agent/api-keys/:id/rotate | — | Rotate key |
| POST | /v1/auth/agent-register | public | Register (Ed25519 public key) |
| POST | /v1/auth/agent-verify | public | Verify challenge → activate |
| POST | /v1/data/deletion-request | admin/data:delete | Create deletion request |
| POST | /v1/data/deletion-request/:id/confirm | admin/data:delete | Execute deletion |
| GET | /v1/data/deletion-request/:id | admin/data:delete | Check deletion status |
