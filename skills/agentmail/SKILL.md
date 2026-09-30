---
name: agentmail
description: Use when an AI agent needs email capabilities — creating email accounts, sending/receiving email, managing webhooks, or checking karma balance. Triggers on requests like "send an email", "create an email account", "check my inbox", "sign up for a service", or any task requiring programmatic email access.
---

# AgentMail — Email for AI Agents

AgentMail gives AI agents real email addresses (`@theagentmail.net`) with a REST API. Agents can send and receive email, sign up for services (GitHub, AWS, Slack, etc.), and get verification codes. A karma system prevents spam and keeps the shared domain's reputation high.

Base URL: `https://api.theagentmail.net`

## Quick start

All requests require `Authorization: Bearer am_...` header (API key from dashboard).

### Create an email account (-10 karma)

```bash
curl -X POST https://api.theagentmail.net/v1/accounts \
  -H "Authorization: Bearer am_..." \
  -H "Content-Type: application/json" \
  -d '{"address": "my-agent@theagentmail.net"}'
```

Response: `{"data": {"id": "...", "address": "my-agent@theagentmail.net", "displayName": null, "createdAt": 123}}`

### Send email (-1 karma)

```bash
curl -X POST https://api.theagentmail.net/v1/accounts/{accountId}/messages \
  -H "Authorization: Bearer am_..." \
  -H "Content-Type: application/json" \
  -d '{
    "to": ["recipient@example.com"],
    "subject": "Hello from my agent",
    "text": "Plain text body",
    "html": "<p>Optional HTML body</p>"
  }'
```

Optional fields: `cc`, `bcc` (string arrays), `inReplyTo`, `references` (strings for threading), `attachments` (array of `{filename, contentType, content}` where content is base64).

### Read inbox

```bash
# List messages
curl https://api.theagentmail.net/v1/accounts/{accountId}/messages \
  -H "Authorization: Bearer am_..."

# Get full message (with body and attachments)
curl https://api.theagentmail.net/v1/accounts/{accountId}/messages/{messageId} \
  -H "Authorization: Bearer am_..."
```

### Check karma

```bash
curl https://api.theagentmail.net/v1/karma \
  -H "Authorization: Bearer am_..."
```

Response: `{"data": {"balance": 90, "events": [...]}}`

### Register webhook (real-time inbound)

```bash
curl -X POST https://api.theagentmail.net/v1/accounts/{accountId}/webhooks \
  -H "Authorization: Bearer am_..." \
  -H "Content-Type: application/json" \
  -d '{"url": "https://my-agent.example.com/inbox"}'
```

Webhook deliveries include two security headers:
- `X-AgentMail-Signature` -- HMAC-SHA256 hex digest of the request body, signed with the webhook secret
- `X-AgentMail-Timestamp` -- millisecond timestamp of when the delivery was sent

Verify the signature and reject requests with timestamps older than 5 minutes to prevent replay attacks:

```typescript
import { createHmac } from "crypto";

const verifyWebhook = (body: string, signature: string, timestamp: string, secret: string) => {
  if (Date.now() - Number(timestamp) > 5 * 60 * 1000) return false;
  return createHmac("sha256", secret).update(body).digest("hex") === signature;
};
```

### Download attachment

```bash
curl https://api.theagentmail.net/v1/accounts/{accountId}/messages/{messageId}/attachments/{attachmentId} \
  -H "Authorization: Bearer am_..."
```

Returns `{"data": {"url": "https://signed-download-url..."}}`.

## Full API reference

| Method | Path | Description | Karma |
|--------|------|-------------|-------|
| POST | `/v1/accounts` | Create email account | -10 |
| GET | `/v1/accounts` | List all accounts | |
| GET | `/v1/accounts/:id` | Get account details | |
| DELETE | `/v1/accounts/:id` | Delete account | +10 |
| POST | `/v1/accounts/:id/messages` | Send email | -1 |
| GET | `/v1/accounts/:id/messages` | List messages | |
| GET | `/v1/accounts/:id/messages/:msgId` | Get full message | |
| GET | `/v1/accounts/:id/messages/:msgId/attachments/:attId` | Get attachment URL | |
| POST | `/v1/accounts/:id/webhooks` | Register webhook | |
| GET | `/v1/accounts/:id/webhooks` | List webhooks | |
| DELETE | `/v1/accounts/:id/webhooks/:whId` | Delete webhook | |
| GET | `/v1/karma` | Get balance + events | |

## Karma system

Every action has a karma cost or reward:

| Event | Karma | Why |
|---|---|---|
| `money_paid` | +100 | Purchase credits |
| `email_received` | +2 | Someone replied from a trusted domain |
| `account_deleted` | +10 | Karma refunded when you delete an address |
| `email_sent` | -1 | Sending costs karma |
| `account_created` | -10 | Creating addresses costs karma |

**Important rules:**
- Karma is only awarded for inbound emails from trusted providers (Gmail, Outlook, Yahoo, iCloud, ProtonMail, Fastmail, Hey, etc.). Emails from unknown/throwaway domains don't earn karma.
- You only earn karma once per sender until the agent replies. If sender X emails you 5 times without a reply, only the first earns karma. Reply to X, and the next email from X earns karma again.
- Deleting an account refunds the 10 karma it cost to create.

When karma reaches 0, sends and account creation return HTTP 402. Always check balance before operations that cost karma.

## TypeScript SDK

```typescript
import { createClient } from "@agentmail/sdk";

const mail = createClient({ apiKey: "am_..." });

// Create account
const account = await mail.accounts.create({
  address: "my-agent@theagentmail.net",
});

// Send email
await mail.messages.send(account.id, {
  to: ["human@example.com"],
  subject: "Hello",
  text: "Sent by an AI agent.",
});

// Read inbox
const messages = await mail.messages.list(account.id);
const detail = await mail.messages.get(account.id, messages[0].id);

// Attachments
const att = await mail.attachments.getUrl(accountId, messageId, attachmentId);
// att.url is a signed download URL

// Webhooks
await mail.webhooks.create(account.id, {
  url: "https://my-agent.example.com/inbox",
});

// Karma
const karma = await mail.karma.getBalance();
console.log(karma.balance);
```

## Error handling

```typescript
import { AgentMailError } from "@agentmail/sdk";

try {
  await mail.messages.send(accountId, { to: ["a@b.com"], subject: "Hi", text: "Hey" });
} catch (e) {
  if (e instanceof AgentMailError) {
    console.log(e.status);   // 402, 404, 401, etc.
    console.log(e.code);     // "INSUFFICIENT_KARMA", "NOT_FOUND", etc.
    console.log(e.message);
  }
}
```

## Common patterns

### Sign up for a service and read verification email

```typescript
const account = await mail.accounts.create({
  address: "signup-bot@theagentmail.net",
});

// Use the address to sign up (browser automation, API, etc.)

// Poll for verification email
for (let i = 0; i < 30; i++) {
  const messages = await mail.messages.list(account.id);
  const verification = messages.find(m =>
    m.subject.toLowerCase().includes("verify") ||
    m.subject.toLowerCase().includes("confirm")
  );
  if (verification) {
    const detail = await mail.messages.get(account.id, verification.id);
    // Parse verification link/code from detail.bodyText or detail.bodyHtml
    break;
  }
  await new Promise(r => setTimeout(r, 2000));
}
```

### Send email and wait for reply

```typescript
const sent = await mail.messages.send(account.id, {
  to: ["human@company.com"],
  subject: "Question about order #12345",
  text: "Can you check the status?",
});

for (let i = 0; i < 60; i++) {
  const messages = await mail.messages.list(account.id);
  const reply = messages.find(m =>
    m.direction === "inbound" && m.timestamp > sent.timestamp
  );
  if (reply) {
    const detail = await mail.messages.get(account.id, reply.id);
    // Process reply
    break;
  }
  await new Promise(r => setTimeout(r, 5000));
}
```

## Types

```typescript
type Account = { id: string; address: string; displayName: string | null; createdAt: number };
type Message = { id: string; from: string; to: string[]; subject: string; direction: "inbound" | "outbound"; status: string; timestamp: number };
type MessageDetail = Message & { cc: string[] | null; bcc: string[] | null; bodyText: string | null; bodyHtml: string | null; inReplyTo: string | null; references: string | null; attachments: AttachmentMeta[] };
type AttachmentMeta = { id: string; filename: string; contentType: string; size: number };
type KarmaBalance = { balance: number; events: KarmaEvent[] };
type KarmaEvent = { id: string; type: string; amount: number; timestamp: number; metadata?: Record<string, unknown> };
```
