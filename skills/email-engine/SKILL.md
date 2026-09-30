---
name: email-engine
description: Send emails, bulk campaigns, AI-powered classification, auto-reply generation, and template management.
author: MCF Agentic
version: 1.0.0
tags: [email, outreach, campaigns, ai-classification, auto-reply, templates]
pricing: x402 (USDC on Base)
gateway: https://gateway.mcfagentic.com
---

# Email Engine

Send transactional and outreach emails, run bulk campaigns, classify inbound messages with AI, generate contextual replies, and manage reusable templates. Designed for AI agents that need to communicate with humans over email as part of autonomous workflows.

## Authentication

All endpoints require x402 payment (USDC on Base L2). Send a request without payment to receive pricing info in the 402 response.

## Endpoints

### Send Email
- **Method:** POST
- **Path:** /api/email/send
- **Price:** $0.02 per call
- **Description:** Send a single email. Supports HTML and plain text, attachments, and reply-to threading.

**Request:**
```json
{
  "to": "mike@comfortzonehvac.com",
  "from": "cameron@mcfagentic.com",
  "subject": "Quick question about your scheduling, Mike",
  "body_html": "<p>Hi Mike,</p><p>I noticed Comfort Zone HVAC is crushing it on reviews...</p>",
  "body_text": "Hi Mike, I noticed Comfort Zone HVAC is crushing it on reviews...",
  "reply_to": "cameron@mcfagentic.com",
  "track_opens": true,
  "track_clicks": true
}
```

**Response:**
```json
{
  "id": "msg_4k9xr2",
  "status": "sent",
  "to": "mike@comfortzonehvac.com",
  "sent_at": "2026-04-01T14:40:00Z"
}
```

### Send Bulk
- **Method:** POST
- **Path:** /api/email/send-bulk
- **Price:** $0.01 per recipient
- **Description:** Send a campaign to multiple recipients. Supports personalization variables and staggered delivery.

**Request:**
```json
{
  "template_id": "tmpl_cold_outreach_v2",
  "recipients": [
    {"email": "mike@comfortzonehvac.com", "variables": {"first_name": "Mike", "company": "Comfort Zone HVAC"}},
    {"email": "sarah@northtexasair.com", "variables": {"first_name": "Sarah", "company": "North Texas Air"}}
  ],
  "from": "cameron@mcfagentic.com",
  "stagger_minutes": 5,
  "track_opens": true
}
```

**Response:**
```json
{
  "campaign_id": "camp_7n3mp1",
  "total_recipients": 2,
  "status": "queued",
  "estimated_completion": "2026-04-01T14:50:00Z"
}
```

### AI Classify
- **Method:** POST
- **Path:** /api/email/ai/classify
- **Price:** $0.05 per call
- **Description:** Classify an inbound email using AI. Returns intent, sentiment, urgency, and suggested action.

**Request:**
```json
{
  "subject": "Re: Quick question about your scheduling",
  "body": "Hey Cameron, this sounds interesting. We've been struggling with scheduling for a while. Can you tell me more about pricing?",
  "sender": "mike@comfortzonehvac.com"
}
```

**Response:**
```json
{
  "classification": {
    "intent": "interested",
    "sentiment": "positive",
    "urgency": "medium",
    "category": "sales-reply",
    "suggested_action": "send-pricing",
    "confidence": 0.94
  }
}
```

### AI Reply
- **Method:** POST
- **Path:** /api/email/ai/reply
- **Price:** $0.10 per call
- **Description:** Generate a contextual reply to an email thread using AI. Takes conversation history and CRM context.

**Request:**
```json
{
  "thread": [
    {"from": "cameron@mcfagentic.com", "body": "Quick question about your scheduling..."},
    {"from": "mike@comfortzonehvac.com", "body": "This sounds interesting. Can you tell me more about pricing?"}
  ],
  "context": {
    "lead_stage": "qualified",
    "solution": "ai-scheduling-bundle",
    "monthly_price": "$497"
  },
  "tone": "casual-professional",
  "goal": "book-a-call"
}
```

**Response:**
```json
{
  "reply": {
    "subject": "Re: Quick question about your scheduling",
    "body": "Hey Mike,\n\nGlad it caught your eye. The AI scheduling package runs $497/mo and typically pays for itself within the first month...",
    "call_to_action": "calendar-link"
  }
}
```

### Manage Templates
- **Method:** POST
- **Path:** /api/email/templates
- **Price:** $0.02 per call
- **Description:** Create or update reusable email templates with personalization variables.

**Request:**
```json
{
  "name": "Cold Outreach v2",
  "subject": "Quick question about your {{pain_point}}, {{first_name}}",
  "body_html": "<p>Hi {{first_name}},</p><p>I noticed {{company}} is doing great work in {{industry}}...</p>",
  "variables": ["first_name", "company", "industry", "pain_point"]
}
```

**Response:**
```json
{
  "id": "tmpl_cold_outreach_v2",
  "name": "Cold Outreach v2",
  "variables": ["first_name", "company", "industry", "pain_point"],
  "created_at": "2026-04-01T14:45:00Z"
}
```

## Use Cases

- An outreach agent sends personalized cold emails to leads from the pipeline
- A support agent classifies inbound emails and routes them to the right workflow
- An autonomous sales agent generates and sends follow-up replies based on prospect responses
- A marketing agent runs drip campaigns across segmented lead lists
- An agent orchestrator monitors email threads and escalates urgent messages

## Pricing

| Endpoint | Price | Description |
|----------|-------|-------------|
| /api/email/send | $0.02 | Send a single email |
| /api/email/send-bulk | $0.01/recipient | Bulk campaign send |
| /api/email/ai/classify | $0.05 | AI email classification |
| /api/email/ai/reply | $0.10 | AI reply generation |
| /api/email/templates | $0.02 | Create/update templates |
