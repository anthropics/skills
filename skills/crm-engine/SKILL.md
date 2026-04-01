---
name: crm-engine
description: Full CRM with accounts, leads, deals, contacts, pipelines, and work orders — built for AI agents.
author: MCF Agentic
version: 1.0.0
tags: [crm, sales, leads, deals, contacts, pipeline, work-orders]
pricing: x402 (USDC on Base)
gateway: https://gateway.mcfagentic.com
---

# CRM Engine

A complete CRM system designed for autonomous AI agents. Manage accounts, track leads through pipelines, close deals, organize contacts, and create work orders — all via API. Built to be the persistent memory layer for sales and service agents.

## Authentication

All endpoints require x402 payment (USDC on Base L2). Send a request without payment to receive pricing info in the 402 response.

## Endpoints

### Create Account
- **Method:** POST
- **Path:** /api/crm/accounts
- **Price:** $0.05 per call
- **Description:** Create a new business account in the CRM.

**Request:**
```json
{
  "name": "Comfort Zone HVAC",
  "industry": "HVAC",
  "website": "comfortzonehvac.com",
  "phone": "214-555-0142",
  "address": "1200 Commerce St, Dallas, TX 75201",
  "tags": ["prospect", "hvac", "dallas"]
}
```

**Response:**
```json
{
  "id": "acc_8x2kf9",
  "name": "Comfort Zone HVAC",
  "created_at": "2026-04-01T14:30:00Z",
  "status": "active"
}
```

### Manage Leads
- **Method:** POST
- **Path:** /api/crm/leads
- **Price:** $0.05 per call
- **Description:** Create or update a lead. Leads track prospective clients through qualification stages.

**Request:**
```json
{
  "account_id": "acc_8x2kf9",
  "contact_name": "Mike Torres",
  "email": "mike@comfortzonehvac.com",
  "source": "ai-pipeline",
  "stage": "qualified",
  "score": 85,
  "notes": "Needs scheduling automation, no current CRM"
}
```

**Response:**
```json
{
  "id": "lead_3m7np2",
  "account_id": "acc_8x2kf9",
  "stage": "qualified",
  "score": 85,
  "created_at": "2026-04-01T14:31:00Z"
}
```

### Manage Deals
- **Method:** POST
- **Path:** /api/crm/deals
- **Price:** $0.05 per call
- **Description:** Create or update a deal. Track revenue opportunities through your sales pipeline.

**Request:**
```json
{
  "lead_id": "lead_3m7np2",
  "account_id": "acc_8x2kf9",
  "title": "AI Scheduling Bundle - Comfort Zone HVAC",
  "value": 5964,
  "currency": "USD",
  "stage": "proposal",
  "close_date": "2026-04-15"
}
```

**Response:**
```json
{
  "id": "deal_9k4rt1",
  "title": "AI Scheduling Bundle - Comfort Zone HVAC",
  "value": 5964,
  "stage": "proposal",
  "pipeline_id": "pipe_default"
}
```

### Manage Contacts
- **Method:** POST
- **Path:** /api/crm/contacts
- **Price:** $0.03 per call
- **Description:** Create or update a contact record linked to an account.

**Request:**
```json
{
  "account_id": "acc_8x2kf9",
  "first_name": "Mike",
  "last_name": "Torres",
  "email": "mike@comfortzonehvac.com",
  "phone": "214-555-0142",
  "role": "Owner"
}
```

**Response:**
```json
{
  "id": "con_5h8jw3",
  "account_id": "acc_8x2kf9",
  "full_name": "Mike Torres",
  "role": "Owner"
}
```

### List Pipelines
- **Method:** GET
- **Path:** /api/crm/pipelines
- **Price:** $0.02 per call
- **Description:** List all sales pipelines and their stages.

**Request:**
```
GET /api/crm/pipelines
```

**Response:**
```json
{
  "pipelines": [
    {
      "id": "pipe_default",
      "name": "Default Sales Pipeline",
      "stages": ["prospect", "qualified", "proposal", "negotiation", "closed-won", "closed-lost"]
    }
  ]
}
```

### Create Work Order
- **Method:** POST
- **Path:** /api/crm/work-orders
- **Price:** $0.05 per call
- **Description:** Create a work order tied to an account or deal. Track deliverables, tasks, and service fulfillment.

**Request:**
```json
{
  "account_id": "acc_8x2kf9",
  "deal_id": "deal_9k4rt1",
  "title": "Set up AI scheduling system",
  "description": "Deploy scheduling engine, configure availability, train staff",
  "priority": "high",
  "due_date": "2026-04-20"
}
```

**Response:**
```json
{
  "id": "wo_2n6qp8",
  "title": "Set up AI scheduling system",
  "status": "open",
  "priority": "high",
  "created_at": "2026-04-01T14:35:00Z"
}
```

## Use Cases

- An AI sales agent closes a deal and needs to create the account, contact, and work order automatically
- A lead-gen pipeline deposits qualified leads directly into the CRM for follow-up
- An autonomous agent tracks deal progression and updates stages based on email replies
- A service agent creates work orders when contracts are signed
- An analytics agent pulls pipeline data to forecast revenue

## Pricing

| Endpoint | Price | Description |
|----------|-------|-------------|
| /api/crm/accounts | $0.05 | Create or update accounts |
| /api/crm/leads | $0.05 | Create or update leads |
| /api/crm/deals | $0.05 | Create or update deals |
| /api/crm/contacts | $0.03 | Create or update contacts |
| /api/crm/pipelines | $0.02 | List pipelines and stages |
| /api/crm/work-orders | $0.05 | Create or update work orders |
