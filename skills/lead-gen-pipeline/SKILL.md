---
name: lead-gen-pipeline
description: Autonomous 6-agent pipeline that researches industries, finds businesses, and generates personalized outreach — one API call.
author: MCF Agentic
version: 1.0.0
tags: [lead-generation, outreach, sales, ai-research, cold-email, pipeline, autonomous]
pricing: x402 (USDC on Base)
gateway: https://gateway.mcfagentic.com
---

# Lead Generation Pipeline

This is not just an API — it is a full autonomous research and outreach pipeline powered by 6 coordinated AI agents. Send an industry and location, and the pipeline discovers real businesses, researches them deeply, identifies pain points, matches solution packages, and writes personalized cold emails ready to send. One call replaces hours of manual prospecting.

## Authentication

All endpoints require x402 payment (USDC on Base L2). Send a request without payment to receive pricing info in the 402 response.

## Endpoints

### Generate Leads
- **Method:** POST
- **Path:** /api/pipeline/generate-leads
- **Price:** $1.00 per call
- **Description:** Full pipeline run. Provide an industry and location, receive a list of researched leads with pain-point analysis, matched solutions, and ready-to-send outreach emails.

**Request:**
```json
{
  "industry": "HVAC contractors",
  "location": "Dallas, TX",
  "count": 10,
  "solution_focus": "ai-automation"
}
```

**Response:**
```json
{
  "leads": [
    {
      "business_name": "Comfort Zone HVAC",
      "contact_name": "Mike Torres",
      "email": "mike@comfortzonehvac.com",
      "phone": "214-555-0142",
      "website": "comfortzonehvac.com",
      "pain_points": ["manual scheduling", "missed follow-ups", "no online booking"],
      "matched_solution": "ai-scheduling-bundle",
      "outreach_email": {
        "subject": "Quick question about your scheduling, Mike",
        "body": "..."
      },
      "research_summary": "15-person operation, 4.2 Google rating, heavy residential focus..."
    }
  ],
  "pipeline_metadata": {
    "agents_used": 6,
    "businesses_scanned": 47,
    "leads_qualified": 10,
    "processing_time_seconds": 38
  }
}
```

### Research Business
- **Method:** POST
- **Path:** /api/pipeline/research-business
- **Price:** $0.50 per call
- **Description:** Deep AI research on a single business. Returns company profile, tech stack signals, pain points, competitive landscape, and decision-maker contacts.

**Request:**
```json
{
  "business_name": "Comfort Zone HVAC",
  "location": "Dallas, TX",
  "website": "comfortzonehvac.com"
}
```

**Response:**
```json
{
  "profile": {
    "name": "Comfort Zone HVAC",
    "industry": "HVAC",
    "estimated_revenue": "$2M-5M",
    "employee_count": "10-20",
    "years_in_business": 12,
    "google_rating": 4.2,
    "review_count": 187
  },
  "tech_signals": ["no online booking", "basic WordPress site", "no CRM detected"],
  "pain_points": ["manual scheduling", "missed follow-ups", "no review automation"],
  "competitors": ["ABC Cooling", "North Texas Air"],
  "contacts": [
    {"name": "Mike Torres", "role": "Owner", "email": "mike@comfortzonehvac.com"}
  ]
}
```

### Write Outreach
- **Method:** POST
- **Path:** /api/pipeline/write-outreach
- **Price:** $0.25 per call
- **Description:** Generate a personalized cold email for a specific business based on research data. Returns subject line, body, and follow-up sequence.

**Request:**
```json
{
  "business_name": "Comfort Zone HVAC",
  "contact_name": "Mike Torres",
  "pain_points": ["manual scheduling", "missed follow-ups"],
  "solution": "ai-scheduling-bundle",
  "tone": "casual-professional"
}
```

**Response:**
```json
{
  "email": {
    "subject": "Quick question about your scheduling, Mike",
    "body": "Hi Mike,\n\nI noticed Comfort Zone HVAC is crushing it on Google reviews (4.2 stars, nice). But I also noticed you don't have online booking — which usually means your front desk is fielding a ton of calls...",
    "follow_up_1": { "delay_days": 3, "subject": "...", "body": "..." },
    "follow_up_2": { "delay_days": 7, "subject": "...", "body": "..." }
  },
  "personalization_score": 0.92
}
```

### Browse Solutions
- **Method:** GET
- **Path:** /api/pipeline/solutions
- **Price:** Free
- **Description:** Browse available solution packages that can be matched to leads. Use this to understand what offerings the pipeline can recommend.

**Request:**
```
GET /api/pipeline/solutions
```

**Response:**
```json
{
  "solutions": [
    {
      "id": "ai-scheduling-bundle",
      "name": "AI Scheduling & Booking",
      "monthly_price": "$497",
      "description": "Automated appointment scheduling with AI phone answering",
      "best_for": ["HVAC", "plumbing", "dental", "med-spa"]
    },
    {
      "id": "review-reputation",
      "name": "Review & Reputation Engine",
      "monthly_price": "$297",
      "description": "Automated review requests, response generation, reputation monitoring"
    }
  ]
}
```

## Use Cases

- An AI sales agent needs to build a prospect list for a specific vertical and geography
- An autonomous outreach system needs personalized emails that reference real business data
- A consulting agent needs to research a potential client before a call
- A marketing agent wants to identify pain points across an entire industry segment
- An agent orchestrator needs to feed qualified leads into a CRM or email sequence

## Pricing

| Endpoint | Price | Description |
|----------|-------|-------------|
| /api/pipeline/generate-leads | $1.00 | Full pipeline: research + qualify + outreach |
| /api/pipeline/research-business | $0.50 | Deep AI research on one business |
| /api/pipeline/write-outreach | $0.25 | Personalized cold email generation |
| /api/pipeline/solutions | Free | Browse available solution packages |
