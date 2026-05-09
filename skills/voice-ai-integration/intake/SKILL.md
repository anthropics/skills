---
name: voice-ai-integration-intake
description: |
  First skill to run when the user's Agora product need is unclear or involves
  multiple products. Understands the full product landscape, identifies user needs,
  recommends the optimal product combination, and routes to the appropriate skill.
  Use when the user describes a use case without naming a specific Agora product,
  or says things like "I want to build", "help me set up", or requests multiple
  capabilities (video + AI, recording + live, etc.).
license: MIT
metadata:
  author: agora
  version: "1.1.0"
---

# Voice AI Integration Intake — Product Routing & Needs Analysis

First entry point for vague or multi-product Agora requests. This skill understands
the full product landscape, identifies what the user needs, and routes to the right place.

> **Note:** Skip-intake logic is defined in [skills/voice-ai-integration/SKILL.md](../SKILL.md) (root router).
> If you are here, the root router has already determined that intake is needed.
> Do NOT second-guess the routing decision — proceed with the intake flow below.

---

## Product Landscape

| Product | What it does | Typical user says |
|---------|-------------|-------------------|
| RTC SDK | Real-time audio/video between humans | "video call", "live streaming", "voice chat" |
| RTM | Real-time messaging / signaling | "chat", "messaging", "signaling", "notifications" |
| ConvoAI | AI voice agent (ASR→LLM→TTS over RTC) | "AI assistant", "voice bot", "conversational AI" |
| Cloud Recording | Record RTC sessions server-side | "recording", "archive sessions", "record calls" |
| Server/Tokens | Auth token generation | "token server", "authentication", "App Certificate" |
| Server Gateway SDK | Server-side media streaming (Linux) | "server SDK", "Linux SDK", "send audio from server", "server gateway" |

### Product Relationships

```text
                    ┌─────────────┐
                    │   RTC SDK   │  ← foundation layer
                    └──────┬──────┘
                           │
          ┌────────────────┼────────────────┐
          │                │                │
    ┌─────┴─────┐   ┌─────┴─────┐
    │  ConvoAI  │   │  Cloud    │
    │ (AI Agent)│   │ Recording │
    └─────┬─────┘   └───────────┘
          │
    ┌─────┴─────┐
    │    RTM    │  ← often paired with RTC/ConvoAI
    └───────────┘
```

Key relationships:

- **ConvoAI depends on RTC** — the AI agent joins an RTC channel; the client needs RTC SDK
- **Cloud Recording depends on RTC** — records what happens in an RTC channel
- **RTM is independent** but often paired with RTC or ConvoAI for signaling (call invitation, presence, chat history)

### Common Product Combinations

| Use case | Products needed |
|----------|----------------|
| 1v1 / group video call | RTC SDK |
| Video call + chat | RTC SDK + RTM |
| AI voice assistant | ConvoAI + RTC SDK (client) |
| AI voice assistant + chat history | ConvoAI + RTC SDK + RTM |
| Live streaming with recording | RTC SDK + Cloud Recording |
| Record AI conversations | ConvoAI + RTC SDK + Cloud Recording |


---

## Intake Flow

### Step 1: Understand the Use Case

If the user's intent is not immediately clear, ask:

> "What are you trying to build? Please describe the use case."

Listen for keywords and map to products using the Product Landscape table above.

### Step 2: Identify Products

Based on the user's description, determine:

1. **Primary product** — the main capability they need
2. **Supporting products** — additional products required by the primary, or that enhance the use case
3. **Optional products** — nice-to-haves the user may not have considered

Use the Product Relationships and Common Combinations tables to make this determination.

**Server-side disambiguation** — "backend", "Python/Go/Node.js server", or "server-side" alone is ambiguous. Clarify which server role is needed before routing:

| User says | They need |
|-----------|-----------|
| "authenticate users", "issue tokens", "token server" | Server/Tokens → `references/server/` |
| "start an AI agent", "call the ConvoAI API", "Python ConvoAI backend" | ConvoAI → `references/conversational-ai/` |
| "my server sends audio/video", "server joins RTC channel", "Linux media SDK" | Server Gateway → `references/server-gateway/` |

If unclear, ask: *"Does your server need to (a) generate auth tokens, (b) call the ConvoAI REST API to start agents, or (c) send/receive audio-video media directly?"*

**Example analysis:**

> User: "I want to build an AI customer service bot where users call in and an AI answers"
>
> - Primary: ConvoAI (AI voice agent)
> - Supporting: RTC SDK (client-side for user to join channel)
> - Optional: Cloud Recording (record conversations for QA), RTM (send chat transcript)

### Step 3: Confirm with User

Present your analysis:

```text
Needs Analysis:
─────────────────────────────────────
Use case:           [user's described use case]
Primary product:    [primary product]
Supporting:         [supporting products]
Optional:           [optional enhancements]
─────────────────────────────────────

Does this look right? Any adjustments needed?
```

Wait for user confirmation before proceeding.

### Step 4: Route to Product Skill

For each identified product, route to its skill file:

| Product | Product skill |
|---------|--------------|
| ConvoAI | [references/conversational-ai/README.md](../references/conversational-ai/README.md) |
| RTC SDK | [references/rtc/README.md](../references/rtc/README.md) |
| RTM | [references/rtm/README.md](../references/rtm/README.md) |
| Cloud Recording | [references/cloud-recording/README.md](../references/cloud-recording/README.md) |
| Token generation | [references/server/README.md](../references/server/README.md) |
| Server Gateway SDK | [references/server-gateway/README.md](../references/server-gateway/README.md) |

When multiple products are needed, run the primary product's skill first,
then address supporting products in order.

---

## Decision Shortcuts

For common patterns, skip the full intake flow:

| User says | Shortcut |
|-----------|----------|
| "video call" / "live stream" / "RTC" | → `references/rtc/README.md` directly |
| "screen share" / "screen sharing" | → `references/rtc/README.md` → `cross-platform-coordination.md` |
| "chat" / "messaging" / "signaling" | → `references/rtm/README.md` directly |
| "voice bot" / "AI assistant" / "ConvoAI" | → `references/conversational-ai/README.md` directly |
| "recording" / "record sessions" / "record calls" | → `references/cloud-recording/README.md` directly |
| "generate token" / "token server" / "App Certificate" | → `references/server/README.md` directly |
| "Server Gateway" / "Linux SDK" / "server sends audio" | → `references/server-gateway/README.md` directly |

