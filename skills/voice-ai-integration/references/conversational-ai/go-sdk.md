---
name: agora-server-sdk-go
description: |
  Go SDK for Agora Conversational AI server-side integration. Use when the user is
  building a Go backend to start/stop/manage ConvoAI agents. Triggers on:
  agora-agent-server-sdk-go, agentkit Go, AgentSession Go, Go ConvoAI server,
  context.Context agent, go get agora agent.
license: MIT
metadata:
  author: agora
  version: '1.0.0'
---

# ConvoAI Server SDK — Go

Go SDK for managing Agora Conversational AI agents from a server-side application. Wraps the ConvoAI REST API.

**Module:** `github.com/AgoraIO-Community/agora-agent-server-sdk-go`
**Minimum Go version:** 1.21
**Repo:** <https://github.com/AgoraIO-Conversational-AI/agent-server-sdk-go>

## Installation

```bash
go get github.com/AgoraIO-Community/agora-agent-server-sdk-go
```

## Quick Start

```go
package main

import (
    "context"
    "fmt"
    "log"
    "time"

    "github.com/AgoraIO-Community/agora-agent-server-sdk-go/agentkit"
)

func main() {
    client, err := agentkit.NewAgora(
        agentkit.WithAppID("YOUR_APP_ID"),
        agentkit.WithAppCertificate("YOUR_APP_CERTIFICATE"),
    )
    if err != nil {
        log.Fatal(err)
    }

    agent := agentkit.NewAgent(
        agentkit.WithName("my_agent"),
        agentkit.WithInstructions("You are a helpful voice assistant."),
        agentkit.WithLlm(agentkit.OpenAI{APIKey: "OPENAI_KEY"}),
        agentkit.WithTts(agentkit.ElevenLabs{APIKey: "ELEVENLABS_KEY"}),
        agentkit.WithStt(agentkit.Deepgram{APIKey: "DEEPGRAM_KEY"}),
    )

    session := agent.CreateSession(agentkit.SessionOptions{
        Channel:  "my-channel",
        AgentUID: 0,
    })

    // Bound start time to 10 seconds
    ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
    defer cancel()

    agentID, err := session.Start(ctx)
    if err != nil {
        log.Fatal(err)
    }
    fmt.Printf("Agent started: %s\n", agentID)

    // Stop from the same process
    if err := session.Stop(context.Background()); err != nil {
        log.Fatal(err)
    }
}
```

## context.Context Pattern

Every session method takes `ctx context.Context` as its first argument. Use this to bound operation time:

```go
// Bound start — fails after 10s if the agent hasn't connected
ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
defer cancel()
agentID, err := session.Start(ctx)

// Stateless stop (different request handler) — use a fresh context
agentID, err := client.StopAgent(context.Background(), agentID)
```

## Error Handling

All methods return `(result, error)`. Idiomatic check:

```go
agentID, err := session.Start(ctx)
if err != nil {
    // handle error
    return fmt.Errorf("start agent: %w", err)
}

// Stop returns nil for 404 (agent already stopped) — same graceful behavior as TypeScript/Python
err = session.Stop(context.Background())
if err != nil {
    // genuine error — not "already stopped"
}
```

## Builder Pattern (Functional Options)

Go uses functional options (`With*` functions) instead of chained methods or object literals:

```go
// TypeScript equivalent: new Agent({ name: "..." }).withLlm(new OpenAI({ ... }))
agent := agentkit.NewAgent(
    agentkit.WithName("my_agent"),
    agentkit.WithLlm(agentkit.OpenAI{APIKey: "OPENAI_KEY", Model: "gpt-4o"}),
    agentkit.WithTts(agentkit.ElevenLabs{APIKey: "ELEVENLABS_KEY", VoiceID: "..."}),
)
```

## Session Status Constants

Check `session.Status` before calling methods:

| Constant | Meaning |
|----------|---------|
| `agentkit.StatusIdle` | Ready, not started |
| `agentkit.StatusStarting` | Start in progress |
| `agentkit.StatusRunning` | Active — `Stop`, `Say`, `Interrupt`, `Update` available |
| `agentkit.StatusStopping` | Stop in progress |
| `agentkit.StatusStopped` | Stopped — `Start` available again |
| `agentkit.StatusError` | Error — `Start` available again |

## Token Helpers

```go
// Generate an RTC token
rtcToken, err := agentkit.GenerateRTCToken(agentkit.TokenOptions{
    AppID:       "YOUR_APP_ID",
    Certificate: "YOUR_CERTIFICATE",
    Channel:     "my-channel",
    UID:         12345,
    ExpiresIn:   agentkit.ExpiresInHours(1),
})

// Generate a combined RTC+RTM ConvoAI token (for Token Auth mode)
convoAIToken, err := agentkit.GenerateConvoAIToken(agentkit.TokenOptions{
    AppID:       "YOUR_APP_ID",
    Certificate: "YOUR_CERTIFICATE",
    Channel:     "my-channel",
    Account:     "agent-account",
    ExpiresIn:   agentkit.ExpiresInHours(1),
})
```

## Auth Modes

Same three modes as TypeScript and Python. Pass exactly one set of credentials:

```go
// App Credentials (recommended) — SDK generates ConvoAI token per request
client, _ := agentkit.NewAgora(
    agentkit.WithAppID("..."),
    agentkit.WithAppCertificate("..."),
)

// Token Auth — pre-built combined RTC+RTM token; reused until you replace it
client, _ := agentkit.NewAgora(
    agentkit.WithAppID("..."),
    agentkit.WithAuthToken("YOUR_TOKEN"),
)

// Basic Auth — Customer ID + Secret; for testing only
client, _ := agentkit.NewAgora(
    agentkit.WithAppID("..."),
    agentkit.WithCustomerID("..."),
    agentkit.WithCustomerSecret("..."),
)
```
