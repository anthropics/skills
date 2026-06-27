# Claude API — Go

> **Note:** The Go SDK supports the Claude API and beta tool use with `BetaToolRunner`. Agent SDK is not yet available for Go.

## Installation

```bash
go get github.com/anthropics/anthropic-sdk-go
```

## Client Initialization

```go
import (
    "github.com/anthropics/anthropic-sdk-go"
    "github.com/anthropics/anthropic-sdk-go/option"
)

// Default (uses ANTHROPIC_API_KEY env var)
client := anthropic.NewClient()

// Explicit API key
client := anthropic.NewClient(
    option.WithAPIKey("your-api-key"),
)
```

---

## Model Constants

The Go SDK provides typed model constants: `anthropic.ModelClaudeFable5`, `anthropic.ModelClaudeOpus4_8`, `anthropic.ModelClaudeOpus4_7`, `anthropic.ModelClaudeSonnet4_6`, `anthropic.ModelClaudeHaiku4_5_20251001`. Use `ModelClaudeOpus4_8` unless the user specifies otherwise; if they ask for Fable or the most powerful model, use `anthropic.ModelClaudeFable5` (see `shared/models.md` for the full resolution table).

---

## Basic Message Request

```go
response, err := client.Messages.New(context.Background(), anthropic.MessageNewParams{
    Model:     anthropic.ModelClaudeOpus4_8,
    MaxTokens: 16000,
    Messages: []anthropic.MessageParam{
        anthropic.NewUserMessage(anthropic.NewTextBlock("What is the capital of France?")),
    },
})
if err != nil {
    log.Fatal(err)
}
for _, block := range response.Content {
    switch variant := block.AsAny().(type) {
    case anthropic.TextBlock:
        fmt.Println(variant.Text)
    }
}
```

---

## Thinking

Enable Claude's internal reasoning by setting `Thinking` in `MessageNewParams`. The response will contain `ThinkingBlock` content before the final `TextBlock`.

**Adaptive thinking is the recommended mode for Claude 4.6+ models.** Claude decides dynamically when and how much to think. Combine with the `effort` parameter for cost-quality control.

Derived from `anthropic-sdk-go/message.go` (`ThinkingConfigParamUnion`, `ThinkingConfigAdaptiveParam`).

```go
// There is no ThinkingConfigParamOfAdaptive helper — construct the union
// struct-literal directly and take the address of the variant.
adaptive := anthropic.ThinkingConfigAdaptiveParam{}
params := anthropic.MessageNewParams{
    Model:     anthropic.ModelClaudeSonnet4_6,
    MaxTokens: 16000,
    Thinking:  anthropic.ThinkingConfigParamUnion{OfAdaptive: &adaptive},
    Messages: []anthropic.MessageParam{
        anthropic.NewUserMessage(anthropic.NewTextBlock("How many r's in strawberry?")),
    },
}

resp, err := client.Messages.New(context.Background(), params)
if err != nil {
    log.Fatal(err)
}

// ThinkingBlock(s) precede TextBlock in content
for _, block := range resp.Content {
    switch b := block.AsAny().(type) {
    case anthropic.ThinkingBlock:
        fmt.Println("[thinking]", b.Thinking)
    case anthropic.TextBlock:
        fmt.Println(b.Text)
    }
}
```

> **Fable 5, Opus 4.8, Opus 4.7, Opus 4.6, and Sonnet 4.6:** Use adaptive thinking (above). `ThinkingConfigParamOfEnabled(budgetTokens)` is removed on Fable 5, Opus 4.8, and 4.7 (400 if sent); deprecated on Opus 4.6 and Sonnet 4.6.
> **Older models:** Use `anthropic.ThinkingConfigParamOfEnabled(N)` (budget must be < `MaxTokens`, min 1024).

To disable: `anthropic.ThinkingConfigParamUnion{OfDisabled: &anthropic.ThinkingConfigDisabledParam{}}`.

---

## Prompt Caching

`System` is `[]TextBlockParam`; set `CacheControl` on the last block to cache tools + system together. For placement patterns and the silent-invalidator audit checklist, see `shared/prompt-caching.md`.

```go
System: []anthropic.TextBlockParam{{
    Text:         longSystemPrompt,
    CacheControl: anthropic.NewCacheControlEphemeralParam(), // default 5m TTL
}},
```

For 1-hour TTL: `anthropic.CacheControlEphemeralParam{TTL: anthropic.CacheControlEphemeralTTLTTL1h}`. There's also a top-level `CacheControl` on `MessageNewParams` that auto-places on the last cacheable block.

Verify hits via `resp.Usage.CacheCreationInputTokens` / `resp.Usage.CacheReadInputTokens`.

---

## Stop Details

When `StopReason` is `anthropic.StopReasonRefusal`, the response includes structured `StopDetails`:

```go
if resp.StopReason == anthropic.StopReasonRefusal {
    fmt.Println("Category:", resp.StopDetails.Category)     // e.g. "cyber", "bio", "reasoning_extraction", "frontier_llm", or "" — see docs for the full set
    fmt.Println("Explanation:", resp.StopDetails.Explanation)
}
```

**Refusal fallbacks (Claude Fable 5) — opt in by default.** Fallbacks are opt-in: without them a refused request simply stops. In `claude-fable-5` code, include `Fallbacks: []anthropic.BetaFallbackParam{{Model: "claude-opus-4-8"}}` plus the `anthropic.AnthropicBetaServerSideFallback2026_06_01` beta on `client.Beta.Messages.New` by default — a policy decline is re-served by the fallback model inside the same call. Not available on Amazon Bedrock, Vertex AI, or Microsoft Foundry — register the client-side middleware there: `option.WithMiddleware(betafallback.BetaRefusalFallbackMiddleware(...))` from `lib/betafallback`, with per-conversation state via `betafallback.WithBetaFallbackState(&betafallback.BetaFallbackState{})`. Full semantics (billing, sticky routing, streaming) and a runnable example: `shared/model-migration.md` → Migrating to Claude Fable 5 → `refusal` stop reason, and the Go SDK repo's `examples/` (WebFetch via `shared/live-sources.md`).

---

## PDF / Document Input

`NewDocumentBlock` generic helper accepts any source type. `MediaType`/`Type` are auto-set.

```go
b64 := base64.StdEncoding.EncodeToString(pdfBytes)

msg := anthropic.NewUserMessage(
    anthropic.NewDocumentBlock(anthropic.Base64PDFSourceParam{Data: b64}),
    anthropic.NewTextBlock("Summarize this document"),
)
```

Other sources: `URLPDFSourceParam{URL: "https://..."}`, `PlainTextSourceParam{Data: "..."}`.

---

## Context Editing / Compaction (Beta)

Use `Beta.Messages.New` with `ContextManagement` on `BetaMessageNewParams`. There is no `NewBetaAssistantMessage` — use `.ToParam()` for the round-trip.

```go
params := anthropic.BetaMessageNewParams{
    Model:     anthropic.ModelClaudeOpus4_8,  // also supported: ModelClaudeSonnet4_6
    MaxTokens: 16000,
    Betas:     []anthropic.AnthropicBeta{"compact-2026-01-12"},
    ContextManagement: anthropic.BetaContextManagementConfigParam{
        Edits: []anthropic.BetaContextManagementConfigEditUnionParam{
            {OfCompact20260112: &anthropic.BetaCompact20260112EditParam{}},
        },
    },
    Messages: []anthropic.BetaMessageParam{ /* ... */ },
}

resp, err := client.Beta.Messages.New(ctx, params)
if err != nil {
    log.Fatal(err)
}

// Round-trip: append response to history via .ToParam()
params.Messages = append(params.Messages, resp.ToParam())

// Read compaction blocks from the response
for _, block := range resp.Content {
    if c, ok := block.AsAny().(anthropic.BetaCompactionBlock); ok {
        fmt.Println("compaction summary:", c.Content)
    }
}
```

Other edit types: `BetaClearToolUses20250919EditParam`, `BetaClearThinking20251015EditParam` — these need `Betas: []anthropic.AnthropicBeta{"context-management-2025-06-27"}`, not `compact-2026-01-12`.
