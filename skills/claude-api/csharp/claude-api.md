# Claude API — C#

> **Note:** The C# SDK is the official Anthropic SDK for C#. Tool use is supported via the Messages API. A class-annotation-based tool runner is not available; use raw tool definitions with JSON schema. The SDK also supports Microsoft.Extensions.AI IChatClient integration with function invocation.

## Installation

```bash
dotnet add package Anthropic
```

## Client Initialization

```csharp
using Anthropic;

// Default (uses ANTHROPIC_API_KEY env var)
AnthropicClient client = new();

// Explicit API key (use environment variables — never hardcode keys)
AnthropicClient client = new() {
    ApiKey = Environment.GetEnvironmentVariable("ANTHROPIC_API_KEY")
};
```

---

## Basic Message Request

```csharp
using Anthropic.Models.Messages;

var parameters = new MessageCreateParams
{
    Model = Model.ClaudeOpus4_6,
    MaxTokens = 1024,
    Messages = [new() { Role = Role.User, Content = "What is the capital of France?" }]
};
var message = await client.Messages.Create(parameters);
Console.WriteLine(message);
```

---

## Streaming

```csharp
using Anthropic.Models.Messages;

var parameters = new MessageCreateParams
{
    Model = Model.ClaudeOpus4_6,
    MaxTokens = 1024,
    Messages = [new() { Role = Role.User, Content = "Write a haiku" }]
};

await foreach (RawMessageStreamEvent streamEvent in client.Messages.CreateStreaming(parameters))
{
    if (streamEvent.TryPickContentBlockDelta(out var delta) &&
        delta.Delta.TryPickText(out var text))
    {
        Console.Write(text.Text);
    }
}
```

---

## Tool Use (Manual Loop)

The C# SDK supports raw tool definitions via JSON schema. See the [shared tool use concepts](../shared/tool-use-concepts.md) for the tool definition format and agentic loop pattern.
