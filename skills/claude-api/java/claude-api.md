# Claude API — Java

> **Note:** The Java SDK supports the Claude API and beta tool use with annotated classes. Agent SDK is not yet available for Java.

## Installation

Maven:

```xml
<dependency>
    <groupId>com.anthropic</groupId>
    <artifactId>anthropic-java</artifactId>
    <version>2.15.0</version>
</dependency>
```

Gradle:

```groovy
implementation("com.anthropic:anthropic-java:2.15.0")
```

## Client Initialization

```java
import com.anthropic.client.AnthropicClient;
import com.anthropic.client.okhttp.AnthropicOkHttpClient;

// Default (reads ANTHROPIC_API_KEY from environment)
AnthropicClient client = AnthropicOkHttpClient.fromEnv();

// Explicit API key
AnthropicClient client = AnthropicOkHttpClient.builder()
    .apiKey("your-api-key")
    .build();
```

---

## Basic Message Request

```java
import com.anthropic.models.messages.MessageCreateParams;
import com.anthropic.models.messages.Message;
import com.anthropic.models.messages.Model;

MessageCreateParams params = MessageCreateParams.builder()
    .model(Model.CLAUDE_OPUS_4_6)
    .maxTokens(1024L)
    .addUserMessage("What is the capital of France?")
    .build();

Message response = client.messages().create(params);
response.content().stream()
    .flatMap(block -> block.text().stream())
    .forEach(textBlock -> System.out.println(textBlock.text()));
```

---

## Streaming

```java
import com.anthropic.core.http.StreamResponse;
import com.anthropic.models.messages.RawMessageStreamEvent;

MessageCreateParams params = MessageCreateParams.builder()
    .model(Model.CLAUDE_OPUS_4_6)
    .maxTokens(1024L)
    .addUserMessage("Write a haiku")
    .build();

try (StreamResponse<RawMessageStreamEvent> streamResponse = client.messages().createStreaming(params)) {
    streamResponse.stream()
        .flatMap(event -> event.contentBlockDelta().stream())
        .flatMap(deltaEvent -> deltaEvent.delta().text().stream())
        .forEach(textDelta -> System.out.print(textDelta.text()));
}
```

---

## Tool Use (Beta)

The Java SDK supports beta tool use with annotated classes. Tool classes implement `Supplier<String>` for automatic execution via `BetaToolRunner`.

### Tool Runner (automatic loop)

```java
import com.anthropic.models.beta.messages.MessageCreateParams;
import com.anthropic.models.beta.messages.BetaMessage;
import com.anthropic.helpers.BetaToolRunner;
import com.fasterxml.jackson.annotation.JsonClassDescription;
import com.fasterxml.jackson.annotation.JsonPropertyDescription;
import java.util.function.Supplier;

@JsonClassDescription("Get the weather in a given location")
static class GetWeather implements Supplier<String> {
    @JsonPropertyDescription("The city and state, e.g. San Francisco, CA")
    public String location;

    @Override
    public String get() {
        return "The weather in " + location + " is sunny and 72°F";
    }
}

BetaToolRunner toolRunner = client.beta().messages().toolRunner(
    MessageCreateParams.builder()
        .model("claude-opus-4-6")
        .maxTokens(1024L)
        .putAdditionalHeader("anthropic-beta", "structured-outputs-2025-11-13")
        .addTool(GetWeather.class)
        .addUserMessage("What's the weather in San Francisco?")
        .build());

for (BetaMessage message : toolRunner) {
    System.out.println(message);
}
```

### Non-Beta Tool Use

Tool use is also available through the non-beta `com.anthropic.models.messages.MessageCreateParams` with `addTool(Tool)` for manually defined JSON schemas, without needing the beta namespace. The beta namespace is only needed for the class-annotation convenience layer (`@JsonClassDescription`, `BetaToolRunner`).

### Manual Loop

For manual tool loops, define tools as JSON schema in the request, handle `tool_use` blocks in the response, send `tool_result` back, and loop until `stop_reason` is `"end_turn"`. See the [shared tool use concepts](../shared/tool-use-concepts.md) for the agentic loop pattern.
