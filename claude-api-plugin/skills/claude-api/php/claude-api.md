# Claude API — PHP

> **Note:** The PHP SDK is the official Anthropic SDK for PHP. Tool runner and Agent SDK are not available. Bedrock, Vertex AI, and Foundry clients are supported.

## Installation

```bash
composer require "anthropic-ai/sdk"
```

## Client Initialization

```php
use Anthropic\Client;

// Using API key from environment variable
$client = new Client(apiKey: getenv("ANTHROPIC_API_KEY"));
```

### Amazon Bedrock

```php
use Anthropic\BedrockClient;

$client = new BedrockClient(
    region: 'us-east-1',
);
```

### Google Vertex AI

```php
use Anthropic\VertexClient;

$client = new VertexClient(
    region: 'us-east5',
    projectId: 'my-project-id',
);
```

### Anthropic Foundry

```php
use Anthropic\FoundryClient;

$client = new FoundryClient(
    authToken: getenv("ANTHROPIC_AUTH_TOKEN"),
);
```

---

## Basic Message Request

```php
$message = $client->messages->create(
    model: 'claude-opus-4-6',
    maxTokens: 1024,
    messages: [
        ['role' => 'user', 'content' => 'What is the capital of France?'],
    ],
);
echo $message->content[0]->text;
```

---

## Streaming

```php
$stream = $client->messages->createStream(
    model: 'claude-opus-4-6',
    maxTokens: 1024,
    messages: [
        ['role' => 'user', 'content' => 'Write a haiku'],
    ],
);

foreach ($stream as $event) {
    echo $event;
}
```

---

## Tool Use (Manual Loop)

The PHP SDK supports raw tool definitions via JSON schema. See the [shared tool use concepts](../shared/tool-use-concepts.md) for the tool definition format and agentic loop pattern.
