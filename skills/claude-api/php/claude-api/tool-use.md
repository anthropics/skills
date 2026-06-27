# Tool Use — PHP

For conceptual overview (tool definitions, tool choice, tips), see [shared/tool-use-concepts.md](../../shared/tool-use-concepts.md).

## Tool Use

### Tool Runner (Beta)

**Beta:** The PHP SDK provides a tool runner via `$client->beta->messages->toolRunner()`. Define tools with `BetaRunnableTool` — a definition array plus a `run` closure:

```php
use Anthropic\Lib\Tools\BetaRunnableTool;

$weatherTool = new BetaRunnableTool(
    definition: [
        'name' => 'get_weather',
        'description' => 'Get the current weather for a location.',
        'inputSchema' => [
            'type' => 'object',
            'properties' => [
                'location' => ['type' => 'string', 'description' => 'City and state'],
            ],
            'required' => ['location'],
        ],
    ],
    run: function (array $input): string {
        return "The weather in {$input['location']} is sunny and 72°F.";
    },
);

$runner = $client->beta->messages->toolRunner(
    maxTokens: 16000,
    messages: [['role' => 'user', 'content' => 'What is the weather in Paris?']],
    model: 'claude-opus-4-8',
    tools: [$weatherTool],
);

foreach ($runner as $message) {
    foreach ($message->content as $block) {
        if ($block->type === 'text') {
            echo $block->text;
        }
    }
}
```

### Manual Loop

Tools are passed as arrays. **The SDK uses camelCase keys** (`inputSchema`, `toolUseID`, `stopReason`) and auto-maps to the API's snake_case on the wire — since v0.5.0. See [shared tool use concepts](../../shared/tool-use-concepts.md) for the loop pattern.

```php
use Anthropic\Messages\ToolUseBlock;

$tools = [
    [
        'name' => 'get_weather',
        'description' => 'Get the current weather in a given location',
        'inputSchema' => [  // camelCase, not input_schema
            'type' => 'object',
            'properties' => [
                'location' => ['type' => 'string', 'description' => 'City and state'],
            ],
            'required' => ['location'],
        ],
    ],
];

$messages = [['role' => 'user', 'content' => 'What is the weather in SF?']];

$response = $client->messages->create(
    model: 'claude-opus-4-8',
    maxTokens: 16000,
    tools: $tools,
    messages: $messages,
);

while ($response->stopReason === 'tool_use') {  // camelCase property
    $toolResults = [];
    foreach ($response->content as $block) {
        if ($block instanceof ToolUseBlock) {
            // $block->name  : string               — tool name to dispatch on
            // $block->input : array<string,mixed>  — parsed JSON input
            // $block->id    : string               — pass back as toolUseID
            $result = executeYourTool($block->name, $block->input);
            $toolResults[] = [
                'type' => 'tool_result',
                'toolUseID' => $block->id,  // camelCase, not tool_use_id
                'content' => $result,
            ];
        }
    }

    // Append assistant turn + user turn with tool results
    $messages[] = ['role' => 'assistant', 'content' => $response->content];
    $messages[] = ['role' => 'user', 'content' => $toolResults];

    $response = $client->messages->create(
        model: 'claude-opus-4-8',
        maxTokens: 16000,
        tools: $tools,
        messages: $messages,
    );
}

// Final text response
foreach ($response->content as $block) {
    if ($block->type === 'text') {
        echo $block->text;
    }
}
```

`$block->type === 'tool_use'` also works; `instanceof ToolUseBlock` narrows for PHPStan.


---

## Structured Outputs

### Using StructuredOutputModel (Recommended)

Define a PHP class implementing `StructuredOutputModel` and pass it as `outputConfig`:

```php
use Anthropic\Lib\Contracts\StructuredOutputModel;
use Anthropic\Lib\Concerns\StructuredOutputModelTrait;
use Anthropic\Lib\Attributes\Constrained;

class Person implements StructuredOutputModel
{
    use StructuredOutputModelTrait;

    #[Constrained(description: 'Full name')]
    public string $name;

    public int $age;

    public ?string $email = null;  // nullable = optional field
}

$message = $client->messages->create(
    model: 'claude-opus-4-8',
    maxTokens: 16000,
    messages: [['role' => 'user', 'content' => 'Generate a profile for Alice, age 30']],
    outputConfig: ['format' => Person::class],
);

$person = $message->parsedOutput();  // Person instance
echo $person->name;
```

Types are inferred from PHP type hints. Use `#[Constrained(description: '...')]` to add descriptions. Nullable properties (`?string`) become optional fields.

### Raw Schema

```php
$message = $client->messages->create(
    model: 'claude-opus-4-8',
    maxTokens: 16000,
    messages: [['role' => 'user', 'content' => 'Extract: John (john@co.com), Enterprise plan']],
    outputConfig: [
        'format' => [
            'type' => 'json_schema',
            'schema' => [
                'type' => 'object',
                'properties' => [
                    'name' => ['type' => 'string'],
                    'email' => ['type' => 'string'],
                    'plan' => ['type' => 'string'],
                ],
                'required' => ['name', 'email', 'plan'],
                'additionalProperties' => false,
            ],
        ],
    ],
);

// First text block contains valid JSON
foreach ($message->content as $block) {
    if ($block->type === 'text') {
        $data = json_decode($block->text, true);
        break;
    }
}
```

---

## Beta Features & Anthropic-Defined Tools

**`betas:` is NOT a param on `$client->messages->create()`** — it only exists on the beta namespace. Use it for features that need an explicit opt-in header:

```php
use Anthropic\Beta\Messages\BetaRequestMCPServerURLDefinition;

$response = $client->beta->messages->create(
    model: 'claude-opus-4-8',
    maxTokens: 16000,
    mcpServers: [
        BetaRequestMCPServerURLDefinition::with(
            name: 'my-server',
            url: 'https://example.com/mcp',
        ),
    ],
    betas: ['mcp-client-2025-11-20'],  // only valid on ->beta->messages
    messages: [['role' => 'user', 'content' => 'Use the MCP tools']],
);
```

### Task budgets

```php
$response = $client->beta->messages->create(
    model: 'claude-opus-4-8',
    maxTokens: 16000,
    outputConfig: ['taskBudget' => ['type' => 'tokens', 'total' => 64000]],
    tools: [...],
    messages: [...],
    betas: ['task-budgets-2026-03-13'],
);
```

### Cache diagnostics

Pass the previous response's `id` on the next request; print the `diagnostics` object on the response:

```php
$r2 = $client->beta->messages->create(
    model: 'claude-opus-4-8', maxTokens: 1024,
    diagnostics: ['previousMessageId' => $r1->id],
    betas: ['cache-diagnosis-2026-04-07'],
    messages: [...],
);
```

**Anthropic-defined tools** (bash, web_search, text_editor, code_execution) are GA and work on both paths. Of these, web_search and code_execution are server-executed; bash and text_editor are client-executed (you handle the `tool_use` locally) — `Anthropic\Messages\ToolBash20250124` / `WebSearchTool20260209` / `ToolTextEditor20250728` / `CodeExecutionTool20260120` for non-beta, `Anthropic\Beta\Messages\BetaToolBash20250124` / `BetaWebSearchTool20260209` / `BetaToolTextEditor20250728` / `BetaCodeExecutionTool20260120` for beta. No `betas:` header needed for these.

### Tool search (non-beta, server-side)

```php
tools: [
    ['type' => 'tool_search_tool_regex_20251119', 'name' => 'tool_search_tool_regex'],
    ['name' => 'get_weather', 'description' => '...', 'inputSchema' => [...], 'deferLoading' => true],
    // ... other user tools with 'deferLoading' => true
],
```

### Memory tool (non-beta, client-executed)

Declare `['type' => 'memory_20250818', 'name' => 'memory']`. Handle the `tool_use` by reading/writing files under a fixed `/memories` directory. **Validate every model-supplied path**: resolve to its canonical form and verify it remains within the memory directory; reject traversal (`..`, symlinks) — see `shared/tool-use-concepts.md` § Client-Side Tools.

---

