# Agent SDK — Python

The Claude Agent SDK provides a higher-level interface for building AI agents with built-in tools, safety features, and agentic capabilities.

## Installation

```bash
pip install claude-agent-sdk
```

---

## Quick Start

```python
import anyio
from claude_agent_sdk import query, ClaudeAgentOptions, ResultMessage

async def main():
    async for message in query(
        prompt="Explain this codebase",
        options=ClaudeAgentOptions(allowed_tools=["Read", "Glob", "Grep"])
    ):
        if isinstance(message, ResultMessage):
            print(message.result)

anyio.run(main)
```

---

## Built-in Tools

| Tool      | Description                          |
| --------- | ------------------------------------ |
| Read      | Read files in the workspace          |
| Write     | Create new files                     |
| Edit      | Make precise edits to existing files |
| Bash      | Execute shell commands               |
| Glob      | Find files by pattern                |
| Grep      | Search files by content              |
| WebSearch | Search the web for information       |
| WebFetch        | Fetch and analyze web pages          |
| AskUserQuestion | Ask user clarifying questions         |
| Agent           | Spawn subagents                      |

---

## Primary Interfaces

### `query()` — Simple One-Shot Usage

The `query()` function is the simplest way to run an agent. It returns an async iterator of messages.

```python
from claude_agent_sdk import query, ClaudeAgentOptions, ResultMessage

async for message in query(
    prompt="Explain this codebase",
    options=ClaudeAgentOptions(allowed_tools=["Read", "Glob", "Grep"])
):
    if isinstance(message, ResultMessage):
        print(message.result)
```

### `ClaudeSDKClient` — Full Control

`ClaudeSDKClient` provides full control over the agent lifecycle. Use it when you need custom tools, hooks, streaming, or the ability to interrupt execution.

```python
import anyio
from claude_agent_sdk import ClaudeSDKClient, ClaudeAgentOptions, AssistantMessage, TextBlock

async def main():
    options = ClaudeAgentOptions(allowed_tools=["Read", "Glob", "Grep"])
    async with ClaudeSDKClient(options=options) as client:
        await client.query("Explain this codebase")
        async for message in client.receive_response():
            if isinstance(message, AssistantMessage):
                for block in message.content:
                    if isinstance(block, TextBlock):
                        print(block.text)

anyio.run(main)
```

`ClaudeSDKClient` supports:

- **Context manager** (`async with`) for automatic resource cleanup
- **`client.query(prompt)`** to send a prompt to the agent
- **`receive_response()`** for streaming messages until completion
- **`interrupt()`** to stop agent execution mid-task
- **Required for custom tools** (via SDK MCP servers)

---

## Permission System

```python
from claude_agent_sdk import query, ClaudeAgentOptions, ResultMessage

async for message in query(
    prompt="Refactor the authentication module",
    options=ClaudeAgentOptions(
        allowed_tools=["Read", "Edit", "Write"],
        permission_mode="acceptEdits"  # Auto-accept file edits
    )
):
    if isinstance(message, ResultMessage):
        print(message.result)
```

Permission modes:

- `"default"`: Prompt for dangerous operations
- `"plan"`: Planning only, no execution
- `"acceptEdits"`: Auto-accept file edits
- `"bypassPermissions"`: Skip all prompts (use with caution)

---

## MCP (Model Context Protocol) Support

```python
from claude_agent_sdk import query, ClaudeAgentOptions, ResultMessage

async for message in query(
    prompt="Open example.com and describe what you see",
    options=ClaudeAgentOptions(
        mcp_servers={
            "playwright": {"command": "npx", "args": ["@playwright/mcp@latest"]}
        }
    )
):
    if isinstance(message, ResultMessage):
        print(message.result)
```

---

## Hooks

Customize agent behavior with hooks using callback functions:

```python
from claude_agent_sdk import query, ClaudeAgentOptions, HookMatcher, ResultMessage

async def log_file_change(input_data, tool_use_id, context):
    file_path = input_data.get('tool_input', {}).get('file_path', 'unknown')
    print(f"Modified: {file_path}")
    return {}

async for message in query(
    prompt="Refactor utils.py",
    options=ClaudeAgentOptions(
        permission_mode="acceptEdits",
        hooks={
            "PostToolUse": [HookMatcher(matcher="Edit|Write", hooks=[log_file_change])]
        }
    )
):
    if isinstance(message, ResultMessage):
        print(message.result)
```

Hook callback inputs for tool-lifecycle events (`PreToolUse`, `PostToolUse`, `PostToolUseFailure`) include `agent_id` and `agent_type` fields, allowing hooks to identify which agent (main or subagent) triggered the tool call.

Available hook events: `PreToolUse`, `PostToolUse`, `PostToolUseFailure`, `UserPromptSubmit`, `Stop`, `SubagentStop`, `PreCompact`, `Notification`, `SubagentStart`, `PermissionRequest`

---

## Common Options

`query()` takes a top-level `prompt` (string) and an `options` object (`ClaudeAgentOptions`):

```python
async for message in query(prompt="...", options=ClaudeAgentOptions(...)):
```

| Option                              | Type   | Description                                                                |
| ----------------------------------- | ------ | -------------------------------------------------------------------------- |
| `cwd`                               | string | Working directory for file operations                                      |
| `allowed_tools`                     | list   | Tools the agent can use (e.g., `["Read", "Edit", "Bash"]`)                |
| `tools`                             | list   | Built-in tools to make available (restricts the default set)               |
| `disallowed_tools`                  | list   | Tools to explicitly disallow                                               |
| `permission_mode`                   | string | How to handle permission prompts                                           |
| `mcp_servers`                       | dict   | MCP servers to connect to                                                  |
| `hooks`                             | dict   | Hooks for customizing behavior                                             |
| `system_prompt`                     | string | Custom system prompt                                                       |
| `max_turns`                         | int    | Maximum agent turns before stopping                                        |
| `max_budget_usd`                    | float  | Maximum budget in USD for the query                                        |
| `model`                             | string | Model ID (default: determined by CLI)                                      |
| `agents`                            | dict   | Subagent definitions (`dict[str, AgentDefinition]`)                        |
| `output_format`                     | dict   | Structured output schema                                                   |
| `thinking`                          | dict   | Thinking/reasoning control                                                 |
| `betas`                             | list   | Beta features to enable (e.g., `["context-1m-2025-08-07"]`)               |
| `setting_sources`                   | list   | Settings to load (e.g., `["project"]`). Default: none (no CLAUDE.md files) |
| `env`                               | dict   | Environment variables to set for the session                               |

---

## Message Types

```python
from claude_agent_sdk import query, ClaudeAgentOptions, ResultMessage, SystemMessage

async for message in query(
    prompt="Find TODO comments",
    options=ClaudeAgentOptions(allowed_tools=["Read", "Glob", "Grep"])
):
    if isinstance(message, ResultMessage):
        print(message.result)
        print(f"Stop reason: {message.stop_reason}")  # e.g., "end_turn", "max_turns"
    elif isinstance(message, SystemMessage) and message.subtype == "init":
        session_id = message.data.get("session_id")  # Capture for resuming later
```

`AssistantMessage` includes per-turn `usage` data (a dict matching the Anthropic API usage shape) for tracking costs:

```python
from claude_agent_sdk import query, ClaudeAgentOptions, AssistantMessage

async for message in query(prompt="...", options=ClaudeAgentOptions()):
    if isinstance(message, AssistantMessage) and message.usage:
        print(f"Input: {message.usage['input_tokens']}, Output: {message.usage['output_tokens']}")
```

Typed task message subclasses are available for better type safety when handling subagent task events:
- `TaskStartedMessage` — emitted when a subagent task is registered
- `TaskProgressMessage` — real-time progress updates with cumulative usage metrics
- `TaskNotificationMessage` — task completion notifications

`RateLimitEvent` is emitted when the rate limit status transitions (e.g., from `allowed` to `allowed_warning` or `rejected`). Use it to warn users or back off gracefully:

```python
from claude_agent_sdk import query, ClaudeAgentOptions, RateLimitEvent

async for message in query(prompt="...", options=ClaudeAgentOptions()):
    if isinstance(message, RateLimitEvent):
        print(f"Rate limit status: {message.rate_limit_info.status}")
        if message.rate_limit_info.resets_at:
            print(f"Resets at: {message.rate_limit_info.resets_at}")
```

---

## Subagents

```python
from claude_agent_sdk import query, ClaudeAgentOptions, AgentDefinition, ResultMessage

async for message in query(
    prompt="Use the code-reviewer agent to review this codebase",
    options=ClaudeAgentOptions(
        allowed_tools=["Read", "Glob", "Grep", "Agent"],
        agents={
            "code-reviewer": AgentDefinition(
                description="Expert code reviewer for quality and security reviews.",
                prompt="Analyze code quality and suggest improvements.",
                tools=["Read", "Glob", "Grep"]
            )
        }
    )
):
    if isinstance(message, ResultMessage):
        print(message.result)
```

---

## Error Handling

```python
from claude_agent_sdk import query, ClaudeAgentOptions, CLINotFoundError, CLIConnectionError, ResultMessage

try:
    async for message in query(
        prompt="...",
        options=ClaudeAgentOptions(allowed_tools=["Read"])
    ):
        if isinstance(message, ResultMessage):
            print(message.result)
except CLINotFoundError:
    print("Claude Code CLI not found. Install with: pip install claude-agent-sdk")
except CLIConnectionError as e:
    print(f"Connection error: {e}")
```

---

## Session History

Retrieve past session data with top-level functions:

```python
from claude_agent_sdk import list_sessions, get_session_messages

# List all past sessions (sync function — no await)
sessions = list_sessions()
for session in sessions:
    print(f"{session.session_id}: {session.cwd}")

# Get messages from a specific session (sync function — no await)
messages = get_session_messages(session_id="...")
for msg in messages:
    print(msg)
```

### Session Mutations

Rename or tag sessions (sync functions — no await):

```python
from claude_agent_sdk import rename_session, tag_session

# Rename a session
rename_session(session_id="...", title="My refactoring session")

# Tag a session (tags are Unicode-sanitized automatically)
tag_session(session_id="...", tag="experiment")

# Clear a tag
tag_session(session_id="...", tag=None)

# Optionally scope to a specific project directory
rename_session(session_id="...", title="New title", directory="/path/to/project")
```

---

## MCP Server Management

Manage MCP servers at runtime using `ClaudeSDKClient`:

```python
async with ClaudeSDKClient(options=options) as client:
    # Reconnect a disconnected MCP server
    await client.reconnect_mcp_server("my-server")

    # Toggle an MCP server on/off
    await client.toggle_mcp_server("my-server", enabled=False)

    # Get status of all MCP servers
    status = await client.get_mcp_status()  # returns McpStatusResponse
```

---

## Best Practices

1. **Always specify allowed_tools** — Explicitly list which tools the agent can use
2. **Set working directory** — Always specify `cwd` for file operations
3. **Use appropriate permission modes** — Start with `"default"` and only escalate when needed
4. **Handle all message types** — Check for `ResultMessage` to get agent output
5. **Limit max_turns** — Prevent runaway agents with reasonable limits
