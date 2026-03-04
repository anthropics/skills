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
- `"dontAsk"`: Don't prompt (useful for CI/CD)
- `"bypassPermissions"`: Skip all prompts (requires `allow_dangerously_skip_permissions=True` in options)

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

Available hook events: `PreToolUse`, `PostToolUse`, `PostToolUseFailure`, `Notification`, `UserPromptSubmit`, `SessionStart`, `SessionEnd`, `Stop`, `SubagentStart`, `SubagentStop`, `PreCompact`, `PermissionRequest`, `Setup`, `TeammateIdle`, `TaskCompleted`, `ConfigChange`

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
| `allow_dangerously_skip_permissions`| bool   | Must be `True` to use `permission_mode="bypassPermissions"`                |
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
    elif isinstance(message, SystemMessage) and message.subtype == "init":
        session_id = message.session_id  # Capture for resuming later
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

## Best Practices

1. **Always specify allowed_tools** — Explicitly list which tools the agent can use
2. **Set working directory** — Always specify `cwd` for file operations
3. **Use appropriate permission modes** — Start with `"default"` and only escalate when needed
4. **Handle all message types** — Check for `ResultMessage` to get agent output
5. **Limit max_turns** — Prevent runaway agents with reasonable limits
