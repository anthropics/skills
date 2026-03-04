# Agent SDK — TypeScript

The Claude Agent SDK provides a higher-level interface for building AI agents with built-in tools, safety features, and agentic capabilities.

## Installation

```bash
npm install @anthropic-ai/claude-agent-sdk
```

---

## Quick Start

```typescript
import { query } from "@anthropic-ai/claude-agent-sdk";

for await (const message of query({
  prompt: "Explain this codebase",
  options: { allowedTools: ["Read", "Glob", "Grep"] },
})) {
  if ("result" in message) {
    console.log(message.result);
  }
}
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

## Permission System

```typescript
for await (const message of query({
  prompt: "Refactor the authentication module",
  options: {
    allowedTools: ["Read", "Edit", "Write"],
    permissionMode: "acceptEdits",
  },
})) {
  if ("result" in message) console.log(message.result);
}
```

Permission modes:

- `"default"`: Prompt for dangerous operations
- `"plan"`: Planning only, no execution
- `"acceptEdits"`: Auto-accept file edits
- `"dontAsk"`: Don't prompt (useful for CI/CD)
- `"bypassPermissions"`: Skip all prompts (requires `allowDangerouslySkipPermissions: true` in options)

---

## MCP (Model Context Protocol) Support

```typescript
for await (const message of query({
  prompt: "Open example.com and describe what you see",
  options: {
    mcpServers: {
      playwright: { command: "npx", args: ["@playwright/mcp@latest"] },
    },
  },
})) {
  if ("result" in message) console.log(message.result);
}
```

### In-Process MCP Tools

You can define custom tools that run in-process using `tool()` and `createSdkMcpServer`:

```typescript
import { query, tool, createSdkMcpServer } from "@anthropic-ai/claude-agent-sdk";
import { z } from "zod";

const myTool = tool("my-tool", "Description", { input: z.string() }, async (args) => {
  return { content: [{ type: "text", text: "result" }] };
});

const server = createSdkMcpServer({ name: "my-server", tools: [myTool] });

// Pass to query
for await (const message of query({
  prompt: "Use my-tool to do something",
  options: { mcpServers: { myServer: server } },
})) {
  if ("result" in message) console.log(message.result);
}
```

---

## Hooks

```typescript
import { query, HookCallback } from "@anthropic-ai/claude-agent-sdk";
import { appendFileSync } from "fs";

const logFileChange: HookCallback = async (input) => {
  const filePath = (input as any).tool_input?.file_path ?? "unknown";
  appendFileSync(
    "./audit.log",
    `${new Date().toISOString()}: modified ${filePath}\n`,
  );
  return {};
};

for await (const message of query({
  prompt: "Refactor utils.py to improve readability",
  options: {
    allowedTools: ["Read", "Edit", "Write"],
    permissionMode: "acceptEdits",
    hooks: {
      PostToolUse: [{ matcher: "Edit|Write", hooks: [logFileChange] }],
    },
  },
})) {
  if ("result" in message) console.log(message.result);
}
```

Available hook events: `PreToolUse`, `PostToolUse`, `PostToolUseFailure`, `Notification`, `UserPromptSubmit`, `SessionStart`, `SessionEnd`, `Stop`, `SubagentStart`, `SubagentStop`, `PreCompact`, `PermissionRequest`, `Setup`, `TeammateIdle`, `TaskCompleted`, `ConfigChange`

---

## Common Options

`query()` takes a top-level `prompt` (string) and an `options` object:

```typescript
query({ prompt: "...", options: { ... } })
```

| Option                              | Type   | Description                                                                |
| ----------------------------------- | ------ | -------------------------------------------------------------------------- |
| `cwd`                               | string | Working directory for file operations                                      |
| `allowedTools`                      | array  | Tools the agent can use (e.g., `["Read", "Edit", "Bash"]`)                |
| `tools`                             | array  | Built-in tools to make available (restricts the default set)               |
| `disallowedTools`                   | array  | Tools to explicitly disallow                                               |
| `permissionMode`                    | string | How to handle permission prompts                                           |
| `allowDangerouslySkipPermissions`   | bool   | Must be `true` to use `permissionMode: "bypassPermissions"`                |
| `mcpServers`                        | object | MCP servers to connect to                                                  |
| `hooks`                             | object | Hooks for customizing behavior                                             |
| `systemPrompt`                      | string | Custom system prompt                                                       |
| `maxTurns`                          | number | Maximum agent turns before stopping                                        |
| `maxBudgetUsd`                      | number | Maximum budget in USD for the query                                        |
| `model`                             | string | Model ID (default: determined by CLI)                                      |
| `agents`                            | object | Subagent definitions (`Record<string, AgentDefinition>`)                   |
| `outputFormat`                      | object | Structured output schema                                                   |
| `thinking`                          | object | Thinking/reasoning control                                                 |
| `betas`                             | array  | Beta features to enable (e.g., `["context-1m-2025-08-07"]`)               |
| `settingSources`                    | array  | Settings to load (e.g., `["project"]`). Default: none (no CLAUDE.md files) |
| `env`                               | object | Environment variables to set for the session                               |

---

## Subagents

```typescript
for await (const message of query({
  prompt: "Use the code-reviewer agent to review this codebase",
  options: {
    allowedTools: ["Read", "Glob", "Grep", "Agent"],
    agents: {
      "code-reviewer": {
        description: "Expert code reviewer for quality and security reviews.",
        prompt: "Analyze code quality and suggest improvements.",
        tools: ["Read", "Glob", "Grep"],
      },
    },
  },
})) {
  if ("result" in message) console.log(message.result);
}
```

---

## Message Types

```typescript
for await (const message of query({
  prompt: "Find TODO comments",
  options: { allowedTools: ["Read", "Glob", "Grep"] },
})) {
  if ("result" in message) {
    console.log(message.result);
  } else if (message.type === "system" && message.subtype === "init") {
    const sessionId = message.session_id; // Capture for resuming later
  }
}
```

---

## Best Practices

1. **Always specify allowedTools** — Explicitly list which tools the agent can use
2. **Set working directory** — Always specify `cwd` for file operations
3. **Use appropriate permission modes** — Start with `"default"` and only escalate when needed
4. **Handle all message types** — Check for `result` property to get agent output
5. **Limit maxTurns** — Prevent runaway agents with reasonable limits
