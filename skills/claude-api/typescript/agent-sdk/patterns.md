# Agent SDK Patterns — TypeScript

## Basic Agent

```typescript
import { query } from "@anthropic-ai/claude-agent-sdk";

async function main() {
  for await (const message of query({
    prompt: "Explain what this repository does",
    options: {
      cwd: "/path/to/project",
      allowedTools: ["Read", "Glob", "Grep"],
    },
  })) {
    if ("result" in message) {
      console.log(message.result);
    }
  }
}

main();
```

---

## Hooks

### After Tool Use Hook

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

---

## Subagents

```typescript
import { query } from "@anthropic-ai/claude-agent-sdk";

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

## MCP Server Integration

### Browser Automation (Playwright)

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

---

## Session Resumption

```typescript
import { query } from "@anthropic-ai/claude-agent-sdk";

let sessionId: string | undefined;

// First query: capture the session ID
for await (const message of query({
  prompt: "Read the authentication module",
  options: { allowedTools: ["Read", "Glob"] },
})) {
  if (message.type === "system" && message.subtype === "init") {
    sessionId = message.session_id;
  }
}

// Resume with full context from the first query
for await (const message of query({
  prompt: "Now find all places that call it",
  options: { resume: sessionId },
})) {
  if ("result" in message) console.log(message.result);
}
```

---

## Custom System Prompt

```typescript
import { query } from "@anthropic-ai/claude-agent-sdk";

for await (const message of query({
  prompt: "Review this code",
  options: {
    allowedTools: ["Read", "Glob", "Grep"],
    systemPrompt: `You are a senior code reviewer focused on:
1. Security vulnerabilities
2. Performance issues
3. Code maintainability

Always provide specific line numbers and suggestions for improvement.`,
  },
})) {
  if ("result" in message) console.log(message.result);
}
```
