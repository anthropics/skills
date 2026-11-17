---
name: tamalebot
description: Deploy, manage, and interact with autonomous AI agents on TamaleBot. Send messages, check status, view audit logs, manage schedules, and deploy new agents — all from your coding agent.
---

# TamaleBot Agent Management

Use this skill when the user wants to deploy, manage, monitor, or interact with TamaleBot AI agents. TamaleBot hosts autonomous agents that can execute shell commands, browse the web, manage files, connect to Slack/Discord/Telegram/WhatsApp/Email, and integrate with Shopify, Stripe, HubSpot, Notion, and Google Workspace.

## Setup

Install the MCP server to get full tool access:

```bash
claude mcp add tamalebot -- npx -y @tamalebot/mcp-server
```

Set your token:

```bash
export TAMALEBOT_TOKEN=tb_your_token_here
```

Get a token by deploying your first agent at https://tamalebot.com

## Available Tools

### Messaging
- **tamalebot_message** — Send a message to a running agent and get its response. The agent processes it with its LLM, executes tool calls (shell, git, SSH, etc.), and returns the result. Use `chat_id` for separate conversation threads.

### Agent Management
- **tamalebot_list_agents** — List all deployed agents with status, provider, model, and creation date.
- **tamalebot_agent_status** — Get detailed status: running/stopped, provider, model, security policy, enabled skills, container state.
- **tamalebot_agent_logs** — View the audit trail: tool calls, policy decisions (allowed/blocked), and events. Filter by decision type. Essential for debugging and security review.
- **tamalebot_agent_skills** — List available and enabled skills for an agent.

### Deployment
- **tamalebot_deploy** — Deploy a new agent or update an existing one. Configure LLM provider (Anthropic, OpenAI, Google, Moonshot, MiniMax), system prompt, integrations (Slack, Discord, Telegram, WhatsApp, Email, GitHub), SaaS connectors (Shopify, Stripe, HubSpot, Notion), security policy, and add-ons (knowledge base, always-on, team seats, analytics).

### Scheduling
- **tamalebot_manage_schedule** — Create, list, delete, pause, or resume cron jobs on an agent. Schedules execute agent instructions on a timer (e.g., "check server health every 5 minutes").

### Lifecycle
- **tamalebot_clear_conversation** — Reset an agent's conversation history for a specific chat or the default conversation.
- **tamalebot_destroy_agent** — Permanently destroy an agent and all its data. Requires name confirmation.

### Browser Automation
- **tamalebot_webmcp_invoke** — Use an agent's headless browser to discover and invoke WebMCP tools on websites.

## Example Prompts

- "List my TamaleBot agents"
- "Send a message to ops-bot: check disk usage on all servers"
- "Show me the audit logs for deploy-bot — just the blocked actions"
- "Deploy a new agent called research-bot using claude-sonnet-4-5-20250929 with Slack integration"
- "Create a schedule on ops-bot to run server health checks every hour"
- "What skills does my support-bot have enabled?"

## Guidelines

- Always use `tamalebot_list_agents` first if you don't know the agent name.
- Use `chat_id` to maintain separate conversation threads with the same agent.
- Check `tamalebot_agent_status` before sending messages to confirm the agent is running.
- When deploying, `provider` is auto-detected from the model name if omitted.
- The `tamalebot_destroy_agent` tool requires passing `confirm_name` matching `agent_name` — this is intentional to prevent accidental deletion.
- Audit logs (`tamalebot_agent_logs`) show both allowed and blocked actions. Filter with `decision: "blocked"` to quickly find security policy violations.
- Managed mode (`llm_mode: "managed"`) uses TamaleBot's Claude — no API key needed. BYOK mode requires your own provider API key.
