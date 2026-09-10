---
name: ai-to-ai
description: >
  AI-to-AI communication over HTTP -- send tasks to and receive tasks from other AI agents.
  Use this skill when you need to: communicate with another AI agent, delegate tasks to Jarvis
  or another assistant, build an AI agent server, set up multi-agent coordination, implement
  agent-to-agent protocols, or create tools that let AI systems talk to each other. Triggers on:
  "talk to Jarvis", "send task to agent", "AI-to-AI", "A2A", "multi-agent", "agent communication",
  "delegate to", "inter-agent", or any request involving one AI calling another AI over HTTP.
---

# AI-to-AI Communication: Sending Tasks Between Agents Over HTTP

AI-to-AI (A2A) communication lets one AI agent send a natural language task to another and get back a structured result. The pattern is simple: POST a JSON body with a `task` field to the target agent's HTTP endpoint. The agent executes the task using its own tools and capabilities, then returns the result with metadata like execution time and tools used.

This is how Claude Code can delegate work to Jarvis (a macOS AI assistant), how Jarvis can delegate to peer agents on the local network, or how any two AI systems can collaborate.

## Protocol Overview

The core protocol is a single HTTP POST:

```
POST /ai-to-ai HTTP/1.1
Host: localhost:8765
Content-Type: application/json
Authorization: Bearer <token>

{
  "task": "What is the current weather in San Francisco?",
  "context": "User is planning outdoor activities this weekend"
}
```

**Request fields:**
- `task` (string, required) -- The natural language instruction for the agent to execute.
- `context` (string, optional) -- Additional context prepended to the task as "Context: ... Task: ...".

**Response (200 OK):**
```json
{
  "status": "success",
  "result": "The current weather in San Francisco is 62F, partly cloudy...",
  "execution_time_ms": 3450,
  "tools_used": ["web_search", "summarize"],
  "request_id": "550e8400-e29b-41d4-a716-446655440000"
}
```

**Response fields:**
- `status` -- `"success"` or `"error"`.
- `result` -- The agent's natural language response (secrets are redacted automatically).
- `execution_time_ms` -- How long the agent spent executing the task.
- `tools_used` -- Array of tool names the agent invoked (may be empty).
- `request_id` -- Unique ID for this request, useful for debugging and audit trails.

## Status Check

Verify the agent is running before sending tasks:

```
GET /ai-to-ai/status HTTP/1.1
Host: localhost:8765
```

Response:
```json
{
  "status": "ok",
  "port": 8765,
  "connections": 2,
  "uptime": "running"
}
```

## Authentication

Remote requests require a Bearer token in the `Authorization` header. Localhost requests (127.0.0.1, ::1, localhost) bypass authentication and are treated as admin.

For remote agents, tokens are generated and stored encrypted. Each token is associated with an RBAC role (admin, user, guest, automation) that controls what the caller can do. The token format in storage is `token|role|created_at`, and lookup uses constant-time comparison to prevent timing attacks.

**Roles:**
- `admin` -- Full access to all capabilities.
- `user` -- Standard task execution.
- `automation` -- Default for generated keys. Task execution with audit logging.
- `guest` -- Limited access, may be restricted from certain tools.

## Error Responses

The server returns standard HTTP status codes with JSON error bodies:

| Status | Meaning | Example |
|--------|---------|---------|
| 400 | Bad request -- missing or empty `task` field | `{"status":"error","error":"Invalid request -- must include non-empty 'task' field"}` |
| 401 | Unauthorized -- invalid or missing Bearer token | `{"status":"error","error":"Unauthorized -- invalid or missing API key"}` |
| 403 | Forbidden -- token's role lacks permission | `{"status":"error","error":"Forbidden -- role 'guest' is not permitted"}` |
| 429 | Rate limited -- too many requests | `{"status":"error","error":"Rate limit exceeded -- try again later"}` |
| 503 | Server not ready -- workflow engine not wired | `{"status":"error","error":"AI-to-AI server not yet wired to WorkflowEngine"}` |

All error responses include a `request_id` for tracing.

The server enforces a 600-second timeout. If the task takes longer, the response will be:
```json
{"status": "success", "result": "Error: AI-to-AI request timed out after 600s", "execution_time_ms": 600000}
```

## Client Examples

### curl

```bash
# Health check
curl -s http://localhost:8765/ai-to-ai/status | python3 -m json.tool

# Send a task (localhost -- no auth needed)
curl -s -X POST http://localhost:8765/ai-to-ai \
  -H "Content-Type: application/json" \
  -d '{"task": "What time is it?"}' | python3 -m json.tool

# Send a task with context
curl -s -X POST http://localhost:8765/ai-to-ai \
  -H "Content-Type: application/json" \
  -d '{
    "task": "Summarize the latest 3 commits",
    "context": "Working in the Open-Jarvis repo at ~/Open-Jarvis"
  }' | python3 -m json.tool

# Remote request with Bearer token
curl -s -X POST http://192.168.1.50:8765/ai-to-ai \
  -H "Content-Type: application/json" \
  -H "Authorization: Bearer abc123def456..." \
  -d '{"task": "Check disk usage on this Mac"}'
```

### Python (requests)

```python
import requests

JARVIS_URL = "http://localhost:8765/ai-to-ai"

def send_task(task: str, context: str | None = None, token: str | None = None) -> dict:
    """Send a task to a Jarvis AI-to-AI server and return the parsed response."""
    headers = {"Content-Type": "application/json"}
    if token:
        headers["Authorization"] = f"Bearer {token}"

    payload = {"task": task}
    if context:
        payload["context"] = context

    resp = requests.post(JARVIS_URL, json=payload, headers=headers, timeout=120)
    resp.raise_for_status()
    return resp.json()


# Simple task
result = send_task("What apps are currently running?")
print(result["result"])
print(f"Took {result['execution_time_ms']}ms, used tools: {result.get('tools_used', [])}")

# Task with context
result = send_task(
    task="Run the test suite and report failures",
    context="Python project at /Users/me/myproject, uses pytest"
)
if result["status"] == "success":
    print(result["result"])
else:
    print(f"Error: {result['error']}")
```

### Python (aiohttp -- async)

```python
import aiohttp
import asyncio

async def send_task_async(task: str, context: str | None = None) -> dict:
    payload = {"task": task}
    if context:
        payload["context"] = context

    async with aiohttp.ClientSession() as session:
        async with session.post(
            "http://localhost:8765/ai-to-ai",
            json=payload,
            timeout=aiohttp.ClientTimeout(total=120)
        ) as resp:
            resp.raise_for_status()
            return await resp.json()

# Run multiple tasks concurrently
async def main():
    tasks = await asyncio.gather(
        send_task_async("What is the system uptime?"),
        send_task_async("How much free disk space is there?"),
        send_task_async("List running Python processes"),
    )
    for result in tasks:
        print(result["result"])
        print("---")

asyncio.run(main())
```

### Node.js (fetch)

```javascript
async function sendTask(task, context = null, token = null) {
  const headers = { "Content-Type": "application/json" };
  if (token) headers["Authorization"] = `Bearer ${token}`;

  const body = { task };
  if (context) body.context = context;

  const resp = await fetch("http://localhost:8765/ai-to-ai", {
    method: "POST",
    headers,
    body: JSON.stringify(body),
    signal: AbortSignal.timeout(120_000),
  });

  if (!resp.ok) {
    const err = await resp.json().catch(() => ({ error: resp.statusText }));
    throw new Error(`A2A error ${resp.status}: ${err.error}`);
  }
  return resp.json();
}

// Usage
const result = await sendTask("Search the web for 'latest Node.js release' and summarize");
console.log(result.result);
console.log(`Tools: ${result.tools_used?.join(", ") || "none"}`);
```

## Building an A2A Server

Any HTTP server that accepts `POST /ai-to-ai` with a JSON `task` field and returns the response format above is A2A-compatible. Here are minimal implementations:

### Python Server (Flask)

```python
from flask import Flask, request, jsonify
import time
import uuid

app = Flask(__name__)

# Replace with your actual AI execution logic
def execute_task(task: str, context: str | None) -> tuple[str, list[str]]:
    """Execute a task and return (result_text, tools_used)."""
    # Your AI logic here -- call an LLM, run tools, etc.
    return f"Processed: {task}", ["example_tool"]

@app.route("/ai-to-ai", methods=["POST"])
def handle_task():
    data = request.get_json(silent=True) or {}
    task = data.get("task", "").strip()
    if not task:
        return jsonify({
            "status": "error",
            "error": "Invalid request -- must include non-empty 'task' field",
            "request_id": str(uuid.uuid4())
        }), 400

    context = data.get("context")
    request_id = str(uuid.uuid4())
    start = time.time()

    try:
        result, tools = execute_task(task, context)
        elapsed_ms = int((time.time() - start) * 1000)
        return jsonify({
            "status": "success",
            "result": result,
            "execution_time_ms": elapsed_ms,
            "tools_used": tools,
            "request_id": request_id
        })
    except Exception as e:
        return jsonify({
            "status": "error",
            "error": str(e),
            "request_id": request_id
        }), 500

@app.route("/ai-to-ai/status", methods=["GET"])
def status():
    return jsonify({"status": "ok", "port": 8765, "uptime": "running"})

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=8765)
```

### Node.js Server (Express)

```javascript
import express from "express";
import { randomUUID } from "crypto";

const app = express();
app.use(express.json());

// Replace with your actual AI execution logic
async function executeTask(task, context) {
  // Your AI logic here
  return { result: `Processed: ${task}`, toolsUsed: ["example_tool"] };
}

// Bearer token validation middleware
function authenticate(req, res, next) {
  const host = req.hostname;
  if (["localhost", "127.0.0.1", "::1"].includes(host)) return next();

  const auth = req.headers.authorization;
  if (!auth?.startsWith("Bearer ")) {
    return res.status(401).json({
      status: "error",
      error: "Unauthorized -- missing Bearer token",
      request_id: randomUUID(),
    });
  }

  const token = auth.slice(7);
  if (!isValidToken(token)) {
    return res.status(401).json({
      status: "error",
      error: "Unauthorized -- invalid API key",
      request_id: randomUUID(),
    });
  }
  next();
}

function isValidToken(token) {
  // Implement your token validation -- check against a database or secrets store
  const validTokens = new Set([process.env.A2A_API_KEY]);
  return validTokens.has(token);
}

app.post("/ai-to-ai", authenticate, async (req, res) => {
  const { task, context } = req.body;
  const requestId = randomUUID();

  if (!task?.trim()) {
    return res.status(400).json({
      status: "error",
      error: "Invalid request -- must include non-empty 'task' field",
      request_id: requestId,
    });
  }

  const start = Date.now();
  try {
    const { result, toolsUsed } = await executeTask(task, context);
    res.json({
      status: "success",
      result,
      execution_time_ms: Date.now() - start,
      tools_used: toolsUsed,
      request_id: requestId,
    });
  } catch (err) {
    res.status(500).json({
      status: "error",
      error: err.message,
      request_id: requestId,
    });
  }
});

app.get("/ai-to-ai/status", (req, res) => {
  res.json({ status: "ok", port: 8765, uptime: "running" });
});

app.listen(8765, () => console.log("A2A server on port 8765"));
```

## Multi-Agent Patterns

### Fan-Out: One Agent Delegates to Many

Send subtasks to multiple specialized agents in parallel, then combine results:

```python
import asyncio
import aiohttp

AGENTS = {
    "researcher": "http://localhost:8765/ai-to-ai",
    "coder": "http://localhost:8766/ai-to-ai",
    "reviewer": "http://localhost:8767/ai-to-ai",
}

async def fan_out(subtasks: dict[str, str]) -> dict[str, dict]:
    """Send different tasks to different agents concurrently."""
    async with aiohttp.ClientSession() as session:
        async def call_agent(name: str, task: str):
            async with session.post(AGENTS[name], json={"task": task}, timeout=aiohttp.ClientTimeout(total=120)) as resp:
                return name, await resp.json()

        results = await asyncio.gather(*[
            call_agent(name, task)
            for name, task in subtasks.items()
        ])
        return dict(results)

# Usage: three agents work in parallel
results = asyncio.run(fan_out({
    "researcher": "Find the top 3 Python web frameworks by GitHub stars",
    "coder": "Write a hello world HTTP server in each: Flask, FastAPI, Django",
    "reviewer": "What are common security pitfalls in Python web apps?",
}))

for agent, result in results.items():
    print(f"[{agent}] {result['result'][:200]}...")
```

### Pipeline: Sequential Agent Chain

Pass the output of one agent as context to the next:

```python
import requests

def pipeline(steps: list[tuple[str, str]], initial_context: str = "") -> str:
    """Run a chain of (agent_url, task) pairs, passing each result as context to the next."""
    context = initial_context
    for agent_url, task in steps:
        payload = {"task": task}
        if context:
            payload["context"] = context
        resp = requests.post(agent_url, json=payload, timeout=120)
        resp.raise_for_status()
        data = resp.json()
        if data["status"] != "success":
            raise RuntimeError(f"Agent failed: {data.get('error', 'unknown')}")
        context = data["result"]
    return context

# Usage: research -> code -> review
final = pipeline([
    ("http://localhost:8765/ai-to-ai", "Research best practices for REST API pagination"),
    ("http://localhost:8766/ai-to-ai", "Implement a paginated API endpoint based on the research"),
    ("http://localhost:8767/ai-to-ai", "Review this code for bugs, security issues, and style"),
])
print(final)
```

### Supervisor: One Agent Orchestrates Others

A supervisor agent decides which sub-agents to call and how to combine their work:

```python
import requests

AGENTS = {
    "search": "http://localhost:8765/ai-to-ai",
    "code": "http://localhost:8766/ai-to-ai",
    "memory": "http://localhost:8767/ai-to-ai",
}

def supervisor_dispatch(user_request: str) -> str:
    """A supervisor agent that routes tasks to the appropriate sub-agent."""
    # Step 1: Ask the planning agent to decompose the task
    plan = requests.post(AGENTS["memory"], json={
        "task": f"Decompose this request into sub-tasks and identify which agent should handle each. "
                f"Available agents: search (web research), code (write/run code), memory (recall facts). "
                f"Request: {user_request}"
    }, timeout=60).json()

    # Step 2: Execute sub-tasks (simplified -- in practice, parse the plan)
    results = {}
    for agent_name, agent_url in AGENTS.items():
        sub_result = requests.post(agent_url, json={
            "task": user_request,
            "context": f"You are the {agent_name} agent. Focus on your specialty."
        }, timeout=120).json()
        results[agent_name] = sub_result.get("result", "")

    # Step 3: Synthesize
    synthesis = requests.post(AGENTS["memory"], json={
        "task": "Synthesize these results into a coherent answer",
        "context": "\n\n".join(f"[{k}]: {v}" for k, v in results.items())
    }, timeout=60).json()

    return synthesis.get("result", "Synthesis failed")
```

## Google A2A Protocol (Advanced)

Jarvis also implements Google's open A2A specification (https://google.github.io/A2A/) for standardized agent interoperability. This uses JSON-RPC 2.0 over HTTPS with optional Server-Sent Events for streaming.

**Key differences from the simple HTTP protocol above:**
- Uses JSON-RPC 2.0 envelope (`jsonrpc`, `id`, `method`, `params`).
- Agent capabilities are described in an AgentCard at `GET /.well-known/agent.json`.
- Tasks have a lifecycle with states: submitted, working, completed, failed, cancelled, input-required.
- Messages are structured with typed parts (text, file, data).
- Discovery uses Bonjour/mDNS (`_a2a._tcp`) for zero-config LAN peer discovery.
- HTTPS is required for remote agents; HTTP is permitted only for localhost and `.local` hosts.

**AgentCard (served at `/.well-known/agent.json`):**
```json
{
  "name": "Jarvis",
  "description": "Autonomous AI assistant with tool execution and multi-agent coordination",
  "url": "https://agent.example.com",
  "version": "1.0",
  "capabilities": {
    "streaming": true,
    "pushNotifications": false,
    "stateTransitionHistory": true
  },
  "skills": [
    {
      "id": "task_execution",
      "name": "Task Execution",
      "description": "Execute multi-step tasks using tools: shell, web search, file ops",
      "tags": ["automation", "tools"],
      "examples": ["Run my test suite", "Search the web for X"]
    }
  ],
  "authentication": {"schemes": ["bearer"]}
}
```

**Sending a task via JSON-RPC:**
```bash
curl -s -X POST https://agent.example.com/rpc \
  -H "Content-Type: application/json" \
  -d '{
    "jsonrpc": "2.0",
    "id": "req-1",
    "method": "tasks/send",
    "params": {
      "id": "task-abc",
      "message": {
        "role": "user",
        "parts": [{"type": "text", "text": "Summarize my unread emails"}]
      }
    }
  }'
```

For most use cases, the simple HTTP protocol (`POST /ai-to-ai` with a `task` field) is all you need. Use the Google A2A protocol when you need interoperability with agents that implement that spec, or when you need streaming, lifecycle management, or LAN discovery.

## Practical Tips

1. **Always check status first.** Call `GET /ai-to-ai/status` before sending tasks. A 503 means the agent's workflow engine is not ready yet.

2. **Set reasonable timeouts.** The server has a 600-second internal timeout. Set your client timeout to match or be slightly longer. For quick tasks, a 30-60 second client timeout avoids hanging.

3. **Use context for better results.** The `context` field gives the agent background information without mixing it into the task instruction. Use it for: working directory, project details, prior conversation, constraints.

4. **Handle errors gracefully.** Always check `status` in the response. A 200 with `"status": "error"` is possible if the task itself fails but the server processed it.

5. **Localhost is special.** Requests from localhost skip authentication and get admin role. This is by design for local development tools like Claude Code. For remote access, always use Bearer tokens.

6. **Rate limits apply.** The server enforces rate limiting. If you get a 429, back off and retry after a delay. Do not retry in a tight loop.

7. **Max connections.** The server allows at most 20 concurrent connections. Fan-out patterns should respect this limit or use a semaphore.

8. **Max message size.** Request bodies are limited to 1MB. If you need to send large content, reference it by file path in the task instead of embedding it.

9. **Secrets are redacted.** The server automatically strips secrets from responses using `TextUtils.redactSecrets()`. Do not rely on the agent to avoid leaking sensitive data in its response -- the server handles this.

10. **Audit trail.** Every task execution is logged with the caller's key name, role, task preview, tools used, and duration. Self-assessment tasks (containing "rate yourself", "score yourself", etc.) are excluded from memory persistence to prevent feedback loops.
