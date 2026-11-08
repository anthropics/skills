# Custom LLM Server

OpenAI-compatible LLM proxy for Agora Conversational AI. Intercepts LLM requests for RAG, tool calling, and conversation memory.

**Repo:** <https://github.com/AgoraIO-Conversational-AI/server-custom-llm>

## Implementations

| Language | Framework | Port | Notes |
|----------|-----------|------|-------|
| Python | FastAPI | 8100 | |
| Node.js | Express | 8101 | Advanced — exclusive features below |
| Go | Gin | 8102 | |

## Endpoints

- `/chat/completions` — LLM proxy with server-side tool execution (up to 5 passes)
- `/rag/chat/completions` — RAG-enhanced with retrieval step
- `/audio/chat/completions` — Multimodal audio responses

> **[README — Endpoints](https://github.com/AgoraIO-Conversational-AI/server-custom-llm#endpoints)**

## Integration with ConvoAI

Set `LLM_URL` to your server endpoint, `LLM_VENDOR=custom` in agent-samples `.env`.

> **[README — Integration](https://github.com/AgoraIO-Conversational-AI/server-custom-llm#integration-with-agora-conversational-ai)**

## Features

- Server-side tool execution (get_weather, calculate examples)
- Conversation memory (per appId:userId:channel, 100 message limit, 24h cleanup)
- RTM integration for text messaging (Node.js)
- Streaming SSE responses

> **[README — Features](https://github.com/AgoraIO-Conversational-AI/server-custom-llm#features)**

## Node.js-Exclusive Features

- `/register-agent` and `/unregister-agent` endpoints — agent lifecycle hooks
- Pluggable module system: `init()`, `getToolDefinitions()`, `onRequest`/`onResponse` hooks
- Dynamic RTM initialization via request headers (`X-Agora-Customllm-*`)
- Go audio subscriber for RTC audio capture (spawned as child process)

> **[node/integrations/README.md](https://github.com/AgoraIO-Conversational-AI/server-custom-llm/blob/main/node/integrations/README.md)** — Module system and integrations
