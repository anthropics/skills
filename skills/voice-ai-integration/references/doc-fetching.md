# Documentation Lookup

**Level 1 — Bundled references (always try first)**

Check the relevant file under `skills/agora/references/`. These are inline-stable:
RTC init patterns, RTM messaging, token generation, ConvoAI gotchas and generation
rules. If the answer is here, stop — no fetch needed.

**Level 2 — Live docs (when Level 1 is insufficient)**

When bundled references don't cover the detail needed (full request/response schemas,
vendor-specific configs, language-specific quick-start code):

If the Agora Docs MCP tool is available in the current tool/runtime, prefer it for Level 2 lookup. Otherwise use the HTTP fetch flow below. If MCP returns no useful result, fall back to HTTP fetch.

1. Fetch the Agora docs sitemap:
   ```
   GET https://docs.agora.io/en/llms.txt
   ```
2. Scan the response for a URL matching the product and topic.
3. Fetch that URL and use its content to answer.

## Fallback

If `llms.txt` is unreachable or the fetched URL returns no useful content, try these
known markdown entry points directly:

| Product / Language | Markdown URL |
|---|---|
| RTC (Web/general) | https://docs-md.agora.io/en/video-calling/get-started/get-started-sdk.md |
| RTC (voice-only) | https://docs-md.agora.io/en/voice-calling/get-started/get-started-sdk.md |
| RTM (Web/general) | https://docs-md.agora.io/en/signaling/get-started/sdk-quickstart.md |
| RTM (iOS) | https://docs-md.agora.io/en/signaling/get-started/sdk-quickstart?platform=ios.md |
| RTM (Android) | https://docs-md.agora.io/en/signaling/get-started/sdk-quickstart?platform=android.md |
| ConvoAI | https://docs-md.agora.io/en/conversational-ai/get-started/quickstart.md |
| ConvoAI (TypeScript SDK) | https://docs-md.agora.io/en/conversational-ai/develop/integrate-sdk.md |
| ConvoAI (Python SDK) | https://docs-md.agora.io/en/conversational-ai/develop/integrate-sdk?platform=python.md |
| Cloud Recording | https://docs-md.agora.io/en/cloud-recording/get-started/getstarted.md |
| Server Gateway (C++) | https://docs-md.agora.io/en/server-gateway/get-started/integrate-sdk.md |
| Server Gateway (Java) | https://docs-md.agora.io/en/server-gateway/get-started/integrate-sdk?platform=java.md |
| Server Gateway (Python) | https://docs-md.agora.io/en/server-gateway/get-started/integrate-sdk?platform=python.md |
| Server Gateway (Go) | https://docs-md.agora.io/en/server-gateway/get-started/integrate-sdk?platform=go.md |
| Tokens | https://docs-md.agora.io/en/video-calling/token-authentication/deploy-token-server.md |

## Agora MCP Server (optional)

Agora also provides an MCP server that gives AI assistants direct tool-call access
to documentation — an alternative to the Level 2 HTTP fetch above. If a user asks
about installing or using the Agora MCP, see [mcp-tools.md](mcp-tools.md).
