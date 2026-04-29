# Agora Doc MCP Server

The Agora Doc MCP server gives AI assistants direct tool-call access to Agora
documentation. It is an optional enhancement — the skill works without it using
the two-tier fetch approach in [doc-fetching.md](doc-fetching.md).

**Only use MCP when the user explicitly asks for it.** The default documentation
lookup is the two-tier fetch approach in [doc-fetching.md](doc-fetching.md) — use
that regardless of whether MCP is installed.

**MCP endpoint:** `https://mcp.agora.io`

## Tools

| Tool | Input | Returns |
|---|---|---|
| `get-doc-content` | `{"uri": "docs://..."}` | Full markdown content |
| `search-docs` | `{"query": "keyword"}` | List of matching doc URIs |
| `list-docs` | `{"category": "...", "limit": 20}` | All docs in a category |

Use `search-docs` when the topic is known but the URI isn't. Use `get-doc-content`
directly when the URI is known.

## Installation

**Claude Code:**
```bash
claude mcp add agora-docs --transport http https://mcp.agora.io
```

**Cursor / Windsurf / other MCP-compatible tools:** Add `https://mcp.agora.io` as
an HTTP MCP server in your tool's MCP settings. See your tool's documentation for
the exact configuration format.

For the latest setup instructions and any changes to the endpoint, see:
<https://docs.agora.io/en/mcp>

## Usage Note

After fetching quick-start docs via MCP, use the content for API structure and field
names only. Do NOT copy sample code verbatim — quick-start examples typically hardcode
credentials and omit production requirements. Apply the gotchas and generation rules
in `references/conversational-ai/README.md` to any generated code.
