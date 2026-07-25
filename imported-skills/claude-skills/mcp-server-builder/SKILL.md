---
name: "mcp-server-builder"
description: "Design and ship production-ready MCP (Model Context Protocol) servers from OpenAPI contracts instead of hand-written tool wrappers. Python and TypeScript support, schema validation, safe evolution. Use when exposing an existing API as an MCP server, building tool integrations for Claude or Codex or Cursor, or scaffolding an MCP project from scratch."
---

# MCP Server Builder

**Tier:** POWERFUL · **Category:** Engineering · **Domain:** AI / API Integration

## Overview

Use this skill to design and ship production-ready MCP servers from API contracts instead of hand-written one-off tool wrappers. It focuses on fast scaffolding, schema quality, validation, and safe evolution.

The workflow supports both Python and TypeScript MCP implementations and treats OpenAPI as the source of truth.

## Core Capabilities

- Convert OpenAPI paths/operations into MCP tool definitions
- Generate starter server scaffolds (Python or TypeScript)
- Enforce naming, descriptions, and schema consistency
- Validate MCP tool manifests for common production failures
- Apply versioning and backward-compatibility checks
- Separate transport/runtime decisions from tool contract design

## When to Use

- You need to expose an internal/external REST API to an LLM agent
- You are replacing brittle browser automation with typed tools
- You want one MCP server shared across teams and assistants
- You need repeatable quality checks before publishing MCP tools
- You want to bootstrap an MCP server from existing OpenAPI specs

## Key Workflows

### 1. OpenAPI to MCP Scaffold

1. Start from a valid OpenAPI spec.
2. Generate tool manifest + starter server code.
3. Review naming and auth strategy.
4. Add endpoint-specific runtime logic.

```bash
python3 scripts/openapi_to_mcp.py \
  --input openapi.json \
  --server-name billing-mcp \
  --language python \
  --output-dir ./out \
  --format text
```

Supports stdin as well:

```bash
cat openapi.json | python3 scripts/openapi_to_mcp.py --server-name billing-mcp --language typescript
```

### 2. Validate MCP Tool Definitions

Run validator before integration tests:

```bash
python3 scripts/mcp_validator.py --input out/tool_manifest.json --strict --format text
```

Checks include duplicate names, invalid schema shape, missing descriptions, empty required fields, and naming hygiene.

### 3. Runtime Selection

- Choose **Python** for fast iteration and data-heavy backends.
- Choose **TypeScript** for unified JS stacks and tighter frontend/backend contract reuse.
- Keep tool contracts stable even if transport/runtime changes.

### 4. Harden for Production

Key items before publishing:

- Keep secrets in env vars, not tool schemas
- Prefer outbound host allowlists over open proxies
- Use additive-only changes; never rename tool names in-place

Full hardening guidance: [references/production-hardening-guide.md](references/production-hardening-guide.md).

## Script Interfaces

- `python3 scripts/openapi_to_mcp.py --help`
  - Reads OpenAPI from stdin or `--input`
  - Produces manifest + server scaffold
  - Emits JSON summary or text report
- `python3 scripts/mcp_validator.py --help`
  - Validates manifests and optional runtime config
  - Returns non-zero exit in strict mode when errors exist

## Reference Material

- [references/production-hardening-guide.md](references/production-hardening-guide.md) — auth & safety design, versioning strategy, common pitfalls, best practices, architecture decisions, contract quality gates, testing strategy, deployment practices, security controls
- [references/openapi-extraction-guide.md](references/openapi-extraction-guide.md)
- [references/python-server-template.md](references/python-server-template.md)
- [references/typescript-server-template.md](references/typescript-server-template.md)
- [references/validation-checklist.md](references/validation-checklist.md)
- [README.md](README.md)
