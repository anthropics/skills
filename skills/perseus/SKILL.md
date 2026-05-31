---
name: perseus
description: >-
  Use when you need live project state (git branch, service health checks,
  recent sessions, task board, env vars, agent inbox) injected into context
  BEFORE the AI reads it. Perseus is a compile-before-context engine — it runs
  directives like @query, @services, @waypoint, @agora and hands the assistant
  a fully-resolved markdown briefing. Use for: deterministic session starts,
  multi-agent coordination, workspace audits, and anywhere you want "all the
  facts first."
---

# Perseus — Live Context Engine for AI Assistants

Perseus pre-resolves your entire workspace state — git, services, memory, team
coordination — into a single markdown document every assistant reads at session
start. Deterministic. Cacheable. Assistant-agnostic.

## Quick Start

```bash
pip install perseus-ctx        # or: uv tool install perseus-ctx
perseus init                    # scaffold .perseus/context.md
perseus render --format agents-md  # render to AGENTS.md
```

## Installation as a Claude Code Skill

```bash
# Install Perseus
uv tool install perseus-ctx

# Set up Claude Code hooks — auto-injects Perseus context every session
cd your-project
perseus install --target claude-code

# Render your first briefing
perseus render .perseus/context.md --format claude-md
```

This drops `SessionStart` + `UserPromptSubmit` hooks into `.claude/settings.json`.
Every Claude Code session now starts with Perseus-resolved context injected
automatically.

## Core Directives

Write a `.perseus/context.md` file with `@perseus` as the first line, then use
any of these 20 directives:

| Directive | What it does |
|-----------|-------------|
| `@query "command"` | Run a shell command and embed stdout |
| `@services` | Health-check listed services (HTTP, TCP, etc.) |
| `@read path=file` | Embed file contents |
| `@env VAR` | Embed environment variable |
| `@waypoint` | Latest session checkpoint (crash recovery) |
| `@agora` | Task board from `tasks/*.md` |
| `@inbox` | Inter-agent messages |
| `@memory` | Narrative project memory (federated across workspaces) |
| `@skills` | List available agent skills |
| `@session` | Recent session digests |
| `@health` | Context maintenance report |
| `@date` | Current date/time |
| `@include path=file` | Include and render another file |
| `@if / @else / @endif` | Conditional blocks |
| `@cache ttl=N` | Cache directive output for N seconds |
| `@cache session` | In-memory cache (session lifetime) |
| `@constraint` | Constraint block for validation |
| `@validate schema=` | Validate a rendered block |
| `@tree` | Tree view of directory |
| `@list` | List directory or structured data |

## Example .perseus/context.md

```markdown
@perseus v1.0.2

# Project Context

## Git
@query git branch --show-current
@query git log --oneline -5

## Services
@services

## Session State
@waypoint
@session count=3

## Team Coordination
@agora
@inbox unread=true
```

## Multi-Agent Coordination

Perseus's strongest differentiator is multi-agent shared state. With `@agora`
(task board), `@inbox` (inter-agent messaging), and `@memory federation`, every
agent in your swarm reads the same resolved context at session start. The
filesystem-based coordination protocol handles 150+ concurrent writers with zero
collisions.

## MCP Server Mode

Perseus also runs as an MCP server, exposing all directives as native MCP tools:

```bash
perseus mcp serve --workspace /path/to/project
```

Any MCP-compatible assistant (Claude Desktop, Cursor, Continue) can call
`perseus_query`, `perseus_services`, `perseus_memory`, etc. as tools.

## Tips

- **Deterministic sessions**: Run `perseus render` before starting work. Your
  AI assistant gets the same briefing every time.
- **CI integration**: `perseus render --format agents-md -o AGENTS.md` in your
  CI pipeline. Every PR gets Perseus-resolved context.
- **PR descriptions**: Render the snapshot as HTML comments in PR descriptions.
  Reviewers (human and AI) see the same briefing.
- **Trust boundaries**: Perseus supports schemas, path guards, and redaction
  policies. By default, dangerous operations are restricted.

## Resources

- **Homepage**: https://github.com/tcconnally/perseus
- **Docs**: https://github.com/tcconnally/perseus/blob/main/docs/index.md
- **PyPI**: https://pypi.org/project/perseus-ctx/
