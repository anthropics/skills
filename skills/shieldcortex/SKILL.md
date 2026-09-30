---
name: shieldcortex
description: Persistent memory system with security for AI agents. Remembers decisions, preferences, architecture, and context across sessions with knowledge graphs, decay, contradiction detection, and a 6-layer defence pipeline. Use when asked to "remember this", "what do we know about", "recall context", "scan for threats", "run security audit", "check memory stats", or when starting a new session and needing prior context.
license: MIT
metadata:
  author: Drakon Systems
  version: 2.10.3
  mcp-server: shieldcortex
  category: memory-and-security
  tags: [memory, security, knowledge-graph, mcp]
---

# ShieldCortex — Persistent Memory & Security for AI Agents

Give your agent a brain that persists between sessions and protect it from memory poisoning attacks.

## When to Use This Skill

- You want to remember things between sessions (decisions, preferences, architecture, context)
- You need to recall relevant past context at the start of a session
- You want knowledge graph extraction from memories (entities, relationships)
- You need to protect memory from prompt injection or poisoning attacks
- You want credential leak detection in memory writes
- You want to audit what has been stored in and retrieved from memory
- You want to scan instruction files (SKILL.md, .cursorrules, CLAUDE.md) for threats

## Setup

Install the npm package globally, then configure the MCP server:

```bash
npm install -g shieldcortex
shieldcortex install
```

## Core Workflow

### Session Start

At the start of every session, retrieve prior context:

1. Call `start_session` to begin a new session and get relevant memories
2. Or call `get_context` with a query describing the current task

### Remembering

Call `remember` immediately when any of these happen:

- **Architecture decisions** — "We're using PostgreSQL for the database"
- **Bug fixes** — capture root cause and solution
- **User preferences** — "Always use TypeScript strict mode"
- **Completed features** — what was built and why
- **Error resolutions** — what broke and how it was fixed
- **Project context** — tech stack, key patterns, file structure

Parameters:
- `title` (required): Short summary
- `content` (required): Detailed information
- `category`: architecture, pattern, preference, error, context, learning, todo, note
- `importance`: low, normal, high, critical
- `project`: Scope to a specific project (auto-detected if omitted)
- `tags`: Array of tags for categorisation

### Recalling

Call `recall` to search for past memories:

- `mode: "search"` — query-based semantic search (default)
- `mode: "recent"` — most recent memories
- `mode: "important"` — highest-salience memories

Filter by `category`, `tags`, `project`, or `type` (short_term, long_term, episodic).

### Forgetting

Call `forget` to remove outdated or incorrect memories:

- Delete by `id` for a specific memory
- Delete by `query` to match content
- Always use `dryRun: true` first to preview what will be deleted
- Use `confirm: true` for bulk deletions

### Session End

Call `end_session` with a summary to trigger memory consolidation. This promotes short-term memories to long-term and runs decay on old, unaccessed memories.

## Knowledge Graph

ShieldCortex automatically extracts entities and relationships from memories.

- `graph_query` — traverse from an entity, returns connected entities up to N hops
- `graph_entities` — list known entities, filter by type (person, tool, concept, file, language, service, pattern)
- `graph_explain` — find the path connecting two entities

Use the knowledge graph to understand relationships between concepts, technologies, and decisions across the project.

## Memory Intelligence

- `consolidate` — merge duplicate/similar memories, run decay. Use `dryRun: true` to preview
- `detect_contradictions` — find conflicting memories (e.g., "use Redis" vs "don't use Redis")
- `get_related` — find memories connected to a specific memory ID
- `link_memories` — create explicit relationships (references, extends, contradicts, related)
- `memory_stats` — view total counts, category breakdown, decay stats

## Security & Defence

Every memory write passes through a 6-layer defence pipeline:

1. Input Sanitisation — strips control characters and null bytes
2. Pattern Detection — regex matching for known injection patterns
3. Semantic Analysis — embedding similarity to attack corpus
4. Structural Validation — JSON/format integrity checks
5. Behavioural Scoring — anomaly detection over time
6. Credential Leak Detection — blocks API keys, tokens, private keys

### Security Tools

- `audit_query` — query the forensic audit log of all memory operations
- `defence_stats` — view defence system statistics (blocks, allows, quarantines)
- `quarantine_review` — review and manage quarantined memories (list, approve, reject)
- `scan_memories` — scan existing memories for signs of poisoning
- `scan_skill` — scan an instruction file for hidden threats (SKILL.md, .cursorrules, CLAUDE.md, etc.)

## Project Scoping

- `set_project` — switch active project context
- `get_project` — show current project scope
- Use `project: "*"` for global/cross-project memories

## Best Practices

1. **Remember immediately** — call `remember` right after a decision is made or a bug is fixed, not at the end of the session
2. **Use categories** — architecture, pattern, preference, error, context, learning
3. **Set importance** — mark critical decisions as `importance: "critical"` so they resist decay
4. **Recall at session start** — always call `get_context` or `start_session` first
5. **End sessions properly** — call `end_session` with a summary to trigger consolidation
6. **Review contradictions** — periodically run `detect_contradictions` to catch conflicting information
7. **Scope by project** — memories are automatically scoped to the current project directory

## Troubleshooting

**Memory not found in recall:**
- Try `mode: "search"` with different query phrasing
- Check `set_project` — you may be searching the wrong project scope
- Use `includeDecayed: true` to find memories that have faded

**Memory blocked by firewall:**
- The defence pipeline detected a potential threat (injection, credential leak)
- Check `audit_query` for the specific block reason
- Review with `quarantine_review` if it was a false positive
- Avoid including literal API keys or tokens in memory content

**Consolidation removing memories:**
- Run `consolidate` with `dryRun: true` first to preview
- Mark important memories as `importance: "critical"` to prevent decay
- Access memories regularly — `recall` boosts activation and prevents decay

## Links

- npm: https://www.npmjs.com/package/shieldcortex
- GitHub: https://github.com/Drakon-Systems-Ltd/ShieldCortex
- Website: https://shieldcortex.ai
