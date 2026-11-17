# Shodh Memory Skill

Persistent memory system for AI agents. Store decisions, learnings, and context that persists across conversations.

## Installation

### With Claude Code
```bash
claude mcp add shodh-memory -- npx -y @shodh/memory-mcp
```

Or add the skill directly:
```bash
# Copy the SKILL.md to your skills directory
cp SKILL.md ~/.claude/skills/shodh-memory/SKILL.md
```

### With MCP Server (Local)
```bash
# Install the MCP server
cargo install shodh-memory

# Or run with npx
npx -y @shodh/memory-mcp
```

## What This Skill Teaches

This skill teaches Claude how to effectively use the Shodh Memory MCP server:

- **When to store memories** - Decisions, learnings, errors, patterns
- **How to structure memories** - Rich content, proper types, useful tags
- **Retrieval strategies** - Semantic, associative, and hybrid search
- **Best practices** - Proactive context, consistent tagging, periodic review

## Core Capabilities

| Capability | Description |
|------------|-------------|
| `proactive_context` | Automatically surface relevant memories every message |
| `remember` | Store new memories with type and tags |
| `recall` | Semantic search across all memories |
| `recall_by_tags` | Fast tag-based filtering |
| `context_summary` | Quick overview of recent learnings |

## Example Usage

```
User: "What authentication approach should we use?"

Claude (with skill):
1. Calls proactive_context to surface past auth decisions
2. Recalls any security-related memories
3. Responds with context-aware recommendation
4. Stores the decision for future reference
```

## Requirements

- Shodh Memory MCP server running (local or cloud)
- Claude Code, Claude.ai, or any MCP-compatible client

## Links

- [GitHub Repository](https://github.com/varun29ankuS/shodh-memory)
- [Documentation](https://shodh-memory.com)
- [MCP Server on npm](https://www.npmjs.com/package/@shodh/memory-mcp)

## License

Apache 2.0
