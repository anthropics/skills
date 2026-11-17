---
name: muninn-memory
description: Persistent memory layer for AI agents. Knowledge graph with temporal reasoning, entity extraction, and multi-hop retrieval. Use when you need to remember information across sessions, recall past conversations, store facts, or retrieve context about people, projects, or topics.
---

# Muninn Memory System

**Persistent memory for AI agents.** Store and retrieve information across sessions with knowledge graph capabilities, temporal reasoning, and multi-hop retrieval.

## When to Use

Use Muninn when you need to:
- Remember information across sessions
- Store facts about people, projects, or topics
- Recall past conversations or decisions
- Build a knowledge graph of entities and relationships
- Answer questions like "What did we discuss last Tuesday?"

## Installation

### Local Mode (Free)

```bash
# Install via ClawHub
clawhub install muninn-skill

# Pull embedding model (required for local mode)
ollama pull nomic-embed-text

# Start MCP server
cd ~/.openclaw/workspace/skills/muninn-skill
npm install
npm run mcp
```

### Cloud Mode (Paid)

```bash
# Get API key at https://muninn.au/dashboard
export MUNINN_API_KEY=muninn_xxx

# Cloud mode is automatic when API key is set
```

## Key Features

### Memory Types

1. **Episodic Memory** - Events and conversations with timestamps
2. **Semantic Memory** - Facts and knowledge about entities
3. **Procedural Memory** - How-to knowledge and processes

### Operations

```bash
# Store a memory
mcporter call muninn.memory_remember --args '{"observation": "User prefers Australian English spelling"}'

# Recall memories
mcporter call muninn.memory_recall --args '{"query": "user preferences"}'

# Get session briefing
mcporter call muninn.memory_briefing --args '{"context": "session start"}'

# Search entities
mcporter call muninn.entity_search --args '{"query": "Phillip"}'

# Get related entities
mcporter call muninn.entity_get_related --args '{"entity_id": "entity_123"}'
```

### Temporal Reasoning

Muninn resolves temporal references:
- "last Tuesday" → actual date
- "yesterday" → date-1
- "last week" → date range

### Multi-hop Retrieval

Find connections between entities:
```bash
mcporter call muninn.path_find --args '{"from": "Phillip", "to": "AgentHired"}'
```

## Architecture

| Mode | Storage | Embeddings | Cost |
|------|---------|------------|------|
| **Local** | SQLite | Ollama (nomic-embed-text) | Free |
| **Cloud** | PostgreSQL | BYOK (OpenAI/Anthropic) | $10/mo |

## MCP Integration

Muninn exposes an MCP server compatible with any agent framework:

```json
{
  "mcpServers": {
    "muninn": {
      "command": "node",
      "args": ["/path/to/muninn-skill/src/mcp/server.js"]
    }
  }
}
```

## Example Usage

**Store a conversation:**
```
User: "I'm working on a project called AgentHired, it's a marketplace for AI agents"
Muninn: Stores: AgentHired (project) → marketplace (type) → AI agents (domain)
```

**Recall context:**
```
User: "What projects am I working on?"
Muninn: Retrieves all project entities and their statuses
```

**Temporal query:**
```
User: "What did we discuss last Tuesday about Muninn?"
Muninn: Resolves "last Tuesday" → retrieves relevant conversations
```

## Documentation

- **GitHub:** https://github.com/Phillipneho/muninn-skill
- **Website:** https://muninn.au
- **ClawHub:** `clawhub install muninn-skill`

## License

MIT License