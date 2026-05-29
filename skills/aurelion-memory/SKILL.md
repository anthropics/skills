---
name: "AURELION Memory"
version: "1.0.0"
description: "A file-based personal knowledge graph that organizes markdown documents into a queryable 5-floor architecture with automatic relationship detection. Available as a Python API, CLI, and MCP server for use in Claude Desktop and VS Code Copilot Chat."
author: "chase-key"
license: "MIT"
categories:
  - memory
  - knowledge-management
  - mcp
  - tools
homepage: "https://github.com/chase-key/aurelion-memory-lite"
---

# AURELION Memory — Knowledge Graph & MCP Server

## What This Skill Does

AURELION Memory is the persistence layer for the AURELION ecosystem. It stores, indexes, and retrieves knowledge organized in the 5-floor architecture — so knowledge from one session is available in the next, across any AI client that supports MCP.

This skill covers two surfaces:
1. **Skill instructions** — how this AI should use Memory concepts to help organize knowledge
2. **MCP server** — a local Python server that exposes your Memory store to Claude Desktop, VS Code Copilot Chat, and any MCP-compatible AI client

Use this skill when you need to:
- Persist knowledge across AI sessions (context that survives window resets)
- Build a queryable personal knowledge base from markdown files
- Link related concepts across floors with automatic relationship detection
- Connect your full AURELION Kernel/Advisor/Agent documents to an AI that can read them on demand

---

## The Memory Architecture

AURELION Memory mirrors the 5-floor Kernel architecture. Every document lives on exactly one floor, and relationships can span floors.

### Floor Assignments
| Floor | Domain | Memory Role |
|-------|---------|-------------|
| Floor 1 — Foundation | Career, skills, operations | Core identity facts; highest-confidence retrieval |
| Floor 2 — Systems | SOPs, methodologies, frameworks | Process knowledge; versioned documents |
| Floor 3 — Networks | People, organizations, relationships | Graph-heavy; relationship traversal |
| Floor 4 — Action | Active projects, current state | High churn; time-stamped entries |
| Floor 5 — Vision | Goals, roadmaps, transformations | Long-horizon; low-frequency update |

### Relationship Types
The graph tracks five relationship types between documents:
- `RELATED_TO` — general semantic connection
- `DEPENDS_ON` — one concept requires another to be true
- `PRECEDES` — temporal or logical ordering
- `CONTRADICTS` — flagged conflicts between documents (used in integrity checking)
- `SUPPORTS` — evidence relationship (one document strengthens another's claim)

---

## How This AI Should Use Memory

### When the user says "remember this"
1. Identify the floor (Foundation, Systems, Networks, Action, or Vision).
2. Identify the document type (career fact, SOP, relationship record, project note, goal).
3. Output a formatted Memory document in the correct Kernel template.
4. Suggest a file path: `Floor_0{N}_{Domain}/{descriptive_name}.md`
5. If the MCP server is running, offer to write it directly.

### When the user says "what did we decide about X"
1. Search the active Memory store for documents related to X.
2. Return the most recent relevant document from the appropriate floor.
3. Surface any `CONTRADICTS` relationships (if two documents conflict on the topic).
4. Offer to update the document if the answer is stale.

### When the user starts a new session
The Memory system should resolve context loss automatically:
1. Load the active session handoff note (Floor 4 — Action).
2. Load the top three Floor 5 goals (vision anchors for this session).
3. Load any Floor 2 documents referenced in the last session.
4. Present: "Here's where we left off. [Summary]. Ready to continue?"

---

## MCP Server Setup

The AURELION Memory MCP server exposes your local knowledge graph to any MCP-compatible AI client.

### Install (one command)
```bash
pip install aurelion-memory-lite
```

### Configure in Claude Desktop
Add to your `claude_desktop_config.json`:
```json
{
  "mcpServers": {
    "aurelion-memory": {
      "command": "python",
      "args": ["-m", "aurelion_memory_mcp"],
      "env": {
        "AURELION_MEMORY_PATH": "/absolute/path/to/your/memory-store"
      }
    }
  }
}
```

### Configure in VS Code (Copilot Chat MCP)
Add to your VS Code `settings.json`:
```json
{
  "github.copilot.chat.mcp.servers": {
    "aurelion-memory": {
      "command": "python",
      "args": ["-m", "aurelion_memory_mcp"],
      "env": {
        "AURELION_MEMORY_PATH": "${workspaceFolder}"
      }
    }
  }
}
```

### Available MCP Tools (exposed to the AI)

| Tool | Description |
|------|-------------|
| `memory_search` | Full-text + floor-scoped search across all documents |
| `memory_read` | Read a specific document by path |
| `memory_write` | Write or update a document (with floor assignment) |
| `memory_graph` | Return relationship graph for a document or concept |
| `memory_session` | Load the active session context (handoff + goals) |
| `memory_floor` | List all documents on a given floor |

### Python API (programmatic use)
```python
from aurelion_memory_lite import MemoryGraph

graph = MemoryGraph("./my-memory-store")
results = graph.search("promotion criteria", floor=1)
doc = graph.read("Floor_01_Foundation/career-master.md")
graph.write("Floor_04_Action/sprint-notes.md", content, floor=4)
```

---

## MCP Server Implementation

See `mcp/server.py` in this repository for the server implementation.  
See `mcp/README.md` for full setup and troubleshooting instructions.

---

## Integration with Other AURELION Modules

- **AURELION Kernel** — Memory stores and retrieves all Kernel floor documents. The two modules are designed to be used together. Memory is the persistence layer; Kernel is the schema.
- **AURELION Advisor** — Career plans, decision records, and stakeholder maps created by Advisor sessions are stored in Memory for cross-session continuity.
- **AURELION Agent** — When Agent triggers a "data integrity flag," it checks the Memory graph for conflicting or outdated documents.

Full ecosystem: https://github.com/chase-key/aurelion-hub
