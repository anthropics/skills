---
name: shodh-memory
description: Persistent memory system for AI agents. Use this skill to remember context across conversations, recall relevant information, and build long-term knowledge. Activate when you need to store decisions, learnings, errors, or context that should persist beyond the current session.
version: 1.0.0
author: Shodh AI
tags:
  - memory
  - persistence
  - context
  - recall
  - knowledge-management
---

# Shodh Memory - Persistent Context for AI Agents

Shodh Memory gives you persistent memory across conversations. Unlike your context window which resets each session, memories stored here persist indefinitely and can be recalled semantically.

## When to Use Memory

**ALWAYS call `proactive_context` at the start of every conversation** with the user's first message. This surfaces relevant memories automatically.

### Store memories (`remember`) when:
- User makes a **decision** ("Let's use PostgreSQL for this project")
- You **learn** something new ("The codebase uses a monorepo structure")
- An **error** occurs and you find the fix
- You discover a **pattern** in the user's preferences
- Important **context** that will be useful later

### Recall memories (`recall`) when:
- User asks about past decisions or context
- You need to remember project-specific information
- Looking for patterns in how problems were solved before

## Memory Types

Choose the right type for better retrieval:

| Type | When to Use | Example |
|------|-------------|---------|
| `Decision` | User choices, architectural decisions | "User chose React over Vue for the frontend" |
| `Learning` | New knowledge gained | "This API requires OAuth2 with PKCE flow" |
| `Error` | Bugs found and fixes | "TypeError in auth.js fixed by null check" |
| `Discovery` | Insights, aha moments | "The performance issue was caused by N+1 queries" |
| `Pattern` | Recurring behaviors | "User prefers functional components over classes" |
| `Context` | Background information | "Working on e-commerce platform for client X" |
| `Task` | Work in progress | "Currently refactoring the payment module" |
| `Observation` | General notes | "User typically works in the morning" |

## Best Practices

### 1. Call `proactive_context` First

```
Every user message → call proactive_context with the message
```

This automatically:
- Retrieves relevant memories
- Stores the conversation context
- Builds association graph over time

### 2. Write Rich, Searchable Memories

**Good:**
```
"Decision: Use PostgreSQL with pgvector extension for the RAG application.
Reasoning: Need vector similarity search, user already has Postgres expertise,
avoids adding new infrastructure. Alternative considered: Pinecone (rejected
due to cost)."
```

**Bad:**
```
"Use postgres"
```

### 3. Use Tags for Organization

Tags enable fast filtering without semantic search:

```json
{
  "content": "API rate limit is 100 requests/minute",
  "tags": ["api", "rate-limit", "backend", "project-x"]
}
```

Later recall with: `recall_by_tags(["project-x", "api"])`

### 4. Memory Types Affect Importance

The system automatically weights memory types:
- `Decision` and `Error` → Higher importance, slower decay
- `Context` and `Observation` → Lower importance, faster decay

Choose types accurately for better long-term retention.

### 5. Leverage Different Recall Modes

| Mode | When to Use |
|------|-------------|
| `semantic` | Pure meaning-based search ("database optimization") |
| `associative` | Follow learned connections ("what else relates to X?") |
| `hybrid` | Best of both (default, recommended) |

## Common Patterns

### Starting a Session
```
1. User sends first message
2. Call proactive_context(context: user_message)
3. Review surfaced memories
4. Respond with relevant context
```

### After Making Progress
```
1. Complete a significant task
2. Call remember() with:
   - What was done
   - Why it was done
   - Key decisions made
   - Any gotchas discovered
```

### When User Asks "Do you remember..."
```
1. Call recall(query: "what user is asking about")
2. Also try recall_by_tags if you know relevant tags
3. Synthesize memories into response
```

### Debugging a Recurring Issue
```
1. recall(query: "error in [component]")
2. Check if similar errors were solved before
3. Apply previous fix or note new solution
4. remember() the resolution
```

## Memory Lifecycle

```
New Memory → Working Memory (hot, fast access)
            ↓ (consolidation)
         Session Memory (warm, recent context)
            ↓ (importance threshold)
         Long-term Memory (persistent, searchable)
```

The system automatically:
- Strengthens frequently-accessed memories
- Decays unused memories (but never fully forgets)
- Forms associations between co-retrieved memories
- Replays important memories during maintenance

## API Quick Reference

### Core Tools

| Tool | Purpose |
|------|---------|
| `proactive_context` | **Call every message.** Surfaces relevant memories, stores context |
| `remember` | Store a new memory |
| `recall` | Search memories by meaning |
| `recall_by_tags` | Filter memories by tags |
| `recall_by_date` | Filter memories by time range |
| `forget` | Delete a specific memory |
| `forget_by_tags` | Delete memories matching tags |

### Diagnostic Tools

| Tool | Purpose |
|------|---------|
| `memory_stats` | Get counts and health status |
| `context_summary` | Quick overview of recent learnings/decisions |
| `consolidation_report` | See what the memory system is learning |
| `verify_index` | Check index health |
| `repair_index` | Fix orphaned memories |

## Example Workflow

```
User: "Let's start building the user authentication system"

You:
1. proactive_context("Let's start building the user authentication system")
   → Surfaces: Previous auth decisions, security preferences, tech stack

2. Response incorporates remembered context:
   "Based on our earlier decision to use PostgreSQL and your preference
   for JWT tokens, I'll set up auth with..."

3. After implementation:
   remember(
     content: "Implemented JWT authentication with refresh token rotation.
               Used bcrypt for password hashing (cost factor 12).
               Tokens expire in 15 minutes, refresh tokens in 7 days.",
     type: "Learning",
     tags: ["auth", "jwt", "security", "user-system"]
   )
```

## Tips for Effective Memory

1. **Be specific** - "React 18 with TypeScript" not "frontend framework"
2. **Include reasoning** - Why decisions were made, not just what
3. **Tag consistently** - Use a tagging convention across the project
4. **Review periodically** - Use `context_summary` to see what's accumulated
5. **Trust the system** - It strengthens useful memories automatically

---

*Shodh Memory: Because context shouldn't reset with every conversation.*
