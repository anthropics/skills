---
name: open-brain
description: Use this skill when the user wants to capture, recall, or search persistent memory via Open Brain — a self-hosted MCP server backed by PostgreSQL + pgvector. Invoke it when the user says things like "remember this", "capture a thought", "what do I know about X", or "search my brain".
---

# Open Brain — Persistent AI Memory

Open Brain is a self-hosted MCP server that gives AI clients durable, searchable memory using semantic vector search. Thoughts are stored in PostgreSQL with pgvector embeddings, making them retrievable by meaning rather than exact keywords.

## Available Tools

| Tool | When to use |
|---|---|
| `capture_thought` | User wants to save something — an idea, note, observation, decision, or reference |
| `search_thoughts` | User wants to recall something by topic or meaning |
| `list_thoughts` | User wants to browse recent memory, optionally filtered by type, topic, or person |
| `thought_stats` | User wants a summary of what's in the brain |

## Capturing Thoughts

When capturing, write the thought clearly and completely in natural language. Open Brain automatically generates embeddings and extracts metadata (type, topics, people mentioned).

```
capture_thought({
  content: "The k3s cluster uses Traefik for ingress and cert-manager for TLS. All apps are deployed via Helmfile at daveschwinn.com."
})
```

**Thought types** (auto-detected, no need to specify):
- `observation` — facts, notes, things noticed
- `idea` — proposals, plans, creative thoughts
- `task` — things to do or follow up on
- `reference` — links, docs, resources
- `person_note` — notes about a specific person

## Searching Memory

Search uses semantic similarity — you don't need exact words.

```
search_thoughts({
  query: "kubernetes ingress setup",
  limit: 5,
  threshold: 0.5
})
```

Adjust `threshold` (0–1) to control strictness. Lower = broader results.

## Listing Recent Thoughts

```
// Last 10 thoughts
list_thoughts({ limit: 10 })

// Filter by type
list_thoughts({ type: "task", limit: 20 })

// Filter by topic
list_thoughts({ topic: "kubernetes", days: 30 })

// Filter by person
list_thoughts({ person: "Alice" })
```

## Getting Memory Stats

```
thought_stats({})
```

Returns total count, breakdown by type, top topics, and people mentioned.

## Guidelines

- **Capture proactively** — if a conversation produces something worth remembering (a decision, a pattern, a useful fact), offer to capture it without being asked.
- **Search before answering** — when a user asks about something they may have captured before, search first.
- **Write thoughts as complete sentences** — fragments lose context over time. "Use Recreate strategy for stateful k8s apps" is better than "Recreate strategy".
- **Don't summarize away detail** — capture the specific version, name, URL, or value. Vague thoughts are hard to act on later.
- **One thought per capture** — don't bundle unrelated facts. Separate captures are easier to find and update.
