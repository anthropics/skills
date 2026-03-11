---
name: claude-api-live
description: Grounds Claude API advice in live documentation. TRIGGER when: code imports `anthropic`/`@anthropic-ai/sdk`/`claude_agent_sdk`, or user asks to use Claude API, Anthropic SDKs, or Agent SDK. Fetches current model IDs and relevant docs from platform.claude.com before advising, so stale training data never causes bugs. DO NOT TRIGGER when: code imports `openai`/other AI SDK, general programming, or ML/data-science tasks."
license: Complete terms in LICENSE.txt
---

# Claude API Live Documentation Grounding

Claude's training data has a cutoff. Model IDs get renamed, parameters get deprecated,
new features launch behind beta headers, APIs get replaced. The gap between what Claude
remembers and what's actually current is silent — the code looks plausible, runs without
obvious errors, then breaks in ways that are expensive to debug.

This skill fetches live documentation before advising on any Claude API work. It catches
that gap before it becomes tech debt.

---

## Step 1: Identify what the user is doing

Before fetching, determine the task type. This controls which docs to fetch in Step 2:

| Task type | Examples |
|-----------|---------|
| **Planning / architecture** | "which model should I use", "should I use streaming", "how do I structure this" |
| **Code generation** | "write me a function that calls Claude", "add tool use to this" |
| **Debugging** | "this is throwing an error", "why is this failing", "budget_tokens isn't working" |
| **Code review** | "is this correct", "what's wrong with this code", "review my API usage" |

---

## Step 2: Fetch live docs

**Always fetch the models page first.** Model IDs are the most common source of stale guidance —
users copy whatever appears in example code, and a wrong model ID produces a confusing
"model not found" error far from where the mistake was made.

Then fetch **up to two additional pages** based on the task. Three parallel fetches is the ceiling — don't flood context with docs the user doesn't need.

### Always fetch

| Page | URL |
|------|-----|
| **Models** | `https://platform.claude.com/docs/en/about-claude/models/overview.md` |

### Fetch based on task

| If the task involves… | Fetch this |
|-----------------------|-----------|
| Thinking / reasoning depth / effort | `https://platform.claude.com/docs/en/build-with-claude/adaptive-thinking.md` |
| Streaming / real-time output | `https://platform.claude.com/docs/en/build-with-claude/streaming.md` |
| Tool use / function calling / agents | `https://platform.claude.com/docs/en/agents-and-tools/tool-use/overview.md` |
| Structured outputs / response format | `https://platform.claude.com/docs/en/build-with-claude/structured-outputs.md` |
| Batch processing / bulk requests | `https://platform.claude.com/docs/en/build-with-claude/batch-processing.md` |
| File uploads / Files API | `https://platform.claude.com/docs/en/build-with-claude/files.md` |
| Prompt caching | `https://platform.claude.com/docs/en/build-with-claude/prompt-caching.md` |
| Long conversations / context management | `https://platform.claude.com/docs/en/build-with-claude/compaction.md` |
| Errors / rate limits / debugging | `https://platform.claude.com/docs/en/api/errors.md` |
| Agent SDK (file/web/terminal tools) | `https://platform.claude.com/docs/en/agent-sdk.md` |

**If a URL fails or 404s**, search instead — restrict to the canonical domain to avoid
landing on unofficial mirrors:

```
site:platform.claude.com/docs <topic>
```

---

## Step 3: Surface what's current

Present only what's relevant and potentially surprising given your training data.
Aim for 5–10 bullets, not a wall of text:

**Current models:** [list model IDs and key specs from the live page]

**Key details for [features in scope]:** [params, headers, syntax that matters for this task]

**Watch out for:** [deprecations, recently changed behavior — omit entirely if nothing notable]

If nothing is surprising: *"Docs confirm expected behavior. Current recommended model: `claude-opus-4-6`."*

---

## Step 4: Proceed with the original task

Carry the grounded context forward into all code, plans, and reviews. Use correct model IDs,
current parameter names, and current feature knowledge throughout — don't re-summarize the
docs, just use them.

---

## What changes most often

These are the highest-probability sources of stale guidance:

- **Model ID suffixes** — never construct date-suffixed IDs from memory; copy exact aliases
  from the live models page
- **Thinking parameters** — `budget_tokens` is deprecated on current models; `thinking: {type: "adaptive"}`
  is the current pattern; verify from docs before advising
- **`output_format` / structured output params** — naming has changed; current parameter is
  `output_config: {format: {...}}`; verify from docs
- **Beta headers** — required headers and values change with each feature (Files API, compaction,
  etc.); always verify current values from docs before including them in code
- **Effort parameter** — `output_config: {effort: "low"|"medium"|"high"|"max"}` is GA;
  not top-level; verify supported models from docs
