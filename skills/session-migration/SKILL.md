---
name: session-migration
description: >
  Migrate conversation context to a fresh session without losing progress. Use this skill whenever the user
  wants to continue in a new chat, mentions context getting long/confused/dirty, asks to "pack up" current
  state, or says they need to start a new conversation. Works across all AI tools (ChatGPT, Claude, agents)
  and all task types — writing, coding, research, planning, analysis, learning. Produces a self-contained
  handoff summary that the new session's AI can pick up immediately.
license: Apache-2.0
---

# Session Migration

Help users pack their current conversation state into a portable summary, so a fresh session can pick up exactly where they left off.

## When to Trigger

Activate when the user:
- Asks to migrate, transfer, or export conversation state
- Says the context is getting long, confused, or "dirty"
- Wants to "start fresh but keep what we've done"
- Asks for a summary of progress so far (with intent to continue elsewhere)
- Explicitly says "I need to move to a new chat/session"

## Step 1 — Identify the Current Phase

Before extracting anything, determine what *type* of work the user has been doing. This affects what information matters most:

| Phase | Signals | Prioritize |
|-------|---------|------------|
| **Exploration** | Brainstorming, comparing options, gathering info | Directional judgments, open questions, what's been considered |
| **Execution** | Writing, coding, building, producing output | Exact progress, file states, partial deliverables |
| **Validation** | Reviewing, debugging, correcting, iterating | What went wrong, what was tried, current error state |

If multiple task lines are running concurrently, tag each one separately.

## Step 2 — Extract the Summary

Use this exact template. Output only confirmed information — no guessing, no filler.

```markdown
## Goal
What you're primarily working on and what you need to achieve. List all task lines if multiple, mark the main one.

## Confirmed Conclusions
Decisions, directions, approaches, and judgments that are settled. State each one clearly and independently.

## Rejected Approaches (with reasons)
Directions that were discussed and abandoned. Angles/drafts/ideas that didn't work in iteration. Explain why — this is critical to prevent the new session from re-treading dead ends.

## Progress
Tag each task or file with its status:
- ✅ Done: brief result
- 🔧 In progress: where you left off
- ⏳ Pending: not started yet
When multiple files are involved, list each file's status separately.

## Key Constraints
Background conditions, preferences, limitations, non-negotiable rules.

## Concrete Details
Values that would be lost if not written down: paths, parameters, URLs, data, names, tool versions, environment dependencies. When there are multiple output files, explain how they relate.

Rule: bullet-point format, each item self-contained. The new session's AI should be able to pick up immediately.
```

## Step 3 — Quality Check

Before delivering, verify:

1. **Could a fresh AI continue without asking the user anything?** If not, add the missing context.
2. **Are rejected approaches clearly marked with reasons?** This is the #1 thing people forget, and the most painful to re-discover.
3. **Is "Concrete Details" actually specific?** File paths, parameter values, URLs, version numbers — not vague descriptions.
4. **Is anything just filler?** Cut it. The summary should be dense and scannable.

## User Attachments

After extracting the standard summary, **always ask if the user has extra instructions for the new session**. Common examples:

- "Focus on X, skip Y" — redirect the new session's priority
- "First check file Z for recent changes" — preload verification steps
- "Don't repeat the discussion about A, just use the decision" — suppress re-exploration
- "Also do B while you're at it" — inject an additional task line

If the user provides attachments, append a `## Attachments` section to the summary with their exact instructions. The new session must treat these as **constraints**, not suggestions.

If no attachments are given, skip this section silently.

## Gotchas

- **Multiple concurrent tasks** — Users often run 2-3 workstreams in one session. If you only track the "main" one, you'll lose the others. Tag each task line's phase and progress separately.
- **Soft rejections in creative work** — Not every rejection is a hard "we decided against X." In writing/design, there are subtle rejections: "this paragraph doesn't feel right," "I tried this angle but it didn't land." Capture these too — they prevent the new session from regurgitating the same bad drafts.
- **Multi-file projects** — When a task produces multiple files (article + images + config), list each file's status individually and explain how they relate. A single "article done" might miss that the cover image isn't generated yet.
- **The user doesn't know they need to migrate** — Sometimes context degradation is obvious to you before the user notices. If the conversation is getting circular, repetitive, or producing lower-quality output, proactively suggest migration.
- **Don't over-summarize** — The goal is a working handoff, not a brief abstract. Specific decisions, specific file paths, specific rejections. Err on the side of including too much detail over too little.

