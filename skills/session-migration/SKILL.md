---
name: session-migration
description: >
  Pack conversation state into a structured handoff summary that a fresh AI session picks up immediately — no re-explaining, no repeated dead ends. Use when context degrades, the user wants a new session, or conversation turns circular. Phase-aware extraction with a 6-section template (Goal, Conclusions, Rejected Approaches, Progress, Constraints, Details) and a timing guide for optimal migration points. Works across all AI tools and task types.
license: Apache-2.0
---

# Session Migration

Pack the current conversation state into a portable, self-contained handoff summary. A fresh session should be able to continue exactly where this one left off — no re-explanation, no repeated dead ends.

## When to Trigger

Activate when the user:
- Asks to migrate, transfer, hand off, or export conversation state
- Says the context is getting long, confused, "dirty", or degraded
- Wants to "start fresh but keep what we've done"
- Asks for a summary of progress with intent to continue elsewhere
- Says "new chat", "new thread", "let's start over", "continue elsewhere"
- Mentions the AI is forgetting things or repeating itself
- Has been working on a focused task for 10+ turns and the conversation is getting long
- Explicitly says they need to move to a new session

Also consider triggering proactively if you notice the conversation becoming circular, the AI producing lower-quality output than earlier, or the same topics being re-discussed.

**Do NOT trigger for**: simple summaries with no intent to continue, meeting notes, one-off questions. This skill is specifically for migration — the user wants to continue work in a new session.

## Step 1 — Identify the Current Phase

Before extracting anything, determine what type of work the user has been doing. This affects what information matters most:

| Phase | Signals | Prioritize capturing |
|-------|---------|---------------------|
| **Exploration** | Brainstorming, comparing options, gathering info, research | Directional judgments, open questions, what's been considered and rejected |
| **Execution** | Writing, coding, building, producing output | Exact progress, file states, partial deliverables, what's done vs. remaining |
| **Validation** | Reviewing, debugging, correcting, iterating | What went wrong, what was tried, current error state, what fixes worked |

If multiple task lines are running concurrently, tag each one's phase separately. This is critical — losing a secondary task line during migration is a common failure mode.

For guidance on when migration is appropriate, see `references/timing-guide.md`.

## Step 2 — Extract the Summary

Use this template. Fill in only confirmed information — no guessing, no filler, no hedging language.

```markdown
# Session Migration Handoff

## Goal
What you're primarily working on and what you need to achieve. List all active task lines if multiple, mark the main one.

## Confirmed Conclusions
Decisions, directions, approaches, and judgments that are settled. Each one stated independently and specifically.

## Rejected Approaches (with reasons)
Directions discussed and abandoned. Drafts, angles, or ideas that didn't work during iteration. **Explain why for each one** — this prevents the new session from re-treading the same dead ends. Include soft rejections ("this paragraph doesn't feel right", "tried this angle but it didn't land") not just hard decisions.

## Progress
Tag each task or file with its status:
- ✅ **Done**: brief result
- 🔧 **In progress**: exactly where you left off
- ⏳ **Pending**: not started yet

When multiple files/artifacts are involved, list each one's status separately and explain how they relate.

## Key Constraints
Background conditions, user preferences, limitations, non-negotiable rules, style requirements, tool/environment constraints.

## Concrete Details
Values that would be lost if not written down: file paths, parameter values, URLs, data points, names, tool versions, environment dependencies, API keys referenced, branch names. If there are multiple output files, explain their relationships.

---
Rule: bullet-point format, each item self-contained. The new session's AI should be able to pick up immediately without asking the user any clarifying questions.
```

## Step 3 — Quality Check

Before delivering, verify against this checklist:

- [ ] **Fresh AI test**: Could a completely new AI session continue the work without asking the user anything? If not, add the missing context.
- [ ] **Rejection coverage**: Are all rejected approaches clearly marked with reasons? This is the #1 thing people forget, and the most painful to re-discover in a new session.
- [ ] **Concrete details are actually concrete**: File paths (not "the config file"), parameter values (not "the usual settings"), specific URLs (not "the docs page").
- [ ] **Multi-file/multi-task coverage**: If the project has multiple files or task lines, is each one's status listed separately?
- [ ] **No filler**: Every line should carry information. Cut anything that a new AI could figure out on its own.

## Step 4 — Ask About Attachments

After extracting the standard summary, **always ask the user**:

> "Before I finalize this handoff — do you have any extra instructions for the new session? For example:
> - Focus on X, skip Y
> - First check a specific file for recent changes
> - Don't re-discuss something we already decided
> - Add an additional task while you're at it"

If the user provides attachments, append an `## Attachments` section to the summary with their exact instructions. The new session must treat these as **constraints, not suggestions**.

If the user says no or skips this step, omit the Attachments section and proceed to Step 5.

## Step 5 — Deliver and Remind

Present the final summary to the user. If the user is working with an agent or tool that can write files (Claude Code, Hermes, Cursor, etc.), offer to write it to a file instead of copy-paste — a file-based handoff is more reliable than clipboard:

```
Write the handoff to handoff.md (or a path the user specifies).
```

The new session can simply read this file to continue. This is the HANDOFF pattern — more durable than copy-paste, less likely to lose formatting or sections.

Either way, add this reminder:

> "Quick tip: skim through the handoff before using it — make sure nothing important was missed, especially the rejected approaches and concrete details."

This encourages human verification, which catches gaps that automated extraction misses.

## Gotchas

- **Multiple concurrent tasks** — Users often run 2-3 workstreams in one session. If you only track the "main" one, you'll lose the others. Tag each task line's phase and progress separately in the summary.
- **Soft rejections in creative work** — Not every rejection is a hard "we decided against X." In writing/design work, there are subtle rejections: "this paragraph doesn't feel right," "I tried this angle but it didn't land," "the tone is off here." Capture these too — they prevent the new session from regurgitating the same bad drafts.
- **Multi-file projects** — When a task produces multiple files (article + images + config, or frontend + backend + database schema), list each file's status individually and explain how they relate. A single "article done" might miss that the cover image isn't generated yet.
- **Migrate while the AI is still sharp** — If the AI is already confused or degraded, the summary it produces may be unreliable. Extract while output quality is still good. If quality has already dropped, the user should verify the summary extra carefully.
- **Agent users hit context limits much faster** — Each agent turn can produce 5-10x more tokens than a plain chatbot turn due to tool calls (search, file reads, command output). 4-5 agent turns may already consume 40-50% of context. Agent users should consider migration earlier.
- **Don't over-summarize** — The goal is a working handoff, not a brief abstract. Specific decisions, specific file paths, specific rejections with reasons. Err on the side of including too much detail over too little. A good handoff is dense but scannable.
- **Compression ≠ migration** — If the user's tool has automatic context compression (Claude Code's auto-compact, Hermes's auto-compress), that's not the same as migration. Compression is lossy and done by AI guessing what matters. Migration is user-directed — the human decides what to keep. Proactively suggest migration when compression has fired multiple times.
- **The user doesn't know they need to migrate** — Sometimes context degradation is obvious to you before the user notices. If the conversation is getting circular, repetitive, or producing lower-quality output than earlier turns, proactively suggest migration before the user asks.
- **Separate unrelated tasks** — If the conversation has drifted across multiple unrelated topics, don't jam everything into one summary. Offer to create separate handoffs for each distinct workstream.
