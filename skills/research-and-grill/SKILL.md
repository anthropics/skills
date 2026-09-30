---
name: research-and-grill
description: Use when the user wants to research a topic from the web and be tested on it via Socratic questioning. Triggered by "research and grill me on X", "teach me then quiz me", or "/research-and-grill [--deep] <topic>". Scans current repo to make questions relatable to the user's codebase.
---

# Research and Grill

## Overview

Research a topic from the web, silently scan the current repo for relevant context, synthesize key concepts, then grill the user with Socratic questions — blending in analogies to their actual codebase where genuinely useful.

## Invocation

```
/research-and-grill [--deep] <topic>
```

- No flag → quick mode: fetch 3–5 pages, ~5 questions
- `--deep` → thorough mode: fetch 10–15 pages, ~10–15 questions

## Pre-flight: Topic Clarity Check

If the topic is a single generic word or fewer than 3 words with no clear focus (e.g. "databases", "security", "AI"), ask before proceeding:

> *"Are you interested in a specific aspect of [topic]? For example: [suggest 2–3 sub-angles]. Or type 'broad' to proceed with a general overview."*

If the topic is specific enough (e.g. "deploying Rails apps to EC2", "React Server Components"), proceed directly.

## Phase 0: Context Scan

Silently locate the primary dependency manifest in the current directory (any of `package.json`, `Gemfile`, `pyproject.toml`, `go.mod`, `Cargo.toml`, `pom.xml`). Read it to extract the tech stack and key libraries.

Then identify the topic's domain and locate the primary config or schema file for that domain:
- **Deployment / infra** → `Dockerfile`, `.github/workflows/`, `deploy/`, CI config files
- **Database / models** → primary schema file (`schema.rb`, `prisma/schema.prisma`, `models/`, `migrations/`)
- **Frontend / UI** → component directory (`components/`, `pages/`, `src/`)
- **Auth / security** → auth middleware or config files
- **Background jobs** → job/worker config files

Extract: tech stack, key libraries, what the user has been building. Store as `repo_context`.

If no repo or no relevant files exist, skip silently — do not mention it.

## Phase 1: Research

Use WebSearch and WebFetch. Before searching, state the 5 angles you will cover, then search one per angle:
1. Core definition and fundamentals
2. Key mechanisms and how it works
3. Common misconceptions and pitfalls
4. Real-world applications and tradeoffs
5. Recent developments or alternatives

Depth:
- **Quick mode**: 3–5 searches, fetch 3–5 source pages
- **Deep mode**: 10–15 searches, fetch 10–15 source pages

Extract **key concepts worth reasoning about** — ideas, tradeoffs, and relationships, not just facts. Synthesize into a structured summary grouped by concept.

## Phase 2: Show Summary

Present findings as a clear summary with a numbered list of key concepts to be covered.

If `repo_context` is relevant to the research topic, add one line:
> *"I see you're working on [X] — a few questions will connect these concepts to that."*

Only include this line if the connection is genuine and specific. If it is not relevant, omit it entirely — and do not blend repo_context into Phase 3 questions either.

End with: *"Ready to be grilled? Type 'yes' to start. You can type 'skip [concept number]' at any point to skip a topic."*

## Phase 3: Grill

**Ask exactly one question at a time. Wait for the user's response before asking the next. Never batch questions.**

- Number of questions scales with depth: quick → ~5, deep → ~10–15
- **Socratic style** — ask questions that require the user to reason about tradeoffs, failure modes, or relationships between concepts. Never ask definitional recall questions ("what is X?")
- If `repo_context` is relevant (established in Phase 2), blend 2–3 questions naturally into the codebase context. If it is not relevant, ask no repo-grounded questions at all.
- After each answer:
  - Acknowledge what was right
  - Gently correct misconceptions with explanation
  - Connect back to the research findings
  - Ask the next question

## Phase 4: Mastery Report

After all questions (or when user says "stop"), give a short report:
- Concepts the user understood well
- Concepts to revisit
- 1–2 recommended resources for deeper learning

If fewer than 3 questions were answered, note the session was too short for a meaningful assessment. List all concepts as "not yet covered" with a recommended resource for each.

## Rules

- Always cite which source a fact came from when presenting the summary
- If web search is unavailable, tell the user and offer to grill from training knowledge instead
- Never repeat the same question twice
- If the user says "skip [concept]" before grilling starts, remove that concept from the question queue entirely
- If the user says "skip" during grilling, move to the next concept immediately
- If the user says "stop", jump straight to the mastery report
- Do not mention which files you scanned unless the user asks
