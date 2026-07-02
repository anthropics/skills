---
name: project-retrospective
description: Use when a project has accumulated multiple sessions and needs a comprehensive retrospective — after milestones, when vision drift is suspected, before starting a new phase, or periodically every 3-5 sessions. Also use when the user says "retro", "retrospective", "project history", "what changed", "how did we get here", or when MEMORY.md feels stale and disconnected from what actually happened.
argument-hint: [last-N]
---

# Project Retrospective

Analyze a project's full session history by dispatching parallel historian agents to read each export, then synthesizing their findings into a structured analysis document. The value is in the **extraction criteria** — domain-specific signals tuned for Claude Code session exports, not generic summarization.
## Prerequisites

This skill requires **session exports** — plain text files created by running `/export` at the end of Claude Code sessions. Exports must be saved to `~/.claude/exports/{project-name}/` with date-prefixed filenames (e.g., `2026-03-17-session3-description.txt`).

Without exports, this skill cannot function. Start exporting sessions now to enable retrospectives later.

## Arguments

Parse `$ARGUMENTS` to determine scope:

| Argument | Behavior |
|----------|----------|
| *(none)* | Analyze ALL exports in the project directory |
| `last-N` | Analyze only the N most recent exports (by filename date prefix) |

If the argument doesn't match `last-N`, echo it back and ask what was meant.

## Phase 1: Discover & Validate Exports

Find all session exports:
```
~/.claude/exports/{project-name}/*.txt
```

Sort by filename (date-prefixed = chronological). If `last-N` was provided, take only the last N.

**No exports directory or no .txt files:** Stop immediately. Report the issue and suggest the user run `/export` in prior sessions. Do NOT proceed with zero exports.

**Some exports missing:** List what was found, proceed with available files, and note gaps in the final output.

## Phase 2: Spawn Historians (Parallel Background Agents)

Launch N background agents (one per export). Use the literal `Agent` tool (not TaskCreate, not TeamCreate) with these exact parameters:

```
Agent(
  description: "Historian: {SESSION_LABEL}",
  prompt: <extraction template below>,
  model: "opus",
  subagent_type: "general-purpose",
  run_in_background: true
)
```

**Why opus:** Exports are 50-200KB (30-65K tokens). Opus handles deep extraction from large documents. Haiku/sonnet miss nuance.

**Why NOT TeamCreate:** Race conditions with member registration (battle-tested failure in session 4).
**Why NOT TaskCreate:** Tasks track progress. The `Agent` tool dispatches work.

### Historian Extraction Template

Each historian receives this prompt with `{FILE_PATH}` and `{SESSION_LABEL}` filled in:

```
Read the COMPLETE file at {FILE_PATH}. This is a Claude Code session export
from {SESSION_LABEL}.

Session exports are plain text with collapsed tool calls — Agent prompts,
memory writes, and subagent details are behind expansions and NOT visible.
Extract what IS visible: user messages, Claude responses, decisions,
corrections, and deliverables.

Extract the following. Include brief quotes or concrete references — not
vague summaries.

1. **How session started**: First user prompt. Continuation or fresh?
   How was context established?
2. **Original intent vs actual**: What was planned vs what happened.
   Why different?
3. **Key decisions**: Technology, architecture, process decisions — with
   rationale and whether they held or were reversed.
4. **User corrections**: Every time the user caught Claude making a
   mistake. QUOTE the correction verbatim. This is the most valuable
   data — pattern these by type.
5. **Mistakes and anti-patterns**: What went wrong, root causes,
   systemic issues (not just one-offs).
6. **Quality moments**: When user pushed for higher rigor — what was
   the ask and what was Claude's response?
7. **Roadmap evolution**: How did the plan/scope change during the session?
8. **Deliverables**: Files created/modified, PRs opened/merged/closed,
   documents produced.
9. **Handoff**: What was stated as the next session's task? Deferred items?

Output as clean markdown. No preamble. Return TEXT DATA only — do NOT
write any files.
```

**Historian failure:** Relaunch once. If it fails again, proceed with available reports and note the gap. Do NOT approximate from other historians or from MEMORY.md — relaunch, don't guess.

## Phase 3: Synthesize

After ALL historians complete, combine reports into a single analysis. The orchestrator (main conversation) or a dedicated synthesizer agent produces:

### Synthesis Template

```markdown
# {Project Name} — Project History Analysis

**Generated:** YYYY-MM-DD HH:MM UTC | **Sessions:** range | **Agents:** N+1

## 1. Original Vision vs Current State
The user's original vision, how it evolved, honest drift assessment —
were changes justified or accidental?

## 2. Roadmap: Original vs Actual
| Session | Planned | Actual | Deviation Justified? |

## 3. Decision Log
| Session | Decision | Rationale | Status (held/reversed/superseded) |

## 4. Mistakes and Corrections
Pattern mistakes by type:
- Deferral disguised as process (effort avoidance)
- Overconfidence without verification (asserting not checking)
- Not following own rules (loaded but not consulted)
- Fabricated/unverified claims (training data biases)
Count instances per pattern — reveals systemic issues.

## 5. User Teaching Moments
Recurring lessons the user had to teach. These are the user's priorities
and standards — future sessions must internalize them.

## 6. What's Valid Now
Current state: artifacts, what's on main, what's pending. Clear inventory.

## 7. Recommended Next Step
Justified from FULL history, not just latest MEMORY.md. If history
suggests a different priority than MEMORY.md, say so.
```

**Cross-session deduplication:** A decision in S1 referenced in S3 appears once with both session numbers.

## Phase 4: Write & Integrate

### Write the analysis
`docs/YYYY-MM-DD-PROJECT-HISTORY-ANALYSIS.md`

### Update MEMORY.md
1. Add a reference to the retrospective document.
2. Evaluate whether findings warrant new rules or memory:
   - Project-specific lessons → project memory or CLAUDE.md
   - General patterns (cross-project) → propose rule in `~/.claude/rules/`
   - Existing-rule violations → note the enforcement gap, don't duplicate
3. Threshold: happened twice, or high-severity once.

### Commit
Commit the analysis and any memory updates. Push to main — analysis documents are not code changes.

## Anti-Patterns

- **Single agent for all exports** — each agent needs full context for one export. Combining loses depth.
- **Compressing historian reports** — the synthesizer needs full detail for cross-session patterns.
- **Skipping "User corrections"** — the most valuable signal. Without it, the retro is generic.
- **Writing from MEMORY.md** — MEMORY.md is derivative. Exports are the primary source.
- **TeamCreate for historians** — race conditions with member registration. Use background Agents.
- **Haiku/sonnet for historians** — exports are 50-200KB. Cheaper models miss nuance in long documents.
- **Summarizing instead of extracting** — "summarize the session" produces generic output. The 9-point extraction template IS the skill's value.
