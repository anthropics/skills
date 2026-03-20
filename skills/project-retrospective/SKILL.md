---
name: project-retrospective
description: Use when a project has accumulated multiple sessions and needs a comprehensive retrospective — after milestones, when vision drift is suspected, before starting a new phase, or periodically every 3-5 sessions. Also use when the user says "retro", "retrospective", "project history", "what changed", "how did we get here", or when MEMORY.md feels stale and disconnected from what actually happened.
argument-hint: [full | since-last-retro | last-N]
---

# Project Retrospective

Analyze a project's session history by dispatching parallel historian agents to read each export, then synthesizing their findings into a structured analysis document. The value is in the **extraction criteria** — domain-specific signals tuned for Claude Code session exports, not generic summarization.

## Modes

Two modes, selected by argument:

| Mode | When to Use |
|------|-------------|
| **full** (default) | Phase transitions, major incidents, no prior retro exists, first retro for a project |
| **since-last-retro** | Periodic check-ins (every 3-5 sessions), ongoing projects with an existing retro baseline |

**Full** re-analyzes all exports and produces a standalone superset document. **Incremental** reads the prior retro as baseline and only dispatches historians for new exports — O(delta) instead of O(N).

## Arguments

Parse `$ARGUMENTS` to determine scope and mode:

| Argument | Behavior |
|----------|----------|
| *(none)* or `full` | **Full mode.** Analyze ALL exports in the project directory |
| `since-last-retro` | **Incremental mode.** Find prior retro, analyze only new exports since then |
| `last-N` | **Full mode** but scoped to the N most recent exports only |

If the argument doesn't match any of the above, echo it back and ask what was meant.

## Phase 1: Discover & Validate Exports

Find all session exports:
```
~/.claude/exports/{project-name}/*.txt
```

Sort by filename (date-prefixed = chronological). If `last-N` was provided, take only the last N.

**No exports directory or no .txt files:** Stop immediately. Report the issue and suggest the user run `/export` in prior sessions. Do NOT proceed with zero exports.

**Some exports missing:** List what was found, proceed with available files, and note gaps in the final output.

## Phase 1.5: Detect Prior Retro (incremental mode only)

Skip this phase entirely in full mode.

In incremental mode, find the most recent full retro document:
```
docs/retros/*-PROJECT-HISTORY-ANALYSIS.md
```

**Fallback for pre-v2 projects:** If `docs/retros/` has no matches, also check `docs/*-PROJECT-HISTORY-ANALYSIS.md` (pre-v2 output path). If found there, move it to `docs/retros/` first, then proceed.

**If no prior retro exists anywhere:** Report this and switch to full mode automatically. Incremental requires a baseline.

**If prior retro found:**
1. Read it fully — it contains the synthesized analysis of previously-analyzed sessions.
2. Extract the session range it covers (from the `**Sessions:** S1-S11` header line).
3. Determine which exports are NEW (not covered by the prior retro's session range).
4. If zero new exports exist since the prior retro, report "nothing new to analyze" and stop.

**Chaining semantics:** Incremental always chains from the last *full* retro (ANALYSIS file), never from a prior *incremental update* (UPDATE file). This means multiple incremental updates can accumulate between full retros. Each delta is independently interpretable against the same baseline. To reset the chain, run a full retro.

**Gaps in prior retro:** If the prior full retro noted missing exports (sessions it couldn't analyze), those gaps are permanent unless a new full retro is run. Incremental mode does not backfill gaps — it only analyzes exports newer than the prior retro's session range.

## Phase 2: Spawn Historians (Parallel Background Agents)

**Full mode:** Launch one background agent per export (all exports).
**Incremental mode:** Launch one background agent per NEW export only.

Use the literal `Agent` tool (not TaskCreate, not TeamCreate) with these exact parameters:

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

After ALL historians complete, combine reports into a single analysis. The orchestrator (main conversation) or a dedicated synthesizer agent produces the output.

**Full mode** uses the Full Synthesis Template. **Incremental mode** uses the Incremental Synthesis Template.

### Full Synthesis Template

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

### Incremental Synthesis Template

```markdown
# {Project Name} — Project History Update

**Generated:** YYYY-MM-DD HH:MM UTC | **New sessions:** range | **Prior baseline:** prior-retro-filename
**Cumulative sessions:** full-range | **Agents:** N+1

## Prior Retro Summary
One-paragraph summary of what the prior retro established as the
project state, key patterns, and outstanding issues.

## 1. What Changed Since Last Retro
New decisions, direction shifts, scope changes in the delta sessions.
Reference prior retro for context where relevant.

## 2. New Decisions
| Session | Decision | Rationale | Status |

## 3. Correction Pattern Update
Carry forward the prior retro's correction patterns. For each pattern:
- Prior count + new count = cumulative total
- Trend: improving / stable / worsening (compare per-session rate)
- Any NEW patterns not in the prior retro get their own entry.

## 4. New Teaching Moments
Lessons from new sessions only. Note which are genuinely new vs
reinforcement of prior patterns.

## 5. Current State
Updated inventory: what's on main, what's pending, what changed.

## 6. Recommended Next Step
Justified from cumulative history (prior retro + new sessions).
```

**Cross-session deduplication:** A decision in S1 referenced in S3 appears once with both session numbers.

## Phase 4: Write & Integrate

### Write the analysis

Output to the retros directory (create if needed):

**Full mode:** `docs/retros/YYYY-MM-DD-PROJECT-HISTORY-ANALYSIS.md`
**Incremental mode:** `docs/retros/YYYY-MM-DD-PROJECT-HISTORY-UPDATE.md`

### Update MEMORY.md
1. Add a reference to the retrospective document.
2. Evaluate whether findings warrant new rules or memory:
   - Project-specific lessons → project memory or CLAUDE.md
   - General patterns (cross-project) → propose rule in `~/.claude/rules/`
   - Existing-rule violations → note the enforcement gap, don't duplicate
3. Threshold: happened twice, or high-severity once.

### Commit
Commit the analysis and any memory updates.

## Deletion Semantics

| Mode | Prior retro safe to delete? | Why |
|------|-----------------------------|-----|
| **Full** | Yes | Full output is a superset — contains everything the prior retro had plus more. Prior becomes redundant. |
| **Incremental** | **Never** | Incremental output is a delta — it references and builds on the prior retro. Deleting the prior loses the deep extraction from earlier sessions permanently. The chain of incremental retros forms a linked history. |

## Anti-Patterns

- **Single agent for all exports** — each agent needs full context for one export. Combining loses depth.
- **Compressing historian reports** — the synthesizer needs full detail for cross-session patterns.
- **Skipping "User corrections"** — the most valuable signal. Without it, the retro is generic.
- **Writing from MEMORY.md** — MEMORY.md is derivative. Exports are the primary source.
- **TeamCreate for historians** — race conditions with member registration. Use background Agents.
- **Haiku/sonnet for historians** — exports are 50-200KB. Cheaper models miss nuance in long documents.
- **Summarizing instead of extracting** — "summarize the session" produces generic output. The 9-point extraction template IS the skill's value.
- **Re-analyzing old sessions in incremental mode** — the whole point of incremental is O(delta). If you're spawning historians for sessions the prior retro already covers, you're doing it wrong.
- **Deleting prior retro after incremental** — incremental output is a delta, not a superset. The chain breaks.
- **Running incremental without a baseline** — if no prior retro exists, switch to full mode. Don't produce a delta with nothing to delta against.
