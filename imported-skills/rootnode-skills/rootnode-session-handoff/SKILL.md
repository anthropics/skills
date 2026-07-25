---
name: rootnode-session-handoff
description: >-
  Produces structured markdown session continuation documents for
  multi-session workflows. Captures active work streams, decisions with
  rationale, knowledge-file deltas learned during the session, the exact
  files to load next conversation, ingested content, artifacts, and open
  items into an ingestion-optimized handoff. Carries pending KF updates and
  unresolved items forward across handoff chains so context never drops.
  Generates a closeout checklist and echoes the starter prompt to chat. Use
  when approaching context limits, wrapping up a session, or managing work
  across conversations. Trigger on: "create a handoff," "session closeout,"
  "wrap up this session," "build session handoff," "BSH," "continue next
  session," "we're running out of context," "context is getting long." Do
  NOT use for Memory optimization, context budget analysis, project audits,
  deciding whether work is ready for autonomous/Claude Code execution (use
  rootnode-handoff-trigger-check), or summaries with no continuation intent.
license: Apache-2.0
metadata:
  author: rootnode
  version: "2.0"
  predecessor: "rootnode-session-handoff v1.0"
  original-source: "Seed-project methodology synthesis + rootnode-session-handoff v1.0 source"
  discipline_post: phase-32
---

# Session Handoff

> **Calibration:** Tier 1, broad-tier. Built and calibrated for Opus 4.8; runs on Sonnet 4.6 and Haiku 4.5. See repository README for model compatibility.

> **Version 2.0:** Markdown output (was XML). Adds forced knowledge-file delta capture, a files-to-load-next-conversation list split by track, a chat echo of the starter prompt and load list, datetime-stamped naming with a Handoff Card, a completeness gate, and a carry-forward ledger that survives long handoff chains. v1.0 capture discipline preserved.

Produce a markdown session continuation document when multi-session work needs a clean breakpoint. The document is the next session's only inheritance from this one — it carries active tracks, decisions, knowledge gained, the files to reload, and open items so work resumes immediately instead of being re-derived.

## Important

The handoff is everything the next session gets. **The next session's Claude has no access to this conversation.** Anything that matters lives in the handoff document or a persistent store (Memory, knowledge files, delivered files). Conversation-only content goes in the document at full fidelity, or it is lost.

These are gates. Each runs every handoff; skipping any produces a broken artifact:

- **Knowledge-file deltas are never silent.** Every handoff evaluates what the session learned that belongs in a knowledge file and emits drop-in KF blocks — or states `KF deltas this session: none — confirmed`. Absence is a deliberate, stated output, never an omission. This is the v2.0 headline: context gained in a session must reach the KFs, not evaporate.
- **Decisions carry rationale.** A decision logged as "chose X" forces the next session to follow blindly or re-derive. Capture the why and the implications. This is the #1 continuity failure.
- **The completeness gate runs before emit.** Verify every stream, decision, KF-delta evaluation, load list, carry-forward inheritance, and the starter prompt before finalizing. The gate is the backstop against silent drops.
- **Output is markdown.** Always. Structured markdown parses reliably and stays human-readable for direct review. Preserve the section schema and the status vocabulary; never substitute freeform structure.
- **Each handoff is a snapshot, not a log.** Continuing from a prior handoff replaces it. Unresolved items and pending KF deltas carry forward explicitly through the ledger. The document never grows by appending.

## What the handoff must achieve

A correct handoff satisfies four outcomes. The method below is the reliable path to them, not a checklist to recite — lead with the outcome, let the steps serve it.

1. **Complete capture.** Every active work stream, decision, and piece of conversation-only knowledge is present at full fidelity.
2. **Persistence-correct.** Content that lives in a persistent store is referenced, not duplicated; content that exists only in this conversation is captured in full.
3. **Forward-carrying.** Pending KF deltas and unresolved open items from this session and any predecessor survive into the next handoff until applied or resolved.
4. **Ingestion-optimized.** Dense, specific, state-over-history, consistently structured, fast for the next session to act on.

## How to get there

The method that reliably hits those outcomes:

**Inventory the session.** Catalog objectives, every activity track (starting state, progress, current state, next steps), decisions with rationale, uploaded content (working understanding, not raw text), conversation-only knowledge (most at-risk — exists nowhere else), artifacts, and open items. If continuing a chain, pull the predecessor's pending KF deltas and unresolved items.

**Assess against the persistence test.** For each item: if the next session's Claude wouldn't have it without this document, it goes in at full fidelity; otherwise it becomes a reference pointer. Memory edits → reference. Knowledge files → reference by name. Delivered files → reference path + `{code}_` name. Conversation-only → full fidelity.

**Evaluate KF deltas (gate).** Separately from session progress, ask: what did this session learn or change that updates context for *future* sessions — methodology, principle, decision rationale, taxonomy, threshold, convention? Each qualifying item becomes a drop-in KF block (target file + section, action, the block, rationale), tagged with status and origin. If nothing qualifies, state it explicitly. Read `references/handoff-template.md` for the block format.

**Structure to the schema.** Organize into the markdown sections in `references/handoff-template.md`, leading with the Handoff Card. Apply ingestion optimization: density over prose, specific over summary, state over history (except rejected alternatives, which prevent re-proposal), consistent structure, re-upload flags on every ingested file.

**Produce and verify.** Output the handoff as a downloadable markdown file. Run the completeness gate. Produce the closeout checklist in conversation (read `references/closeout-checklist.md`). Echo the starter prompt and files-to-load list into the chat.

## Naming and the Handoff Card

**Filename:** `{code}_SH_{MMDDYY-HHMM}_{theme-slug}.md` — e.g. `root_SH_062426-1430_skill-calibration.md`.

- `{code}` is the project code; if not yet established, ask once, then it is known.
- `{MMDDYY-HHMM}` is the datetime; chronological sort equals build order, so it is the unique sequence key — no integer is needed and none is written, which removes the duplication risk a manual counter would carry.
- `{theme-slug}` is 1–3 words, lowercase, hyphenated, capturing the session theme.
- Same-minute collision appends `-2`. A re-issued or corrected handoff for the same session appends `_v2` to the stem; versioning disambiguates revisions, not order.

**Handoff Card** — the first block of the document body, ~5 lines, glanceable, ID matching the filename stem:

```
root · SH 062426-1430 · skill-calibration · v1
Reach-back: Self-contained
Carry-forward: 2 KF deltas pending, 1 open item carried
Advances: 4.8 alignment | session-handoff redesign
```

The reach-back line names the minimum predecessors needed to reconstruct this handoff (`Self-contained`, or `Requires SH 062326-0900, …`). When a stack of handoffs is loaded, chronological order of the datetime IDs is build order; orient by ID and reach-back rather than any written ordinal. Full card and reach-back rules: `references/handoff-template.md`.

## The forward-carry mechanism

KF deltas and open items each carry a `status` (`pending` / `applied` / `resolved`) and an `origin` (the datetime ID of the handoff where they first appeared). **When continuing a chain, inherit all still-pending KF deltas and unresolved open items from the predecessor(s), preserving origin** — applied and resolved items drop out, so the ledger self-prunes. This is what makes "context never silently drops" hold across a 20-handoff chain, not just one hop. Flag any item carried across 2+ handoffs: stale (remove) or blocked (escalate).

## Files to load next conversation

Distinct from project knowledge files (loaded into the Project, not the chat) and from per-source re-upload flags. List the conversation files needed to resume, split by track and by necessity — a "required to continue (all tracks)" group plus per-track groups marking each file required or optional. Derive from each track's next steps: which files do those steps depend on? Format: `references/handoff-template.md`.

## Chat echo

After delivering the handoff file and the closeout checklist, post to the current chat, copy-paste-ready: the starter prompt (fenced) and the files-to-load list. Both also live in the handoff; the echo exists so the next conversation launches fast without opening the handoff first.

## Proactive vs. requested

**Requested** ("wrap up," "create a handoff," "BSH"): full method at full depth. Finish in-flight deliverables that complete quickly first; thoroughness is the priority.

**Proactive** (context pressure ~70%): same outcomes and gates, urgency-aware execution. Inventory prioritizes in-flight over completed work; assess whether near-complete items (under ~10% of remaining budget) finish first; the document leads with active-track state and next steps, compresses completed work; the Card notes estimated remaining context. The KF-delta and completeness gates still run — pressure is not a reason to drop them.

## Conventions

Recommended patterns, not platform requirements — adopt where they fit.

- **Institutional memory file:** if the project maintains a `build_context.md` or equivalent, the closeout assesses whether it needs updating and what. KF deltas captured in the handoff are often the source of that update.
- **Propagation:** if the session changed system-wide facts, flag propagation items so downstream references stay in sync. KF deltas are a first-class propagation vehicle.
- **Phase-gated work:** capture current phase, objectives, within-phase progress; cross-phase sessions document both.
- **Cross-project artifacts:** flag with the target project name in artifacts and as an explicit open item.
- **Terse starter prompts:** match the user's style; reference the handoff file, state the first action, done.
- **Cloud storage as canonical:** reference paths/URIs for files stored outside the conversation; note the delivery output path.

## Examples

### Example 1 — Single track, clean break, with a KF delta

A 2-hour Skill-design session. "Wrap this up."

Inventory: one track (Skill design), three decisions with rationale, no uploads, several conversation-only design-rationale items, one delivered spec file. Assess: spec file delivered → reference; decisions and rationale → full fidelity. **KF-delta evaluation:** the session established a reusable naming convention that future sessions must follow → one KF block (`target: build_context.md › conventions`, action ADD, the block, rationale), status `pending`, origin this handoff. Structure: Card, one track IN_PROGRESS, three decisions, one KF delta, one artifact, two open items, files-to-load (the spec, required), starter prompt. Produce + verify gate + echo.

Result: `{code}_SH_062426-1610_skill-design.md`. The naming convention reaches the KFs instead of living only in the dead conversation.

### Example 2 — Continuing a chain, carry-forward in action

Session 3 in a chain. The prior handoff left 2 pending KF deltas and 1 unresolved open item; this session applied 1 delta and resolved nothing.

Inventory pulls the predecessor's ledger. **Carry-forward:** the 1 still-pending KF delta re-surfaces with its *original* origin ID; the applied delta drops; the unresolved open item carries with its origin; this session adds 1 new delta. The item now carried across 3 handoffs is flagged — escalate or remove. Reach-back: this handoff integrated the predecessor's still-relevant decisions, so `Self-contained`; had it left a large ingested-content summary in the predecessor, it would name it.

Result: nothing from three sessions back falls through; the ledger shows exactly what is still pending and where each item originated.

### Example 3 — Proactive trigger

Context pressure ~70%. Two tracks, one ~80% done, one ~30%. The ~80% track needs ~5% of remaining budget — finish it first, then run the method. Document leads with the 30% track at full detail, compresses the completed one. KF-delta and completeness gates still run. Starter prompt focuses on the 30% track; Card notes remaining context.

## When to Use This Skill

Use when approaching context limits and continuing in a new session, wrapping up a session with intent to continue, managing multi-track work across conversation boundaries, or when context pressure hits ~70% and in-flight work cannot complete.

Do NOT use for optimizing Memory content (use rootnode-memory-optimization if available), analyzing context budget (use rootnode-context-budget if available), auditing project structure (use rootnode-project-audit if available), deciding whether work is ready for autonomous/Claude Code execution (use rootnode-handoff-trigger-check if available), summarizing with no continuation intent, or when work is fully complete with no pending items.

## Troubleshooting

**Next session doesn't resume cleanly:** starter prompt too vague, or conversation-only knowledge was summarized instead of captured at full fidelity. The prompt must name the handoff file, state the first action, and orient to the project.

**Decisions get re-litigated:** rationale missing or thin. Capture the reasoning, the implications, and any rejected alternative so it isn't re-proposed.

**Context gained in a session never reaches the KFs:** the KF-delta gate was skipped or produced an empty result without the explicit confirmation line. Every handoff emits blocks or `none — confirmed`. If deltas exist, they belong in the handoff body with status and origin, not only flagged in the closeout.

**Items fall through across sessions:** carry-forward inheritance didn't run. When continuing a chain, inherit all pending KF deltas and unresolved items with origin preserved. Check the ledger.

**Handoff numbering or order is ambiguous:** rely on the datetime ID, not a written count — chronological order of `{MMDDYY-HHMM}` is build order. Use `_v2` only for a re-issue of the same handoff.

**Uploaded file content lost between sessions:** re-upload flag wrong, or the key-content summary too thin. Capture every fact, constraint, or data point that influenced the work.

**Handoff too long for the next context:** too much completed-work detail. Compress completed tracks to final state; the next session needs current state and next steps.

## Reference table

| Reference | When to read |
|---|---|
| `references/handoff-template.md` | The markdown schema — all section formats, status vocabulary, Handoff Card, KF-delta block, files-to-load, carry-forward ledger, reach-back, naming. Read when structuring and producing. |
| `references/closeout-checklist.md` | The closeout checklist delivered in chat — Memory update patterns, build_context assessment, propagation (KF deltas as vehicle), chain handling, cross-project items, chat echo, completeness line. Read at produce. |

*End of SKILL.md.*
