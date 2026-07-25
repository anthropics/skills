# Handoff Template Reference

The complete markdown schema for session handoff documents. Read this when structuring (organizing the inventory) and producing (writing the file). The handoff is markdown — structured for reliable parsing and direct human review.

---

## Status vocabulary

Use these exact values in every status field. No variations, no freeform text.

| Status | Meaning |
|--------|---------|
| `COMPLETE` | Work finished, no further action |
| `IN_PROGRESS` | Started, not finished |
| `BLOCKED` | Cannot proceed until a dependency resolves |
| `NOT_STARTED` | Identified, no work done |
| `DEFERRED` | Deliberately postponed — not blocked, chosen to delay |
| `NEEDS_VERIFICATION` | Done, outcome needs validation |

Carry-forward items add a lifecycle status: `pending` / `applied` / `resolved` (see Carry-forward ledger).

---

## Naming

```
{code}_SH_{MMDDYY-HHMM}_{theme-slug}.md
```

- `{code}` — project code (root, dt, mc…). Ask once if unestablished, then it is known.
- `{MMDDYY-HHMM}` — datetime. Chronological sort = build order. This is the unique sequence key; no integer is written, which removes the duplication a manual counter carries.
- `{theme-slug}` — 1–3 words, lowercase, hyphenated, the session's main theme (`skill-calibration`, `de-scaffold`).
- Same-minute collision → append `-2`, `-3`.
- Re-issue / correction of the same logical handoff → append `_v2` to the stem. Versioning disambiguates revisions, not order.

---

## Document schema

The document is markdown with fixed section headers in this order. Single-track sessions still use every applicable section.

### Handoff Card — first block of the body

~5 lines, glanceable. The ID matches the filename stem exactly.

```
{code} · SH {MMDDYY-HHMM} · {theme-slug} · v{N}
Reach-back: {Self-contained | Requires SH {id}, SH {id}}
Carry-forward: {N KF deltas pending, M open items carried | none}
Advances: {track | track | track}
```

- **ID line:** code, the `SH {datetime}` id, theme-slug, version.
- **Reach-back:** the minimum predecessors needed to fully reconstruct this handoff. `Self-contained` when all still-relevant predecessor content was integrated here. Name predecessors only when this handoff deliberately leaves context in them (e.g. a large ingested-content summary not re-carried).
- **Carry-forward:** counts of pending KF deltas and carried open items, or `none`.
- **Advances:** the track(s)/workstream(s) this session moved.

### Session header

```
# Session Handoff — {project} — {theme}

[Handoff Card]

## Session header
- **Project:** {full name}
- **Code:** {code}
- **Date:** {YYYY-MM-DD}
- **Phase:** {phase, or a brief context label for non-phase-gated projects}
- **Prior handoff:** {datetime id of predecessor, or "none"}
- **Objectives:** {1–3 sentences — what this session set out to do}
- **Completion:** {1 sentence — "2 of 3 objectives done; track 3 deferred"}
```

### Activity tracks

One subsection per concurrent work stream. The structural core.

```
## Activity tracks

### Track 1 — {specific name} — **[IN_PROGRESS]**
- **Objective:** {what this track accomplishes}
- **Starting state:** {where it stood at session start; "new this session" for new tracks}
- **Progress:**
  - **[COMPLETE]** {what the step produced or decided — not just "did step 3"}
  - **[IN_PROGRESS]** {substantive detail}
- **Current state:** {precise resumption point — specific enough to resume without re-deriving. "SKILL.md body complete at ~320 lines; reference files not started; spec is the source, in Drive." Not "most of it is done."}
- **Next steps:**
  1. {sequenced, specific action}
  2. {next action}
- **Dependencies:** {none, or specific blockers}
```

### Key decisions

Every substantive decision with rationale. Never just the choice.

```
## Key decisions

### Decision 1 — {topic}
- **Choice:** {what was chosen}
- **Rationale:** {the reasoning that supports it}
- **Implications:** {what this shapes about future work}
- **Rejected:** {alternatives considered and rejected, so they aren't re-proposed — omit if none}
```

### KF deltas

What the session learned that updates context for future sessions. Runs every handoff. Distinct from session progress (which lives in tracks). The test: *would a future session, lacking this, work from stale or missing methodology?*

When deltas exist, one block each:

```
## KF deltas

### KF Delta 1 — [pending] — origin: SH {MMDDYY-HHMM}
- **Target:** {knowledge file} › {section}
- **Action:** ADD | REPLACE | REVISE
- **Block:**
  ```
  {the exact markdown to insert into the KF — complete, drop-in ready}
  ```
- **Rationale:** {what the session learned that makes this delta necessary}
```

When none exist, the section is exactly one line:

```
## KF deltas
KF deltas this session: none — confirmed
```

Silence is impossible — absence is a stated output. KF deltas live in the handoff body (not only the closeout) so they ride the carry-forward ledger. `status` and `origin` are required on every delta.

Generalization: written as "knowledge file"; `root_*.md` targets and `build_context.md` are examples, not hardcoded. Projects without knowledge files omit this section.

### Ingested content

Working understanding of uploaded files and external sources, not raw content.

```
## Ingested content

### Source 1 — {filename or identifier}
- **Type:** uploaded_file | web_reference | conversation_context | external_data
- **Key content:** {the relevant facts, data, constraints — dense and specific. "Revenue $4.2M Q3, 62% gross margin, enterprise +34% YoY, SMB −8%, CAC payback 14mo." Not "the spreadsheet had financials."}
- **Usage:** {how it shaped the session}
- **Re-upload needed:** true | false
```

### Artifacts produced

```
## Artifacts produced

### Artifact 1
- **Filename:** {full name with {code}_ prefix}
- **Location:** {cloud path "Projects/{code}/", /mnt/user-data/outputs/, repo path — both if applicable}
- **Status:** COMPLETE
- **Description:** {what it is and contains, 1–2 sentences}
- **Cross-project:** {target project name — include ONLY if intended for another project; omit otherwise}
```

### Open items

Unresolved questions, deferred items, blockers, follow-ups. Carry `status` and `origin`.

```
## Open items

### Item — [priority: high] — [status: pending] — origin: SH {MMDDYY-HHMM}
- **Description:** {specific, actionable}
- **Context:** {why it matters, urgency, what blocks on it — enough that the next session needs no background}
```

`status`: `pending` (unresolved) / `resolved` (drops from the next handoff's ledger). `origin`: the datetime id where the item first appeared.

### Files to load next conversation

The conversation files needed to resume — distinct from project knowledge files (loaded into the Project) and from per-source re-upload flags. Split by track and by necessity.

```
## Files to load next conversation

### Required to continue (all tracks)
- {file} — {why}
- {this handoff} — load first

### Track: {name}
- {file} — required for this track
- {file} — optional, only if pursuing {sub-goal}
```

Derive from each track's next steps: which files do those steps depend on? The "required (all tracks)" group holds what every resumption needs (a governing spec, the handoff itself). This list is what the chat echo reproduces.

### Continuation plan

```
## Continuation plan
- **Summary:** {1–2 sentences — where things stand, what to focus on}
- **Scope estimate:** {"completable in one session" | "likely N sessions" | "depends on X"}
- **Priority sequence:** (sequenced across tracks; first action = immediate resumption point)
  1. ({track 1}) {first action — typically the highest-priority unblocker or near-completion item; reason for priority}
  2. ({track 1}) {what comes once #1 clears}
  3. ({track 2}) {action on another track}
- **Items carried forward:** (the ledger — unresolved items + pending KF deltas from prior handoffs, with origin; omit if none)
  - [from SH {id}] {item — carried because not addressed this session due to {reason}}
```

### Starter prompt

```
## Starter prompt
```
Uploading session handoff {datetime id}. Covers {brief scope}.
Resume with {specific first action from the continuation plan}. Full sequence in the continuation plan.
{Any orientation beyond the handoff — files to load, Memory state, prerequisite actions.}
```
```

A fenced code block — no CDATA (that was an XML concern). 2–5 sentences, terse, directive. References the handoff filename, states the single first action, points to the continuation plan, adds only orientation the handoff doesn't already carry. Match the user's communication style.

---

## Carry-forward ledger

The mechanism that makes pending context survive a long chain.

1. KF deltas (status `pending`) and open items (status `pending`) each carry an `origin` — the datetime id of the handoff where they first appeared.
2. **When this handoff continues from prior handoff(s) in context, inherit all still-pending KF deltas and unresolved open items, preserving origin.** Items marked `applied` / `resolved` drop. The ledger self-prunes.
3. This extends v1.0's open-item carry-forward to also cover KF deltas, and the explicit status is what lets the ledger shrink instead of growing forever.
4. Flag any item carried across 2+ handoffs: stale (remove) or blocked (escalate priority).

Skipping inheritance is the "items fall through the cracks" failure — so it runs whenever a chain is continued.

---

## Markdown design notes

**Section headers are the schema.** Fixed `##` headers in the order above. Content that doesn't fit a section goes in the most relevant one — never invent a new section header. Consistent structure is what makes the document parse reliably across sessions.

**Status inline.** Track and step status render as `**[STATUS]**` inline so they scan at a glance. Carry-forward lifecycle status renders as `[status: pending]`.

**ID labels for cross-reference.** Tracks carry numeric labels (Track 1, Track 2); the continuation plan references them by number. KF deltas and open items carry their `origin` datetime id, which is globally unique — so reach-back and ledger references are unambiguous.

**The Card is the index.** Reach-back and carry-forward counts live in the Card so the document's dependencies and pending load are readable in five lines without scrolling.

---

## Starter prompt construction

The most important single paragraph — it determines whether the next session starts productively. Requirements:

1. Reference the handoff by its datetime id / filename (it will be uploaded).
2. State the single first action from the continuation plan.
3. Point to the full continuation plan for sequencing.
4. Add only orientation beyond the handoff (files to load, Memory state, prerequisites).

Style: match the user's preferences — typically terse and directive, no context re-establishment beyond the handoff reference. Length 2–5 sentences; longer is wasted context.

**Examples:**

Single-track:
```
Uploading handoff SH 062426-1610. Resume the escalation decision tree — reference templates next. Design doc also loaded.
```

Multi-track:
```
Uploading handoff SH 062426-1430. Three tracks — start with the build_context update (Track 2, top priority per continuation plan). Track 1 (template library) is complete. Track 3 (cross-project propagation) needs the strategy project's positioning doc loaded.
```

Proactive:
```
Uploading handoff SH 062426-1500. Context pressure forced early closeout. Resume Track 1 step 4 — the 80%-complete deliverable. Continuation plan has the full sequence.
```
