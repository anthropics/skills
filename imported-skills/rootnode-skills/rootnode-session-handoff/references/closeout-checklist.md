# Closeout Checklist Reference

Template and guidance for the closeout produced after the handoff file. Read this at produce, after outputting the markdown handoff. The closeout is delivered in conversation (not in the handoff file) and is the Skill's final output, alongside the chat echo.

---

## Closeout checklist template

Present after delivering the handoff document:

```
## Closeout Actions

- [ ] **Handoff delivered:** {filename} — /mnt/user-data/outputs/
- [ ] **Completeness:** verified — every stream, decision (with rationale), KF-delta evaluation, load list, and carry-forward inheritance present
- [ ] **KF deltas:** {N blocks captured in the handoff, status pending | "none — confirmed"}
- [ ] **Memory updates:** {specific recommendations | "none needed"}
- [ ] **build_context.md:** {specific updates needed | "current — no update needed"}
- [ ] **Propagation:** {cross-file items | "none"}
- [ ] **Files to load:** listed in the handoff and echoed to chat below
- [ ] **Starter prompt:** in the handoff and echoed to chat below
```

The `Completeness: verified` line is the visible result of the completeness gate. If the gate fails, the handoff isn't done — fix the gap before delivering.

---

## Chat echo

After the checklist, post to the current chat, copy-paste-ready, so the next conversation launches without opening the handoff:

```
**To start the next conversation:**

Starter prompt:
```
{the exact starter prompt from the handoff}
```

Files to load:
- {required file} — {why}
- {track file} — {required / optional}
```

Both also live in the handoff. The echo is a convenience copy, not the source of truth.

---

## Memory update recommendations

The Skill recommends Memory updates; it does not execute them. Present as specific, actionable items.

A fact qualifies for Memory if it passes both tests: **persistence** (still relevant in 5+ sessions?) and **orientation** (does Claude need it to orient correctly at the start of *every* conversation?). Session-specific facts stay in the handoff; task-specific facts belong in a knowledge file.

Common patterns: **phase advancement** ("Phase N COMPLETE; Phase N+1 active" — the most common), **project-state changes** (KFs/Skills added, architectural decisions), **workflow-convention changes** (new recurring patterns), **key facts discovered** (thresholds, constraints, empirical findings).

Does NOT go in Memory: session progress (handoff), deliverable-specific decisions (the deliverable or build_context), file contents (knowledge files), step-by-step plans (the continuation plan), anything duplicating a knowledge file.

```
**Memory updates recommended:**
1. ADD: "Phase {N} active — {brief description}"
2. UPDATE: {entry superseded by a new decision/finding}
3. REMOVE: {outdated entry}
```

Or: "No Memory updates needed — current entries are accurate."

---

## build_context.md assessment

For projects with a `build_context.md`, assess whether it needs updating. This file is institutional memory — phases, decisions, evolution.

Needs updating when: a phase advanced, a significant architectural decision was made, KFs/Skills/components changed, a design spec was produced that drives future work, or operational state changed. Does NOT when: routine within-phase work (unless a milestone was hit), pure discussion with no deliverables, or work fully captured in the deliverable with no project-level effect.

**KF deltas captured in the handoff are frequently the source of the build_context update** — a delta targeting `build_context.md` is both a carry-forward item and the content of the update. Cross-check: every `build_context.md`-targeted KF delta should appear here.

```
**build_context.md update needed:** Yes
- Add Build History entry for the work completed
- Update next-priorities to reflect completion
- Apply KF Delta {n} (targets build_context.md)
```

Or: "**build_context.md:** Current — no update needed this session."

---

## Propagation assessment

If the session changed system-wide facts, flag propagation items per any propagation checklist the project documents (commonly in `build_context.md`).

Triggers: file counts, block/approach counts, tendency-taxonomy changes, Compiler/Optimizer mode changes, architectural-state changes (new layer model, new thresholds), Skill-inventory changes.

Targets: **build_context.md** (always when system facts change), **CONTENTS_INDEX.md** (if KF inventory changed), **Memory** (if orientation facts changed), **CI / Custom Instructions** (if KF routing, Skill references, or modes changed — this is the *first* trigger when KFs are added), **dependent knowledge files** (anything referencing the changed fact).

**KF deltas are a first-class propagation vehicle.** When a delta updates methodology that lives in multiple landing locations (seed Project KF, repo canonical copy, installed Skill copies, global CLAUDE.md for universal disciplines), list each location as a propagation item so the delta lands everywhere, not just the seed.

```
**Propagation items:**
1. KF Delta {n} (methodology change) → seed KF + canonical-kfs/ + installed Skill copies + (if universal) global CLAUDE.md
2. New Skill / version bump → README, build_context.md Skills inventory, Memory, personal install
3. Workflow-convention change → Memory entry so future sessions follow it
```

Or: "**Propagation:** None — no system-wide facts changed."

---

## Chain-of-handoff handling

When this session started from a prior handoff, the closeout accounts for the chain.

1. **The new handoff replaces the prior one.** The next session uploads only the new handoff (plus any files in its load list) — not the whole chain by default. The new document is self-contained unless its reach-back line names predecessors.
2. **Carry forward via the ledger.** Every still-pending KF delta and unresolved open item from the predecessor is inherited with origin preserved; applied/resolved items drop. (See the ledger rules in `handoff-template.md`.)
3. **Reference, don't reproduce.** Still-relevant predecessor decisions and ingested content are integrated into this handoff's own sections — no "prior session" section. This is what earns a `Self-contained` reach-back.
4. **Audit long chains.** Flag any item carried across 2+ handoffs — stale (remove) or blocked (escalate). The datetime origin id makes "how long has this been carried" answerable at a glance.

```
**Handoff chain:** Session 3 (SH 062326-0900 → SH 062426-1015 → this).
- 1 KF delta carried from SH 062326-0900, still pending (elevated)
- 1 open item from SH 062426-1015 resolved this session
- 1 new KF delta added; reach-back Self-contained
```

Or: "**Handoff chain:** New chain — no prior handoff."

---

## Cross-project handoff items

When session work produces artifacts or decisions for another project, flag them separately.

Qualifies: design specs for build elsewhere, decisions affecting another project's architecture, files to load into another project's knowledge base, information to propagate to another project's Memory or CI.

```
**Cross-project items:**
1. Design spec produced → target build project for implementation
2. Strategic positioning update → strategy project (note reference files to load)
```

Or: "**Cross-project items:** None — all work contained within this project."
