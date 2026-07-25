# Grill-Me Section Walk Discipline

This reference answers exactly one decision: **how does inbox-setup walk 8 sections of ~25-31 questions without violating grill-me discipline, and what makes the discipline survive heavy intake?**

## The Core Tension

Capture's grill-me is **max-1 question** per dump (light intake). Inbox-setup is **25-31 questions across 8 sections** (heavy intake). At that scale, the one-question-at-a-time rule is easy to break — the interviewer is tempted to batch, the user is tempted to dump everything at once.

The discipline survives because:

1. **Section boundaries** create natural commit points
2. **Skip-logic** removes ~6 questions when irrelevant (Section 4)
3. **Per-section file writes** make partial completion still useful
4. **Forcing format** keeps questions answerable in seconds

## The Four Rules

### Rule 1: One Question Per Turn — Across Section Boundaries

The rule does NOT relax when moving between sections. After S2.Q3 commits `email-taxonomy.md`, ask S3.Q1 alone — not "S3.Q1 and S3.Q2 since you already know your voice."

**Why:** the user is fatigued by question 18; bundling 3 at once produces shallower answers. Better to be slow than to lose answer quality on the high-leverage voice + framework questions.

### Rule 2: "Why I'm Asking" On Every Single Question

Without the rationale, users either:
- Skip past the question thinking it's optional
- Answer minimally because they don't know what's at stake
- Misunderstand the depth needed

The rationale is short (1-2 sentences) and concrete ("This becomes a forbidden token in drafts" beats "this helps me understand your style").

### Rule 3: Forcing Format > Open-Ended

| ✅ Forcing | ❌ Open-ended |
|---|---|
| "Run frequency: once daily / 2x daily / 3x daily / on-demand only?" | "How often should I run?" |
| "Does this taxonomy match: yes / mostly / no?" | "What do you think of this taxonomy?" |
| "Register: formal / casual / in-between?" | "Describe your tone." |

Open-ended works for: pet peeves (S3.Q2), sign-offs (S3.Q3), hard rules (S3.Q6), VIP list (S4.Q6), tracker entries (S6.Q1) — where the answer space is genuinely unbounded and forcing format would harm signal.

### Rule 4: Commit Per Section, Not End-Of-Interview

After Section 2's 3 questions: write `email-taxonomy.md`. Do NOT wait until Section 8 to write all files at once.

**Why:** if the user drops off after Section 4 (~16 questions in), the user has a useful partial KB (taxonomy + patterns + framework + rate card). If files were batched at the end, drop-off leaves nothing.

## The 8 Sections at a Glance

| Section | Questions | Skip-Logic | Files Written at End |
|---|---:|---|---|
| 1. The Big Picture | 6 | always run | (none — build mental model) |
| 2. Email Categories | 3 | always run | `email-taxonomy.md` |
| 3. Reply Style & Voice | 6 + samples | always run | `email-patterns.md` |
| 4. Evaluation Framework | 6 | skipped if no opportunity category in S1 | `evaluation-framework.md` + `rate-card.md` (cond) |
| 5. Blocklist & Patterns | 3 | always run | `blocklist.md` |
| 6. Current State | 3 | always run | `tracker.md` + `triage-log/` dir |
| 7. Report Preferences | 3 | always run | appended to `email-taxonomy.md` |
| 8. Confirmation & Handoff | 0 (summary) | always run | (no file write; handoff message) |

**Total: 24 + 6 conditional = 30 max** (or 24 if S4 skipped). Hard ceiling 35 includes sub-clarifications.

## Skip-Logic Detail

### Section 4 Skip

After S1.Q2 ("what dominates your inbox?"), if the answer does NOT include:
- "sales pitches" / "opportunities" / "client work proposals"

Then mark S4 as skipped. State to user:

> Skipping Section 4 (Evaluation Framework) since your inbox doesn't include pitches/opportunities. Moving to Section 5.

The user CAN override: "Actually I do get opportunity emails — run that section." Honor the override.

### Per-Question Conditional Skips

Some individual questions have "(Skip if none)" suffix:

- S2.Q2 (missing categories?) — skip if user says all listed
- S5.Q1 (skip-senders?) — skip if user has none yet
- S6.Q1 (active threads?) — skip if user has none
- S6.Q2 (overdue?) — skip if user has none
- S6.Q3 (deadlines?) — skip if user has none

These skips ALSO commit to the file (with empty section) so triage knows the section was considered, not forgotten.

## Per-Section File Commit Pattern

```
1. Ask all questions in Section N (one at a time)
2. Synthesize answers into structured file content
3. Write file(s) at ${WORKSPACE}/Email/{filename}
4. Confirm to user: "✓ Section N complete. {file(s)} committed."
5. Record in session tracker:
     python scripts/section_progress_tracker.py \
       --action record_section_done --session NAME \
       --section N --files "{filename}"
6. Move to Section N+1's first question.
```

## Re-Run Mode

Detect re-run when `${WORKSPACE}/Email/email-taxonomy.md` exists.

Walk the user through per-file consent:

```
Found email-taxonomy.md from 2026-03-04 (45 days ago).
Replace / merge / skip?
- replace: rewrite from new interview answers
- merge: keep existing categories, add new ones from this run
- skip: leave file as-is; move to next file
```

Walk only the sections whose files the user chose to replace or merge. If user chose skip for a file, do NOT re-ask that section's questions.

## Sample-Collection Discipline (S3.SAMPLES)

The sample-emails ask is **the highest-quality voice signal** the skill has. It is NOT optional from a quality standpoint, but it IS skippable by user choice.

**Discipline:**

1. Ask for 3-5 real sent emails. Frame it as "the best signal I have."
2. If user pastes them: run `scripts/voice_sample_analyzer.py` and incorporate the output into `email-patterns.md` under "Voice Patterns (Extracted from Samples)."
3. If user refuses: use S3.Q1-Q6 self-description only. Flag in `email-patterns.md`:
   > `[calibration may need iteration — voice samples not collected during setup. First few triage runs will likely produce drafts that need editing; the system learns from your edits.]`
4. Never proceed past Section 3 without either samples OR explicit user-skip + flag.

## Anti-Patterns To Reject

- Asking S1.Q1-Q3 in one message ("tell me your role, what dominates your inbox, and rough volume split")
- Asking S2.Q1 without "Why I'm asking"
- Writing all 7 files at end of S8 (no per-section commit)
- Asking S4 questions when no opportunities surfaced in S1
- Asking S5.Q1 again when user already said "I have no blocklist yet" in S1
- Forcing closed-format on genuinely open questions (e.g., "Pet peeves: a) clichés b) emojis c) other" — kills signal)
- Skipping the rationale ("Why I'm asking") to "save time"
- Skipping the sample ask in S3
- Re-running and overwriting existing files without per-file consent

## Citations

The grill-me discipline this reference enforces is canonical in this repo. See:

- [`engineering/grill-me/`](../../../../engineering/grill-me/) — the source skill that formalized the discipline
- Matt Pocock's original grill-me skill (MIT)
- This repo's PR #657 cross-skill consistency audit, which verified the discipline transfers consistently across all intake-having skills (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13)
