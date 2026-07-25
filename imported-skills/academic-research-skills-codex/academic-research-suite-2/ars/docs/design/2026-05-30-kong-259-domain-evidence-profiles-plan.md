# Domain Evidence Profiles (#259) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use subagent-driven-development (recommended) or executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Let a scholar select a discipline-relative `domain_evidence_profile` at paper intake so the literature-screening agent loosens (never tightens) its post-retrieval evidence gates to that discipline, instead of applying one Western EBM pyramid to every field — advisory only, scholar-confirmed, with a PCR field as the single carrier.

**Architecture:** The active profile lives as a single-value field on the Paper Configuration Record (PCR), exactly like `Style Profile` — NOT on the Material Passport, NOT a numbered handoff Schema. `intake_agent` (Phase 0) produces the PCR row; `literature_strategist_agent` (Phase 1, sole consumer) resolves it and applies monotonic admit-only loosening to four screening gates plus two upstream filters. A new academic-paper reference doc carries the profile definitions, copying (not editing) the field guidance from the deep-research evidence-hierarchy file so deep-research stays byte-identical.

**Tech Stack:** Markdown agent prompts (`*.md`), Python 3 static linter (`scripts/check_*.py`) run with **system `python3`** (no `.venv`), pytest mutation suite (`scripts/test_check_*.py`), GitHub Actions (`.github/workflows/spec-consistency.yml`).

**Spec:** `docs/design/2026-05-29-kong-259-domain-evidence-profiles-spec.md` (PCR-native, reviewed to 0 P0/P1). This plan implements that spec; do not re-derive design decisions — the spec is authoritative.

---

## Anchor verification (done 2026-05-30 — use THESE line numbers, the spec drifted in 4 places)

Every anchor the spec cites was re-grepped against the worktree before this plan was written. Most held; **four drifted and this plan uses the corrected numbers**. The most load-bearing correction is the screening-tree node order (Task 3) — getting it wrong would loosen a *universal* gate and break INVARIANT 5.

| Spec cited | Reality (use this) | Why it matters |
|---|---|---|
| `intake_agent.md:263` plan-mode 3-question intake | plan-mode block is `:74-106`; simplified interview `:74-80` | Task 2 plan-mode exemption |
| `literature_strategist_agent.md:421-423` = relevance node | `:421` is peer-review "Yes" arm; **relevance node is `:427-429`** | Task 3: relevance is UNIVERSAL, must NOT be loosened |
| `literature_strategist_agent.md:425-428` = methodology node | `:423-425` is foundational-works arm; **methodology node is `:430-433`** | Task 3: methodology is UNIVERSAL, must NOT be loosened |
| `literature_strategist_agent.md:550` = "go directly to Phase B" | content is on **`:549`** (off by one) | Task 2/3 reading; cosmetic |

Confirmed accurate (no drift): `intake_agent.md:37-50, :110-204, :204 (Step 11 end), :216 (## Output Format), :221-239 (PCR table), :228 (Discipline), :238 (Style Profile)`; `literature_strategist_agent.md:46-55 (Step 2 DB table), :57-70 (Step 3+4 filters), :413 (## Screening Tree), :417 (peer-review node), :422 (time-range/currency node), :436 (## Quick Assessment), :442 (Journal-ranking item), :468 (## Quality Gates), :479 (>=70% peer-reviewed), :480 (>=50% currency), :551 (## Quality Criteria), :558-559 (mirror prose)`; `literature_strategist_agent.md` contains **no** `source_quality_hierarchy` mention (confirmed — consumer does not read the deep-research file); `source_quality_hierarchy.md:132-143 (## Field-Specific Adjustments, exactly 6 rows)`; `academic-paper/SKILL.md:139 (skip Phase 1), :270 (revision loop 8→5→6)`; `deep-research/SKILL.md:352, :354 (skip literature *search*)`.

**Re-verify before editing.** Each task's Step 1 re-greps its own anchors. Line numbers shift as earlier tasks edit files; never trust a stale number — grep the heading text, not the digit.

---

## File structure

| File | Task | Responsibility |
|---|---|---|
| `academic-paper/references/domain_evidence_profiles.md` | T1 | **New.** Profile definitions: 4-row table, 5 reserved names, copied legacy field guidance, #246 forward-ref, advisory-only statement. The single source of truth the consumer reads. |
| `academic-paper/agents/intake_agent.md` | T2 | **Modify.** Producer: new `### Step 12: Domain Evidence Profile` + new PCR row. |
| `academic-paper/agents/literature_strategist_agent.md` | T3 | **Modify.** Sole consumer: new `### Domain Evidence Profile Resolution` block + 4 gate loosenings + 2 upstream-filter loosenings (all monotonic admit-only). |
| `scripts/check_domain_evidence_profile.py` | T4 | **New.** 7 documentation-surface checks (C1–C7). |
| `scripts/test_check_domain_evidence_profile.py` | T4 | **New.** Mutation suite: 7 negative fixtures must each FAIL + scope-lock positive tests. |
| `.github/workflows/spec-consistency.yml` | T4 | **Modify.** One step wiring the new lint into CI. |
| `scripts/_ci_pytest_manifest.toml` | T4 | **Modify.** One `[[pytest]]` entry so the mutation suite runs in CI. |

**Task numbering vs commit/execution order.** Tasks keep stable numbers by change (T1 = Change C reference doc, T2 = Change B intake producer, T3 = Change E consumer, T4 = test/CI) — every cross-reference in this plan uses those numbers. But the **commit/execution order is T1 → T3 → T2 → T4** (consumer before producer). Implement and commit in that order:

- **T1 first** — new file, zero dependency, safest. Defines the enum/reserved vocabulary the others reference.
- **T3 before T2 (consumer before producer).** The consumer reads the *PCR row format*, which the spec already fixes (the leading effective token) — it needs only the documented row shape, not T2's edit. Ship it first and, while no producer has written a row, it hits an **absent row → neutral fallback + `[NO-PROFILE-NEUTRAL]`** (INVARIANT 4/11): a fully safe, surfaced state. **The reverse order is NOT safe:** if T2 (producer) shipped first, intake would prompt the scholar and write the PCR row, but the un-upgraded consumer would silently ignore it — the scholar picks a profile, gets neutral screening, and **no advisory explains why** (the `[NO-PROFILE-NEUTRAL]` logic lives in T3). That is a silent quality degradation. Consumer-first avoids it.
- **T2 after T3** — producer. Once it writes the row, the already-shipped consumer resolves it immediately. T2's row text must match the shape T3 parses; T4 lints both.
- **T4 last** — lint/test/CI assert over the surface produced by T1/T3/T2.

Each task ends at a green commit, and **every intermediate commit is self-consistent** in the T1→T3→T2 order: after T1 the reference exists (inert, read by nobody yet); after T3 the consumer safely neutral-falls-back on the still-absent row; after T2 producer + consumer are both live. (If all four ship in one atomically-merged PR, the order is cosmetic — but consumer-first keeps each commit independently shippable, per INVARIANT 4.)

---

## Cross-cutting rules every task must honor

These come straight from the spec's INVARIANTS. Re-read them before each task; they are the acceptance bar.

1. **Monotonic admit-only (INVARIANT 5).** A non-neutral profile may only *add* admit paths to the named loosenable gate; it must NEVER exclude, down-rank, or fail any source the neutral gate currently admits. Combine neutral ∪ profile by **OR**, never replacement. The universal gates (relevance / methodology / predatory) are never touched by any profile.
2. **Loosenable vs universal gates (the line that must not blur):**
   - **PROFILE_LOOSENABLE:** peer-review requirement, publication-type, currency window, provenance expectation.
   - **UNIVERSAL (never loosen):** relevance-to-RQ, methodology-not-fatally-flawed, not-predatory/fabricated.
3. **Effective value ∈ exactly 4 enum** (`general_social_science`, `cs_ml`, `humanities_interpretive`, `unknown_user_defined`). The 5 reserved values (`clinical`, `wet_lab`, `materials_physics`, `legal_case_based`, `education`) may appear only as a scholar *request*, never as a stored effective value (INVARIANT 1).
4. **Reserved → fallback + advisory** (INVARIANT 2, 12). Request ∈ reserved ⇒ store `unknown_user_defined`, surface the reserved-fallback advisory, display the request parenthesized (`unknown_user_defined (requested: clinical)`).
5. **No deep-research file is edited** (INVARIANT 9). `source_quality_hierarchy.md` is **read** to copy its guidance into T1's new file; it is never modified. T4 has a guard that FAILS if a profile section leaks into it.
6. **Mirrored-artifact discipline (the R2/R3 catch).** In `literature_strategist_agent.md` the two corpus-ratio gates appear in TWO places that must move together: `## Quality Gates` (`:479-480`) and the prose restatement in `## Quality Criteria` (`:558-559`). Change one without the other and a profile-admitted source passes the gate only to be re-tightened by the mirror. T3 edits BOTH in the same commit. (Plus the upstream Step 3/4 filters at `:57-70` are a third loosen point for the same evidence types — also in T3.)
7. **Advisory-only (INVARIANT 5).** The profile never changes the A-F Overall Grade and never blocks ship. It never touches the Step 2 database table (that stays `Discipline`-driven).
8. **Plan-doc boundary.** This plan and every commit message must contain **zero** traces of internal tooling, author identity, organization names, or private-repo paths. Before each commit, run the local boundary linter over the staged diff (see "Boundary scan" at the end). Commits use `Ref #259` + `[skip-closes-check]`, never `Closes`.

---

## The 4 advisory tags (who emits which)

| Tag | Emitter | When | Task |
|---|---|---|---|
| `[NO-PROFILE-NEUTRAL]` | `literature_strategist_agent` (consumer), full mode | PCR row absent ⇒ neutral fallback, surfaced not silent | T3 |
| `[PROFILE-UNRESOLVED]` | `literature_strategist_agent` (consumer) | row holds a value not in the 4 enum (hallucinated / reserved-as-effective) ⇒ neutral | T3 |
| `[PROFILE-DISCIPLINE-MISMATCH]` | `literature_strategist_agent` (consumer) | profile's implied discipline ≠ PCR `Discipline` ⇒ both signals proceed in own lanes | T3 |
| `[PROFILE-OVERRIDE-NO-RESCREEN]` | `intake_agent` (producer) | override recorded after Phase 1 **already ran OR was explicitly skipped** (corpus frozen) | T2 |

T4 C1 checks the intake-emitted tag; C3 checks the three consumer-emitted tags.

---

### Task 1: New profile reference doc (Change C)

**Files:**
- Create: `academic-paper/references/domain_evidence_profiles.md`
- Read-only reference (DO NOT EDIT): `deep-research/references/source_quality_hierarchy.md:132-143`

- [ ] **Step 1: Re-verify the source table before copying**

Run: `grep -n "## Field-Specific Adjustments" deep-research/references/source_quality_hierarchy.md`
Expected: one hit. Then read the table (currently `:132-143`) and confirm it has **exactly 6 rows**: Medicine/Health, Education, Social Science, Policy, Humanities, Technology, with columns `Field | Gold Standard | Common Level | Notes`.
This file is **read, never written** (INVARIANT 9). You are copying its substance into the new academic-paper file.

- [ ] **Step 2: Write the new reference doc**

Create `academic-paper/references/domain_evidence_profiles.md` with exactly this structure (fill the table cells from the 6-row source table per the mapping below):

````markdown
# Domain Evidence Profiles

> **Advisory only.** A domain evidence profile changes which evidence types the literature screening *admits*. It never changes the A-F Overall Grade and never blocks manuscript ship. It never changes which databases are queried (that stays `Discipline`-driven in `literature_strategist_agent` Step 2). Consumed only by `academic-paper`'s `literature_strategist_agent`; produced by `intake_agent` Step 12 as the PCR `Domain Evidence Profile` row.

## Domain Evidence Profiles

The ship-ready enum is exactly four values. `unknown_user_defined` is the default and the neutral fallback.

| Profile | Standard evidence types | Common provenance requirements | Critical gaps to surface | Reserved-note |
|---|---|---|---|---|
| `general_social_science` | Peer-reviewed empirical studies, mixed-methods, expert-panel / context-dependent policy analyses | Journal or proceedings; expert-panel reports acceptable where context-dependent | Single-context generalization; weak external validity | — (ship-ready) |
| `cs_ml` | Peer-reviewed papers AND archival preprints (e.g. arXiv), conference proceedings; industry technical reports | Preprint server or proceedings acceptable; peer-review lags the field | Non-reproducible results; benchmark cherry-picking | — (ship-ready) |
| `humanities_interpretive` | Primary sources, archival material, canonical/older texts, monographs | Primary-source provenance; recency is not a quality signal | Interpretive over-reach; missing primary-source grounding | — (ship-ready) |
| `unknown_user_defined` | Neutral single-pyramid (pre-#259 behavior) — peer-reviewed default | Standard peer-review expectation | (no profile-specific loosening) | Default / neutral fallback |

**Reserved profiles (documented, NOT in the enum).** Selecting one records effective `unknown_user_defined` and surfaces a reserved-fallback advisory — its checklist does not exist yet, so it falls back to neutral to prevent false rigor:

`clinical` · `wet_lab` · `materials_physics` · `legal_case_based` · `education` — *not in enum yet; selecting this falls back to `unknown_user_defined`.*

## Field-guidance carry-forward (seeded from the deep-research evidence hierarchy)

The substance of the field-centric `## Field-Specific Adjustments` table in `deep-research/references/source_quality_hierarchy.md` is carried forward here so no per-field guidance is silently dropped. The deep-research file is **read, not edited** — this is a one-time authoring copy, not a runtime dual-read.

Normative (folded into a ship-ready profile row above):
- **Social Science** → folded into `general_social_science` (Level III-V; mixed methods common).
- **Technology** → folded into `cs_ml` (Level III + industry reports; peer review lags reality).
- **Humanities** → folded into `humanities_interpretive` (Level VI primary sources; different epistemology — "evidence" means different things).
- **Policy** → folded into `general_social_science` (Level IV-V + VII expert panels; context-dependent, expert opinion valued). There is no dedicated Policy profile.

**Historical reference — non-normative; current behavior for these domains is neutral `unknown_user_defined` until the `clinical` / `education` profile ships:**
- **Medicine/Health** — Level I-II (RCTs, meta-analyses); Level I-III common; evidence-based-medicine tradition. *(maps to reserved `clinical`)*
- **Education** — Level III-IV (quasi-experimental); Level IV-VI common; randomization often impractical. *(maps to reserved `education`)*

These two rows are preserved verbatim for the eventual `clinical` / `education` profiles. They do NOT change runtime behavior today: until those reserved profiles ship, Medicine/Health and Education runs use the neutral `unknown_user_defined` pyramid, exactly as every other unmapped selection does.

## #246 forward reference

Discipline-relative *grade aggregation* (how these evidence expectations roll up into an Overall Grade) is tracked separately in #246 and is **not yet implemented**. Until #246 ships, the A-F Overall Grade lookup in `deep-research/references/source_quality_hierarchy.md` applies unchanged. #259 ships no aggregation logic and no placeholder aggregation code.
````

- [ ] **Step 3: Self-check against the spec's INVARIANTS for this file**

Verify by re-reading your new file:
- 4-row table present; gaps column is literally `Critical gaps to surface` (NOT "disqualifying") — INVARIANT 5.
- 5 reserved names present with the "not in enum" note — INVARIANT 1/2.
- Legacy carry-forward present, labeled non-normative, contains the **Medicine/Health AND Education** verbatim text, and the `general_social_science` row references the folded **Policy** substance — INVARIANT 7.
- Advisory-only statement at top + #246 forward-ref present — INVARIANT 5/8.
- You did **not** touch `source_quality_hierarchy.md` — INVARIANT 9. Run: `git status --short deep-research/` → expect empty output.

- [ ] **Step 4: Boundary scan + commit**

Run the boundary scan (see end of plan) on the staged diff, then:

```bash
git add academic-paper/references/domain_evidence_profiles.md
git commit -m "Add domain evidence profiles reference doc (Change C)  Ref #259 [skip-closes-check]

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 2: Intake produces the PCR row (Change B)

**Files:**
- Modify: `academic-paper/agents/intake_agent.md` (new step after Step 11; new PCR row after Style Profile row)

- [ ] **Step 1: Re-verify the two edit anchors**

Run: `grep -n "### Step 11: Funding Sources\|^## Output Format\|Style Profile" academic-paper/agents/intake_agent.md`
Expected: Step 11 heading (~`:204`), `## Output Format` (~`:216`), and the `| **Style Profile** | [attached / null] |` PCR row (~`:238`). The new step goes **between** Step 11's body and `## Output Format`; the new PCR row goes **immediately after** the Style Profile row inside the PCR fenced table.

- [ ] **Step 2: Insert `### Step 12: Domain Evidence Profile` (after Step 11 body, before `## Output Format`)**

The heading MUST be exactly `### Step 12: Domain Evidence Profile` (T4 C1 + C7 carrier-regression guard scan this exact heading). Insert:

````markdown
### Step 12: Domain Evidence Profile

Reference: `references/domain_evidence_profiles.md`

The domain evidence profile lets the scholar tell `literature_strategist_agent` which discipline's evidence standards to screen by, so it does not apply one Western evidence-based-medicine pyramid to every field. **Advisory only** — it changes which evidence types the literature screening *admits*; it never changes the A-F grade and never blocks ship. **Scholar-confirmed only — nothing auto-activates** (you MAY *suggest* a default inferred from a deep-research handoff or the Step 1 topic interview, but the scholar must confirm).

**Present the 4 ship-ready profiles as an explicit choice:**

> "Which discipline's evidence standards should the literature screening use? This only affects which evidence *types* are admitted, never the grade.
> - `general_social_science` — empirical + mixed-methods + policy/expert-panel evidence
> - `cs_ml` — admits archival preprints (arXiv) and proceedings alongside peer-reviewed papers
> - `humanities_interpretive` — admits primary/archival/canonical sources; recency is not a quality signal
> - `unknown_user_defined` — neutral single-pyramid (default; pick this if unsure)"

`unknown_user_defined` is the **default** if the scholar does not pick or is unsure.

**Reserved profiles** (`clinical`, `wet_lab`, `materials_physics`, `legal_case_based`, `education`): these are documented but NOT in the enum. If the scholar selects one, record effective `unknown_user_defined` **and surface this advisory**: "this domain has no profile yet — falling back to neutral evidence standards (`unknown_user_defined`)." Display the row as `unknown_user_defined (requested: <reserved>)` so the scholar's intent is visibly acknowledged.

**Write the resolved effective value into the PCR `Domain Evidence Profile` row.** This is the single authoritative home — there is no Material Passport copy, no `selections[]` ledger, and no Schema number. (The profile is a PCR field, mirroring `Style Profile`.)

**Profile-value rules (prose validation — there is NO JSON Schema file):**
- The scholar's *request* MUST be one of the 4 ship-ready values OR one of the 5 reserved values — nothing else.
- The stored **effective** value MUST be one of the 4 ship-ready enum values.
- **Request/effective coherence:** if the request is ship-ready, the stored effective value MUST equal it. If the request is reserved, the stored effective value MUST be `unknown_user_defined` and you MUST surface the reserved-fallback advisory. No other combination is valid (you may never silently store, e.g., a `general_social_science` request as an effective `cs_ml`).

**Phase-1-fully-skipped carve-out (no placebo prompt) — narrow, explicit trigger only.** The profile's only consumer is `literature_strategist_agent` (Phase 1). The carve-out applies **only when `literature_strategist_agent` will not run at all** — i.e. the scholar explicitly skips the literature phase entirely (`academic-paper/SKILL.md:139` "User can skip Phase 1 if providing own sources"), e.g. a mid-entry start with a finished draft where no literature screening will occur. On that explicit signal, do NOT prompt; record `unknown_user_defined` + a one-line `[NO-PROFILE-NEUTRAL]` advisory ("this run skips literature screening entirely, so a domain evidence profile would have no consumer; to apply one, run Phase 1").
**Critical distinction:** a `deep-research → academic-paper` handoff carrying a bibliography does **NOT** trigger this carve-out — that handoff still runs `literature_strategist_agent`, which "goes directly to Phase B (full-text assessment), skipping Phase A" search, so the profile DOES have a live consumer. In that case **prompt Step 12 normally**.
**Default when ambiguous: prompt Step 12** (assume the consumer runs) — under-prompting silently drops a usable profile, which is worse than one extra question.

**Mid-pipeline override.** If the scholar later changes the profile (a fresh `academic-paper` invocation that re-runs intake, or an in-session correction), overwrite the PCR row. An override recorded **before Phase 1 runs** is consumed normally. An override recorded when **Phase 1 has already run OR was explicitly skipped** (the corpus is already fixed) cannot retroactively re-screen it, so you MUST emit a one-line `[PROFILE-OVERRIDE-NO-RESCREEN]` advisory: "the literature corpus is already fixed (already screened, or this run skips literature screening); to apply this profile, run Phase 1." The override is still honored for any future Phase-1 run.

**Not folded into Step 10 Style Calibration** — Step 10 is writing-sample calibration the scholar frequently declines; the domain profile is a separate concern with a separate lifecycle.
````

- [ ] **Step 3: Add the PCR output row (immediately after the Style Profile row)**

In the `## Paper Configuration Record` fenced table, after `| **Style Profile** | [attached / null] |`, add:

```markdown
| **Domain Evidence Profile** | [effective_value, or `unknown_user_defined (requested: <reserved>)` for a reserved fallback, or absent if Step 12 not run] |
```

- [ ] **Step 4: Mark plan mode exempt**

Confirm the plan-mode simplified intake (`:74-106`, the `## Paper Configuration Record (Plan Mode)` block and `### Plan Mode Simplified Interview` `:74-80`) does NOT run Step 12 and does NOT add the row. If there is a plan-mode step list, add no Step 12 there. Add one sentence in the Step 12 body if not already implied: "**plan mode is exempt:** the simplified plan-mode intake does not run Step 12; a plan-mode run leaves no profile row, and `literature_strategist_agent` (if reached) takes the neutral fallback."

- [ ] **Step 5: Self-check against INVARIANTS for this file**

Re-read the inserted text and confirm: exact heading `### Step 12: Domain Evidence Profile` present; 4 enum + 5 reserved listed; reserved-fallback advisory + display form `(requested: <reserved>)` present; request/effective coherence rule present; Phase-1-fully-skipped carve-out present with BOTH the "explicit skip" trigger AND the "deep-research handoff does NOT trigger" distinction; `[PROFILE-OVERRIDE-NO-RESCREEN]` present with the "already run **OR** was skipped" condition (both halves — T4 C1 requires both); new PCR row present after Style Profile. The text never mentions Material Passport / Schema 13 / `selections[]` as the carrier (only the PCR).

- [ ] **Step 6: Boundary scan + commit**

```bash
git add academic-paper/agents/intake_agent.md
git commit -m "Intake produces Domain Evidence Profile PCR row (Change B)  Ref #259 [skip-closes-check]

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 3: literature_strategist consumes the PCR row (Change E)

**Files:**
- Modify: `academic-paper/agents/literature_strategist_agent.md` (new resolution block + 4 gate edits + 2 upstream-filter edits)

**This is the highest-risk task — it is where the monotonic admit-only contract lives, and where the anchor drift bites.** The screening-tree node order is: peer-review (`:417`, loosenable) → time-range/currency (`:422`, loosenable) → **relevance (`:427-429`, UNIVERSAL — do not touch)** → **methodology (`:430-433`, UNIVERSAL — do not touch)**. Loosen only the peer-review and currency nodes; leave relevance and methodology byte-identical.

- [ ] **Step 1: Re-verify ALL six edit anchors by heading text**

Run:
```bash
grep -n "### Domain Evidence Profile Resolution\|### Literature Screening Decision Tree\|### Literature Quality Quick Assessment Checklist\|^## Quality Gates\|^## Quality Criteria\|### Step 3: Search String Construction\|Is it peer-reviewed?\|Does the abstract directly address\|Is the methodology reliable" academic-paper/agents/literature_strategist_agent.md
```
Expected: screening tree (`:413`), peer-review node (`:417`), relevance node (`:427`), methodology node (`:430`), quick-assessment (`:436`), Quality Gates (`:468`), Quality Criteria (`:551`), Step 3 (`:57`). There is no existing `### Domain Evidence Profile Resolution` heading yet (you create it). Also confirm `grep -c source_quality_hierarchy academic-paper/agents/literature_strategist_agent.md` returns `0` (consumer must not read the deep-research file).

- [ ] **Step 2: Add the `### Domain Evidence Profile Resolution` block**

Place it **immediately before `### Step 2: Database Selection`** (so resolution happens before screening, and the next same-level heading bounding the block is deterministically `### Step 2` — this keeps C3/C7's `_heading_range` range stable and reviewable). Heading MUST be exactly `### Domain Evidence Profile Resolution` (T4 C3 + C7 scan this exact heading). Insert:

````markdown
### Domain Evidence Profile Resolution

Reference: `academic-paper/references/domain_evidence_profiles.md`

**Resolve `domain_evidence_profile` from the PCR `Domain Evidence Profile` row** (NOT the Material Passport, NOT a ledger, NOT a Schema number). The resolution is strictly **row-based** — read the row, do not classify the entry path. `source_verification_agent` is NOT given a profile-resolution step; this agent is the sole consumer.

Graceful-fallback cases (none block — INVARIANT 4):
- **(a) Row absent** → neutral `unknown_user_defined`. **In `full` mode, emit `[NO-PROFILE-NEUTRAL]`** so the neutral default is visible. (Paths that leave the row absent: `plan → full` and true mid-entry, where intake never set it. Resume-from-checkpoint carries whatever the prior intake wrote — present ⇒ that profile applies with no advisory; absent ⇒ neutral + advisory. A `deep-research → academic-paper` handoff is NOT absent — intake set the row.)
- **(b) Row = `unknown_user_defined`** → neutral. **No `[NO-PROFILE-NEUTRAL]`** — the scholar actively chose/accepted neutral at intake; that tag is only for the absent-row case.
- **(c) Row holds a value not in the 4 enum** (hallucinated, or a reserved value somehow stored as effective) → neutral, **and emit `[PROFILE-UNRESOLVED]`**.
- **(d) Discipline mismatch** (the profile's implied discipline ≠ PCR `Discipline`) → proceed with BOTH signals in their own lanes, **emit `[PROFILE-DISCIPLINE-MISMATCH]`**. This is a warning, not a fallback — admissibility still uses the profile; `Discipline` still drives database selection. Nothing is blocked.

**Profile → implied-discipline map** (so "implies a discipline" is deterministic, a string-category comparison — not inference):

| Profile | Implied discipline(s) |
|---|---|
| `cs_ml` | CS / Engineering / Technology |
| `humanities_interpretive` | Humanities |
| `general_social_science` | Social Science **or** Policy (matches either) |
| `unknown_user_defined` | none — neutral default never triggers a mismatch check |

The mismatch advisory fires only when PCR `Discipline` falls **outside** the profile's implied set. `unknown_user_defined` and an absent row never warn.

**There is no `HANDOFF_INCOMPLETE` concern** — the profile is a PCR field, not a handoff object, so the general handoff-validation convention never applies. A profile defect simply falls back to neutral with the advisory.

**Monotonic admit-only resolution (the load-bearing contract — INVARIANT 5).** Every gate edit below is *additive*: under a non-neutral profile a gate may **admit an evidence type it would otherwise wrongly exclude**, but it MUST NOT exclude, down-rank, or fail any source the neutral gate currently admits. Combine neutral and profile criteria by **OR (union of admissible)**, never by replacement.

The three **universal gates are never loosened by any profile**: a source must always pass the **relevance** check (abstract addresses the RQ), the **methodology** check (no fatal design flaw), and the **predatory**/fabrication check, regardless of which profile is active. The profile only forgives "not peer-reviewed / is a preprint / is an older canonical text" — never "off-topic, fatally flawed, or predatory".

```
profile = resolve_from_PCR_row()    # 4 enum values; absent/non-enum -> unknown_user_defined (+advisory on non-enum)

# Universal gates apply to EVERY source regardless of profile — the profile can never bypass them:
UNIVERSAL_GATES        = [relevance_to_RQ, methodology_not_fatally_flawed, not_predatory_or_fabricated]
# Only these may be loosened by a non-neutral profile:
PROFILE_LOOSENABLE     = [peer_review_requirement, publication_type, currency_window, provenance_expectation]

def admit(source):
    if not all(g(source) for g in UNIVERSAL_GATES):
        return False                                  # profile NEVER bypasses relevance / methodology / predatory
    if neutral_passes(source, PROFILE_LOOSENABLE):
        return True                                   # never tighten: anything neutral admits stays admitted
    if profile != unknown_user_defined and profile_admits(source, profile, PROFILE_LOOSENABLE):
        return True                                   # only loosen: profile ADDs admit paths on loosenable gates only
    return False
# Under unknown_user_defined, admit() == the full neutral tree exactly.
# A cs_ml preprint that is off-topic, fatally flawed, or predatory is STILL excluded.
```
````

- [ ] **Step 3: Loosen sub-edit 1 — Screening Decision Tree (peer-review node `:417` ONLY)**

In `### Literature Screening Decision Tree` (`:413`), at the **`Is it peer-reviewed?`** node (`:417`), add a profile-aware admit path so the profile's standard evidence types are *additionally* admissible. Edit the `No` arm to add (do not replace the existing gray-literature arm):

```
├── Is it peer-reviewed?
│   ├── No -> Is it gray literature (government report/white paper) and directly relevant to RQ?
│   │   ├── Yes -> Include (tag as gray literature)
│   │   └── No -> Is it admissible under the active domain evidence profile?
│   │       (cs_ml: archival preprint / proceedings; humanities_interpretive: primary / archival / canonical source)
│   │       ├── Yes -> tag by evidence type, then CONTINUE to the relevance + methodology nodes below
│   │       │          (profile admit path, loosen-only — it does NOT short-circuit to Include)
│   │       └── No -> Exclude
│   └── Yes ->
```

**Critical control-flow fix (do not write `Yes -> Include` here).** In a decision tree an `Include` leaf is *terminal* — it halts traversal and bypasses every downstream node. The existing gray-literature arm uses `Include` and thereby intentionally short-circuits, but a profile-admitted source MUST NOT: it has to still pass the universal relevance (`:427-429`) and methodology (`:430-433`) nodes (INVARIANT 5 — the profile only forgives "not peer-reviewed", never "off-topic / fatally flawed"). So the profile arm routes to **"tag by evidence type, then CONTINUE to the relevance + methodology nodes"**, NOT to `Include`. This deliberately makes the profile arm *stricter* than the gray-literature arm, which is correct per spec ("a profile-admitted preprint must still pass them").

**Do NOT touch the relevance node (`:427-429`) or the methodology node (`:430-433`).** Add one sentence after the tree: "A profile-admitted source is added at the peer-review node only and then continues through the unchanged relevance and methodology nodes; the profile never bypasses a universal-quality node and never short-circuits to Include."

- [ ] **Step 4: Loosen sub-edit 2 — Quick Assessment Checklist (Journal-ranking item `:442` ONLY)**

In `### Literature Quality Quick Assessment Checklist` (`:436`), the 5-item score penalizes preprints/archival via the **Journal-ranking** item (`:442`). Add prose after the table: "Under a non-neutral domain evidence profile, a source passes the quick assessment if it meets the neutral total-score outcome **OR** meets the profile's evidence-type expectation on the **Journal-ranking item only** (union scoped to the publication-type axis, not replacement). The other four items — methodological rigor, relevance to RQ, citation count, data/evidence quality — are universal-quality and stay in force: a profile-admitted source must still clear them."

- [ ] **Step 5: Loosen sub-edit 3 — Quality Gates two ratio rows (`:479-480`)**

In `## Quality Gates` (`:468`) Pass Criteria table, make the `Peer-reviewed ratio >= 70%` (`:479`) and `Currency >= 50% last 5 years` (`:480`) rows profile-relative **in the loosening direction only**. Add prose after the table: "Under a non-neutral domain evidence profile these two corpus-ratio gates loosen (never tighten): preprints count toward the `cs_ml` peer-reviewed-equivalent ratio; canonical/older texts do not count against `humanities_interpretive` currency. The thresholds are never raised, and a corpus that passes the neutral gate always passes the profile-relative gate. The other gate rows (source count, annotation completeness, matrix coverage, research-gap count) are not evidence-type gates and are untouched."

- [ ] **Step 6: Loosen sub-edit 4 — Quality Criteria MIRROR (`:558-559`) — SAME COMMIT as Step 5**

This is the mirrored-artifact catch (cross-cutting rule 6). In `## Quality Criteria` (`:551`) the two ratios are restated in prose at `:558-559`:
```
- Source quality distribution: majority should be peer-reviewed
- Recency: >50% of sources from last 5 years (unless historical topic)
```
Apply the **identical** loosening so a profile-admitted source is not re-tightened by this mirror. Append to those two bullets (or add a note directly under them): "Under a non-neutral domain evidence profile, 'majority peer-reviewed' counts the profile's peer-reviewed-equivalent types (e.g. `cs_ml` preprints), and the recency criterion does not penalize the profile's canonical/older sources — the same union/loosen-only rule as the Quality Gates rows above. Changing one without the other reintroduces the contradiction the gate fix removes."

- [ ] **Step 7: Loosen the upstream filters — Step 3/4 (`:57-70`)**

In `### Step 3: Search String Construction` (`:57`, the `Filters: peer-reviewed, [year range]` line `:61`) and the Step 4 inclusion/exclusion table (`:64-70`, the publication-type include/exclude rows), add the same loosen-only treatment: "Under a non-neutral domain evidence profile, the profile's standard evidence types are added to the includable set before screening — the peer-reviewed filter relaxes to peer-reviewed-equivalent for `cs_ml`; the year-range relaxes for `humanities_interpretive` canonical texts. Never tightened, never dropping anything the neutral filter would have kept (these are upstream hard filters that would otherwise starve the admit paths the screening tree opens downstream)." Also note search-string enrichment is optional/additive and does NOT change the Step 2 `Discipline`-driven database table.

- [ ] **Step 8: Self-check the monotonic + mirror + universal-gate invariants**

Re-read the whole agent file and confirm:
- The resolution block names the PCR row as carrier, lists cases (a)/(b)/(c)/(d), the three consumer tags, the implied-discipline map, and the universal-vs-loosenable distinction — INVARIANT 4/5/10/11.
- Sub-edits 1–4 + upstream filters all say "loosen / union / never tighten"; **none** edits the relevance node (`:427-429`) or methodology node (`:430-433`) — INVARIANT 5. Run `git diff academic-paper/agents/literature_strategist_agent.md` and eyeball that the relevance/methodology tree lines are unchanged.
- Quality Gates (`:479-480`) AND Quality Criteria mirror (`:558-559`) BOTH changed — cross-cutting rule 6.
- The Step 2 database table (`:46-55`) is byte-unchanged — INVARIANT 5/10 (advisory never touches DB selection).

- [ ] **Step 9: Boundary scan + commit (Steps 2–7 in ONE commit so the mirror moves together)**

```bash
git add academic-paper/agents/literature_strategist_agent.md
git commit -m "literature_strategist consumes Domain Evidence Profile, loosen-only gates (Change E)  Ref #259 [skip-closes-check]

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 4: Lint + mutation suite + CI wiring (test/CI)

**Files:**
- Create: `scripts/check_domain_evidence_profile.py`
- Create: `scripts/test_check_domain_evidence_profile.py`
- Modify: `.github/workflows/spec-consistency.yml` (add the lint step)
- Modify: `scripts/_ci_pytest_manifest.toml` (add the mutation-suite `[[pytest]]` entry so it runs in CI)

The linter is **honest about its reach**: it verifies *documentation surface* (presence/shape of required text), NOT runtime semantics. Runtime semantics are covered by the worked examples (next section) at plan-stage review, not by this lint.

- [ ] **Step 1: Write the failing test first (TDD) — test asserts the lint exists and passes on the real repo**

Create `scripts/test_check_domain_evidence_profile.py` starting with the integration positive test (it will fail until the lint script exists):

```python
"""Mutation suite for check_domain_evidence_profile.py (#259).

Per the iron law: positive + negative tests for every check. Each negative
fixture mutates ONE artifact so exactly one check (C1-C7) fails, proving the
linter cannot trivially accept-all. Fixtures use cwd-swap (REPO_ROOT = Path.cwd()).
"""
from __future__ import annotations

import shutil
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
LINT = REPO_ROOT / "scripts" / "check_domain_evidence_profile.py"

# The four files the lint reads.
INTAKE = "academic-paper/agents/intake_agent.md"
PROFILES = "academic-paper/references/domain_evidence_profiles.md"
CONSUMER = "academic-paper/agents/literature_strategist_agent.md"
SQH = "deep-research/references/source_quality_hierarchy.md"


def run_lint(cwd: Path) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, str(LINT)], cwd=str(cwd),
        capture_output=True, text=True,
    )


def test_integration_passes_against_real_repo():
    """The lint passes against the actual repo after Tasks 1-3 land."""
    result = run_lint(REPO_ROOT)
    assert result.returncode == 0, result.stderr
```

Run: `python3 -m pytest scripts/test_check_domain_evidence_profile.py::test_integration_passes_against_real_repo -v`
Expected: FAIL (lint script does not exist yet — `FileNotFoundError` / non-zero).

- [ ] **Step 2: Write `scripts/check_domain_evidence_profile.py` with checks C1–C7**

Mirror the structure of `scripts/check_corpus_consumer_protocol.py`: `REPO_ROOT = Path.cwd()`, each check returns `list[str]`, a `CHECKS` list of `(name, fn)`, `main()` aggregates and exits 0/1. Create:

```python
#!/usr/bin/env python3
"""Lint domain evidence profile documentation surface (#259).

Seven documentation-surface checks C1-C7. Honest about reach: verifies presence/
shape of required text, NOT runtime semantics (those rely on worked examples +
plan-stage review per the spec Test strategy). Exit 0 pass / 1 fail.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path
from typing import Callable

# Path.cwd() (not __file__) so fixture tests can subprocess.run(cwd=fixture_repo).
REPO_ROOT = Path.cwd()
INTAKE = REPO_ROOT / "academic-paper" / "agents" / "intake_agent.md"
PROFILES = REPO_ROOT / "academic-paper" / "references" / "domain_evidence_profiles.md"
CONSUMER = REPO_ROOT / "academic-paper" / "agents" / "literature_strategist_agent.md"
SQH = REPO_ROOT / "deep-research" / "references" / "source_quality_hierarchy.md"

SHIP_ENUM = ("general_social_science", "cs_ml", "humanities_interpretive", "unknown_user_defined")
RESERVED = ("clinical", "wet_lab", "materials_physics", "legal_case_based", "education")

INTAKE_STEP12_HEADING = "### Step 12: Domain Evidence Profile"
CONSUMER_RESOLUTION_HEADING = "### Domain Evidence Profile Resolution"


def _read(p: Path) -> str:
    return p.read_text(encoding="utf-8") if p.exists() else ""


def _heading_range(text: str, heading: str) -> str | None:
    """Byte range from `heading` to the next same-or-higher-level ATX heading
    (or EOF), IGNORING `#`-prefixed lines inside fenced code blocks.

    Determines the heading level by counting leading '#'. The block this guards
    contains fenced pseudocode whose comment lines start with `# ` at column 0;
    a naive `^#{1,level} ` scan would treat that comment as the next heading and
    truncate the range at the first pseudocode comment (so C3 would miss the
    universal-gate keywords / forbidden-carrier tokens that follow). We track
    fence state line-by-line and only accept a heading match OUTSIDE a fence.
    Scans only this range so C7 does not false-fail on historical-contrast prose
    elsewhere in the file.
    """
    idx = text.find(heading)
    if idx == -1:
        return None
    level = len(heading) - len(heading.lstrip("#"))
    rest = text[idx + len(heading):]
    lines = rest.splitlines(keepends=True)
    offset = 0
    in_fence = False
    heading_re = re.compile(rf"^#{{1,{level}}} ")
    for ln in lines:
        stripped = ln.lstrip()
        if stripped.startswith("```") or stripped.startswith("~~~"):
            in_fence = not in_fence
            offset += len(ln)
            continue
        if not in_fence and heading_re.match(ln):
            return text[idx: idx + len(heading) + offset]
        offset += len(ln)
    return text[idx: idx + len(heading) + len(rest)]


def _strip_fences(text: str) -> str:
    """Return `text` with all fenced code blocks (``` or ~~~) removed.

    Used by checks that must anchor a requirement in PROSE, not in a pseudocode
    identifier. e.g. C3's universal-gate keywords (relevance/methodology/
    predatory) must appear in the prose sentence, not merely inside the
    `UNIVERSAL_GATES = [relevance_to_RQ, ...]` pseudocode line — otherwise
    deleting the prose while leaving the code would falsely pass.
    """
    out, in_fence = [], False
    for ln in text.splitlines(keepends=True):
        s = ln.lstrip()
        if s.startswith("```") or s.startswith("~~~"):
            in_fence = not in_fence
            continue
        if not in_fence:
            out.append(ln)
    return "".join(out)


def check_c1() -> list[str]:
    """intake_agent: enum + reserved + PCR row + coherence + reserved-fallback +
    display form + Step 12 heading + carve-out + override tag (both halves)."""
    f: list[str] = []
    t = _read(INTAKE)
    if not t:
        return ["C1: intake_agent.md not found"]
    if INTAKE_STEP12_HEADING not in t:
        f.append(f"C1: missing exact heading '{INTAKE_STEP12_HEADING}'")
    for v in SHIP_ENUM:
        if v not in t:
            f.append(f"C1: intake missing enum value '{v}'")
    for v in RESERVED:
        if v not in t:
            f.append(f"C1: intake missing reserved value '{v}'")
    if "Domain Evidence Profile" not in t or "| **Domain Evidence Profile** |" not in t:
        f.append("C1: intake missing PCR 'Domain Evidence Profile' row")
    if "(requested:" not in t:
        f.append("C1: intake missing reserved-fallback display form '(requested: <reserved>)'")
    if "[PROFILE-OVERRIDE-NO-RESCREEN]" not in t:
        f.append("C1: intake missing [PROFILE-OVERRIDE-NO-RESCREEN] advisory")
    # Both halves of the override condition: already-run AND was-skipped.
    if not (re.search(r"already run", t) and re.search(r"was (explicitly )?skipped|skipped entirely", t)):
        f.append("C1: override condition missing 'already run OR was skipped' (both halves required)")
    if "Phase-1-fully-skipped carve-out" not in t and "skips literature screening" not in t:
        f.append("C1: intake missing Phase-1-fully-skipped carve-out")
    return f


def check_c2() -> list[str]:
    """profiles doc: exists, gaps column wording, reserved list, and a
    CLOSED-SET 4-profile table (exactly the 4 SHIP_ENUM rows — no 5th effective
    profile, no reserved value smuggled in as an effective row)."""
    f: list[str] = []
    t = _read(PROFILES)
    if not t:
        return ["C2: domain_evidence_profiles.md not found"]
    if "## Domain Evidence Profiles" not in t:
        f.append("C2: missing '## Domain Evidence Profiles' section")
    if "Critical gaps to surface" not in t:
        f.append("C2: gaps column must be 'Critical gaps to surface', not 'disqualifying'")
    if "disqualifying" in t.lower():
        f.append("C2: forbidden word 'disqualifying' present (profile is advisory)")
    for v in RESERVED:
        if v not in t:
            f.append(f"C2: profiles doc missing reserved value '{v}'")
    if "not in enum" not in t:
        f.append("C2: profiles doc missing 'not in enum' reserved note")

    # Closed-set table enforcement (hardening from review rounds). Parse the
    # `## Domain Evidence Profiles` section's table and check EVERY data row's
    # first cell — not just the ones that happen to be backticked tokens. The
    # earlier "only record backticked first cells" version had a false-pass: a
    # 5th effective row written WITHOUT backticks (`| clinical | ... |`) was
    # silently skipped, leaving got == SHIP_ENUM. Now every pipe data row counts,
    # and a first cell that is not exactly one of the four backticked SHIP_ENUM
    # values FAILS. The set must equal exactly the 4 SHIP_ENUM values, with no
    # duplicates.
    sec = _heading_range(t, "## Domain Evidence Profiles")
    if sec is None:
        f.append("C2: '## Domain Evidence Profiles' section not found for table parse")
        return f
    valid_first = {f"`{v}`" for v in SHIP_ENUM}
    row_tokens: list[str] = []
    for line in sec.splitlines():
        ln = line.strip()
        if not ln.startswith("|"):
            continue
        cells = [c.strip() for c in ln.strip("|").split("|")]
        first = cells[0] if cells else ""
        # Skip the header row and the |---|---| separator row.
        if first in ("Profile", "") or set(first) <= set("-: "):
            continue
        # Every remaining data row's first cell MUST be a backticked SHIP_ENUM.
        if first not in valid_first:
            f.append(
                f"C2: profile table data row has an invalid first cell {first!r} "
                f"(must be exactly one of {sorted(valid_first)} — no 5th effective "
                f"profile, no un-backticked or reserved value smuggled in)"
            )
            continue
        row_tokens.append(first.strip("`"))
    got = set(row_tokens)
    want = set(SHIP_ENUM)
    if got != want:
        f.append(
            f"C2: profile table is not the closed 4-row SHIP_ENUM set "
            f"(extra={sorted(got - want)}, missing={sorted(want - got)})"
        )
    if len(row_tokens) != len(set(row_tokens)):
        f.append(f"C2: profile table has duplicate profile rows: {row_tokens}")
    return f


def check_c3() -> list[str]:
    """consumer: resolution block, PCR-row resolve, 3 fallback cases, 3 consumer
    tags, universal-gate carve-out language; source_verification NOT a consumer."""
    f: list[str] = []
    t = _read(CONSUMER)
    if not t:
        return ["C3: literature_strategist_agent.md not found"]
    block = _heading_range(t, CONSUMER_RESOLUTION_HEADING)
    if block is None:
        return [f"C3: missing exact heading '{CONSUMER_RESOLUTION_HEADING}'"]
    # Backtick-strip before substring match: the prose writes the field name
    # backticked (`PCR \`Domain Evidence Profile\` row`), so the contiguous
    # substring "Domain Evidence Profile row" only exists after stripping.
    block_nb = block.replace("`", "")
    if "PCR" not in block_nb or "Domain Evidence Profile row" not in block_nb:
        f.append("C3: resolution block must resolve from the PCR 'Domain Evidence Profile row'")
    for tag in ("[NO-PROFILE-NEUTRAL]", "[PROFILE-UNRESOLVED]", "[PROFILE-DISCIPLINE-MISMATCH]"):
        if tag not in block:
            f.append(f"C3: resolution block missing consumer tag '{tag}'")
    # graceful-fallback cases
    for kw in ("absent", "unknown_user_defined", "not in the 4 enum"):
        if kw not in block:
            f.append(f"C3: resolution block missing fallback keyword '{kw}'")
    # Universal-gate carve-out language must be in PROSE, not only the pseudocode.
    # Strip fenced code first: otherwise the `UNIVERSAL_GATES = [relevance_to_RQ,
    # methodology_not_fatally_flawed, not_predatory_or_fabricated]` identifiers
    # would satisfy the check even if the prose sentence naming the three gates
    # were deleted — which would silently weaken the documented INVARIANT 5
    # contract. (hardening from a review round.)
    block_prose = _strip_fences(block)
    for kw in ("relevance", "methodology", "predatory"):
        if kw not in block_prose:
            f.append(f"C3: resolution PROSE (outside code fences) missing universal-gate keyword '{kw}'")
    # source_verification must NOT be given a profile step in this consumer file
    if "source_verification_agent is NOT" not in t.replace("`", ""):
        f.append("C3: consumer must state source_verification_agent is NOT a profile consumer")
    return f


def check_c4() -> list[str]:
    """profiles doc: advisory-only statement + #246 forward-ref."""
    f: list[str] = []
    t = _read(PROFILES)
    if "Advisory only" not in t:
        f.append("C4: profiles doc missing advisory-only statement")
    if "#246" not in t:
        f.append("C4: profiles doc missing #246 forward-reference note")
    return f


def check_c5() -> list[str]:
    """profiles doc: legacy guidance present, non-normative label, Medicine/Health
    + Education verbatim, Policy fold reference.

    Asserts the *content* of each legacy row, not the bare label — "Education"
    and "Policy" also appear in the reserved list / fold notes, so a bare-token
    check would false-pass even if the legacy row itself were deleted. Each
    assertion below binds a label to a distinctive phrase from its verbatim
    carry-forward, so deleting the row actually fails the check.
    """
    f: list[str] = []
    t = _read(PROFILES)
    if "non-normative" not in t.lower():
        f.append("C5: legacy carry-forward must be labeled non-normative")
    # Medicine/Health legacy row — distinctive phrase from the verbatim text.
    if "Medicine/Health" not in t or "evidence-based-medicine" not in t.lower():
        f.append("C5: missing preserved Medicine/Health legacy row (verbatim 'evidence-based-medicine' text)")
    # Education legacy row — distinctive phrase, NOT the bare reserved token.
    if "quasi-experimental" not in t.lower():
        f.append("C5: missing preserved Education legacy row (verbatim 'quasi-experimental' text)")
    # Policy fold — must bind "Policy" to the fold ON THE SAME LINE. The phrase
    # "folded into general_social_science" appears for BOTH Social Science and
    # Policy, so checking the bare phrase would still pass if only the Policy row
    # were deleted (Social Science's identical phrase survives). Require a single
    # line containing both "Policy" and the fold target. (hardening from a review round.)
    policy_fold = re.compile(
        r"Policy.*folded into\s*`?general_social_science`?", re.IGNORECASE
    )
    if not any(policy_fold.search(line) for line in t.splitlines()):
        f.append("C5: missing Policy→general_social_science fold (a single line binding 'Policy' to 'folded into general_social_science')")
    return f


def check_c6() -> list[str]:
    """R-5 leak guard: source_quality_hierarchy.md NOT modified by #259.

    INVARIANT 9 requires the deep-research file to stay substance-identical. A
    no-leaked-heading + heading-present check is too weak — editing the 6 table
    rows would pass. So we pin the `## Field-Specific Adjustments` block by
    SHA-256 against a baseline captured at plan time (the block is read-only for
    #259). If a legitimate, unrelated change to that block ever lands, the
    implementer updates EXPECTED_FSA_SHA256 in the same commit — making any edit
    a conscious, reviewed act rather than a silent #259 leak. The digest below is
    pinned to the current repo state; since #259 does not touch this file, a clean
    implementation matches it as-is (no implementer action needed unless the
    deep-research table legitimately changes for an unrelated reason).
    """
    import hashlib
    f: list[str] = []
    t = _read(SQH)
    if not t:
        return ["C6: source_quality_hierarchy.md not found"]
    if "## Domain Evidence Profiles" in t:
        f.append("C6: '## Domain Evidence Profiles' leaked into source_quality_hierarchy.md (R-5 violation)")
    block = _heading_range(t, "## Field-Specific Adjustments")
    if block is None:
        f.append("C6: source_quality_hierarchy.md '## Field-Specific Adjustments' block missing (was it edited?)")
        return f
    # Normalize trailing whitespace per line so a stray editor newline does not
    # false-fail, but any substantive row/cell change does.
    norm = "\n".join(ln.rstrip() for ln in block.strip().splitlines())
    digest = hashlib.sha256(norm.encode("utf-8")).hexdigest()
    # Pinned digest of the normalized Field-Specific Adjustments block as it
    # stands at plan time (#259 does NOT touch this file — INVARIANT 9 — so this
    # value is stable for a clean implementation). If a future, unrelated change
    # to deep-research's table is ever intentional, the implementer recomputes
    # and updates this constant IN THE SAME COMMIT — making the edit a conscious,
    # reviewed act rather than a silent #259 leak. Recompute with the same
    # _heading_range + per-line rstrip normalization used above.
    EXPECTED_FSA_SHA256 = "f7b38d39c5252c2d1ec931e563f32e40fce86a65d39fde5c590aa484b9686906"
    if digest != EXPECTED_FSA_SHA256:
        f.append(
            f"C6: Field-Specific Adjustments block changed (R-5 violation): "
            f"got {digest}, expected {EXPECTED_FSA_SHA256}. #259 must not edit "
            f"deep-research; if this change is intentional and unrelated, update "
            f"the pin in the same commit."
        )
    return f


def check_c7() -> list[str]:
    """Carrier-regression guard: within the Step 12 / Resolution heading ranges,
    the profile must NOT be carried by Schema 13 / selections[] / Material Passport.

    Per-OCCURRENCE negation filter (not per-line): the spec-compliant prose
    deliberately writes "NOT the Material Passport", "no selections[] ledger",
    "not a Schema number" to assert the carrier choice. A bare token scan would
    false-fail on that. But a per-LINE "any negation word anywhere" filter has a
    false-NEGATIVE hole: a real regression line like
    "Store on the Material Passport, do not use the PCR" contains both the
    affirmative carrier AND a (distant) negation, so a line-level filter would
    wrongly let it through. We instead require the negation to be CLOSE BEFORE the
    forbidden token (within ~30 chars, i.e. negating THAT carrier). An occurrence
    with no immediately-preceding negation trips the guard. So "NOT the Material
    Passport" passes (negation hugs the token) while "Store on the Material
    Passport, do not use the PCR" still fails (the negation is after, negating the
    PCR, not the carrier). Mutation fixture (g) inserts an affirmative line and
    must fail; the negation prose stays clean. Scoped to heading ranges so
    historical-contrast prose elsewhere in the file never reaches here.
    """
    f: list[str] = []
    forbidden = ("Schema 13", "selections[]", "Material Passport")
    # Negation immediately before the carrier token (<=30 chars). The window must
    # tolerate Markdown punctuation that legitimately sits between the negation
    # word and the (often backticked) carrier — e.g. "no `selections[]` ledger"
    # has a backtick between "no" and the token. Include backtick / asterisk /
    # parens so clean Markdown prose is not false-failed.
    #
    # "not only" / "not just" are AFFIRMATIVE, not negating: "Store not only on
    # the Material Passport but also in the PCR" affirms the carrier. The
    # negative lookahead `(?!\s+only|\s+just)` after the negation word rejects
    # those, so such a line is NOT exempted and still trips the guard. (hardening
    # from a review round.)
    neg_before = re.compile(
        r"\b(?:not(?!\s+only|\s+just)|no|never|n't)\b[\s\w,'\-`*()]{0,30}$",
        re.IGNORECASE,
    )
    for path, heading in ((INTAKE, INTAKE_STEP12_HEADING), (CONSUMER, CONSUMER_RESOLUTION_HEADING)):
        t = _read(path)
        block = _heading_range(t, heading)
        if block is None:
            f.append(f"C7: required heading '{heading}' not found in {path.name}")
            continue
        for line in block.splitlines():
            for token in forbidden:
                for m in re.finditer(re.escape(token), line):
                    pre = line[:m.start()]
                    if neg_before.search(pre):
                        continue  # this occurrence is explicitly negated -> allowed
                    f.append(
                        f"C7: affirmative forbidden-carrier '{token}' inside "
                        f"'{heading}' block ({path.name}): {line.strip()[:80]!r}"
                    )
    return f


CHECKS: list[tuple[str, Callable[[], list[str]]]] = [
    ("C1", check_c1), ("C2", check_c2), ("C3", check_c3), ("C4", check_c4),
    ("C5", check_c5), ("C6", check_c6), ("C7", check_c7),
]


def main() -> int:
    all_failures: list[str] = []
    for name, fn in CHECKS:
        try:
            all_failures.extend(fn())
        except Exception as exc:
            all_failures.append(f"{name}: check raised {type(exc).__name__}: {exc}")
    if all_failures:
        print("Domain evidence profile lint FAILED:", file=sys.stderr)
        for x in all_failures:
            print(f"  - {x}", file=sys.stderr)
        return 1
    print("Domain evidence profile lint OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
```

> **Note on C1's `(requested:`, C7's `_heading_range`, and the consumer's "source_verification_agent is NOT" string:** Tasks 1–3 MUST produce those exact tokens. If a check string here does not match what T1–T3 wrote, fix the *agent prose* to match the documented contract (the spec is authoritative), not the check — the check encodes the spec's required surface. If the spec genuinely allows a synonym, widen the check; do not silently weaken it.

- [ ] **Step 3: Run the integration test — now it should pass**

Run: `python3 -m pytest scripts/test_check_domain_evidence_profile.py::test_integration_passes_against_real_repo -v`
Expected: PASS (Tasks 1–3 landed the required surface). If it FAILS, the failure names the exact check + missing token — fix the agent prose from T1–T3 to supply it, then re-run.

- [ ] **Step 4: Add the 7 negative-fixture mutation tests (each must make the lint FAIL)**

Append to `scripts/test_check_domain_evidence_profile.py`. Each test copies the repo into `tmp_path`, mutates ONE file, and asserts the lint fails on the matching check:

```python
def _clone_repo(tmp_path: Path) -> Path:
    """Copy the four lint-relevant files into a minimal repo tree under tmp_path."""
    dst = tmp_path / "repo"
    for rel in (INTAKE, PROFILES, CONSUMER, SQH):
        target = dst / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(REPO_ROOT / rel, target)
    return dst


def _mutate(repo: Path, rel: str, old: str, new: str) -> None:
    """Replace ALL occurrences of `old` (not just the first).

    A single-occurrence replace silently self-breaks a mutation test when the
    token appears more than once in the file: the lint's `if token not in text`
    check still finds the surviving copy, the lint passes, and the negative
    test's `assert returncode != 0` fails. We replace all, then assert the token
    is actually gone so a future multi-occurrence token can't reintroduce the bug.
    """
    p = repo / rel
    text = p.read_text(encoding="utf-8")
    assert old in text, f"fixture precondition: '{old}' not found in {rel}"
    p.write_text(text.replace(old, new), encoding="utf-8")
    assert old not in p.read_text(encoding="utf-8"), (
        f"fixture postcondition: '{old}' still present in {rel} after replace-all"
    )


def test_clone_passes_clean():
    """Sanity: an unmutated clone passes (so each negative isolates one break)."""
    import tempfile
    with tempfile.TemporaryDirectory() as d:
        repo = _clone_repo(Path(d))
        assert run_lint(repo).returncode == 0


def test_neg_a_drop_ship_enum(tmp_path):
    """(a) make a ship-ready enum value go missing (rename all copies) -> C2's
    closed-set table check fails. `humanities_interpretive` occurs twice in the
    profiles doc (table row + carry-forward fold), so _mutate must replace ALL."""
    repo = _clone_repo(tmp_path)
    _mutate(repo, PROFILES, "humanities_interpretive", "humanities_BOGUS")
    r = run_lint(repo)
    assert r.returncode != 0 and "C2" in r.stderr


def test_neg_a2_fifth_effective_row(tmp_path):
    """(a2) add a 5th effective profile row (`clinical`) to the table -> C2's
    closed-set check fails (extra row not in SHIP_ENUM). This is the spec's
    'add a 5th effective enum value' mutation strategy; the bare-presence check
    would have missed it. (closed-set regression coverage.)"""
    repo = _clone_repo(tmp_path)
    p = repo / PROFILES
    text = p.read_text(encoding="utf-8")
    # Insert a 5th data row right after the unknown_user_defined table row.
    marker = "| `unknown_user_defined` |"
    assert marker in text
    idx = text.index(marker)
    line_end = text.index("\n", idx)
    injected = "\n| `clinical` | RCTs | journal | gaps | smuggled-in effective |"
    p.write_text(text[:line_end] + injected + text[line_end:], encoding="utf-8")
    r = run_lint(repo)
    assert r.returncode != 0 and "C2" in r.stderr


def test_neg_a3_intake_drop_enum_C1(tmp_path):
    """(a3) drop a ship enum value from INTAKE (not PROFILES) -> C1 fails. test_neg_a
    only mutates PROFILES (proves C2); this one proves C1 actually fires on the
    intake surface. (C1/C4 negative-fixture coverage.)"""
    repo = _clone_repo(tmp_path)
    _mutate(repo, INTAKE, "general_social_science", "general_BOGUS")
    r = run_lint(repo)
    assert r.returncode != 0 and "C1" in r.stderr


def test_neg_c4_drop_advisory_or_246(tmp_path):
    """(c4) remove the advisory-only statement -> C4 fails. C4 previously had no
    negative fixture at all. (C1/C4 negative-fixture coverage.)"""
    repo = _clone_repo(tmp_path)
    _mutate(repo, PROFILES, "Advisory only", "Mandatory grading")
    r = run_lint(repo)
    assert r.returncode != 0 and "C4" in r.stderr


def test_neg_b_disqualifying_rename(tmp_path):
    """(b) rename gaps column back to 'disqualifying' -> C2 fails."""
    repo = _clone_repo(tmp_path)
    _mutate(repo, PROFILES, "Critical gaps to surface", "Disqualifying gaps")
    r = run_lint(repo)
    assert r.returncode != 0 and "C2" in r.stderr


def test_neg_c_strip_fallback_case(tmp_path):
    """(c) strip a graceful-fallback case from the consumer -> C3 fails."""
    repo = _clone_repo(tmp_path)
    _mutate(repo, CONSUMER, "[PROFILE-UNRESOLVED]", "REMOVED-TAG")
    r = run_lint(repo)
    assert r.returncode != 0 and "C3" in r.stderr


def test_neg_d_delete_legacy_text(tmp_path):
    """(d) delete the preserved Medicine/Health legacy row -> C5 fails. We mutate
    the distinctive verbatim phrase ('evidence-based-medicine') that C5 now binds
    to the Medicine/Health row, NOT the bare 'Medicine/Health' label (which could
    survive elsewhere). Replace-all removes every copy of the phrase."""
    repo = _clone_repo(tmp_path)
    _mutate(repo, PROFILES, "evidence-based-medicine", "REMOVED")
    r = run_lint(repo)
    assert r.returncode != 0 and "C5" in r.stderr


def test_neg_e_remove_policy_fold(tmp_path):
    """(e) delete ONLY the Policy fold line (not Social Science's identical fold)
    -> C5 fails. This is the real regression a review round flagged: the phrase
    'folded into general_social_science' appears for BOTH Social Science and
    Policy, so a phrase-only check (or replace-all) would miss a Policy-only
    deletion. C5 now binds 'Policy' to the fold on the same line; this fixture
    removes exactly that line and the bound check must fire."""
    repo = _clone_repo(tmp_path)
    p = repo / PROFILES
    lines = p.read_text(encoding="utf-8").splitlines(keepends=True)
    kept = [ln for ln in lines if not ("Policy" in ln and "folded into" in ln)]
    assert len(kept) == len(lines) - 1, "fixture expects exactly one Policy-fold line"
    p.write_text("".join(kept), encoding="utf-8")
    r = run_lint(repo)
    assert r.returncode != 0 and "C5" in r.stderr


def test_neg_f_leak_into_deep_research(tmp_path):
    """(f) add a Domain Evidence Profiles section to source_quality_hierarchy.md
    -> C6 R-5 leak guard (heading branch) fails."""
    repo = _clone_repo(tmp_path)
    p = repo / SQH
    p.write_text(p.read_text() + "\n## Domain Evidence Profiles\nleak\n", encoding="utf-8")
    r = run_lint(repo)
    assert r.returncode != 0 and "C6" in r.stderr


def test_neg_f2_edit_fsa_table_cell(tmp_path):
    """(f2) edit ONE cell of the Field-Specific Adjustments table (no leaked
    heading) -> C6's SHA-256 pin branch fails. Fixture (f) only trips the leaked-
    heading guard; without this, the hash-pin behavior could regress while C6
    still has a passing negative. Mutate a distinctive cell substring that exists
    in the real table (e.g. the Medicine/Health 'evidence-based medicine' note)."""
    repo = _clone_repo(tmp_path)
    p = repo / SQH
    text = p.read_text(encoding="utf-8")
    # Pick a substring guaranteed to be inside the FSA table; edit it so the
    # block digest changes but no `## Domain Evidence Profiles` heading appears.
    assert "Evidence-based medicine tradition" in text, "fixture expects the EBM note cell"
    p.write_text(text.replace("Evidence-based medicine tradition", "EDITED note"), encoding="utf-8")
    r = run_lint(repo)
    assert r.returncode != 0 and "C6" in r.stderr


def test_neg_g_carrier_regression(tmp_path):
    """(g) inside the Step 12 block, store the profile via Material Passport
    -> C7 carrier-regression guard fails."""
    repo = _clone_repo(tmp_path)
    # Insert a forbidden carrier line right after the Step 12 heading.
    p = repo / INTAKE
    text = p.read_text(encoding="utf-8")
    text = text.replace(
        "### Step 12: Domain Evidence Profile",
        "### Step 12: Domain Evidence Profile\n\nStore the profile on the Material Passport.",
        1,
    )
    p.write_text(text, encoding="utf-8")
    r = run_lint(repo)
    assert r.returncode != 0 and "C7" in r.stderr


def test_neg_g2_carrier_regression_with_distant_negation(tmp_path):
    """(g2) C7 false-negative guard: a regression line that ALSO contains a
    distant negation word ("Store on the Material Passport, do not use the PCR")
    must STILL fail C7. A per-line "any negation anywhere" filter would wrongly
    let this through; C7's per-occurrence "negation immediately before the token"
    rule catches it (the 'do not' negates the PCR, not the carrier)."""
    repo = _clone_repo(tmp_path)
    p = repo / CONSUMER
    text = p.read_text(encoding="utf-8")
    text = text.replace(
        "### Domain Evidence Profile Resolution",
        "### Domain Evidence Profile Resolution\n\nStore on the Material Passport, do not use the PCR.",
        1,
    )
    p.write_text(text, encoding="utf-8")
    r = run_lint(repo)
    assert r.returncode != 0 and "C7" in r.stderr


def test_neg_g3_carrier_regression_not_only(tmp_path):
    """(g3) C7 'not only/not just' guard: "Store not only on the Material Passport
    but also in the PCR" AFFIRMS the carrier (not only X = also X), so it must FAIL
    C7. C7's negation exemption uses a `(?!\\s+only|\\s+just)` lookahead so 'not
    only' is not treated as a negation. This fixture locks that branch — without
    it, a future edit could drop the lookahead while the other C7 fixtures still
    pass."""
    repo = _clone_repo(tmp_path)
    p = repo / CONSUMER
    text = p.read_text(encoding="utf-8")
    text = text.replace(
        "### Domain Evidence Profile Resolution",
        "### Domain Evidence Profile Resolution\n\nStore not only on the Material Passport but also in the PCR.",
        1,
    )
    p.write_text(text, encoding="utf-8")
    r = run_lint(repo)
    assert r.returncode != 0 and "C7" in r.stderr


def test_pos_historical_contrast_does_not_trip_c7(tmp_path):
    """Scope-lock: a Material Passport mention OUTSIDE the heading ranges (e.g.
    historical-contrast prose) must NOT trip C7."""
    repo = _clone_repo(tmp_path)
    p = repo / CONSUMER
    # Append contrast prose far from the resolution heading range.
    p.write_text(
        p.read_text() + "\n\n## History\nThe R1-R6 design used the Material Passport and Schema 13.\n",
        encoding="utf-8",
    )
    r = run_lint(repo)
    assert r.returncode == 0, r.stderr
```

Run: `python3 -m pytest scripts/test_check_domain_evidence_profile.py -v`
Expected: ALL PASS (7 core negatives (a-g) each FAIL the lint as asserted; g2 confirms the C7 false-negative guard; 2 positives confirm clean clone + scope-lock).

- [ ] **Step 5: Wire the lint into CI**

In `.github/workflows/spec-consistency.yml`, after an existing `python3 scripts/check_*.py` step (e.g. after the corpus consumer protocol step), add:

```yaml
      - name: Validate domain evidence profile documentation surface (#259)
        run: python3 scripts/check_domain_evidence_profile.py
```

**The mutation suite MUST run in CI — this repo uses the pytest manifest, so add it there (do not leave it as an uncommitted/unrun local test).** Append this `[[pytest]]` block to `scripts/_ci_pytest_manifest.toml` (mirroring the existing entries' shape — `id` unique, `path` exists):

```toml
[[pytest]]
id = "kong-259-domain-evidence-profile"
path = "scripts/test_check_domain_evidence_profile.py"
```

Then verify the manifest drift-guard accepts it: `python3 scripts/check_ci_pytest_manifest.py` (must pass — it checks path existence + id uniqueness) and smoke-run it: `python3 scripts/run_ci_pytest_manifest.py --id kong-259-domain-evidence-profile`. The lint step above + this manifest entry are BOTH required; `_ci_pytest_manifest.toml` must be in the Step 7 commit.

- [ ] **Step 6: Full local verification**

Run:
```bash
python3 scripts/check_domain_evidence_profile.py          # expect: "... lint OK", exit 0
python3 -m pytest scripts/test_check_domain_evidence_profile.py -v   # expect: all pass
git status --short deep-research/                          # expect: empty (INVARIANT 9)
```

- [ ] **Step 7: Boundary scan + commit**

```bash
git add scripts/check_domain_evidence_profile.py \
        scripts/test_check_domain_evidence_profile.py \
        scripts/_ci_pytest_manifest.toml \
        .github/workflows/spec-consistency.yml
git commit -m "Add domain evidence profile lint + mutation suite + CI wiring (#259 test/CI)  Ref #259 [skip-closes-check]

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Worked examples (MANDATORY — these cover what the linter cannot)

The spec's Test strategy is explicit: the linter verifies documentation surface only. Several INVARIANTS are runtime semantics (the monotonic "never tighten" half of INVARIANT 5, the reserved-fallback runtime behavior, the mismatch-advisory behavior, no-auto-SELECT). Those are verified by **reviewers reading the agent prose against these three worked examples** at plan-stage review — the linter does not claim to enforce them. An implementer MUST trace each example through the edited prose and confirm the prose produces the stated outcome.

### Worked example (i): reserved-fallback

**Setup:** Scholar at intake selects `clinical` (a reserved profile).
**Expected through Change B prose (Task 2):**
1. Intake recognizes `clinical` ∈ reserved.
2. PCR `Domain Evidence Profile` row stores effective `unknown_user_defined`, displayed as `unknown_user_defined (requested: clinical)`.
3. Intake surfaces: "this domain has no profile yet — falling back to neutral evidence standards (`unknown_user_defined`)."
**Expected through Change E prose (Task 3):** consumer reads the row, parses the leading effective token `unknown_user_defined` → case (b) neutral, **no** `[NO-PROFILE-NEUTRAL]` (scholar was asked and a value is present). Screening behaves exactly as pre-#259.
**INVARIANTS exercised:** 2, 12 (reserved fallback + request/effective coherence), 1 (no reserved value stored as effective).

### Worked example (ii): scholar override at intake (after Phase 1 already ran)

**Setup:** Scholar ran a full pipeline with `unknown_user_defined`; Phase 1 (literature_strategist) completed; now at Stage 4 (drafting) the scholar re-runs intake and changes the profile to `cs_ml`.
**Expected through Change B prose (Task 2):**
1. Intake overwrites the PCR row to effective `cs_ml`.
2. Because Phase 1 has **already run** (corpus frozen — the revision loop `8→5→6` does not re-run Phase 1), intake emits `[PROFILE-OVERRIDE-NO-RESCREEN]`: "the literature corpus is already fixed; to apply this profile, run Phase 1."
3. The override is honored for any *future* Phase-1 run; the current corpus is NOT retroactively re-screened (no placebo).
**INVARIANTS exercised:** 3 (single-value overwrite, no ledger), 5 (advisory — does not silently re-screen or block). This is the half C1 enforces only at the surface (the tag's presence + "already run OR was skipped" condition); the *behavior* (honored-future / not-retroactive) is what the reviewer confirms here.

### Worked example (iii): discipline mismatch

**Setup:** PCR `Discipline: Education`, scholar-confirmed profile `cs_ml`.
**Expected through Change E prose (Task 3):**
1. Consumer resolves `cs_ml` from the row. Implied-discipline map: `cs_ml` → CS/Engineering/Technology. PCR `Discipline: Education` is outside that set → mismatch.
2. Consumer emits `[PROFILE-DISCIPLINE-MISMATCH]` and proceeds with **both** signals in their lanes: `Discipline: Education` still drives Step 2 database selection (Education DBs — ERIC etc.), `cs_ml` still drives admissibility (preprints admissible at the peer-review node).
3. Known limitation surfaced: Education DBs may surface few preprints, so the opened admit path may have little to admit — the corpus is **not bricked** (peer-reviewed Education sources flow through unchanged universal+neutral gates), merely not enriched. Step-3 search-string enrichment partially mitigates. Nothing blocks; the advisory tells the scholar that aligning `Discipline` would feed the admit path.
**INVARIANTS exercised:** 5 (monotonic — Education peer-reviewed sources still admitted, nothing tightened), 10 (separation of duties — profile never touches DB selection), 11 (advisory, never blocks).

### Worked example (iv): absent row (plan→full) — the no-intake-no-profile runtime path

**Setup:** Scholar runs `plan` mode (simplified 3-question intake, Step 12 exempt), then transitions to `full`. No `Domain Evidence Profile` row was ever written.
**Expected through Change E prose (Task 3):**
1. Consumer resolves from the PCR row → **row absent** → case (a) → neutral `unknown_user_defined`.
2. Because this is a `full`-mode run, consumer emits `[NO-PROFILE-NEUTRAL]`: "neutral (single-pyramid) standards are in effect; re-run intake to select a domain profile."
3. Screening proceeds exactly as pre-#259. Nothing blocks; the degradation is *visible*, not silent.
**Contrast:** if the same absent-row run were `plan` mode (not full), no advisory is required (plan mode is lightweight by design). And a deep-research handoff is NOT this case — intake set the row.
**INVARIANTS exercised:** 11 (row-based, absent ⇒ neutral *visible*), 4 (graceful fallback, never blocks). This is the load-bearing fallback the whole missing-profile gate rests on, so a reviewer MUST confirm the prose emits the tag on absent-row + full-mode and stays silent on absent-row + plan-mode.

### Worked example (v): no-auto-SELECT (suggest-then-confirm)

**Setup:** A `deep-research → academic-paper` handoff carries an inferred discipline of "CS". Intake Step 12 runs.
**Expected through Change B prose (Task 2):**
1. Intake MAY *suggest* `cs_ml` as the pre-filled default (because the inferred discipline is CS), but it MUST present it as a choice the scholar confirms or changes.
2. The profile is NOT written to the PCR row until the scholar confirms. If the scholar does not respond / is unsure, the default is `unknown_user_defined`, not the inferred `cs_ml`.
**INVARIANTS exercised:** 6 (no auto-SELECT — inference may suggest, only scholar confirmation activates). A reviewer MUST confirm the prose never writes an inferred profile to the row without an explicit confirm step.

**Reviewer checklist for all five worked examples:** does the edited prose
- (a) never tighten a neutral admit,
- (b) never touch the universal relevance / methodology / predatory nodes,
- (c) never touch the Step 2 DB table,
- (d) emit exactly the right tag for each case (and stay silent where no tag is due — absent-row+plan, row=`unknown_user_defined`),
- (e) **never auto-activate an inferred profile without scholar confirmation (INV6)**,
- (f) **ship no grade-aggregation logic — only the #246 forward-reference note (INV8)**?

If any answer is no, the prose — not these examples — is wrong.

**deep-research-handoff enrichment caveat (surface, do not silently swallow):** a `deep-research → academic-paper` handoff hands in a bibliography that deep-research already screened under its own (neutral, byte-identical — INVARIANT 9) criteria. Phase 1 then runs Phase-B screening over those handed-in sources under the profile. A profile that opens an admit path (e.g. `cs_ml` preprints) can only admit what the upstream handoff actually contains — if deep-research's neutral search surfaced no preprints, the opened path has little to admit. This is the **same advisory-only limitation as the discipline-mismatch corner** (worked example iii), not a defect: nothing is bricked, the corpus is merely not enriched with the profile's preferred type. Task 3's consumer prose SHOULD note this so the scholar understands why a `cs_ml` handoff run may still show few preprints, and that a fresh `full` run (with profile-aware Phase-A search-string enrichment) would feed the path. (It is acceptable for #259 to surface this as a known limitation rather than re-screen upstream — deep-research stays untouched per INVARIANT 9.)

---

## Mirrored-artifact inventory (grep before declaring Task 3 done)

The spec's three mirror points for the two corpus ratios. Editing one without the others reintroduces the contradiction (R2/R3 caught this). Task 3 must touch all three in one commit:

| Mirror point | Anchor | Edited in |
|---|---|---|
| `## Quality Gates` ratio rows | `:479-480` | Task 3 Step 5 |
| `## Quality Criteria` prose restatement | `:558-559` | Task 3 Step 6 |
| Step 3/4 upstream filters | `:57-70` | Task 3 Step 7 |

Verification grep after Task 3: `grep -n "domain evidence profile\|loosen\|peer-reviewed-equivalent\|canonical" academic-paper/agents/literature_strategist_agent.md` — expect hits near all three anchor regions plus the resolution block and screening tree. If only one of `:479-480` / `:558-559` has profile language, the mirror is broken.

---

## Boundary scan (run on the staged diff before EVERY commit)

This is a public repository. The plan doc, the agent prose, and all commit messages must contain zero references to internal tooling, author identity, organization names, internal URLs, or private-repo paths. Before each `git commit`, run your local boundary linter over the staged diff (the project's pre-push boundary hook / personal denylist — the denylist itself lives outside this repo and must never be committed into it). A clean scan is the gate; anything it flags must be redacted before committing. (The `Co-Authored-By` trailer is allowed.) This plan was authored to stay clean — keep it that way in any edits, and never paste a literal denylist of forbidden terms into a file that ships in a public repo.

---

## Self-review (run against the spec before handing off)

**Spec coverage** — every Change + INVARIANT maps to a task:
- Change B (intake producer) → Task 2. Change C (new ref doc) → Task 1. Change E (consumer) → Task 3. Test/CI → Task 4. ✓
- INVARIANT 1 (enum cardinality) → T1 table + T2 enum + C1/C2. INVARIANT 2 (reserved fallback) → T2 + worked ex (i) + C1. INVARIANT 3 (single-value, no ledger) → T2 PCR row + C7 carrier guard + worked ex (ii). INVARIANT 4 (graceful fallback) → T3 cases (a)(b)(c) + C3. INVARIANT 5 (advisory + monotonic) → T3 pseudocode + sub-edits + worked ex (iii) + C3 universal-gate language. INVARIANT 6 (no auto-SELECT) → T2 "scholar must confirm" + worked-ex-review. INVARIANT 7 (no discipline loses guidance) → T1 carry-forward + C5. INVARIANT 8 (#246 boundary) → T1 forward-ref + C4. INVARIANT 9 (deep-research untouched) → T1 read-only + C6 leak guard + git-status checks. INVARIANT 10 (discipline reconcile) → T3 mismatch + map + C3. INVARIANT 11 (row-based, absent⇒neutral visible) → T3 case (a) + missing-profile gate. INVARIANT 12 (request/effective coherence) → T2 rule + C1 + worked ex (i). ✓
- 4 advisory tags: `[NO-PROFILE-NEUTRAL]` (T3, C3), `[PROFILE-UNRESOLVED]` (T3, C3), `[PROFILE-DISCIPLINE-MISMATCH]` (T3, C3), `[PROFILE-OVERRIDE-NO-RESCREEN]` (T2, C1). ✓
- 3 worked examples (reserved-fallback / override / mismatch) per spec Test strategy "out of reach". ✓

**Type/string consistency:** the lint's required tokens (`### Step 12: Domain Evidence Profile`, `### Domain Evidence Profile Resolution`, `Critical gaps to surface`, `(requested:`, the 4 tags, `source_verification_agent is NOT`) are the SAME strings the T1–T3 prose is instructed to write. C7's `_heading_range` relies on the headings being unique top-of-block — confirmed they are new headings.

**Placeholder scan:** no "TBD"/"add appropriate"/"similar to Task N" — every code/prose block is complete and inline.
