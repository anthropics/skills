# Kong #259 — Discipline-Relative Domain Evidence Profiles

**Status:** prompt + PCR field + standalone reference-doc design (R7 PCR-native rewrite)
**Date:** 2026-05-29
**Issue:** #259 (Tier A, `[ACCEPT-MEDIUM]`; attaches to #244 epic alongside #246)
**Scope:** Let a scholar select a `domain_evidence_profile` at **paper intake** so that `literature_strategist_agent` adjusts its post-retrieval screening gates to the scholar's discipline, instead of applying a single Western evidence-based-medicine (EBM) pyramid to every field. Advisory only, scholar-selected, no auto-detect, override first-class.

**Carrier (R7, the load-bearing rewrite decision):** the active profile lives as a **single-value field on the Paper Configuration Record (PCR)** — exactly like `Style Profile` (`intake_agent.md:238`). It is **NOT** carried by the Material Passport, and it is **NOT** a numbered handoff Schema. Rationale below ("Why PCR, not the Material Passport").

**Single consumer = `literature_strategist_agent`.** The profile is produced by `academic-paper`'s `intake_agent` (Phase 0) and consumed only by `literature_strategist_agent` (Phase 1) — both in `academic-paper` Stage 2, intake before literature_strategist. `source_verification_agent` is NOT a consumer (it runs in deep-research Stage 1, upstream of intake; serving it would require a deep-research-stage profile — deferred, see Out of scope).

**Anchor:** Kong et al. 2026 (arXiv:2605.18661) §7.4.6 (`kong2026_full.txt:L2213-L2227`, PDF p.39): "Extending AI-assisted research to chemistry, biology, medicine, materials science, physics, and social science requires more than retraining on domain papers. These fields differ in evidence standards, experimental infrastructure, safety constraints, data availability, and community norms."

---

## Why PCR, not the Material Passport (R7 root-cause correction)

The first six review rounds (R1–R6) all tried to carry the profile on the **Material Passport** and could never pass the gate. The R7 audit (opus subagent carrier-lifecycle trace + codex gpt-5.5 xhigh whole-pipeline scan + scholar's stated design intent) found that the carrier choice itself was the root cause, not any of the individual symptoms the six rounds kept patching.

**The scholar's design intent (highest authority):** the Material Passport is an **opt-in side input** — it lets a user wire their own KB/database in to bring literature into the pipeline. A core feature must NOT depend on the passport; **with no passport, the pipeline must still run.** Repo proof: `shared/handoff_schemas.md:505` (`literature_corpus` is Optional, "ARS does not produce these entries itself"), `:576` ("input port for user-owned literature"), `:580` ("corpus-first, search-fills-gap" — present is used, absent searches normally).

**The decisive precedent (Style Profile):** schema text once called Style Profile "carried by the Material Passport," but that is a simplification, not the runtime mechanism. In practice `intake_agent` writes it to the **PCR** (`intake_agent.md:192, :196, :238`) and `draft_writer_agent` reads it from the **PCR** (`draft_writer_agent.md:46`) — never the passport. Style Profile only *also* appears on the passport because it has a cross-skill consumer living in deep-research. **The domain profile's only consumer (`literature_strategist_agent`) is in `academic-paper`, in the same run as the producer — there is no cross-skill consumer, so there is no reason to involve the passport at all.**

**What "profile selection is a PCR concern" buys (every following item follows from the carrier choice):**

- Producer (intake, Phase 0) and consumer (literature_strategist, Phase 1) are in the same skill, correctly ordered, with no cross-skill carrier hop. The R4 P0-2 "passport does not exist pre-Stage-1" problem is *gone, not mitigated*.
- The profile no longer needs a handoff Schema number (it is a PCR field, not a handoff object) — which dissolves the **Schema-13 collision** (Schema 13 is already the sprint-contract schema: `shared/contracts/README.md:10`, `academic-paper/SKILL.md:163`).
- The PCR is a single-state snapshot table (`intake_agent.md:221-239`), so the profile is a **single-value field** with no append-only ledger — which dissolves the "last-entry resolution rule," the "malformed-ledger carve-out," and the reset/resume ordering key that R1–R6 spent rounds on.

**Form of the PCR field.** A new PCR row, mirroring `Style Profile` exactly:

```
| **Domain Evidence Profile** | [effective_value]                          |   # ship-ready selection
| **Domain Evidence Profile** | unknown_user_defined (requested: clinical) |   # reserved-fallback: effective + the scholar's request, parenthesized
```

The row stores the resolved **effective** profile (one of the 4 ship-ready enum values) — this is the *only* value the consumer reads. When the scholar requested a *reserved* profile, the row appends the request in parentheses (`unknown_user_defined (requested: <reserved>)`) so the scholar's intent is **visibly acknowledged** in the user-facing PCR table rather than looking like the system ignored their choice (the parenthetical is display-only; the consumer parses only the leading effective token). For a ship-ready selection there is no parenthetical (effective == request, so nothing is hidden). The PCR holds the *currently effective* profile — the active state, not a history. Override is "re-run intake, the row is overwritten" (same lifecycle as every other PCR row). There is **no append-only `selections[]` ledger** (R7 design decision: the PCR has no history mechanism — Style Profile does not have one either — and adding one would be unrequested abstraction for a single Phase-1 consumer; see "Override" for what is and is not retained).

---

## Boundary

This patch is the **profile-selection** layer. It is a checklist/search adjustment, not an autonomous grading or domain-detection layer.

- **No auto-SELECT.** The scholar selects the `domain_evidence_profile` at intake; nothing auto-selects it. `intake_agent` MAY *infer the discipline* (from a deep-research handoff or its Step 1 topic interview) to *suggest a default* profile, but the scholar must confirm. The prohibition is specifically on a profile activating without scholar confirmation. (Kong §7.4.6 rejects domain-*autonomous* judgment — an agent silently deciding evidence standards; a suggested-then-confirmed default is not autonomous.)
- **Advisory only.** A profile changes which evidence types / provenance the literature screening *admits*. It does NOT change the A-F Overall Grade, and it does NOT block manuscript ship.
- **Override is first-class — but it only re-screens if Phase 1 re-runs.** The scholar may change the profile by re-running intake (a fresh `academic-paper` invocation, or an in-session correction that re-runs the intake step). Intake overwrites the PCR `Domain Evidence Profile` row with the new effective value. **The load-bearing caveat:** the profile is consumed *only* by `literature_strategist_agent` in Phase 1. An override recorded **before Phase 1 runs** is fully effective (the consumer reads the updated row). An override recorded once the corpus is already fixed — i.e. **Phase 1 (`literature_strategist`) has already completed** (e.g. while drafting at Stage 4; the revision loop `8→5→6`, `academic-paper/SKILL.md:270`, does not re-run Phase 1) **OR Phase 1 was skipped entirely** (the scholar explicitly skipped the literature phase, so no screening ran) — updates the PCR row but does **not** retroactively re-screen the corpus. (Note: a `deep-research` handoff carrying a bibliography is **not** this case — Phase 1 still ran its Phase-B screening over the handed-in sources under the profile then in effect; an override after that completes is the "already completed" branch.) To avoid a *placebo* override (scholar changes the profile expecting a different corpus but the corpus is frozen), `intake_agent` MUST, when it records a profile override and Phase 1 has either already run **or been explicitly skipped** in this pipeline, surface a one-line `[PROFILE-OVERRIDE-NO-RESCREEN]` advisory: "the literature corpus is already fixed (already screened, or this run skips literature screening); to apply this profile, run Phase 1." The override is honored for any *future* Phase-1 run, and the scholar is told plainly that the current corpus is not retroactively changed. (No silent no-op; the scholar decides whether to re-run Phase 1.)
- **No intake ⇒ no profile row ⇒ neutral.** Any run that does not run a full `intake_agent` leaves the PCR `Domain Evidence Profile` row absent (or `unknown_user_defined`): a standalone `deep-research` run, a true mid-entry pipeline start (e.g. entering at Stage 2.5 with an existing draft), or a `plan → full` transition whose simplified intake omits Step 12. (Note: the common `deep-research → academic-paper` handoff is **not** in this list — it *does* run intake and only skips redundant questions, so Step 12 runs and the profile IS asked; see "Missing-profile gate" for the corrected per-path table.) In every genuine no-intake case `literature_strategist_agent`, if it runs at all, takes the neutral `unknown_user_defined` fallback and emits `[NO-PROFILE-NEUTRAL]` (full mode) so the neutral default is visible, not silent. This is intentional and safe: with no scholar-confirmed profile, neutral evidence standards are the conservative default. The profile is "asked at intake when intake runs" — there is no claim that every entry path asks for it.
- **#246 is a forward dependency, not part of this patch.** #259 defines discipline-relative *evidence expectations* (what counts as good evidence per domain). #246 will later define discipline-relative *grade aggregation* (how the six criteria combine into an Overall Grade, e.g. so humanities is not structurally capped at Grade B). #259 ships a forward-reference note where aggregation would plug in; it does NOT import aggregation logic.
- **Conservative default.** The default profile `unknown_user_defined` is the neutral, pre-#259 single-pyramid behavior. Selecting an unimplemented (reserved) profile resolves to `unknown_user_defined` with an explicit advisory, to prevent *false rigor* from a profile that does not exist yet.

---

## Relationship to the existing PCR `Discipline` field (R-3 reconcile — "each manages its own")

The PCR already has a `Discipline` field (`intake_agent.md:228`), and `literature_strategist_agent` already uses it to pick databases and terminology — its `### Step 2: Database Selection` table maps `Discipline` → primary databases (`literature_strategist_agent.md:46-55`: Education → ERIC, CS → IEEE Xplore, etc.). The new `Domain Evidence Profile` is a *second* discipline signal, so the two must be reconciled.

**Resolution: separation of duties, no override (maintainer-approved 2026-05-30).**

- **`Discipline` keeps its existing job:** terminology extraction (Step 1) and database selection (Step 2). The profile does **not** touch the Step 2 database table — it never changes which databases are queried.
- **`Domain Evidence Profile` owns one new job only:** evidence *admissibility* — which evidence types the post-retrieval screening gates (Steps after retrieval) will admit. This is the loosen-only contract in Change E.
- **Mismatch handling:** if the selected profile implies a discipline that disagrees with the PCR `Discipline` (e.g. `Discipline: Education` but `Domain Evidence Profile: cs_ml`), `literature_strategist_agent` emits a one-line `[PROFILE-DISCIPLINE-MISMATCH]` advisory and proceeds with **both** signals in their own lanes — `Discipline` still drives database selection, the scholar-confirmed profile still drives admissibility. Neither overrides the other; nothing is blocked. (This is deliberate: the profile is advisory-only and must not silently rewrite the database strategy, and the scholar may legitimately want, e.g., education-discipline databases with cs_ml-style preprint admissibility.)

  **Profile → implied-discipline map (so "implies a discipline" is deterministic, not guesswork):**

  | Profile | Implied discipline(s) for the mismatch check |
  |---|---|
  | `cs_ml` | CS / Engineering / Technology |
  | `humanities_interpretive` | Humanities |
  | `general_social_science` | Social Science **or** Policy (matches either — no mismatch warning if `Discipline` is either) |
  | `unknown_user_defined` | none — the neutral default never triggers a mismatch check |

  The mismatch advisory fires only when the PCR `Discipline` falls outside the profile's implied-discipline set. `unknown_user_defined` and an absent profile never warn. The check is a string-category comparison against this table, not an inference.

This keeps the change minimal (no edit to the Step 2 database table) and consistent with the advisory-only / no-unrequested-abstraction discipline.

---

## Profiles

### Ship-ready enum (exactly 4)

```
general_social_science | cs_ml | humanities_interpretive | unknown_user_defined
```

`unknown_user_defined` is the **default** and the neutral fallback. The other three are real, populated profiles.

### Reserved (documented, NOT in enum)

```
clinical | wet_lab | materials_physics | legal_case_based | education
```

Reserved profiles are named in the reference doc with a "not in enum yet — selecting this falls back to `unknown_user_defined`" note. They ship per demand in later releases. They are deliberately kept OUT of the enum so that intake cannot select a profile whose checklist does not exist (which would manufacture false rigor).

---

## Design decisions (settled in brainstorm 2026-05-29, carrier revised R7 2026-05-30)

These resolutions deliberately diverge from three of the issue's literal acceptance criteria; §"Acceptance mapping" records each divergence and its reason.

| # | Decision | Rationale |
|---|----------|-----------|
| Q1 carrier | The active profile is a **single-value PCR field** (`Domain Evidence Profile` row), produced by `intake_agent`, consumed by `literature_strategist_agent`. **Not** the Material Passport; **not** a numbered handoff Schema. | *(R7 root-cause rewrite — supersedes the R1–R6 Material-Passport / Schema-13 design.)* The passport is an opt-in side input the pipeline must run without; binding a core feature to it was the root cause of six failed rounds. The profile's only consumer is in the same skill as the producer, so no passport carrier is needed. Mirrors the real Style Profile mechanism (PCR row, `intake_agent.md:238` / `draft_writer_agent.md:46`). Avoids the Schema-13 collision with the sprint-contract schema (`shared/contracts/README.md:10`). |
| Q2 no append-only ledger | The PCR holds only the **currently effective** profile (single value). No `selections[]` event ledger. Override = re-run intake overwrites the row. | *(R7.)* The PCR is a single-state snapshot table with no history mechanism (`intake_agent.md:221-239`); Style Profile is stored the same single-value way. A per-entry append-only ledger would be unrequested abstraction for one Phase-1 consumer, and it is what forced the R1–R6 "last-entry resolution," "malformed-ledger carve-out," and reset/resume-ordering complexity. Dropping it dissolves all three. |
| Q3 discipline reconcile | **Separation of duties:** `Discipline` keeps database/terminology; the profile owns evidence admissibility only; mismatch warns, neither overrides. | *(R7.)* `Discipline` already drives the Step 2 database table (`literature_strategist_agent.md:46-55`); letting the profile touch it would contradict the advisory-only contract and risk regressing database selection. Minimal-edit, no override. |
| Q4 naming reconciliation | In the **new** profile reference doc, the profile-centric table **carries forward the substance of** the field-centric `Field-Specific Adjustments` rows from `source_quality_hierarchy.md`. The deep-research file's own table is left **untouched**. | *(R7 — changed from R1–R6, which replaced the deep-research table in place.)* `source_quality_hierarchy.md` is read by deep-research's `source_verification_agent` + `bibliography` (`deep-research/SKILL.md:392`, `source_verification_agent.md:38`). Editing it would leak #259 into deep-research (R-5). Instead the profile table lives in academic-paper's own reference and *copies* the field guidance; the shared file is not modified, so deep-research is unaffected. |
| Q5 #246 forward-dependency | Add a **forward-reference note** in the profile reference doc; do NOT pull aggregation into #259, do NOT ship placeholder logic. | #246 (grade aggregation) is unbuilt and the maintainer is doing #259 first. A forward note avoids a dangling cross-link without scope-creeping #259 into #246. |
| Q6 profile granularity | Add a single `academic-paper/references/domain_evidence_profiles.md` file with a 4-row structured table. Do NOT create a `deep-research/references/domain_profiles/` directory of per-profile files. | 4 profiles (3 real, 1 neutral fallback), advisory-only, no aggregation, do not justify a directory of mini-specs. A single dedicated file keeps the agent reading one place while giving enough structure to consume reliably. Split into files only when profiles grow long, are independently maintained, or are reused by tooling. |

---

## Change set (3 product/prompt edits + test/CI)

**Product/prompt edits (the user-facing behavior change):** **B (intake produces the PCR row), C (new academic-paper profile reference doc), E (literature_strategist consumes the PCR row).** There is no Change A (no Schema), no Change D (no second consumer).

**Test/CI edits (required, separate from the 3 product edits — see Test strategy for content):** a new `scripts/check_domain_evidence_profile.py` lint, a new `scripts/test_check_domain_evidence_profile.py` mutation suite, and a one-line wiring into `.github/workflows/spec-consistency.yml`. These are implementation artifacts the plan MUST deliver; they are not counted among the 3 product edits because they ship no runtime behavior, but an implementer must not skip them.

> Round history: R1–R6 carried the profile on the Material Passport as "Schema 13" with up to 6 product edits (orchestrator producer + two consumers + in-place edit of the deep-research reference file). The R7 PCR-native rewrite collapses the product surface to **3 edits** with no passport, no Schema number, and no edit to any deep-research file.

### B. Intake production — `academic-paper/agents/intake_agent.md`

`intake_agent` is the **producer** of the PCR `Domain Evidence Profile` row. Add a profile-selection step as a **new intake step** under the heading **`### Step 12: Domain Evidence Profile`** — same `###`-under-`## Interview Protocol` level as the existing `### Step N` steps (`intake_agent.md:110-204`), numbered after the current Step 11 Funding — and add the `| **Domain Evidence Profile** | ... |` row to the Paper Configuration Record output table (after the `Style Profile` row).

- Present the 4 ship-ready profiles as an explicit choice; `unknown_user_defined` is the default if the scholar does not pick or is unsure.
- List the 5 reserved profiles with the explicit note that selecting one records `effective: unknown_user_defined` **and surfaces an advisory** ("this domain has no profile yet — falling back to neutral evidence standards").
- `intake_agent` MAY *suggest* a default profile inferred from a deep-research handoff or its Step 1 topic interview, but the scholar MUST confirm; nothing auto-activates (see Boundary "No auto-SELECT").
- It is NOT folded into Step 10 Style Calibration (Step 10 is writing-sample calibration the scholar frequently declines, `style_profile: null`; the domain profile is a separate concern with a separate lifecycle).
- Write the resolved **effective** profile into the PCR `Domain Evidence Profile` row. This is the single authoritative home; there is no passport copy and no separate ledger.
- **Reserved-fallback (per the rules below):** if the scholar selects a reserved profile, the row records `unknown_user_defined` (the effective value), and intake surfaces the advisory. The PCR row never stores a reserved value as effective.
- **Phase-1-fully-skipped carve-out (no placebo prompt) — narrow, explicit trigger only:** the profile's *only* consumer is `literature_strategist_agent` (Phase 1). The carve-out applies **only when `literature_strategist_agent` will not run at all**, i.e. Phase 1 is skipped *entirely*. **Critical distinction (R3 fix):** a `deep-research → academic-paper` handoff carrying a bibliography does **NOT** trigger this — that handoff still runs `literature_strategist_agent`, it merely "goes directly to Phase B (full-text assessment), skipping Phase A" search (`literature_strategist_agent.md:550`; `deep-research/SKILL.md:354` "skip literature **search**", not skip the agent). In that case the agent still screens the handed-in sources, so the profile **does** have a live consumer and Step 12 **prompts normally**. The carve-out fires only on an **explicit "skip Phase 1 entirely" signal** — the scholar choosing to skip the literature phase outright (`academic-paper/SKILL.md:139` "User *can* skip Phase 1 if providing own sources"), e.g. a mid-entry start with a finished draft where no literature screening will occur. On that explicit signal, intake records `unknown_user_defined` + a one-line `[NO-PROFILE-NEUTRAL]` advisory ("this run skips literature screening entirely, so a domain evidence profile would have no consumer; to apply one, run Phase 1"). Default when ambiguous: **prompt Step 12** (assume the consumer runs) — under-prompting silently drops a usable profile, which is worse than one extra question.
- **Mid-pipeline override:** if the scholar later changes the profile (a fresh `academic-paper` invocation that re-runs intake, or an in-session correction), `intake_agent` overwrites the PCR row. An override recorded **before Phase 1 runs** is consumed normally. An override recorded when **Phase 1 has already run OR was skipped** (the corpus is already fixed) cannot retroactively re-screen it, so intake MUST emit `[PROFILE-OVERRIDE-NO-RESCREEN]` (see Boundary). The override is still honored for any future Phase-1 run.
- **plan mode is exempt:** the plan-mode simplified 3-question intake (`intake_agent.md:95-104`, `:263`) does NOT run Step 12 and does NOT add the row. A plan-mode run leaves no profile; `literature_strategist_agent`, if reached, takes the neutral `unknown_user_defined` fallback. (plan mode is a lightweight structure-planning mode; domain evidence-standard tuning has low value there and the simplified intake stays simple.)

**Profile-value rules (prose validation, mirroring the PCR's other single-value fields — NO JSON Schema file):**

- The scholar's *request* MUST be one of the 4 ship-ready values OR one of the 5 reserved values — nothing else.
- The PCR row's stored **effective** value MUST be one of the 4 ship-ready enum values.
- **Request/effective coherence:** if the request is a ship-ready value, the stored effective value MUST equal it. If the request ∈ {`clinical`, `wet_lab`, `materials_physics`, `legal_case_based`, `education`} (reserved), the stored effective value MUST be `unknown_user_defined` and intake MUST surface the reserved-fallback advisory. No other request/effective combination is valid (this forbids silently storing, e.g., a request of `general_social_science` as an effective `cs_ml`).

### C. Profile definitions — new file `academic-paper/references/domain_evidence_profiles.md`

A new reference doc in academic-paper's own references directory (the consumer, `literature_strategist_agent`, lives in academic-paper). **No deep-research file is touched** — this is the R-5 isolation. Contents:

1. **Carry forward the substance of the existing `## Field-Specific Adjustments` table** from `source_quality_hierarchy.md` (lines ~132-143; **6 rows** — Medicine/Health, Education, Social Science, Policy, Humanities, Technology). The source table is **read, not edited**; its guidance is *copied* into the new profile-centric framing so no per-field guidance is silently dropped. Specifically:
   - `general_social_science`, `cs_ml`, `humanities_interpretive` profile rows **absorb the substance of** the Social Science / Technology / Humanities rows respectively. The **Policy** row's substance is folded into the `general_social_science` profile row as well (Policy has no dedicated profile; its expert-panel/context-dependent guidance is merged into `general_social_science`'s notes).
   - The Medicine/Health and Education rows map to **reserved** profiles (`clinical`, `education`). Their existing adjustment text is **preserved verbatim in a legacy mapping note** within this new file (not deleted, not moved out of the deep-research file — copied).
   - **Preservation is historical / non-normative.** The legacy note records what the field-centric table says, for reference and for the eventual `clinical` / `education` profiles. It does NOT change runtime behavior: until those reserved profiles ship, Medicine/Health and Education runs use the neutral `unknown_user_defined` pyramid, exactly as every other unmapped selection does. Label the note "**historical reference — non-normative; current behavior for these domains is neutral `unknown_user_defined` until the `clinical` / `education` profile ships.**"

   Legacy mapping (old field label → disposition in this new file):
   - Social Science → substance folded into `general_social_science` profile row *(normative, via the profile)*
   - Technology → substance folded into `cs_ml` profile row *(normative, via the profile)*
   - Humanities → substance folded into `humanities_interpretive` profile row *(normative, via the profile)*
   - Policy → substance folded into `general_social_science` profile row *(normative, via the profile; no dedicated Policy profile)*
   - Medicine/Health → text preserved verbatim in the historical/non-normative legacy note; runtime behavior = neutral `unknown_user_defined` until the reserved `clinical` profile ships
   - Education → text preserved verbatim in the historical/non-normative legacy note; runtime behavior = neutral `unknown_user_defined` until the reserved `education` profile ships

2. **A `## Domain Evidence Profiles` section with a 4-row table.** Columns: `Profile` / `Standard evidence types` / `Common provenance requirements` / `Critical gaps to surface` / `Reserved-note`. (The gaps column is named "Critical gaps to surface" — NOT "disqualifying" — because the profile is advisory: it tells the agent what weaknesses to *flag*, it never disqualifies a source or changes the grade.) Plus a separate short list of the 5 reserved profiles with the "not in enum" note.

3. **A `#246` forward-reference note:** "Discipline-relative *grade aggregation* (how these evidence expectations roll up into an Overall Grade) is tracked separately in #246 and is not yet implemented; until then the A-F Overall Grade lookup in `source_quality_hierarchy.md` applies unchanged."

4. **An advisory-only statement** at the top of the file: the profile changes which evidence types the literature screening admits; it never changes the A-F Overall Grade and never blocks ship.

> **Why the deep-research file is not edited (R-5):** `source_quality_hierarchy.md` is a deep-research reference consumed by `source_verification_agent` and `bibliography` for the evidence pyramid + grading rubric. #259's only consumer is in academic-paper. Copying the field guidance into a new academic-paper file (rather than replacing the deep-research table in place) keeps deep-research's behavior byte-identical and contains #259 entirely within academic-paper.
>
> **No dual-table read by the consumer (the key fact):** `literature_strategist_agent` does **not** read `source_quality_hierarchy.md` at all — it has its own screening tree, quick-assessment checklist, and quality gates (`literature_strategist_agent.md:413/436/468`) and does not reference the deep-research evidence-pyramid file (verified: no `source_quality_hierarchy` mention in the consumer). So there is **no "agent reads both the old and the new field table" collision**: the consumer reads only the new `domain_evidence_profiles.md`, the old `Field-Specific Adjustments` table is read only by deep-research's agents, and the two never meet in one context. The new profile table is *seeded from* the old table's substance (a one-time authoring copy), not read alongside it at runtime.

### E. literature_strategist consumption — `academic-paper/agents/literature_strategist_agent.md`

`literature_strategist_agent` is the **sole consumer** of the profile. It resolves the active profile from the **PCR `Domain Evidence Profile` row** (NOT the passport, NOT a ledger). A profile must influence the post-retrieval screening gates (it does **not** touch Step 2 database selection — that stays `Discipline`-driven per the reconcile rule). Graceful-fallback cases, none of which block:

- **(a) row absent** — the rule is strictly **row-based**: if the PCR has no `Domain Evidence Profile` row, fall back to neutral `unknown_user_defined`, **and in `full` mode emit `[NO-PROFILE-NEUTRAL]`** so the neutral default is visible. Paths that leave the row absent: plan→full and true mid-entry (intake never set it). **Resume-from-checkpoint is NOT automatically absent** — it carries whatever the prior intake wrote (present ⇒ that profile applies, no advisory; absent ⇒ neutral + advisory). The `deep-research → academic-paper` handoff with a live Phase 1 is also not absent (intake sets the row). (Resolve by reading the row, not by classifying the path — the path table is only a reviewer aid.)
- **(b) row = `unknown_user_defined`** → neutral (the explicit default; the scholar actively chose/accepted neutral at intake, so no `[NO-PROFILE-NEUTRAL]` advisory is needed — that tag is for the *absent-row* case where no one was asked).
- **(c) row holds a value not in the 4 enum** (e.g. a hallucinated or reserved value somehow stored as effective) → neutral, **and emit a one-line `[PROFILE-UNRESOLVED]` advisory**.
- **(d) discipline mismatch** (profile implies a discipline ≠ PCR `Discipline`, per the profile→implied-discipline map) → proceed with both signals in their lanes, **emit `[PROFILE-DISCIPLINE-MISMATCH]`** (per the reconcile rule); this is a warning, not a fallback — admissibility still uses the profile.

There is **no `HANDOFF_INCOMPLETE` concern**: the profile is a PCR field, not a handoff object, so the general handoff-validation convention (`shared/handoff_schemas.md:7-9`) never applies to it. A profile defect simply falls back to neutral with the advisory.

**Loosen-only / additive contract (realizes INVARIANT 5).** Every sub-edit below is *monotonic admit-only*: under a non-neutral profile a screening gate may **admit an evidence type it would otherwise wrongly exclude**, but it MUST NOT exclude, down-rank, or fail any source that the neutral gate currently admits. Where a gate combines neutral and profile criteria, combine by **OR (union of admissible)**, never by replacement.

```
# Monotonic admit-only resolution (pseudocode — the load-bearing definition)
profile = resolve_from_PCR_row()            # one of 4 enum values; absent/non-enum -> unknown_user_defined (+ advisory on non-enum)

# The neutral screening tree (literature_strategist :413) has SEVERAL branches. The profile
# loosens ONLY the evidence-type / publication-type / currency / provenance branches. It does
# NOT touch the universal-quality branches, which apply to every source regardless of profile:
UNIVERSAL_GATES = [relevance_to_RQ,          # abstract must address >=1 aspect of the RQ (:421-423)
                   methodology_not_fatally_flawed,   # no obvious design flaw / fatal methodology (:425-428)
                   not_predatory_or_fabricated]      # predatory-publisher / fabrication checks
PROFILE_LOOSENABLE_GATES = [peer_review_requirement,  # "is it peer-reviewed?" (:415-419)
                            publication_type,          # preprint / proceedings / archival / primary-source admissibility
                            currency_window,           # ">= 50% in last 5 years" gate (:480)
                            provenance_expectation]     # field-appropriate provenance

def admit(source):
    if not all(g(source) for g in UNIVERSAL_GATES):
        return False                          # profile can NEVER bypass relevance / methodology / predatory
    if neutral_passes(source, PROFILE_LOOSENABLE_GATES):
        return True                           # never tighten: anything neutral admits on these gates stays admitted
    if profile != unknown_user_defined and profile_admits(source, profile, PROFILE_LOOSENABLE_GATES):
        return True                           # only loosen: profile ADDs admit paths on the loosenable gates only
    return False
# The OR (union of neutral + profile) is scoped to PROFILE_LOOSENABLE_GATES, applied AFTER the
# universal gates pass. Under unknown_user_defined, admit() == the full neutral tree exactly.
# A cs_ml preprint that is off-topic, fatally flawed, or predatory is still EXCLUDED — the profile
# only forgives "not peer-reviewed / is a preprint", not "fails core quality".
```

The sub-edits, all reverting to current behavior under fallback cases (a)/(b)/(c). **Each loosens only the peer-review/publication-type/currency/provenance gate it names; none touches the universal relevance / methodology / predatory gates:**

1. **Screening decision tree** (`### Literature Screening Decision Tree`, ~line 413): the current tree excludes non-peer-reviewed unless gov/white-paper gray literature, which would drop `cs_ml` preprints and `humanities_interpretive` archival/primary sources. Add a profile-aware branch **on the "is it peer-reviewed?" node only** so the profile's standard evidence types are **additionally admissible** (preprints includable under `cs_ml`; primary/archival sources includable under `humanities_interpretive`), tagged by type rather than excluded. **The downstream relevance ("abstract addresses the RQ?") and methodology ("no obvious design flaw?") nodes still apply unchanged** — a profile-admitted preprint must still pass them. The branch only *adds* an admit path at the peer-review node; nothing the neutral tree admits becomes excluded, and no universal-quality node is bypassed.
2. **Quality quick-assessment checklist** (`### Literature Quality Quick Assessment Checklist`, ~line 436): the existing 5-item quick-assessment total score penalizes preprints/archival via the **Journal-ranking** item (the other four items — methodological rigor, relevance, citation count, data quality — are universal-quality and stay in force). Under a non-neutral profile, a source passes if it **meets the neutral quick-assessment outcome OR meets the profile's evidence-type expectations on the journal-ranking item only** (union scoped to the publication-type axis, not replacement — a source that passes the neutral score must still pass even if it does not match the profile; and a source the profile would admit on publication type must still clear the methodological-rigor / relevance items, which are universal).
3. **Quality gates** (`## Quality Gates`, ~line 468): the `>= 70% peer-reviewed` (line 479) and `>= 50% currency` (line 480) pass criteria contradict `humanities_interpretive` (primary/older canonical texts) and `cs_ml` (preprints). Make these **two corpus-ratio gates** profile-relative **in the loosening direction only**: under a non-neutral profile the admissible set *expands* (preprints count toward the `cs_ml` peer-reviewed-equivalent ratio; canonical texts do not count against `humanities_interpretive` currency). The thresholds are never raised, and a corpus that passes the neutral gate always passes the profile-relative gate. The other quality-gate rows (source count, annotation completeness, matrix coverage, research-gap count) are not evidence-type gates and are untouched.
4. **Quality-criteria checklist — the mirror constraints** (`## Quality Criteria`, `literature_strategist_agent.md:558-559`): the same two ratios are restated here in prose — "Source quality distribution: majority should be peer-reviewed" and "Recency: >50% of sources from last 5 years (unless historical topic)". These are a **mirror of the Quality Gates row** and MUST receive the **identical** profile-relative loosening, or a profile-admitted `cs_ml` preprint / `humanities_interpretive` canonical text would pass the gate at line 479-480 only to be re-tightened by this duplicate at 558-559. Apply the same union/loosen-only rule: under a non-neutral profile, "majority peer-reviewed" counts the profile's peer-reviewed-equivalent types, and the recency criterion does not penalize the profile's canonical/older sources. (This is the mirrored-artifact catch — both the gate **and** its restated criterion move together; changing one without the other reintroduces the contradiction the gate fix was meant to remove.)

**Search-string enrichment (optional, additive, NOT a database change):** under a non-neutral profile, Step 3 (Search String Construction, ~lines 57-61) MAY add profile-relevant search strings (e.g. `cs_ml` → also include preprint-server-style query terms). This is purely additive to the search strings; it does **not** change the Step 2 database table (which stays `Discipline`-driven). Never drops a search string the neutral strategy would have used.

**Upstream filter carve-out (Step 3 search filters + Step 7 publication-type inclusion criteria, `literature_strategist_agent.md:57-70`):** the Step 3 `Filters: peer-reviewed, [year range]` line and the Step-7-style "Peer-reviewed journals / books / conference proceedings (include) vs blog posts / news (exclude)" publication-type rows are **not** the same corpus-ratio mirror as sub-edits 3/4, but they are *upstream hard filters* that could exclude profile-admissible evidence (preprints, primary sources) before it ever reaches the screening tree. Under a non-neutral profile these MUST receive the same loosen-only treatment: the profile's standard evidence types are added to the includable set (peer-reviewed filter relaxed to peer-reviewed-equivalent for `cs_ml`; year-range relaxed for `humanities_interpretive` canonical texts), never tightened, never dropping anything the neutral filter would have kept. (Same monotonic rule as the gates — this just names the upstream filters so an implementer does not leave them as hard excludes that starve the admit paths sub-edits 1-4 open downstream.)

**Mismatch + enrichment interaction (the `[PROFILE-DISCIPLINE-MISMATCH]` corner — addresses the "search can't feed the admit path" concern):** when `Discipline` and the profile disagree (e.g. `Discipline: Education`, profile `cs_ml`), the Step 2 databases stay `Discipline`-keyed (Education databases), so a profile-opened admit path (e.g. "preprints admissible") may have *little to admit* if those databases surface few preprints. This is a **known advisory-only limitation, not a failure**: the corpus is not bricked (peer-reviewed Education sources still flow through the unchanged universal + neutral gates exactly as today), it is merely not enriched with the profile's preferred evidence type. Step-3 search-string enrichment partially mitigates by adding profile-relevant query terms even under a mismatched discipline. The `[PROFILE-DISCIPLINE-MISMATCH]` advisory tells the scholar both signals are active in their own lanes and that aligning `Discipline` to the profile's field (re-run intake) would let database selection feed the opened admit path. Nothing blocks; the scholar decides.

This composes with the existing `## Distributional Skew Advisory (Kong #257)` section without contradicting it (skew advisory measures distribution; profile sets admissibility — orthogonal).

---

## Missing-profile gate (R-4 — explicit per-path handling)

The resolution rule ("read the PCR row; absent ⇒ neutral") must be correct across **every** path that reaches `literature_strategist_agent`, not just a clean intake. Each path below is **accounted for** — some apply the profile, some fall back to neutral — and every one is intended behavior, not a defect:

| Path to literature_strategist | Does academic-paper intake run? | Profile state | Result |
|---|---|---|---|
| Standard `academic-paper full` with intake | yes (full Step 12) | PCR row set by Step 12 | profile applies |
| `deep-research → academic-paper` handoff (**with or without** a bibliography) | **yes** — intake_agent runs, skipping only redundant questions (`intake_agent.md:37-50`, `deep-research/SKILL.md:352`), not Step 12 | **PCR row set by Step 12** (intake asks the profile; inferred discipline MAY pre-fill the suggested default, scholar confirms) | **profile applies** — `literature_strategist_agent` still runs even when a bibliography is handed in: it "goes directly to Phase B (full-text assessment), skipping Phase A" search (`literature_strategist_agent.md:550`), so the profile has a live consumer screening the handed-in sources |
| Scholar **explicitly skips Phase 1 entirely** (`academic-paper/SKILL.md:139`, e.g. mid-entry with a finished draft, no literature screening at all) | intake runs, but Step 12 takes the **Phase-1-fully-skipped carve-out** (Change B): no placebo prompt | PCR row recorded `unknown_user_defined` + `[NO-PROFILE-NEUTRAL]` advisory explaining no literature screening will occur, so a profile would have no consumer | **neutral, surfaced** — the scholar is told why a profile is not asked, and that running Phase 1 would let one apply. NOT a placebo. |
| `plan → full` transition (literature_strategist runs from plan artifacts) | plan intake is the simplified 3-question intake → Step 12 exempt → no row | no row | neutral fallback (see note below) |
| Mid-entry pipeline start (e.g. Stage 2.5 with existing draft) | no — intake skipped entirely | no row | neutral fallback |
| Re-entry after reject/restructure or resume-from-checkpoint | no new intake (resumes existing PCR) | PCR row carries whatever the prior intake set (or absent if intake never ran) | profile applies if the row was set, else neutral fallback |
| Standalone `deep-research` run | n/a — never reaches academic-paper intake or literature_strategist | n/a | profile not in play |

**Correction vs R1–R6 framing:** the `deep-research → academic-paper` handoff is the *common* path; it **does** run `intake_agent` (skipping only redundant questions) AND `literature_strategist_agent` still runs (Phase-B screening over the handed-in bibliography, `literature_strategist_agent.md:550`), so Step 12 runs, the profile IS asked, and it has a live consumer — a profile-applies path regardless of whether a bibliography was handed in. The genuine **always-absent-row** paths are `plan → full` and true mid-entry (intake never sets the row). **Resume is row-based, not always-absent** — it keeps whatever the prior intake wrote, so it is a missing-profile path *only* when the prior intake left the row absent. The only neutral-by-carve-out path is the scholar **explicitly skipping Phase 1 entirely** (no literature screening at all), where Step 12 records neutral + `[NO-PROFILE-NEUTRAL]` rather than prompting. Resolve by reading the row; the table classifies paths only to confirm each was considered.

**`plan → full` note (a deliberate gap, surfaced not silent):** because plan-mode intake is the simplified 3-question intake that omits Step 12, a scholar who goes plan→full is never asked for a profile and silently gets neutral evidence standards. This is acceptable for plan mode's lightweight purpose, but to avoid a *silent* quality degradation, `literature_strategist_agent` MUST, when it runs with no PCR profile row in a `full`-mode run, emit a one-line `[NO-PROFILE-NEUTRAL]` advisory noting that neutral (single-pyramid) standards are in effect and the scholar may re-run intake to select a domain profile. (This makes "absent ⇒ neutral" observable rather than invisible — it never blocks.)

The gate is therefore the single rule "resolve from the PCR row; absent ⇒ neutral + `[NO-PROFILE-NEUTRAL]` advisory in full mode" (Change E cases (a)) applied uniformly. The table exists so a reviewer can confirm each run shape was considered; there is no run shape where a missing profile breaks the pipeline, and no run shape where a missing profile degrades quality *invisibly*.

---

## Acceptance mapping (incl. deliberate divergences)

| Issue acceptance criterion | How this spec satisfies it | Divergence |
|----------------------------|----------------------------|------------|
| #1 Intake adds `domain_evidence_profile` with enum = 4 ship-ready values + default `unknown_user_defined` | Change B (intake Step 12 + PCR row) | aligned |
| #2 `deep-research/references/domain_profiles/` directory + 4 profile md files | **Changed to** a single `academic-paper/references/domain_evidence_profiles.md` with a 4-row table (Change C) | **DIVERGES** — maintainer-approved (Q6): single dedicated file, not a directory; and it lives in academic-paper (the consumer's skill), not deep-research, to avoid leaking #259 into the shared deep-research reference (R-5). To be noted on #259 at close. |
| #3 Reserved profile list documented with "not in enum yet" note | Change B (profile-value rules) + Change C (reserved-note column + reserved list) | aligned |
| #4 `source_verification_agent.md` + `literature_strategist_agent.md` consume the profile | **Only `literature_strategist_agent` consumes it** (Change E). `source_verification_agent` is dropped from the consumer set. | **DIVERGES** — maintainer-approved: `source_verification_agent` runs in deep-research (Stage 1), upstream of the producer (intake, Stage 2), and serving it would require a deep-research-stage profile. Its domain-aware verification is deferred (see Out of scope). To be noted on #259 at close. |
| #5 #246 cross-links to relevant profiles | **Changed to** a forward-reference note (Change C.3), because #246 is not yet implemented | **DIVERGES** — maintainer-approved (Q5): forward-reference note instead of a live cross-link, to avoid a dangling reference. The live cross-link lands when #246 ships. |
| #6 User can override profile mid-pipeline, recorded in Material Passport | Override = re-run intake overwrites the PCR `Domain Evidence Profile` row (Change B); active = the row's current value (Change E) | **DIVERGES** — maintainer-approved (R7 Q1/Q2): recorded in the **PCR**, not the Material Passport, and as the *current effective value*, not an append-only history. The passport is an opt-in side input the pipeline must run without, so a core feature cannot be carried there; and the PCR has no history mechanism, so override is overwrite (the scholar's latest choice is authoritative). If a future release needs an override audit trail, it can add a history block then — out of scope now. To be noted on #259 at close. |

---

## INVARIANTS

1. **Enum cardinality.** The ship-ready enum (the PCR row's stored effective values) is exactly 4 (`general_social_science`, `cs_ml`, `humanities_interpretive`, `unknown_user_defined`); the 5 reserved values (`clinical`, `wet_lab`, `materials_physics`, `legal_case_based`, `education`) are NOT valid stored effective values (they may appear only as a scholar *request*, which resolves to `unknown_user_defined`).
2. **Reserved fallback.** A request ∈ reserved → the PCR row stores `unknown_user_defined` + intake surfaces an explicit advisory naming the requested reserved value. No reserved profile ever silently activates a checklist.
3. **Single-value PCR carrier (no ledger).** The active profile is the **current value of the PCR `Domain Evidence Profile` row** — a single state, not a history. Override overwrites the row (same lifecycle as `Style Profile` and every other PCR row). There is no append-only `selections[]` ledger and no "last-entry" resolution rule. Safe because the sole consumer runs once in Phase 1 and the revision loop (`8→5→6`, `academic-paper/SKILL.md:270`) does not re-run Phase 1, so the consumer never observes a stale-vs-current ambiguity. (Supersedes the R1–R6 passport-ledger design.)
4. **Graceful fallback.** Absent PCR row / row = `unknown_user_defined` / row value not in the 4 enum (incl. hallucinated or reserved-as-effective) → the consumer applies the current neutral single-pyramid behavior, unchanged, with no block; the non-enum case also emits `[PROFILE-UNRESOLVED]`. The profile is a PCR field, not a handoff object, so the `HANDOFF_INCOMPLETE` convention never applies — a profile defect never blocks.
5. **Advisory only.** A profile never changes the A-F Overall Grade and never blocks manuscript ship. In `literature_strategist`, profile-relative screening gates are **monotonic admit-only**: they only *admit* evidence types the neutral gates would wrongly exclude (combining by OR / union), and never exclude, down-rank, or fail any source the neutral gate currently admits. The profile never touches Step 2 database selection.
6. **No auto-SELECT.** No agent activates a `domain_evidence_profile` without scholar confirmation. The producer is `intake_agent`; discipline *inference* (deep-research handoff or Step 1 topic interview) MAY suggest a default, but the scholar confirms.
7. **No discipline loses existing guidance.** Carrying forward the 6-row field-centric table into the new profile reference MUST account for every row: Social Science / Technology / Humanities / **Policy** fold their substance into ship-ready profile rows (Policy → `general_social_science`); Medicine/Health + Education are preserved verbatim in a **historical, non-normative** legacy note whose runtime behavior is neutral `unknown_user_defined` until their reserved profiles ship. No row is dropped, and the preserved note is non-normative (no "applies until" normative claim). **Scope clarification (Education does not regress):** "existing guidance" here means the *documentation* in the deep-research `Field-Specific Adjustments` table. That table is consumed by deep-research's `source_verification`/`bibliography`, **not** by `literature_strategist_agent` — the academic-paper literature screening already runs on its own tree/checklist/gates and never used the deep-research field table. So for an Education paper, `literature_strategist`'s screening behavior is **identical before and after #259**: #259 only *adds* (advisory, monotonic) admit paths under ship-ready profiles, and Education maps to a not-yet-shipped reserved profile, so it stays on exactly the neutral behavior it has today. Nothing Education-specific is taken away, because nothing Education-specific was in the consumer to begin with. The deep-research table that *is* preserved (copied into the legacy note) keeps serving its actual consumers unchanged (INVARIANT 9).
8. **#246 boundary.** #259 references grade aggregation as a forward dependency only; it ships no aggregation logic and no placeholder aggregation code.
9. **Deep-research reference untouched (R-5).** `source_quality_hierarchy.md` (and every other deep-research file) is **not modified** by #259. The profile-centric table lives only in the new `academic-paper/references/domain_evidence_profiles.md`; the field guidance is *copied* into it, not moved. deep-research's `source_verification_agent` + `bibliography` behavior stays byte-identical.
10. **Discipline reconcile — separation of duties.** The PCR `Discipline` field continues to drive database/terminology (Step 2); the `Domain Evidence Profile` drives evidence admissibility only. Neither overrides the other. A mismatch emits `[PROFILE-DISCIPLINE-MISMATCH]` and both signals proceed in their own lanes; nothing is blocked.
11. **Row-based resolution ⇒ absent row ⇒ neutral (visible).** The active profile is resolved by **reading the PCR row**, never by classifying the entry path. An absent row ⇒ neutral `unknown_user_defined` fallback (INVARIANT 4 case (a)) + `[NO-PROFILE-NEUTRAL]` in full mode so neutral is visible. Paths that leave the row absent: `plan → full` (simplified intake omits Step 12) and true mid-entry start. **Resume-from-checkpoint preserves the existing row** — it is neutral only if the prior intake left it absent, otherwise the resumed profile applies (so resume is NOT an unconditional missing-profile path). **The `deep-research → academic-paper` handoff is also not a missing-profile path** — intake sets the row and `literature_strategist_agent` still runs (Phase-B screening of the handed-in bibliography), so the profile applies whether or not a bibliography accompanied the handoff. The only carve-out is the scholar **explicitly skipping Phase 1 entirely**, where Step 12 records neutral + `[NO-PROFILE-NEUTRAL]` (no placebo, Change B). The Missing-profile gate table enumerates every path and which side it falls on. No path degrades quality invisibly.
12. **Request/effective coherence.** The scholar's request ∈ {4 ship-ready ∪ 5 reserved}; if ship-ready, the stored effective value == the request; if reserved, the stored effective value == `unknown_user_defined` with an advisory. No other combination is valid — a stored effective value can never silently differ from the scholar's confirmed ship-ready selection.

---

## Test strategy

Prose contract (the profile is a PCR field, not a JSON schema — mirrors how `Style Profile` is validated by prose, no JSON Schema file). The checker is **honest about its reach**: a markdown structural checker verifies *documentation surface* (presence/shape of required text), NOT runtime semantics. Several INVARIANTS are semantic; the split below makes that explicit.

**`scripts/check_domain_evidence_profile.py` — documentation-surface checks (deterministic):**

1. `intake_agent.md` documents the 4 effective enum values + the 5 reserved values; the PCR output table contains a `Domain Evidence Profile` row; the request/effective coherence rule, the reserved-fallback advisory text, the reserved-fallback display form (`unknown_user_defined (requested: <reserved>)`), the `### Step 12: Domain Evidence Profile` heading, the Phase-1-fully-skipped carve-out, and the `[PROFILE-OVERRIDE-NO-RESCREEN]` advisory (emitted when an override lands after Phase 1 **has already run OR was explicitly skipped** — the checker requires both halves of that condition, and a mutation fixture that drops the "or was skipped" half must FAIL) are present (INVARIANTS 1, 2, 12).
2. `academic-paper/references/domain_evidence_profiles.md` exists and has a `## Domain Evidence Profiles` section with a 4-profile table whose gaps column is "Critical gaps to surface" (NOT "disqualifying"), plus the 5 reserved names with the "not in enum" note (INVARIANTS 1, 2, 5).
3. The consumer agent (`literature_strategist_agent`), in its `### Domain Evidence Profile Resolution` block, contains a "resolve `domain_evidence_profile` from the PCR row" instruction AND the graceful-fallback cases (absent / `unknown_user_defined` / non-enum incl. hallucinated) AND the **three** advisory tags it (the consumer) is specified to emit — `[NO-PROFILE-NEUTRAL]` (absent-row, full mode), `[PROFILE-UNRESOLVED]` (non-enum), `[PROFILE-DISCIPLINE-MISMATCH]` (reconcile) — plus the universal-gate carve-out language ("relevance / methodology / predatory still apply") so the monotonic contract is documented (INVARIANTS 4, 5, 10). It also confirms `source_verification_agent` is NOT given a profile-resolution step. (The fourth tag, `[PROFILE-OVERRIDE-NO-RESCREEN]`, is emitted by `intake_agent`, not the consumer — checked in item 1.)
4. `domain_evidence_profiles.md` carries the advisory-only statement + the #246 forward-reference note (INVARIANTS 5, 8).
5. The legacy field guidance is present in `domain_evidence_profiles.md`, labeled non-normative AND containing the preserved Medicine/Health + Education text; the `general_social_science` profile row references the folded **Policy** substance (INVARIANTS 7).
6. **No deep-research file is modified by #259:** `source_quality_hierarchy.md` does NOT contain a `## Domain Evidence Profiles` section and its `## Field-Specific Adjustments` table is unchanged (a guard asserting the profile table did NOT leak into the shared file) (INVARIANT 9).
7. The PCR `Domain Evidence Profile` row is named in `intake_agent.md` as the single carrier (INVARIANT 3). **Carrier-regression guard (scoped by concrete heading delimiters to be deterministic):** the implementation MUST place the profile instructions under two named headings — **`### Step 12: Domain Evidence Profile`** in `intake_agent.md` (matching the existing `### Step N` level under `## Interview Protocol`) and **`### Domain Evidence Profile Resolution`** in `literature_strategist_agent.md`. The guard scans **only the byte range from each of those headings to the next same-or-higher-level heading**, and asserts that within those ranges the profile is NOT stored on or resolved from a `Schema 13` number, a `selections[]` ledger, or the Material Passport. It does **not** scan the whole repo, the whole agent file, or this spec's prose: the spec deliberately cites `Schema 13` / `selections[]` / Material Passport as the *superseded* R1–R6 design, and unrelated repo sections legitimately use Material-Passport / Schema language for other features (e.g. `shared/handoff_schemas.md`, the corpus blocks of the same agent files). The named-heading range makes the scope a deterministic delimiter rather than a fuzzy "instruction block," so the guard neither false-fails on contrast prose nor misses a regression. (Requiring the exact headings is itself one of the documentation-surface checks.)

**Negative fixtures + mutation test (`scripts/test_check_domain_evidence_profile.py`):** deliberately (a) add a 5th effective enum value, (b) rename the gaps column back to "disqualifying", (c) strip one graceful-fallback case, (d) delete the preserved Medicine/Education text, (e) **remove the Policy fold reference**, (f) **add a `## Domain Evidence Profiles` section to `source_quality_hierarchy.md`** (must FAIL — the R-5 leak guard), (g) **inside the Step 12 / profile-resolution instruction blocks, store/resolve the profile via `selections[]` / `Schema 13` / Material Passport** (must FAIL — the carrier-regression guard, scoped to instruction blocks so the spec's own historical-contrast mentions do NOT trip it) — each must make the checker FAIL (so it cannot trivially accept-all). A companion positive test asserts the guard does **not** fire on the historical-contrast paragraphs (lock the scope). Wired into `.github/workflows/spec-consistency.yml`.

**Out of the checker's reach — relies on plan-stage review + worked example:** INVARIANT 2's runtime reserved-fallback behavior; INVARIANT 5's no-grade/no-block runtime behavior **and its monotonic admit-only ("never tighten") half** (a markdown surface checker cannot verify that a gate only loosens); INVARIANT 6's no-auto-SELECT; INVARIANT 8's no-aggregation-logic; INVARIANT 10's mismatch-advisory runtime behavior; INVARIANT 11's no-intake-no-profile runtime path. These are agent-prompt semantics. The implementation plan MUST include worked examples exercising (i) a reserved-fallback, (ii) a scholar override at intake, and (iii) a discipline mismatch; the dual-track reviewers verify the prompt text — the linter does not claim to enforce these.

---

## Out of scope (forward work)

- **#246** discipline-relative grade aggregation (Overall Grade formula). #259 only forward-references it.
- Reserved profiles (`clinical` / `wet_lab` / `materials_physics` / `legal_case_based` / `education`) ship per demand in later releases.
- **`source_verification_agent` domain-aware verification (deferred).** Making `source_verification_agent` profile-aware (IRB checks for clinical, reagent-provenance for wet-lab, primary-source verification for humanities, etc.) requires the profile to be available in deep-research at Stage 1. The PCR is an academic-paper Stage-2 artifact, so a deep-research-stage profile (or a passport carrier for the cross-skill case) would have to be designed. Until then, only `literature_strategist_agent` is profile-aware.
- **Override audit trail.** #259 stores only the current effective profile (overwrite-on-re-intake). If a future release needs a per-change history of profile selections, it can add a history block (e.g. on the passport, where append-only ledgers already live) at that time. Out of scope now — a single Phase-1 consumer does not need it.
- `citation_compliance_agent` profile integration (consistent with the v3.6.5 deferral of corpus integration for that agent).
- No JSON Schema file for `domain_evidence_profile` (it is a prose-validated PCR field, mirroring how `Style Profile` is handled).
- Profile-relative grade aggregation (#246) — only forward-referenced; the A-F lookup is unchanged.
