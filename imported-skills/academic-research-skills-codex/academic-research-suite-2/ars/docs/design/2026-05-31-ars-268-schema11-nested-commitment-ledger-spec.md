# ARS #268 — Schema 11 Commitment Ledger: parallel-list → nested-object refactor

**Issue:** #268 (Kong A1 / #256 follow-up — structural redesign)
**Anchor:** Gemini R3 review of PR #264, Finding 1 (P1, deferred from A1 scope)
**Date:** 2026-05-31
**Type:** Structural schema redesign (breaking correction to Kong A1 shape)

## 1. Problem

Kong A1 (#256) shipped the Commitment Ledger on Schema 11 as **three index-aligned parallel lists**:

- `commitment_extracted: [{commitment_text, commitment_type, required_evidence_type}, ...]` — list of objects
- `fulfillment_status: [<enum>, ...]` — list of strings, parallel
- `unfulfilled_rationale: ["" | <text>, ...]` — list of strings, parallel

Position `i` across all three refers to the same commitment. The equal-length invariant is **prose-only** (`shared/handoff_schemas.md` Validation rule) — there is no JSON-Schema and no Python lint enforcing it.

Gemini R3 Finding 1: a human hand-editing the Markdown tracking table can drop a `<br>` separator or mis-number an entry, silently desyncing the three lists. A re-review agent walking the triples in lockstep then pairs the wrong status/rationale to a commitment and emits a false `COMMITMENT_GAP` advisory. The cognitive load of maintaining 3-way alignment grows linearly with commitment count (currently 3 of 12 seed cases are multi-commitment).

## 2. Decision (user-confirmed, 2026-05-31)

**Scope 1 — REPLACE (not coexist-with-deprecation).** The parallel-list shape is removed entirely; nested-object becomes the only shape. A single legacy normalization note is added to the schema for any old artifact still carrying top-level `fulfillment_status` / `unfulfilled_rationale`.

Justification (first-party verified 2026-05-31, corroborated by an independent design review):

1. **Zero runnable consumers.** The #263 calibration harness that would consume the ledger has NOT shipped. The 12-case seed file explicitly states "this file is a SEED — not a runnable test."
2. **Zero enforcement code.** No JSON-Schema, no Python lint enforces the equal-length invariant — it is prose-only.
3. **Zero real fixtures.** No Material-Passport fixture in `tests/` or `evals/` carries this field.
4. **Producers/consumers are prose agent instructions only.** `revision_coach_agent` Step 3.5 (producer) and `re_review_mode_protocol` Commitment Ledger Verification (consumer) are Markdown prompts; no code parses the shape at runtime.

In a prose prompt-suite distributed as a git repo / Claude Code plugin, "accept both shapes" is cargo-cult API-compatibility thinking: it teaches agents two patterns, carries a standing ambiguity, and **preserves the exact index-walking failure mode #268 exists to kill**. There is no real in-flight data to migrate — only schema/template/example/seed prose to rewrite in lockstep.

**Scope 3 — DEFER `author_fulfillment_claim`.** Gemini's "promised vs. claimed vs. verified" three-way split is conceptually sound but is NOT required to fix the #268 structural bug. Adding a per-commitment free-text claim field now introduces another field that can drift from row-level `authors_claim` / `revision_location` / `fulfillment_status` / `unfulfilled_rationale`. Per the standing no-unrequested-flexibility rule, it is deferred until a concrete failure case shows row-level `authors_claim` is materially ambiguous on a multi-commitment row. Row-level `authors_claim` stays as-is.

## 3. Final nested shape + lifecycle rules

The three lifecycle fields fold into each `commitment_extracted` object. Lifecycle state is **explicit by key presence** — no placeholder keys at extraction time.

**At extraction (revision_coach_agent Step 3.5)** — only the three extraction fields, lifecycle keys absent:

```yaml
commitment_extracted:
  - commitment_text: "add ablation on CIFAR-100"
    commitment_type: add_experiment
    required_evidence_type: new_table
```

**After revision execution — fulfilled** (append `fulfillment_status` only; NO `unfulfilled_rationale` — the old empty-string `""` placeholder was a parallel-list alignment artifact and is dead weight in the nested shape):

```yaml
commitment_extracted:
  - commitment_text: "add ablation on CIFAR-100"
    commitment_type: add_experiment
    required_evidence_type: new_table
    fulfillment_status: fulfilled
```

**After revision execution — non-fulfilled** (`partial` / `not-fulfilled` / `explicitly-rejected-with-rationale`): append both `fulfillment_status` and `unfulfilled_rationale`; `unfulfilled_rationale` MUST be non-empty:

```yaml
commitment_extracted:
  - commitment_text: "run ablation across 5 random seeds with std errors"
    commitment_type: add_experiment
    required_evidence_type: new_table
    fulfillment_status: partial
    unfulfilled_rationale: "Computational budget allowed 3 seeds; 5-seed deferred per §6 Limitations."
```

**The `COMMITMENT_GAP` failure case** (non-fulfilled status, missing/empty `unfulfilled_rationale`) — the advisory still fires, exactly as before, but now keyed on object-field presence rather than `unfulfilled_rationale[i]` being empty:

```yaml
commitment_extracted:
  - commitment_text: "add error bars from 5-seed runs"
    commitment_type: add_experiment
    required_evidence_type: new_figure
    fulfillment_status: not-fulfilled
    # unfulfilled_rationale absent → COMMITMENT_GAP surfaces
```

**Field semantics (unchanged from A1, only relocated):**

- `fulfillment_status` ∈ `{fulfilled, partial, not-fulfilled, explicitly-rejected-with-rationale}`. Absent before revision execution.
- `unfulfilled_rationale`: free-text, required iff `fulfillment_status ∈ {partial, not-fulfilled, explicitly-rejected-with-rationale}`. **Omitted (not `""`)** when `fulfillment_status == fulfilled` or absent.
- `EVIDENCE_TYPE_UNSPECIFIED` (fires iff `required_evidence_type == other`) is orthogonal and unchanged.
- `residual_action` stays **concern-level** (one per Schema 11 row), unchanged. Its coherence relationship with per-commitment `unfulfilled_rationale` is preserved; only the index-notation prose is reworded to object-field notation.

## 4. Validation rule rewrite

The A1 equal-length invariant is **retired** (structurally impossible under nesting — the safety it provided is now inherent, per harness-retirement reasoning). The new validation rule:

- `commitment_extracted` is a list of objects; each object MUST carry `commitment_text` + `commitment_type` + `required_evidence_type`.
- `fulfillment_status` is an optional per-object field (absent at extraction time; present after revision execution).
- `unfulfilled_rationale` is an optional per-object field. WHEN PRESENT it MUST be non-empty on a non-`fulfilled` status and MUST be absent on a `fulfilled` one. A non-`fulfilled` commitment MAY omit it entirely — that is the valid COMMITMENT_GAP case, not a violation.
- Empty list `commitment_extracted: []` stays valid (comment carried no extractable commitment).
- **Legacy normalization note:** if an old artifact carries top-level `fulfillment_status` / `unfulfilled_rationale` arrays (pre-#268 Kong A1 shape), **first verify all three were the same length** — a pre-#268 ledger may already be desynchronized (the failure mode #268 closes), so do NOT auto-zip a length-mismatched ledger; flag it for manual reconciliation instead. Only for an equal-length row: zip the i-th status/rationale onto the i-th commitment object, copying `unfulfilled_rationale` only when non-empty (a blank `""` / missing entry on a non-`fulfilled` status normalizes to an *absent* nested field — the COMMITMENT_GAP case). Re-review agents verify ONLY the nested shape; they do not walk parallel top-level arrays.

Violations surface as `COMMITMENT_GAP` advisory at re-review (advisory only — author retains final responsibility; unchanged).

## 5. Change-set inventory (6 files + 3 mirror points)

First-party verified 2026-05-31. Schema 11 has **no JSON-schema source-of-truth** (`shared/contracts/` has no commitment/traceability schema), so no `.schema.json` edit.

| File | Change |
|------|--------|
| `shared/handoff_schemas.md` (Schema 11, ~L731-766) | Fold lifecycle fields into `commitment_extracted` object def; rewrite `fulfillment_status` / `unfulfilled_rationale` as per-object; retire equal-length Validation rule; add legacy normalization note; reword `residual_action` coherence section (L755-757) index-notation (`unfulfilled_rationale[i]`) → object-field notation (`commitment.unfulfilled_rationale`). |
| `academic-paper/agents/revision_coach_agent.md` (Step 3.5, ~L89-216) | Producer emits extraction fields only; explicitly state lifecycle keys are appended later (during revision execution), not at extraction. Output-format YAML stays extraction-only (already is). |
| `academic-paper-reviewer/references/re_review_mode_protocol.md` (Commitment Ledger Verification, ~L43-61) | Rewrite `unfulfilled_rationale[i]` index language → `commitment.unfulfilled_rationale` object-field language; "walk each commitment" stays but the desync risk is gone; preserve COMMITMENT_GAP + EVIDENCE_TYPE_UNSPECIFIED semantics. |
| `academic-paper/templates/revision_tracking_template.md` (~L29-33, L67-91) | Collapse the three fragile `<br>`-separated columns (Commitments / Fulfillment / Unfulfilled Rationale) into a **single per-commitment ledger column** rendering one nested YAML block per concern; rewrite the "Parallel-list alignment" guidance (L91) — the alignment burden is gone, replaced by per-commitment object authoring. |
| `academic-paper/examples/commitment_ledger_example.md` | Rewrite the "After revision: author fills..." section (L45-63) — fold the separate `fulfillment_status: [...]` + `unfulfilled_rationale: [...]` blocks into nested objects under each `commitment_extracted` entry; update the COMMITMENT_GAP contrast (L73-87) to object-field shape. |
| `evals/calibration/commitment_ledger_seed.yaml` | Nest `expected_fulfillment_status` + `expected_unfulfilled_rationale` into each `expected_commitments` object as `fulfillment_status` / `unfulfilled_rationale`; drop the `fulfilled → ""` placeholder (omit rationale on fulfilled); update the header schema comment. Keep all 12 cases + their expected gap/evidence-type booleans. |

**Mirror points (per release-discipline / mirrored-artifact rules):**

- `CHANGELOG.md` — add `## [Unreleased]` entry under Kong A1 lineage; record as breaking correction (#268). Note: the existing #256 entry says "10 cases" but #269 already moved it to 12 — the #268 entry references the current 12-case shape.
- `.claude/CLAUDE.md` — Skills Overview / version-relevant section if it references the parallel-list shape (grep first).
- `README.md` — grep for any commitment-ledger shape reference (likely none; verify).

## 6. New lint: nested-shape structural test + mutation

Per the schema-mutation-test discipline (`feedback_schema_mutation_test_for_constraints`): a structural lint that the nested seed shape is correct, plus a mutation test that a violated shape FAILs.

Since Schema 11 has no JSON-schema, the lint operates on the seed YAML + asserts the prose invariants are coherent. New `scripts/check_268_nested_commitment_ledger.py`:

- **N1:** every `expected_commitments[]` entry in the seed is a mapping carrying `commitment_text` + `commitment_type` + `required_evidence_type`.
- **N2:** the seed carries NO top-level `expected_fulfillment_status` / `expected_unfulfilled_rationale` parallel lists on any case (the parallel-list shape is gone — guards against regression to A1 shape).
- **N3:** for each `expected_commitments` entry, `fulfillment_status` (if present) ∈ the enum; `unfulfilled_rationale`, WHEN PRESENT, is non-empty on a non-fulfilled status and absent on a fulfilled one (a non-fulfilled commitment MAY omit it — the valid COMMITMENT_GAP case). A shared `_blank_rationale` helper treats missing / YAML-null / whitespace uniformly as blank (avoids the `str(None) == "None"` truthy trap).
- **N3b:** the case-level `expected_commitment_gap` oracle agrees with the per-commitment shape — gap fires iff some commitment is non-fulfilled with a blank/absent rationale. `expected_commitment_gap` must be a real YAML boolean (a quoted `"false"` is rejected, since it would coerce truthy under `bool()`).
- **N4:** the schema prose (`handoff_schemas.md` Schema 11) contains NO surviving `unfulfilled_rationale[i]` / `fulfillment_status[i]` index-notation (cascade-completeness guard — catches a missed reword in the residual_action coherence section).
- **N5:** `re_review_mode_protocol` Commitment Ledger Verification contains no surviving index-notation either.

Mutation tests (`scripts/test_check_268_nested_commitment_ledger.py`): a trivial accept-all replacement of each invariant must make a deliberately-mutated fixture FAIL, confirming the invariant is load-bearing (N1 missing field / non-mapping, N2 reintroduced parallel list, N3 fulfilled-with-rationale + non-fulfilled-with-empty + non-fulfilled-with-null rationale + bad enum + orphan rationale, N3b incoherent gap oracle + quoted-boolean flag, N4/N5 reintroduced index notation).

Wire into `.github/workflows/spec-consistency.yml` + `_ci_pytest_manifest.toml`.

## 7. Out of scope

- `author_fulfillment_claim` (Scope 3 — deferred, §2).
- Any change to row-level `authors_claim`, `residual_action` semantics (only the index-notation wording reworded).
- The #263 calibration harness (still unshipped; seed remains a non-runnable seed, now in nested shape).
- A JSON-schema source-of-truth for Schema 11 (Schema 11 stays prose-defined, consistent with its current state).

## 8. Ship gate

Quality cleanup pass → independent cross-model review (0 P0/P1) → boundary + secret scan → PR `Closes #268`. v3.10 tag: #268 folds into the pending v3.10 release alongside #127 PR-B.
