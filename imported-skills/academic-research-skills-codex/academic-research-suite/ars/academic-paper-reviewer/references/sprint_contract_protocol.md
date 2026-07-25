# Sprint Contract Protocol (v3.6.2)

> Authoritative orchestration reference for the ARS v3.6.2 sprint-contract hard gate.
> Schema: `shared/sprint_contract.schema.json` (Schema 13.1 since v3.6.6).
> Templates: `shared/contracts/reviewer/*.json`.
> Design spec: `docs/design/2026-04-23-ars-v3.6.2-sprint-contract-design.md`.
>
> **v3.6.6 cross-reference**: this reviewer protocol is byte-equivalent across v3.6.2 → v3.6.6 (zero-touch promise per §3.6 of `docs/design/2026-04-27-ars-v3.6.6-generator-evaluator-contract-design.md`). The v3.6.6 release adds a parallel generator-evaluator protocol inside `academic-paper` for the in-pair writer / evaluator pair (see `academic-paper/SKILL.md` § "v3.6.6 Generator-Evaluator Contract Protocol" and design doc §5).

## 1. Overview

A reviewer sprint contract is a machine-checkable pre-registered acceptance criterion. The orchestrator loads a frozen template, inlines runtime fields (`generated_at`, optional `agent_amendments`), and drives each reviewer through a paper-content-blind Phase 1 followed by a paper-visible Phase 2. The synthesizer then runs a three-step mechanical protocol over the `panel_size` reviewer outputs to emit an editorial decision.

This protocol exists to destroy the "read the paper, then rationalise the scoring standard" drift path. The load-bearing mechanism is the **physical separation of calls**: Phase 1 never sees paper content.

## 2. Two-phase reviewer call

For each reviewer in `range(panel_size)`:

1. **Prepare contract.** Load template from `shared/contracts/<domain>/<mode>.json`. Populate `generated_at` (ISO-8601 UTC). Optionally populate `agent_amendments` (field-specific notes from `field_analyst_agent`). Run `check_sprint_contract.py` on the in-memory object; abort on error.
2. **Phase 1 call (paper-content-blind).**
   - System prompt: the `### Phase 1 — Paper-content-blind pre-commitment` sub-section of the reviewer agent's `## v3.6.2 Sprint Contract Protocol` block.
   - User content: contract JSON + paper metadata ONLY (`title`, `field`, `word_count`).
   - Expected output: `## Contract Paraphrase`, `## Scoring Plan`, terminal `[CONTRACT-ACKNOWLEDGED]` tag.
3. **Phase 1 output lint.** See §4 below.
4. **Phase 2 call (paper-visible).**
   - System prompt: the `### Phase 2 — Paper-visible review` sub-section of the same `## v3.6.2 Sprint Contract Protocol` block.
   - User content: contract JSON (re-injected) + Phase 1 output wrapped in `<phase1_output>...</phase1_output>` data delimiter + full paper.
   - Expected output: optional `## Scoring Plan Dissent`, `## Dimension Scores`, `## Failure Condition Checks`, `## Review Body`, `## Editorial Decision`.
5. **Phase 2 output lint.** See §5 below.
6. **Panel cardinality invariant.** After all reviewers complete, verify `len(usable_phase2_outputs) == panel_size`. If any reviewer was dropped, emit `[PANEL-SHRUNK]` and abort the round (see §6).
7. Feed usable Phase 2 outputs into synthesizer (see §7).

## 3. Contract injection

- **Template on disk is frozen.** Do not mutate. Deep-copy into an in-memory dict.
- **Runtime-only fields:** `generated_at`, `agent_amendments.stage_specific_notes`, `agent_amendments.additional_measurement_hints`.
- **Baseline fields are orchestrator-immutable.** Schema cannot enforce this; the orchestrator must not rewrite `acceptance_dimensions` / `failure_conditions` / `measurement_procedure` / `override_ladder` / `mode` / `stage` / `contract_id` / `baseline_version` / `panel_size` between template load and injection. Optional: emit sha256 of baseline-field subset to audit log for drift detection.

## 4. Phase 1 output lint

Structural checks (orchestrator, not validator). On failure retry Phase 1 once with the specific lint gap hinted in the system prompt; second failure aborts that reviewer.

- Required sections in order: `## Contract Paraphrase`, `## Scoring Plan`, terminal `[CONTRACT-ACKNOWLEDGED]`.
- Paraphrase paragraph count ≥ `measurement_procedure.paraphrase_minimum_dimensions` (for `"all"`, one paragraph per dimension; for integer `k`, at least `k` paragraphs each matching a distinct dimension).
- `## Scoring Plan` has one `### <Dn>: <name>` subsection per acceptance dimension (always full coverage, regardless of `paraphrase_minimum_dimensions`).
- Each `scoring_plan` subsection contains lines matching `measurement_procedure.scoring_plan_schema.required`.
- Phase 1 content refers to `<title>`, `<field>`, `<word_count>` only; no specific paper content. Not schema-enforced; behavioural rule in reviewer prompt.

**Lint is structural, not semantic.** A reviewer can in principle pass this lint by emitting generic boilerplate triggers — semantic judgement (whether triggers are concrete and discriminating) is deferred to a post-v3.6.2 judge-agent layer.

On second Phase 1 failure: emit `[PROTOCOL-VIOLATION: reviewer=<role>, contract=<id>, phase1_lint_failed=true]` and mark this reviewer unusable.

## 5. Phase 2 output lint

Structural checks run before handoff to synthesizer. **No Phase 2 retry** (reviewer has seen the paper; a second call is tainted) EXCEPT the multi-dissent case below.

- Required sections: `## Dimension Scores`, `## Failure Condition Checks`, `## Review Body`, `## Editorial Decision`.
- `## Dimension Scores` has one `### <Dn>: <name>` subsection per contract dimension; each carries a value in `$defs.score` (`block | warn | pass`).
- `## Failure Condition Checks` has one subsection per `failure_conditions[]` entry with `fired: true | false`.
- **Multi-dissent rule:** If `## Scoring Plan Dissent` names two or more `dimension_id` entries, orchestrator aborts this reviewer and retries from **Phase 1** once. If the retried Phase 1/2 also multi-dissents, mark the reviewer unusable (`[PROTOCOL-VIOLATION]`). One-dimension-per-reviewer-per-Phase-2-call is the cap.
- **Consistency check (structural):** For every dimension not under dissent, the Phase 2 score must substring-match the reviewer's Phase 1 `scoring_plan` trigger tokens. Vacuous triggers bypass this check — documented limitation.
- `## Editorial Decision` is one of the `action` values derivable from `## Failure Condition Checks` via the synthesizer precedence rule (§8 step 3). Inconsistency marks the reviewer unusable.

On any Phase 2 lint failure other than multi-dissent: emit `[PROTOCOL-VIOLATION]` and mark reviewer unusable. Do not synthesise a substitute score for the synthesizer.

## 6. Multi-reviewer orchestration

- **Independent cycles.** Each of the `panel_size` reviewers runs its own Phase 1 + Phase 2. Failures in one do not pause the others.
- **Panel cardinality invariant (§2 step 6).** After all reviewers complete, if `len(usable_phase2_outputs) < panel_size`, abort the editorial round with `[PANEL-SHRUNK]`. Do not silently recompute `cross_reviewer_quantifier` thresholds against a smaller panel — the contract's published aggregation semantics bind on a specific `panel_size`.
- **Operational monitor.** Track `[PANEL-SHRUNK]` rate in real SR runs. If > 5% of rounds abort in first 3 months, v3.6.3 introduces graceful-degradation fallback.

## 7. Reviewer panel mapping

| mode                          | panel_size | invoked reviewers |
|-------------------------------|------------|-------------------|
| `reviewer_full`               | 5          | EIC + methodology + domain + perspective + DA |
| `reviewer_methodology_focus`  | 2          | EIC + methodology (only) |
| `reviewer_re_review`          | —          | not shipped in v3.6.2; continues pre-v3.6.2 behaviour |
| `reviewer_calibration`        | —          | not shipped in v3.6.2 |
| `reviewer_guided`             | —          | not shipped in v3.6.2 |

The orchestrator uses `mode` to determine the panel and the contract's `panel_size` as the invariant target. SC-11 validator check ensures mode and `panel_size` are consistent.

## 8. Synthesizer three-step protocol

Let `N = contract.panel_size`.

**Step 1 — Build scoring matrix.** For each `acceptance_dimensions[i]`, gather N reviewers' `## Dimension Scores` for that dimension into a length-N array of `$defs.score` values. Dimensions resolved by `id`.

**Step 2 — Evaluate each `failure_conditions[]`.** For each condition:

1. Parse `expression` against the recognised patterns (see §9 vocabulary). Unrecognised → emit `[EXPRESSION-UNRECOGNISED]`, abort synthesizer.
2. Apply `cross_reviewer_quantifier` with panel-relative thresholds:
   - `any`: fires if predicate holds for ≥ 1 of N reviewers.
   - `majority`: for N ≥ 3, fires if ≥ `⌈N/2⌉ + 1`; for N == 2, fires if all 2; for N == 1, vacuous (SC-11 warns).
   - `all`: fires if predicate holds for all N reviewers.
3. Record `{condition_id, fired}`.

**Step 3 — Precedence and decision.** Among fired conditions, pick the one with highest `severity`. Ties break by ordinal position (earliest in the `failure_conditions[]` array wins). Emit its `action` as `editorial_decision`.

**Forbidden operations (synthesizer prompt hard constraint):**
- Introduce aggregation rules not derivable from `cross_reviewer_quantifier` + `severity`.
- Average or vote-aggregate scores within a single dimension unless `cross_reviewer_quantifier: majority` explicitly requests it.
- Soften a fired condition's `action` on post-hoc grounds.
- Synthesise substitute scores for reviewers marked unusable — the round is either complete with `panel_size` usable outputs or `[PANEL-SHRUNK]` aborted.

## 9. Recognised expression vocabulary

Synthesizer recognises the following patterns (with accepted natural-English variants):

1. **Priority-scoped single-match:** `any <priority> dimension scores '<score>'` | `any dimension with priority=<priority> scores '<score>'` | `any <priority>-priority dimension scores '<score>'`
2. **Priority-scoped count-based:** `two or more <priority> dimensions score '<score>' or worse` | `two or more dimensions with priority=<priority> score '<score>' or worse` (ordering `pass` < `warn` < `block`)
3. **Universal over priority:** `every <priority> dimension scores '<score>'`
4. **Single-dimension literal:** `<Dn> scores '<score>'`
5. **Conjunction:** any of the above joined by `AND`

Shipped template coverage:
- `reviewer/full.json`: F1 pattern 1 (bare mandatory), F2 pattern 2, F3 pattern 1 (`high-priority` variant), F0 pattern 3.
- `reviewer/methodology_focus.json`: F1 / F2 / F0 pattern 4 (literal D1).

New expression forms require a PR updating both this §9 and the synthesizer prompt's recognised-pattern list.

## 10. Token cost expectations

Reviewer total calls = `2 × panel_size`. For `reviewer_full` that is 5 → 10 calls; for `reviewer_methodology_focus` 2 → 4. Phase 1 input is small (contract + metadata only); Phase 1 output is short (paraphrase + scoring_plan). Real token bound is well below 2x raw increase.

## 11. Failure modes and diagnostics

Audit-log tags the orchestrator may emit:

| Tag | When | Action |
|-----|------|--------|
| `[CONTRACT-ACKNOWLEDGED]` | normal Phase 1 completion | none (expected) |
| `[PROTOCOL-VIOLATION: phase1_lint_failed=true]` | Phase 1 lint fails twice for a reviewer | mark reviewer unusable |
| `[PROTOCOL-VIOLATION: phase2_lint_failed=<check>]` | Phase 2 lint fails (non multi-dissent) | mark reviewer unusable |
| `[PROTOCOL-VIOLATION: multi_dissent=true]` | Phase 2 has ≥ 2 dissent entries, retry exhausted | mark reviewer unusable |
| `[PANEL-SHRUNK: usable=<k>, panel_size=<N>]` | §6 invariant failed | abort editorial round |
| `[EXPRESSION-UNRECOGNISED: condition_id=<F>, expression=<...>]` | synthesizer step 2.1 | abort synthesizer |
