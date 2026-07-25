# #260 — Experiment Provenance Intake + claim→experiment alignment (schema-first)

**Status**: design (2026-06-08)
**Issue**: [#260](https://github.com/Imbad0202/academic-research-skills/issues/260) (Kong et al. 2026 META #255, Tier B)
**Paper anchor**: Kong et al. 2026 (arXiv:2605.18661, L. Kong, "Roadmap & User Guide") §3.3 + §7.4.3 — AI research systems should include explicit evidence ledgers, experiment provenance, and revision-tracking.
**Sibling precedent**: the three existing non-citation-shaped claim findings (`uncited_assertion` §3.3, `claim_drift` §3.4, `constraint_violation` §3.5) that each ride their own passport aggregate; this adds a fourth for experiment-backed claims.

This is a **schema-driven** change with a deterministic consumer (the claim-alignment audit chain). Unlike the prose-layer siblings #214/#261/#262, it touches JSON Schemas, lints, and the writer-binding contract — so it follows the schema-first discipline stated in §"Schema-first discipline" below.

---

## Boundary (POSITIONING — load-bearing)

ARS deliberately keeps experiment **execution** outside the pipeline. The scholar runs experiments externally and brings results back. This change adds the **intake + alignment** layer only. Explicit non-goals, carried verbatim into every gate's wording:

- Does **not** run experiments.
- Does **not** judge whether an experiment was correctly designed, correctly run, statistically adequate, or reproducible by ARS.
- Does **not** auto-fill provenance — the scholar enters it, or declares "no experiments" explicitly.
- Does **not** require provenance for literature-only pipelines.

The gate checks **disclosure and claim fidelity against declared provenance** — nothing about experiment correctness. This is the line that keeps the change inside POSITIONING; any gate wording that drifts toward "is the experiment good?" is out of scope.

## What ships (two blocks, both this PR)

**Block A — `experiment_provenance[]` intake array** (new optional Material Passport array).
**Block B — claim→experiment alignment** (manifest join field + a fourth ref_slug-less claim-finding aggregate — alongside the three existing ref_slug-less siblings — so experiment-backed claims become auditable under the same ref_slug-less-aggregate precedent that already serves uncited/drift/constraint findings. Note: the *mechanism* differs from citation auditing — experiment claims are judged by the integrity agent against declared provenance at the Stage 2.5/4.5 gate, not by the citation audit agent against retrieved reference text at Stage 4→5; see D4).

## Design decisions (settled via first-party baseline read + cross-model consult 2026-06-08)

The issue's text carries three assumptions that the **tracked** repo does not support; each is corrected here.

1. **`repro_lock` is an inline-prose OBJECT, not a schema file** (`shared/artifact_reproducibility_pattern.md`, validated by a standalone non-CI `check_repro_lock.py`). So "inherit repro_lock" means: nest a `repro_lock`-shaped block inside each `experiment_provenance[]` entry, reusing the existing field design (`schema_version` / `stochasticity_declaration` / `ars_version` / `model` / `prompts` / `materials` / `external_protocols` / `cross_model`). It does **not** mean reusing a shared schema file (there is none). The new `experiment_provenance_entry.schema.json` declares the repro_lock sub-shape itself. **Drift guard (required):** because the shape is now declared in two places (`check_repro_lock.py`'s `REQUIRED_FIELDS` and the nested copy), extract the canonical field set into a shared `scripts/repro_lock_validation.py` that BOTH `check_repro_lock.py` and `check_experiment_provenance.py` import, plus a drift test asserting the nested schema's required keys equal the shared constant. Without this, the two copies silently diverge over time.

2. **The claim manifest has NO experiment pathway today.** `claim_intent_manifest.schema.json` is `additionalProperties:false`; per-claim `planned_refs` carries literature ref slugs only, and `intended_evidence_kind` (`empirical`/`theoretical`/`definitional`/`normative`) does **not** distinguish experiment-from-literature. The join must be **added**, not assumed.

3. **"Path X / Tier-1 required / writer-binding" are not named conventions in the tracked repo.** The repo practices "spec + agent-prompt + schema land in the same PR" but has no canonical name for it. This spec therefore **describes** the discipline (below) rather than citing a name a reader cannot find.

### D1 — Join lives in the claim manifest (not a separate table)

Add an OPTIONAL per-claim field `planned_experiment_ids[]` to `claim_intent_manifest.schema.json`, parallel to `planned_refs`:

```json
"planned_experiment_ids": {
  "type": "array",
  "items": { "type": "string" },
  "minItems": 1,
  "uniqueItems": true,
  "description": "Passport-local experiment_provenance[].experiment_id values the writer intends to support this claim with. Optional-absent; present only on experiment-backed claims. minItems 1 (an empty array is meaningless — omit the field instead)."
}
```

Rationale: the claim manifest is the writer's pre-commitment artifact. Moving experiment intent to a separate table would create a second source of truth outside that artifact. A separate join table is acceptable only as a future backfill aid, never the canonical contract.

- **Optional-absent**, not required-but-empty — literature-only / definitional / theoretical / normative claims do not carry a meaningless `[]`.
- Claim identity stays the scoped pair `(manifest_id, claim_id)`, exactly as `INV-15` already enforces. Unchanged.

### D2 — NO new `intended_evidence_kind` value

Experiment-backed claims keep `intended_evidence_kind: "empirical"`. An experiment is a **source/subtype** of empirical evidence, not a fifth epistemic category. Adding `experimental` would force an enum migration and conditional logic across all three writers, the audit agent, the lints, and the tests — for no semantic gain. The pairing `empirical` + `planned_experiment_ids[present]` carries everything needed.

### D3 — `experiment_id` scoping + the intake-freeze ordering rule

`experiment_id` is flat **within one Material Passport** (a passport is one run). Cross-passport consumers treat the durable key as `(passport_hash, experiment_id)`. A new invariant enforces in-passport uniqueness (EP-INV-1).

**Ordering (lifecycle race — stated explicitly, not assumed):** `experiment_provenance[]` is scholar-entered at Stage 1 intake; `planned_experiment_ids` is writer-emitted later by the manifest emitters. To prevent dangling pointers from a mid-pipeline rename:

- **`experiment_id` values are FROZEN at intake.** Once `experiment_intake_declaration.status == experiments_declared` is set, the `experiment_id` set is the stable key space writers reference. Writers MUST NOT be dispatched until intake is sealed.
- A **post-intake rename / renumber** (e.g. the scholar relabels `exp-001` → `exp-ablation-A` during a Stage-3 revision) is a **re-intake event**: it requires re-running the manifest emitters so `planned_experiment_ids` re-resolves. It is NOT a silent edit. The spec does not let a rename quietly dangle the manifest — EP-INV-2 will FAIL the passport, and that FAIL means "you renamed without re-emitting," not "data corruption."
- **EP-INV-2 doubles as the forward-reference guard:** a writer that pre-commits `planned_experiment_ids: ["exp-007"]` for an experiment the scholar has not yet entered into provenance (writer ran ahead of intake) is caught by the same dangling-pointer FAIL. One invariant covers both the rename race and the forward-reference race.

### D4 — Experiment-claim alignment rides its own ref_slug-less aggregate, computed AT the integrity gate (the break-point fix)

`claim_audit_result.schema.json` **requires** `ref_slug` (+ `anchor_kind`/`anchor_value`). An experiment-backed claim has no `<!--ref:slug-->` citation marker, so it cannot satisfy that shape — exactly the reason `uncited_assertion` / `claim_drift` / `constraint_violation` each ride their own aggregate rather than forcing a sentinel `ref_slug` or relaxing `claim_audit_result.required`. Experiment-claim alignment follows the **same precedent**: a new `experiment_alignment_results[]` aggregate with its own `experiment_alignment_result.schema.json`. (Naming note: the passport already carries six audit aggregates — `claim_audit_results`, `uncited_assertions`, `claim_drifts`, `constraint_violations`, `audit_sampling_summaries`, `uncited_audit_failures`. This is the **fourth ref_slug-less claim-finding aggregate**, not "the fourth aggregate" — an implementer extending the orchestrator hand-off must extend a 6+-entry list, not a 3-entry one.)

**Producer = the integrity verification agent, NOT the claim-alignment audit agent (resolves the stage-ordering race).** The alignment verdict is computed **at the integrity gate (Stage 2.5 sampling / Stage 4.5 full)**, the same stage that blocks on it — mirroring #261's Phase C3, where the figure-fidelity verdict is computed by the integrity agent at Stage 4.5, not pre-computed upstream. This is deliberate: if the verdict were produced by the claim-alignment audit agent at the Stage 4→5 boundary (as an earlier draft assumed), it would land AFTER the Stage 4.5 gate had already run, so the gate could never see it. By making the integrity agent the producer, the row is emitted and gated in the same pass — no cross-stage hand-off of the verdict is needed. The integrity agent already reads the passport's `experiment_provenance[]` and the claim manifest's `planned_experiment_ids`, so it has both join sides in hand at gate time.

The passport array is `experiment_alignment_results[]` (plural, matching every other aggregate key); the entry schema file is `experiment_alignment_result.schema.json` (singular, matching the file-naming convention).

Shape (mirrors the `uncited_assertion` conventions — `EA-` id prefix, scoped-manifest pairing, frozen `rule_version`):

```json
{
  "required": ["finding_id","scoped_manifest_id","claim_id","claim_text",
               "experiment_id","result_pointer","manuscript_locator",
               "alignment_verdict","rationale","judge_model","judge_run_at","rule_version"],
  "properties": {
    "finding_id":        { "pattern": "^EA-[0-9]{3,}$" },
    "scoped_manifest_id":{ "pattern": "^M-...$" },
    "claim_id":          { "pattern": "^C-[0-9]{3,}$" },
    "claim_text":        { "maxLength": 2000 },
    "experiment_id":     { "type": "string", "minLength": 1 },
    "result_pointer":    { "type": "string", "minLength": 1,
                           "description": "Points INTO the provenance entry's reported results (e.g. a planned_vs_executed result_file + metric, or a JSON-Pointer-style locator) — experiment_id alone is too coarse for a claim like 'F1 improved 4.2%'." },
    "manuscript_locator":{ "type": "string", "minLength": 1,
                           "description": "Section path to the claim sentence (e.g. '4. Results > 4.2 Ablations') so a failing alignment can be fixed in the manuscript." },
    "alignment_verdict": { "enum": ["ALIGNED","OVERSTATED","NOT_SUPPORTED_BY_PROVENANCE","PROVENANCE_INSUFFICIENT"] },
    "rationale":         { "type": "string", "minLength": 1 },
    "judge_model":       { "type": "string" },
    "judge_run_at":      { "format": "date-time" },
    "rule_version":      { "const": "EA-v1" }
  }
}
```

**Verdict enum (MECE, experiment-specific — deliberately NOT reusing `claim_audit_result.judgment` names to avoid two `UNSUPPORTED` semantics):**

- `ALIGNED` — the claim is supported by the declared provenance results.
- `OVERSTATED` — the provenance supports a *weaker* version of the claim (the claim says more than the results show).
- `NOT_SUPPORTED_BY_PROVENANCE` — the referenced experiment ran but its results do not support the claim: no relevant result, contradicts, irrelevant, **OR the claim contradicts a declared `negative_results[]` entry**, **OR every `planned_vs_executed[]` entry for the referenced experiment is `executed:false`** (the claim relies on an experiment that never ran).
- `PROVENANCE_INSUFFICIENT` — the provenance entry exists but lacks the detail needed to judge (the judge ran but cannot reach a support verdict).

**The verdict judge MUST cross-check three provenance regions, not just the reported result `result_pointer` points at:** (1) the pointed-at result; (2) the experiment's `negative_results[]` — a claim that asserts an effect a `negative_results[]` entry says was null/absent is `NOT_SUPPORTED_BY_PROVENANCE`, NOT merely a D6 check-4 advisory note (the advisory is for *disclosure visibility*; the verdict is for *claim fidelity* — both fire, they are different obligations); (3) the experiment's `planned_vs_executed[]` — a claim resting on an experiment whose entries are all `executed:false` is `NOT_SUPPORTED_BY_PROVENANCE` regardless of what other prose says. These two derivation rules (negative-result-contradiction ⟹ NOT_SUPPORTED; all-skipped ⟹ NOT_SUPPORTED) bind the structured verdict to the same conclusion the D6 prose heuristic reaches, so the deterministic and heuristic layers cannot diverge (the divergence fresh-eye flagged).

**Mixed-evidence claims get TWO rows, and worst-verdict-wins.** A claim carrying BOTH `planned_refs` and `planned_experiment_ids` (allowed by EP-INV-3) is audited by both paths: a `claim_audit_results[]` row (citation path) AND an `experiment_alignment_results[]` row (experiment path), keyed by the same `(scoped_manifest_id, claim_id)`. This is intentional, not double-counting to be deduped. The gate decision combines them by **worst-verdict-wins** (mirroring C3's weakest-sub-claim precedence): if the citation path is `SUPPORTED` but the experiment path is `OVERSTATED`, the claim **blocks** — a claim is only clean when every evidence path it pre-committed to clears. The Stage-6 defect histogram counts the claim once per *failing path* (a claim that fails both paths is two findings, by design — they are distinct defects to fix), but a claim's *pass/block* status is a single worst-verdict-wins decision.

**`PROVENANCE_MISSING` is NOT a verdict.** A claim referencing an `experiment_id` with no matching `experiment_provenance[]` entry is a **structural failure caught by EP-INV-2 / EA-INV-2**, not a judge verdict — modelling it as a verdict would force fake `judge_model` / `judge_run_at` values for a row where no judge ran, and would collide with D6's well-formedness short-circuit (which already FAILs before the judge runs). The dangling pointer surfaces as a lint/gate structural failure; no EA row with a judge verdict is emitted for it. The `claim_audit_result.required` shape is **untouched** — no sentinel, no relaxation.

### D5 — New invariants (do NOT mutate existing M-INV / INV-15/17 / U-INV)

- **EP-INV-1**: `experiment_provenance[].experiment_id` unique within the passport.
- **EP-INV-2**: every `planned_experiment_ids[]` value resolves to exactly one `experiment_provenance[].experiment_id` (cross-array integrity, mirroring INV-15's claim↔manifest check).
- **EP-INV-3**: `planned_experiment_ids` present ⟹ the owning claim's `intended_evidence_kind == "empirical"`. This does NOT forbid mixed evidence — a claim may carry BOTH `planned_refs` (literature) AND `planned_experiment_ids` (own experiment); both back an empirical claim. The lint only forbids experiment ids on a non-empirical (`theoretical`/`definitional`/`normative`) claim.
- **EA-INV-1**: `experiment_alignment_results[].finding_id` unique within the passport.
- **EA-INV-2**: in an `experiment_alignment_results` row, `(scoped_manifest_id, claim_id)` resolves to a real manifest claim AND `experiment_id` resolves to a real `experiment_provenance[]` entry. A dangling `experiment_id` is a structural FAIL here (and at EP-INV-2 from the manifest side) — it is never represented as a judge verdict.
- **EP-INV-4 (declaration↔provenance symmetry)**: `experiment_intake_declaration.status == no_experiments_declared` ⟹ `experiment_provenance[]` is absent or empty; `status == experiments_declared` ⟹ `experiment_provenance[]` is non-empty. This is the deterministic structural half of D7's FAIL conditions #2 and #3 (the prose-contradiction direction stays a gate heuristic).
- **EP-INV-5 (declaration well-formedness when present)** *(added at ship-gate review — cross-model consult flagged that a malformed declaration slipped past EP-INV-4, which only fires on the two known status literals)*: when `experiment_intake_declaration` IS present, its `status` ∈ `{experiments_declared, no_experiments_declared, legacy_unknown}`, `declared_by == "scholar"` (an intake decision, never an agent emission), and `declared_at` is a non-empty date-time string. This is the deterministic *shape* half the symmetry check does not cover; a `status: "garbage"` declaration now FAILs deterministically instead of slipping through silently. EP-INV-5 does NOT decide presence/absence — the `ars_version` legacy gate (a Stage-1 gate check, D7) owns that, deliberately kept at the gate layer because the #260 release version it compares against is frozen at ship time, not at intake.

All new invariants land in `scripts/check_claim_audit_consistency.py` alongside the existing ones (same lint, new names — no existing invariant's semantics change).

### D6 — Integrity gate mirrors Phase C3 (narrow, disclosure-only)

A new Phase in `integrity_verification_agent.md` (Mode 1 Stage 2.5 sampling / Mode 2 Stage 4.5 full), mirroring C3's structure:

0. **Well-formedness short-circuit**: a malformed referenced `experiment_provenance[]` entry (missing a required key) → FAIL before semantic checks; checks 1-4 do not run. **Absent-key rule (ported from C3, `integrity_verification_agent.md`):** the `negative_results` and `known_limitations` keys MUST be PRESENT (value MAY be `[]`). An ABSENT key is malformed → FAIL; an empty `[]` is well-formed and routes to the check-4 advisory. Without this, omitting `negative_results` entirely would silently bypass the check-4 advisory — the exact skip C3 was hardened against.
1. **Completeness**: referenced `experiment_id`s resolve; required provenance fields present.
2. **Planned-vs-executed fidelity**: every `planned_vs_executed[]` entry with `executed:false` has a `skip_reason`; manuscript claims do not rely on a skipped/non-executed experiment as if it ran (→ `NOT_SUPPORTED_BY_PROVENANCE`, see D4 derivation rule).
3. **Claim-result fidelity**: manuscript claims do not overstate what the provenance reports (`OVERSTATED`), and do not contradict a declared `negative_results[]` entry (`NOT_SUPPORTED_BY_PROVENANCE`) — both feed `experiment_alignment_results[]`, computed here at the gate (D4).
4. **Negative/limitation visibility** (advisory): declared `negative_results[]` and material `known_limitations[]` are surfaced in Results / Discussion / Limitations prose. This advisory is about *disclosure*; a claim that *contradicts* a negative result is the separate check-3 FAIL, not this advisory.

Severity: FAIL (block) for malformed / unresolved reference / claim-on-skipped-experiment / overstatement; PASS-WITH-NOTES (advisory, never silent) for empty negative-results disclosure or a legacy passport with no provenance block. **Anti-skip**: a passport that references experiment results but omits `experiment_provenance[]` is a FAIL, not advisory (mirrors C3's omitted-trace rule).

**Boundary wording in the gate (verbatim)**: "This check verifies disclosure and claim-to-provenance fidelity. It does not judge whether the experiment was correctly designed, run, statistically adequate, or reproducible by ARS." (Keeps D6 inside POSITIONING — the gate reads prose, it does not evaluate experiments.)

This gates `experiment_provenance[]` while `repro_lock` stays passive (un-gated) — not an inconsistency: `repro_lock` documents LLM/artifact reproducibility settings; `experiment_provenance[]` is evidence backing manuscript claims. Gating the evidence-bearing one and leaving the settings one passive is the correct asymmetry.

**Which gate blocks (resolving the D6-vs-Out-of-scope tension):** the FAILs above block at the **integrity verification gate** (Stage 2.5/4.5) — that is where this check lives and where it is terminal. The **formatter** does not re-evaluate experiment alignment; its only role (if any) is surfacing the `experiment_alignment_results[]` annotations, not blocking on them. So "FAIL blocks" (integrity gate) and "formatter consumption stays advisory/surface-only" (Out of scope) are both true because they name two different gates. The `claim_audit_result` finalizer chain is unaffected.

### D7 — Stage 1 intake detection + a persisted intake declaration (closes the anti-skip circularity)

The naive design — "gate FAILs if the passport references experiments but omits `experiment_provenance[]`" — is **not deterministically enforceable**: the only schema-visible signal would be `planned_experiment_ids`, which is itself optional (D1). If the scholar runs experiments but forgets BOTH the provenance array AND the join field, the gate has no schema-visible signal at all and can only guess from prose. The very signal that would trip the gate is the thing that was forgotten — a circular hole.

**Fix: a persisted passport-level `experiment_intake_declaration`.** New optional Schema-9 object (NOT inside any entry — a passport-level field, like `repro_lock`):

```yaml
experiment_intake_declaration:
  status: "experiments_declared" | "no_experiments_declared" | "legacy_unknown"
  declared_at: "<date-time>"
  declared_by: "scholar"      # always scholar — this is an intake decision, not an agent emission
```

- **The legacy boundary is deterministic AND fail-closed — the default is "treat as post-#260", not "treat as legacy".** This check is fail-closed by design: wrongly blocking an old passport costs the scholar a one-line declaration; wrongly waving through a new run that skipped provenance defeats the whole gate. So the burden of proof is on being legacy, not on being current:
  - A passport is `legacy_unknown` (advisory) **only with POSITIVE proof it predates #260** — `repro_lock.ars_version` present AND `< the #260 release constant` (frozen in the gate at ship time).
  - **Everything else is treated as post-#260**, including a passport with no `repro_lock` block, or a `repro_lock` with no `ars_version`. Version-unprovable ≠ legacy. For these, `experiment_intake_declaration` is REQUIRED and its absence is a **FAIL**. This shuts the back door codex flagged: a new run cannot dodge the declaration by omitting `repro_lock` to make its version unprovable — unprovable defaults to post-#260, so the declaration is still required.
  - `legacy_unknown` therefore cannot be *chosen* or *reached by omission* by a new run; it is reachable only by an artifact carrying positive pre-#260 version proof.
- A post-#260 declaration MUST be either `experiments_declared` (and then `experiment_provenance[]` must be present and non-empty) or `no_experiments_declared`.
- **Now the gate is deterministic**, with four FAIL conditions (the first three structural/deterministic, the fourth heuristic):
  1. treated-as-post-#260 AND the declaration is absent;
  2. `status == experiments_declared` but `experiment_provenance[]` is absent/empty;
  3. **`status == no_experiments_declared` but `experiment_provenance[]` is non-empty** (the symmetric structural partner to #2 — a populated provenance array directly contradicting the declaration is a one-line deterministic FAIL, not left to the prose heuristic; this is EP-INV check, see D5);
  4. the manuscript prose/manifest shows own-experiment claims but `status == no_experiments_declared` (heuristic, per the minimum-signal set below).

**Who runs the prose-contradicts-declaration check, and the minimum signals (so it is auditable, not hand-wavy):** the `integrity_verification_agent`'s new Phase runs it (Stage 2.5 sampling / Stage 4.5 full). The minimum signal set that counts as "the manuscript shows own-experiment claims": a manifest claim with `intended_evidence_kind == empirical` AND `planned_experiment_ids` present, OR a Results-section sentence reporting a first-person experimental outcome (own metric/ablation/run) with no `<!--ref:slug-->` citation marker. Either signal, against `status == no_experiments_declared`, is the contradiction FAIL. The heuristic drives *detection*; the declaration + ars_version give the gate hard anchors so the verdict is reproducible.

`README.md` Experiment Agent flow + the Stage 1 intake prompt gain: detect experiment claims, set the declaration, and prompt the scholar to enter `experiment_provenance[]` (or declare `no_experiments_declared`). **JSON Schema still cannot express "provenance required iff there's an experiment claim"** — but it CAN express "if `status == experiments_declared` then `experiment_provenance[]` is required" (a local conditional), and the ars_version legacy boundary makes "declaration required for post-#260 passports" a deterministic gate check rather than a schema constraint. Together these are the load-bearing halves.

**Literature-only pipelines must still emit the declaration (fail-closed consequence — stated, not hidden).** Because the default is treat-as-post-#260, a pure-literature run (e.g. `deep-research lit-review`) that touches zero experiments STILL needs `experiment_intake_declaration: { status: no_experiments_declared }`, or it FAILs condition #1. The Boundary section's "does not require *provenance* for literature-only pipelines" stays true (no `experiment_provenance[]` needed) — but a one-line declaration IS required. **Producer:** the declaration is set by whichever agent owns Stage 1 intake for that entry path — the intake/orchestrator layer, NOT the three manifest writers (they emit `planned_experiment_ids`, a different field). Every entry path that produces a post-#260 passport (full pipeline, lit-review, standalone draft) must set the declaration at its intake point. A regression test pins that a clean literature-only passport either carries `no_experiments_declared` or is taught to emit it — so this fail-closed gate does not silently break the most common pipeline.

## Schema-first discipline (the writer-binding rule, stated plainly)

> Any field promoted to schema-**required** must have every authoritative producer taught to emit it **in the same PR**, with tests. Otherwise the schema declares a contract no writer satisfies (a reverse-invariant gap).

For this change: `planned_experiment_ids` is **optional-absent**, so it is NOT promoted to required — meaning the writer-binding obligation here is the lighter "teach the writers to emit it WHEN an experiment backs a claim" (a prompt instruction in the three manifest emitters), not a schema-required gate. The three emitters are `synthesis_agent`, `draft_writer_agent`, `report_compiler_agent` (the `emitted_by` enum). All three get the emission instruction in this PR. `experiment_provenance[]` itself is scholar-entered at intake, not writer-emitted, so it has no writer-binding obligation — its producer is the intake flow (D7).

## Change set

| Artifact | Action |
|---|---|
| `shared/contracts/passport/experiment_provenance_entry.schema.json` | CREATE — array-entry schema incl. nested repro_lock sub-shape, `planned_vs_executed[]`, `negative_results[]`, `known_limitations[]` |
| `shared/contracts/passport/experiment_alignment_result.schema.json` | CREATE — fourth ref_slug-less claim-finding aggregate (D4); array key `experiment_alignment_results[]`, verdict enum {ALIGNED, OVERSTATED, NOT_SUPPORTED_BY_PROVENANCE, PROVENANCE_INSUFFICIENT}, `result_pointer` + `manuscript_locator` + frozen `rule_version` |
| `shared/contracts/passport/claim_intent_manifest.schema.json` | EDIT — add optional `planned_experiment_ids[]` per-claim (D1) |
| `shared/handoff_schemas.md` | EDIT — Schema 9 optional-fields rows for `experiment_provenance[]` + `experiment_alignment_results[]` + the passport-level `experiment_intake_declaration` object (D7) + named narrative subsection |
| `academic-pipeline/agents/integrity_verification_agent.md` | EDIT — new Phase (D6) **produces** `experiment_alignment_results[]` (verdict computed at the gate, D4) + blocks; declaration-anchored anti-skip (D7); join `planned_experiment_ids` → provenance |
| `academic-pipeline/agents/claim_ref_alignment_audit_agent.md` | EDIT — aware of `planned_experiment_ids` so experiment-only claims are NOT misrouted into `claim_audit_results[]`/`uncited_assertions[]`; does NOT itself emit the alignment verdict (that is the integrity gate's job, D4) |
| `academic-pipeline/agents/pipeline_orchestrator_agent.md` | EDIT — add `experiment_alignment_results[]` to the explicit aggregate hand-off list (without this the new aggregate is emitted into a void — the orchestrator already enumerates every aggregate it passes; a missing entry stays silent in production) + carry `experiment_intake_declaration` forward |
| `deep-research/agents/synthesis_agent.md`, `academic-paper/agents/draft_writer_agent.md`, `.../report_compiler_agent.md` | EDIT — emit `planned_experiment_ids` when an experiment backs a claim (writer-binding) |
| `README.md` (+ language mirrors) | EDIT — Stage 1 intake detection + set `experiment_intake_declaration` (D7) |
| `scripts/repro_lock_validation.py` | CREATE — shared canonical repro_lock field set imported by both checkers (drift guard) |
| `scripts/check_repro_lock.py` | EDIT — import the shared field set (no behavior change; removes the duplicate constant) |
| `scripts/check_claim_audit_consistency.py` | EDIT — add EP-INV-1/2/3/4/5 + EA-INV-1/2 (cross-array invariants live here; EP-INV-5 declaration well-formedness added at ship-gate) |
| `scripts/check_experiment_provenance.py` | CREATE — standalone validator for `experiment_provenance_entry` *shape only* (mirrors `check_repro_lock.py`); cross-array EP/EA invariants stay in `check_claim_audit_consistency.py` — the two scripts do not duplicate invariant logic |
| `examples/passport_with_experiment_provenance.yaml` | CREATE — ML paper, 2 experiments, full provenance + claim manifest cross-reference (incl. one mixed-evidence claim with both `planned_refs` and `planned_experiment_ids`) + one OVERSTATED alignment row |
| `CHANGELOG.md` | `[Unreleased]` entry |

## INVARIANTS (summary — full text in the lint)

EP-INV-1 (experiment_id unique/passport) · EP-INV-2 (planned_experiment_ids resolve; doubles as rename + forward-reference guard) · EP-INV-3 (experiment ids ⟹ empirical; mixed literature+experiment allowed) · EP-INV-4 (declaration↔provenance symmetry) · EP-INV-5 (declaration well-formedness when present: status enum / declared_by==scholar / non-empty declared_at — ship-gate addition) · EA-INV-1 (finding_id unique) · EA-INV-2 (alignment row references resolve; dangling id = structural FAIL, never a verdict). No existing M-INV/INV-15/17/U-INV semantics change.

## Test strategy

- Schema positive/negative tests for both new schemas + the manifest edit (valid passport; missing required key; dangling experiment_id; `planned_experiment_ids` with non-empirical kind → EP-INV-3 fail; absent `negative_results`/`known_limitations` key → malformed FAIL vs empty `[]` → well-formed advisory).
- **Fail-closed legacy-boundary fixtures (the most security-relevant logic — was untested):** (a) no `repro_lock` → declaration REQUIRED, absent = FAIL; (b) `repro_lock` present but no `ars_version` → declaration REQUIRED; (c) `ars_version < #260 constant` → `legacy_unknown` advisory allowed; (d) `ars_version ≥ constant` → declaration required. Plus EP-INV-4 symmetry: `no_experiments_declared` + non-empty provenance → FAIL; `experiments_declared` + empty provenance → FAIL.
- **Mixed-evidence two-row case:** a claim with both `planned_refs` and `planned_experiment_ids` produces one `claim_audit_results[]` row AND one `experiment_alignment_results[]` row; assert worst-verdict-wins blocks when the experiment path is `OVERSTATED` even if the citation path is `SUPPORTED`.
- **Verdict-derivation tests:** claim contradicting a `negative_results[]` entry → `NOT_SUPPORTED_BY_PROVENANCE` (not just advisory); claim on an all-`executed:false` experiment → `NOT_SUPPORTED_BY_PROVENANCE`.
- **Mutation test**: a trivial accept-all replacement of each new invariant must flip the negative fixtures to PASS (proving the invariant is load-bearing, not vacuous).
- **Reverse-invariant test**: pins "the three manifest writers' prompts contain the `planned_experiment_ids` emission instruction" + "every post-#260 entry path sets `experiment_intake_declaration`" (so a future schema-required promotion can't silently drift ahead of the producers).
- **Literature-only regression:** a clean lit-review passport either carries `no_experiments_declared` or is taught to emit it — confirm the fail-closed gate does not break the most common pipeline.
- `claim_audit_result.required` regression: confirm experiment-**only** claims do NOT appear in `claim_audit_results[]` (they ride the EA aggregate), while mixed-evidence claims correctly appear in both, and the existing chain is byte-unchanged for literature-only claims.
- Full suite green (baseline 2291) + the new tests.

## Out of scope (forward work)

- Experiment correctness / statistical adequacy verification (explicit non-goal).
- Auto-fill of provenance from a repo (scholar-entered only).
- Promoting `planned_experiment_ids` to schema-required (would require the full writer-binding promotion in one PR; deferred unless a future issue wants mandatory experiment intake).
- Formatter-gate consumption of `experiment_alignment_results[]` beyond surfacing (the gate decision stays advisory at this layer).

## Verification (paper-derived discipline)

Full citation to Kong et al. 2026 (L. Kong, "Roadmap & User Guide", arXiv:2605.18661, §3.3 + §7.4.3). No internal / personal / institutional content; no `.local-plans/` content mirrored into the public change; leak scan clean.
