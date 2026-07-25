# ARS v3.8 — Issue #103 `claim_ref_alignment_audit_agent` Implementation Spec

**Date:** 2026-05-15
**Issue:** [#103](https://github.com/Imbad0202/academic-research-skills/issues/103)
**Companion decision doc:** `2026-05-15-issue-103-claim-alignment-audit-decision.md`
**Target release:** v3.8

This spec implements the eight decisions in the companion decision doc. Read the decision doc first — it carries the load-bearing reasons; this spec carries the executable surface.

---

## 1. In-scope deliverables

Numbered list aligned to the implementation surfaces in #103 issue body + decision-doc adjustments.

1. **`academic-pipeline/agents/claim_ref_alignment_audit_agent.md`** — new agent prompt. Estimated 350-500 lines.
2. **`shared/contracts/passport/claim_audit_result.schema.json`** — per-claim audit result entry schema (judge-evaluated citation-bound findings).
3. **`shared/contracts/passport/claim_intent_manifest.schema.json`** — per-agent-invocation manifest entry schema.
3a. **`shared/contracts/passport/uncited_assertion.schema.json`** — per uncited-sentence finding entry schema (separate from `claim_audit_result` because there's no `ref_slug` to bind).
3b. **`shared/contracts/passport/claim_drift.schema.json`** — per claim-intent-drift finding entry schema (separate from `claim_audit_result` because drift is detected by manifest set-diff, not by judge invocation; see §3.4 rationale).
3c. **`shared/contracts/passport/constraint_violation.schema.json`** — per uncited-claim-violates-constraint finding entry schema (separate from `claim_audit_result` because no `ref_slug` exists, but HIGH-WARN gate-refuse semantics differ from LOW-WARN `uncited_assertion`; see §3.5 rationale).
4. **`academic-pipeline/agents/pipeline_orchestrator_agent.md`** — new §3.6 "Claim-Faithfulness Audit Gate (v3.8)". Dispatch wiring for the new agent. Finalizer integration extended to 8-row + advisory tier.
5. **`academic-paper/agents/formatter_agent.md`** — Cite-Time Provenance Hard Gate extended with FIVE new HIGH-WARN refusal classes mirroring §5 finalizer matrix (8-row matrix + constraint_violations[] aggregate): HIGH-WARN-CLAIM-NOT-SUPPORTED, HIGH-WARN-NEGATIVE-CONSTRAINT-VIOLATION, HIGH-WARN-FABRICATED-REFERENCE, HIGH-WARN-CLAIM-AUDIT-ANCHORLESS, HIGH-WARN-CONSTRAINT-VIOLATION-UNCITED. The formatter's existing v3.7.1/v3.7.3 refusal rules remain unchanged; new classes append to the existing REFUSE list. §5 matrix + constraint_violations[] are the source of truth — any new HIGH-WARN class added in future revisions MUST be mirrored here, enforced by a §6 lint rule.
6. **`academic-paper/agents/draft_writer_agent.md`** + **`deep-research/agents/synthesis_agent.md`** + **`deep-research/agents/report_compiler_agent.md`** — new "Claim Intent Manifest Emission (v3.8)" sibling heading following the existing v3.7.3 "Three-Layer Citation Emission" heading. PATTERN PROTECTION (v3.6.7) blocks stay byte-equivalent.
7. **`academic-pipeline/references/claim_audit_calibration_protocol.md`** — new file (modeled on `shared/contracts/reviewer/` calibration convention).
8. **`scripts/check_claim_audit_consistency.py`** — new lint enforcing per-claim invariants (anchor presence, defect_stage presence, precedence rules, audit_status/defect_stage coherence).
9. **CI wiring** — extend `.github/workflows/spec-consistency.yml` (or matching workflow) to call the new lint.
10. **Tests** — `scripts/test_claim_audit_schema.py` covers both schema validation and `check_claim_audit_consistency.py` lint coverage via subprocess pattern (T-S1..T-S8 invariants); plus per-stage unittest modules (`scripts/test_claim_audit_pipeline.py`, `scripts/test_uncited_assertion.py`, `scripts/test_claim_intent_manifest.py`, `scripts/test_claim_audit_finalizer.py`, `scripts/test_e2e_claim_audit.py` for the 5-citation end-to-end synthetic-paper test, `scripts/test_claim_audit_calibration.py`).
11. **CHANGELOG entry** + ROADMAP §3.8 anchor + decision-log entry.

## 2. Out of scope

Restated from decision doc §4, for cross-reference:

- RubricEM reflection meta-policy (post-v3.8)
- Evolving rubric buffer (post-v3.8)
- Rubric discrimination-power audit (→ #89)
- `defect_stage` accuracy measurement (→ #89 / gold fixtures)
- L3-2 contamination signals (→ #105 closed / #102 v3.7.4)
- Cross-paper claim-graph analysis (no issue yet; post-v3.8)

## 3. Schemas

### 3.1 `claim_audit_result.schema.json`

Per-claim audit result. One entry per audited citation in the passport `claim_audit_results[]` aggregate array.

**Required fields:**

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "https://github.com/Imbad0202/academic-research-skills/shared/contracts/passport/claim_audit_result.schema.json",
  "title": "Material Passport Claim Audit Result Entry",
  "type": "object",
  "additionalProperties": false,
  "required": [
    "claim_id",
    "scoped_manifest_id",
    "claim_text",
    "ref_slug",
    "anchor_kind",
    "anchor_value",
    "judgment",
    "audit_status",
    "defect_stage",
    "rationale",
    "judge_model",
    "judge_run_at",
    "ref_retrieval_method"
  ],
  "properties": {
    "claim_id": { "type": "string", "pattern": "^C-[0-9]{3,}$" },
    "scoped_manifest_id": {
      "type": "string",
      "pattern": "^M-[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z-[0-9a-f]{4}$",
      "description": "Points to the owning claim_intent_manifest.manifest_id. The (scoped_manifest_id, claim_id) pair uniquely identifies the claim, since C-001 may collide across manifests in the same run. Enforced by INV-15 (cross-array integrity). For audits running in MANIFEST-MISSING fallback (no manifest present), scoped_manifest_id is the sentinel `M-0000-00-00T00:00:00Z-0000`."
    },
    "claim_text": { "type": "string", "minLength": 1, "maxLength": 2000 },
    "ref_slug": { "type": "string", "minLength": 1 },
    "anchor_kind": { "enum": ["quote", "page", "section", "paragraph", "none"] },
    "anchor_value": { "type": "string" },
    "judgment": { "enum": ["SUPPORTED", "UNSUPPORTED", "AMBIGUOUS", "RETRIEVAL_FAILED"] },
    "audit_status": { "enum": ["completed", "inconclusive"] },
    "defect_stage": {
      "comment": "Three categories of finding are intentionally NOT defect_stages of claim_audit_result and use their own §3.3/§3.4/§3.5 entry-type schemas: (a) uncited_assertion findings — no ref_slug to evaluate, see uncited_assertion.schema.json (§3.3); (b) claim_intent drift findings — detected by manifest set-diff not by judge, see claim_drift.schema.json (§3.4) (drift never produces a claim_audit_result row because the judge is never invoked for these — the only signal is intended ≠ emitted manifest-set difference); (c) uncited constraint violations — claim has no ref_slug AND violates an MNC/NC rule, see constraint_violation.schema.json (§3.5) (HIGH-WARN gate-refuse but no ref to bind into a claim_audit_result row). 8 values listed below.",
      "enum": [
        "retrieval_existence",
        "metadata",
        "source_description",
        "citation_anchor",
        "synthesis_overclaim",
        "negative_constraint_violation",
        "not_applicable",
        null
      ]
    },
    "rationale": { "type": "string", "minLength": 1, "maxLength": 2000 },
    "judge_model": { "type": "string", "minLength": 1 },
    "judge_run_at": { "type": "string", "format": "date-time" },
    "ref_retrieval_method": { "enum": ["api", "manual_pdf", "failed", "not_attempted", "not_found", "audit_tool_failure"] },
    "upstream_owner_agent": {
      "enum": [
        "synthesis_agent",
        "draft_writer_agent",
        "report_compiler_agent",
        null
      ]
    },
    "violated_constraint_id": {
      "type": ["string", "null"],
      "pattern": "^(NC-C[0-9]{3,}-[0-9]+|MNC-[0-9]+)$"
    },
    "upstream_dispute": {
      "type": ["string", "null"],
      "maxLength": 1000
    },
    "audit_run_id": {
      "type": "string",
      "pattern": "^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z-[0-9a-f]{4}$"
    }
  }
}
```

**Allowed (`judgment`, `audit_status`, `defect_stage`) matrix (enforced in `check_claim_audit_consistency.py`, NOT in schema). Any combination outside the table is a lint violation:**

| `judgment` | `audit_status` | `defect_stage` | Notes |
|---|---|---|---|
| SUPPORTED | completed | `null` | INV-1 |
| AMBIGUOUS | completed | source_description, citation_anchor, synthesis_overclaim, or `null` | drift never AMBIGUOUS; constraints binary |
| UNSUPPORTED | completed | source_description | wrong paraphrase of source content |
| UNSUPPORTED | completed | metadata | reference exists but author/year/title wrong |
| UNSUPPORTED | completed | citation_anchor | source correct, anchor points to wrong passage |
| UNSUPPORTED | completed | synthesis_overclaim | source correct, draft over-strengthens claim |
| UNSUPPORTED | completed | negative_constraint_violation | INV-8, requires `violated_constraint_id` |
| RETRIEVAL_FAILED | completed | retrieval_existence | reference genuinely does not exist (fabricated) |
| RETRIEVAL_FAILED | inconclusive | not_applicable | covers (a) anchor=none INV-6 and (b) paywalled INV-10 |

**`uncited_assertion` is NOT a `claim_audit_result` row** — uncited claims have no `ref_slug` to populate the required field. They emit into a separate aggregate `uncited_assertions[]` (schema in §3.3 below) and feed the same Stage 4→5 finalizer integration. This sidesteps a schema-vs-required-field deadlock: `claim_audit_result.ref_slug` stays required for citation-bound audits; `uncited_assertions[]` carries its own entry-type schema with no `ref_slug` field.

**Cross-field invariants:**

- INV-1: `judgment=SUPPORTED` → `defect_stage=null` AND `violated_constraint_id=null` AND `audit_status=completed`
- INV-2: `judgment=UNSUPPORTED` → `defect_stage` ∈ `{source_description, metadata, citation_anchor, synthesis_overclaim, negative_constraint_violation}` AND `defect_stage ≠ null` AND `audit_status=completed` (claim_intent intentionally absent — drift detection is set-diff over manifest, never a judge verdict; drift findings emit into `claim_drifts[]` per §3.4, not into `claim_audit_results[]`)
- INV-3: `judgment=AMBIGUOUS` → `defect_stage` ∈ `{source_description, citation_anchor, synthesis_overclaim, null}` AND `audit_status=completed` (drift excluded — drift is unambiguous when manifest exists; metadata excluded — bibliographic correctness is binary; constraint violations excluded — INV-8 binary)
- INV-4: `judgment=RETRIEVAL_FAILED` AND `audit_status=inconclusive` → `defect_stage=not_applicable`
- INV-5: `judgment=RETRIEVAL_FAILED` AND `audit_status=completed` → `defect_stage=retrieval_existence` (reference genuinely does not exist, distinct from tool failure)
- INV-6: `anchor_kind=none` → `judgment=RETRIEVAL_FAILED`, `audit_status=inconclusive`, `defect_stage=not_applicable`, `ref_retrieval_method=not_attempted`, rationale begins with `v3.7.3 R-L3-1-A violation` (per D1)
- INV-7: `defect_stage=negative_constraint_violation` → `violated_constraint_id ≠ null`
- INV-8: `defect_stage=negative_constraint_violation` → `judgment=UNSUPPORTED` (one-way; negative-constraint violations are always classified UNSUPPORTED, never AMBIGUOUS — explicit author rules are binary. The converse does NOT hold: UNSUPPORTED admits 6 other defect_stages per INV-2.)
- INV-9: `upstream_dispute ≠ null` → `defect_stage ≠ null` AND `defect_stage ≠ not_applicable` (disputes are only meaningful for substantive defect classifications)
- INV-10: `ref_retrieval_method=failed` → `judgment=RETRIEVAL_FAILED` AND `audit_status=inconclusive` AND `defect_stage=not_applicable` (paywall path)
- INV-11: `ref_retrieval_method=not_attempted` ↔ `anchor_kind=none` AND INV-6 holds (anchor=none skips retrieval)
- INV-12: `ref_retrieval_method=not_found` ↔ `judgment=RETRIEVAL_FAILED` AND `audit_status=completed` AND `defect_stage=retrieval_existence` (fabricated reference path)
- INV-13: `defect_stage=metadata` → `judgment=UNSUPPORTED` AND `audit_status=completed` AND `ref_retrieval_method` ∈ `{api, manual_pdf}` (retrieval succeeded but metadata mismatch identified during judging)
- INV-14: `ref_retrieval_method=audit_tool_failure` ↔ `judgment=RETRIEVAL_FAILED` AND `audit_status=inconclusive` AND `defect_stage=not_applicable` AND rationale begins with a fault-class tag in `{judge_timeout, judge_api_error, judge_parse_error, cache_corruption, retrieval_api_error, retrieval_timeout, retrieval_network_error}` followed by a colon and free-form detail (audit-infrastructure / transient failure distinct from access-restricted retrieval; finalizer emits `[CLAIM-AUDIT-TOOL-FAILURE]` MED-WARN advisory; gate passes — retry-next-pass remediation. Discriminator from `ref_retrieval_method=failed`: permanence — paywall/license is stable, API 5xx/timeout is transient.)
- INV-15: For every `claim_audit_result` entry, `(scoped_manifest_id, claim_id)` MUST either (a) match some `claims[].claim_id` in the `claim_intent_manifests[]` entry whose `manifest_id == scoped_manifest_id`, or (b) carry the sentinel `scoped_manifest_id = M-0000-00-00T00:00:00Z-0000` indicating the MANIFEST-MISSING fallback path. Dangling references (scoped_manifest_id present but no matching manifest entry, with non-sentinel value) are a lint violation.
- INV-16: For every `claim_audit_result` entry with `anchor_kind ≠ none`, the URL-decoded `anchor_value` MUST be non-empty (after stripping leading/trailing whitespace). A stale or malformed marker like `<!--anchor:page:-->` would otherwise validate as an auditable locator and bypass the anchorless gate, but v3.7.3 §3.1 firm rule R-L3-1-A treats empty non-`none` anchors as semantically equivalent to `none`. Empty non-`none` `anchor_value` is a lint violation. Per `anchor_kind=none` the value is `""` (sentinel) and INV-6 governs — INV-16 only applies when `anchor_kind ∈ {quote, page, section, paragraph}`.
- INV-17: Constraint id parse rule (canonical). `NC-C{n}-{m}` where `{n}` is the **same** digit sequence used in the corresponding `claim_id` (`C-{n}`). Example: `claim_id=C-001` pairs with constraint ids `NC-C001-1`, `NC-C001-2`, etc. The pattern intentionally does NOT include a hyphen between `C` and `{n}` (i.e., `NC-C001-1`, NOT `NC-C-001-1`) because the canonical claim_id form `C-001` already establishes `001` as the joinable key — lint splits the NC string on the SECOND `-` (after `NC`), strips the leading `C`, then matches against the claim_id digit suffix. M-INV-2 / CV-INV-2 / CV-INV-3 all resolve through this parse rule. Zero-padding is consistent across both forms (`C-001` ↔ `NC-C001-1`); pattern `^NC-C[0-9]{3,}-[0-9]+$` enforces ≥3 digits matching the claim_id zero-padding.
- INV-18 (inverse-rule for inconclusive not_applicable paths): When `judgment=RETRIEVAL_FAILED` AND `audit_status=inconclusive` AND `defect_stage=not_applicable`, `ref_retrieval_method` MUST be exactly one of `{not_attempted, failed, audit_tool_failure}`. Any other value (`api`, `manual_pdf`, `not_found`) is a lint violation. This is the **inverse-direction** check complementing INV-10/INV-11/INV-14: those three each guarantee their own method value implies the (RETRIEVAL_FAILED, inconclusive, not_applicable) row, but they don't collectively guarantee that any entry hitting that row uses one of those three methods. Without INV-18, a malformed entry with `(RETRIEVAL_FAILED, inconclusive, not_applicable, api)` passes the 3-tuple allowed-matrix check, passes INV-10/11/14 (none fire), but matches no finalizer row — silently losing its annotation. INV-18 closes that.

### 3.2 `claim_intent_manifest.schema.json`

One entry per generating-agent invocation. Emitted by `synthesis_agent` / `draft_writer_agent` / `report_compiler_agent` after paper-visible context loads but before prose generation.

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "https://github.com/Imbad0202/academic-research-skills/shared/contracts/passport/claim_intent_manifest.schema.json",
  "title": "Material Passport Claim Intent Manifest Entry",
  "type": "object",
  "additionalProperties": false,
  "required": [
    "manifest_version",
    "manifest_id",
    "emitted_by",
    "emitted_at",
    "claims",
    "manifest_negative_constraints"
  ],
  "properties": {
    "manifest_version": { "const": "1.0" },
    "manifest_id": {
      "type": "string",
      "pattern": "^M-[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z-[0-9a-f]{4}$",
      "description": "Discriminator scoping all claim_id values inside this manifest. Format: M-<ISO-8601-Z>-<4-hex>. Required because a single passport may contain multiple claim_intent_manifests[] entries (e.g., one from synthesis_agent and one from draft_writer_agent on the same run); bare C-001 alone would collide. The pair (manifest_id, claim_id) is the joinable key — see claim_audit_result.scoped_manifest_id + INV-15 / D-INV-2 cross-array integrity."
    },
    "emitted_by": { "enum": ["synthesis_agent", "draft_writer_agent", "report_compiler_agent"] },
    "emitted_at": { "type": "string", "format": "date-time" },
    "session_id": { "type": "string" },
    "claims": {
      "type": "array",
      "items": {
        "type": "object",
        "additionalProperties": false,
        "required": ["claim_id", "claim_text", "intended_evidence_kind", "planned_refs"],
        "properties": {
          "claim_id": { "type": "string", "pattern": "^C-[0-9]{3,}$" },
          "claim_text": { "type": "string", "minLength": 1, "maxLength": 2000 },
          "intended_evidence_kind": { "enum": ["empirical", "theoretical", "definitional", "normative"] },
          "planned_refs": { "type": "array", "items": { "type": "string" }, "minItems": 0 },
          "negative_constraints": {
            "type": "array",
            "items": {
              "type": "object",
              "additionalProperties": false,
              "required": ["constraint_id", "rule"],
              "properties": {
                "constraint_id": { "type": "string", "pattern": "^NC-C[0-9]{3,}-[0-9]+$" },
                "rule": { "type": "string", "minLength": 1, "maxLength": 500 }
              }
            }
          }
        }
      }
    },
    "manifest_negative_constraints": {
      "type": "array",
      "items": {
        "type": "object",
        "additionalProperties": false,
        "required": ["constraint_id", "rule"],
        "properties": {
          "constraint_id": { "type": "string", "pattern": "^MNC-[0-9]+$" },
          "rule": { "type": "string", "minLength": 1, "maxLength": 500 }
        }
      }
    }
  }
}
```

**Cross-field invariants** (lint-enforced):
- M-INV-1: `claim_id` uniqueness within ONE manifest (scoped by `manifest_id`). Cross-manifest collision (C-001 in both manifest A and manifest B) is permitted — the joinable discriminator is the `(manifest_id, claim_id)` pair.
- M-INV-2: `constraint_id` of `NC-C{n}-{m}` form MUST appear under `claims[]` entry where `claim_id=C-{n}` (i.e., claim-level constraint scoping)
- M-INV-3: `MNC-{m}` constraints in `manifest_negative_constraints` are globally applied; cannot be overridden by claim-level NC (claim-level can ADD, never DROP global)
- M-INV-4: `manifest_id` uniqueness across ALL `claim_intent_manifests[]` in one passport. Two manifests sharing the same `manifest_id` is a lint violation — the orchestrator must allocate fresh M-* identifiers per agent invocation.

### 3.3 `uncited_assertion.schema.json`

Per uncited-assertion finding. One entry per sentence in the draft that the D4-c three-condition token rule flagged. Aggregated as `uncited_assertions[]` in the orchestrator passport-tracking, parallel to `claim_audit_results[]`.

The separate schema exists because `uncited_assertion` findings have no `ref_slug` to fill — they describe sentences that *should* have a citation but don't. Embedding them in `claim_audit_result` would either force a sentinel `ref_slug` value or relax the required-field rule, both of which fight the schema's grain.

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "https://github.com/Imbad0202/academic-research-skills/shared/contracts/passport/uncited_assertion.schema.json",
  "title": "Material Passport Uncited Assertion Entry",
  "type": "object",
  "additionalProperties": false,
  "required": [
    "finding_id",
    "sentence_text",
    "section_path",
    "trigger_tokens",
    "detected_at",
    "rule_version"
  ],
  "properties": {
    "finding_id": { "type": "string", "pattern": "^UA-[0-9]{3,}$" },
    "sentence_text": { "type": "string", "minLength": 1, "maxLength": 2000 },
    "section_path": { "type": "string", "minLength": 1, "description": "Hierarchical path from document root to the section containing the sentence, e.g. '2. Methods > 2.3 Sampling'" },
    "trigger_tokens": {
      "type": "array",
      "minItems": 1,
      "items": { "type": "string" },
      "description": "Concrete tokens that matched D4-c condition 1 (quantifiers or empirical-claim verbs). E.g. ['67%', 'showed']."
    },
    "detected_at": { "type": "string", "format": "date-time" },
    "rule_version": { "const": "D4-c-v1" },
    "upstream_owner_agent": {
      "enum": ["synthesis_agent", "draft_writer_agent", "report_compiler_agent", null]
    },
    "manifest_claim_id": {
      "type": ["string", "null"],
      "pattern": "^C-[0-9]{3,}$",
      "description": "When the uncited sentence corresponds to a claim_id in the active claim_intent_manifest. Per D4-c last paragraph: manifest membership does NOT exempt a sentence from being flagged. When present, MUST be paired with scoped_manifest_id to disambiguate against C-001 collision across manifests."
    },
    "scoped_manifest_id": {
      "type": ["string", "null"],
      "pattern": "^M-[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z-[0-9a-f]{4}$",
      "description": "Points to the claim_intent_manifest.manifest_id owning the referenced manifest_claim_id. The (scoped_manifest_id, manifest_claim_id) pair uniquely identifies which manifest's claim this uncited finding corresponds to, since C-001 may collide across manifests in the same passport. Required when manifest_claim_id ≠ null (U-INV-4 cross-array integrity). Null when manifest_claim_id is null (the uncited sentence does not correspond to any manifest claim)."
    }
  }
}
```

**Cross-field invariants** (lint-enforced in `check_claim_audit_consistency.py`):
- U-INV-1: `finding_id` uniqueness across `uncited_assertions[]` in one passport
- U-INV-2: `trigger_tokens` non-empty (rule fires only when condition 1 matches)
- U-INV-3: `rule_version` must equal `D4-c-v1` for v3.8.0 release; future rule revisions bump the const and require re-lint
- U-INV-4: When `manifest_claim_id ≠ null`, `scoped_manifest_id ≠ null` AND the `(scoped_manifest_id, manifest_claim_id)` pair MUST match some `claim_intent_manifests[].manifest_id == scoped_manifest_id` whose `claims[].claim_id` contains the manifest_claim_id (cross-array consistency). When `manifest_claim_id = null`, `scoped_manifest_id MUST also = null` (no orphan manifest pointer).

### 3.4 `claim_drift.schema.json`

Per claim-intent-drift finding. One entry per emitted claim that the manifest set-diff in §4 step 5 flagged as having drifted away from the `claim_intent_manifests[]` baseline. Aggregated as `claim_drifts[]` in the orchestrator passport-tracking, parallel to `claim_audit_results[]` and `uncited_assertions[]`.

The separate schema exists because **claim-intent drift is detected by manifest set-diff, not by judge invocation** — no `judgment` / `audit_status` / `rationale` field would carry meaning for these entries, and the judge is never run for the drift detection path. Embedding drift findings as a `defect_stage` of `claim_audit_result` would force `judgment=UNSUPPORTED` to be recorded without the judge ever evaluating that claim, contaminating both the schema semantics (UNSUPPORTED means "judge said UNSUPPORTED") and the calibration FNR/FPR metrics (which are scoped to the judge's own SUPPORTED/UNSUPPORTED/AMBIGUOUS judgments).

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "https://github.com/Imbad0202/academic-research-skills/shared/contracts/passport/claim_drift.schema.json",
  "title": "Material Passport Claim Drift Entry",
  "type": "object",
  "additionalProperties": false,
  "required": [
    "finding_id",
    "drift_kind",
    "claim_text",
    "detected_at",
    "rule_version"
  ],
  "properties": {
    "finding_id": { "type": "string", "pattern": "^CD-[0-9]{3,}$" },
    "drift_kind": {
      "enum": ["EMITTED_NOT_INTENDED", "INTENDED_NOT_EMITTED"],
      "description": "EMITTED_NOT_INTENDED: an emitted claim that was not in the manifest (the drafted prose introduced a claim the writer did not pre-commit to). INTENDED_NOT_EMITTED: a manifest claim that did not appear in the emitted prose (the writer dropped a pre-committed claim during drafting). Both are advisory — gate-refuse is reserved for negative_constraint_violation."
    },
    "claim_text": { "type": "string", "minLength": 1, "maxLength": 2000, "description": "For EMITTED_NOT_INTENDED, the emitted sentence; for INTENDED_NOT_EMITTED, the manifest claim_text." },
    "manifest_claim_id": {
      "type": ["string", "null"],
      "pattern": "^C-[0-9]{3,}$",
      "description": "For INTENDED_NOT_EMITTED, the dropped manifest claim_id (REQUIRED, conditional on drift_kind — enforced by D-INV-2). For EMITTED_NOT_INTENDED, null (drifted claim has no manifest_claim_id since it was never in the manifest). When present, MUST be paired with scoped_manifest_id."
    },
    "scoped_manifest_id": {
      "type": ["string", "null"],
      "pattern": "^M-[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z-[0-9a-f]{4}$",
      "description": "Points to the claim_intent_manifest.manifest_id owning the referenced manifest_claim_id. Required when drift_kind=INTENDED_NOT_EMITTED (paired with manifest_claim_id per D-INV-2 cross-array integrity, disambiguating C-001 collision across manifests). Null when drift_kind=EMITTED_NOT_INTENDED (the drifted claim has no manifest origin)."
    },
    "section_path": {
      "type": ["string", "null"],
      "minLength": 1,
      "description": "For EMITTED_NOT_INTENDED, hierarchical path from document root to the section containing the drifted sentence (mirrors uncited_assertion.section_path). Null for INTENDED_NOT_EMITTED (dropped claim has no draft location)."
    },
    "detected_at": { "type": "string", "format": "date-time" },
    "rule_version": { "const": "D4-a-v1" },
    "upstream_owner_agent": {
      "enum": ["synthesis_agent", "draft_writer_agent", "report_compiler_agent", null]
    }
  }
}
```

**Cross-field invariants** (lint-enforced in `check_claim_audit_consistency.py`):
- D-INV-1: `finding_id` uniqueness across `claim_drifts[]` in one passport.
- D-INV-2: `drift_kind=INTENDED_NOT_EMITTED` → `manifest_claim_id ≠ null` AND `scoped_manifest_id ≠ null` AND the `(scoped_manifest_id, manifest_claim_id)` pair MUST match some `claim_intent_manifests[].manifest_id == scoped_manifest_id` whose `claims[].claim_id` contains the manifest_claim_id (cross-array integrity, disambiguates C-001 collision across manifests). `drift_kind=EMITTED_NOT_INTENDED` → `manifest_claim_id = null` AND `scoped_manifest_id = null` AND `section_path ≠ null`.
- D-INV-3: `rule_version` must equal `D4-a-v1` for v3.8.0 release; future rule revisions bump the const and require re-lint.
- D-INV-4: A given emitted sentence may produce AT MOST ONE finding across `uncited_assertions[]` and `claim_drifts[]` combined. When a sentence is both uncited AND drifted, the `uncited_assertions[]` entry takes precedence (per §5 finalizer precedence rule 3 restated from issue body) — no companion `claim_drifts[]` entry emits for the same sentence.

### 3.5 `constraint_violation.schema.json`

Per uncited claim that violates a manifest negative constraint. One entry per emitted sentence WITHOUT a `<!--ref:slug-->` marker that triggers `VIOLATED` from the negative-constraint judge prompt. Aggregated as `constraint_violations[]` in the orchestrator passport-tracking, parallel to `claim_audit_results[]` / `uncited_assertions[]` / `claim_drifts[]`.

**The separate schema exists because constraint violations on uncited claims are real HIGH-WARN gate-refuse blockers, but `claim_audit_result.ref_slug` is required and `uncited_assertion` is LOW-WARN advisory only.** A claim like "we observed causality" with no citation, against an MNC rule "will NOT claim causality without RCT evidence", is a genuine MUST-NOT violation the user explicitly declared. Routing it through `uncited_assertions[]` would silently downgrade a HIGH-WARN signal to LOW-WARN; routing it through `claim_audit_result` would require a sentinel `ref_slug` value that doesn't exist. A dedicated entry-type preserves both the HIGH-WARN severity and the schema integrity of each existing aggregate.

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "https://github.com/Imbad0202/academic-research-skills/shared/contracts/passport/constraint_violation.schema.json",
  "title": "Material Passport Constraint Violation Entry",
  "type": "object",
  "additionalProperties": false,
  "required": [
    "finding_id",
    "claim_text",
    "section_path",
    "violated_constraint_id",
    "scoped_manifest_id",
    "judge_verdict",
    "rationale",
    "judge_model",
    "judge_run_at",
    "rule_version"
  ],
  "properties": {
    "finding_id": { "type": "string", "pattern": "^CV-[0-9]{3,}$" },
    "claim_text": { "type": "string", "minLength": 1, "maxLength": 2000 },
    "section_path": { "type": "string", "minLength": 1, "description": "Hierarchical path from document root to the section containing the offending sentence." },
    "violated_constraint_id": { "type": "string", "pattern": "^(NC-C[0-9]{3,}-[0-9]+|MNC-[0-9]+)$" },
    "scoped_manifest_id": {
      "type": "string",
      "pattern": "^M-[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z-[0-9a-f]{4}$",
      "description": "Points to the claim_intent_manifest.manifest_id owning the violated constraint. Required (no MANIFEST-MISSING sentinel admitted — constraints require an active manifest to exist)."
    },
    "manifest_claim_id": {
      "type": ["string", "null"],
      "pattern": "^C-[0-9]{3,}$",
      "description": "For NC-C{n}-{m} (claim-level constraint), the parent claim_id from the manifest. For MNC-{m} (global), null."
    },
    "judge_verdict": { "const": "VIOLATED" },
    "rationale": { "type": "string", "minLength": 1, "maxLength": 2000 },
    "judge_model": { "type": "string", "minLength": 1 },
    "judge_run_at": { "type": "string", "format": "date-time" },
    "rule_version": { "const": "D4-a-v1" },
    "upstream_owner_agent": {
      "enum": ["synthesis_agent", "draft_writer_agent", "report_compiler_agent", null]
    }
  }
}
```

**Cross-field invariants** (lint-enforced in `check_claim_audit_consistency.py`):
- CV-INV-1: `finding_id` uniqueness across `constraint_violations[]` in one passport.
- CV-INV-2: `(scoped_manifest_id, violated_constraint_id)` MUST resolve in some `claim_intent_manifests[]` entry. For `MNC-*` ids, the matching manifest's `manifest_negative_constraints[]` must contain it. For `NC-C{n}-{m}` ids, the matching manifest's `claims[]` entry with `claim_id=C-{n}` must contain a `negative_constraints[].constraint_id` matching the NC-* id, AND `manifest_claim_id` MUST equal `C-{n}`.
- CV-INV-3: When `violated_constraint_id` starts with `MNC-`, `manifest_claim_id = null`; when it starts with `NC-`, `manifest_claim_id` MUST equal the `C-{n}` extracted from the NC-* id.
- CV-INV-4: An uncited sentence MAY appear in BOTH `uncited_assertions[]` AND `constraint_violations[]` simultaneously — these surface different aspects (advisory uncited token-rule + HIGH-WARN constraint violation by judge) and don't trip D-INV-4-style exclusivity. However, a SINGLE sentence MUST NOT appear in `constraint_violations[]` more than once per `(scoped_manifest_id, violated_constraint_id)` — i.e. the lint dedup key is `(scoped_manifest_id, section_path, claim_text_hash, violated_constraint_id)`. Per M-INV-4 each `manifest_id` is unique across the passport but constraint ids (`MNC-*` / `NC-*`) are only unique WITHIN a manifest, so two manifests in the same passport may legitimately carry colliding constraint ids — the same sentence text may then violate both, and the dedupe must respect manifest scope to preserve both findings (v3.8.1).

### 3.6 `uncited_audit_failure.schema.json`

Per uncited-sentence × manifest pair where the constraint judge raised a `JudgeInvocationError` during D6 stream (d) judging. One entry per (sentence, manifest) failure. Aggregated as `uncited_audit_failures[]` in the orchestrator passport-tracking, parallel to `claim_audit_results[]` / `uncited_assertions[]` / `claim_drifts[]` / `constraint_violations[]`.

**The separate schema exists because the cited-path INV-14 `audit_tool_failure` row (a `claim_audit_result` entry carrying `ref_retrieval_method=audit_tool_failure`) cannot be reused on the uncited path — `claim_audit_result.ref_slug` is required, and the uncited path has no ref to bind.** Without a dedicated surface, a transient judge outage on a constraint check would either be silently swallowed (the pre-v3.8.2 bug — `NOT_VIOLATED` substituted, HIGH-WARN constraint check suppressed) or would force the entire audit pass to abort (dropping coverage). This entry-type mirrors INV-14 semantics on the uncited path: MED-WARN advisory at finalizer, retry-next-pass remediation, surfaces the infrastructure failure distinctly from a substantive non-violation. Routing through `uncited_assertions[]` would conflate D4-c token-rule advisory signal with audit-time infrastructure failure (different `rule_version`, different fault model, different annotation tier).

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "https://github.com/Imbad0202/academic-research-skills/shared/contracts/passport/uncited_audit_failure.schema.json",
  "title": "Material Passport Uncited Audit Failure Entry",
  "type": "object",
  "additionalProperties": false,
  "required": [
    "finding_id",
    "claim_text",
    "section_path",
    "scoped_manifest_id",
    "fault_class",
    "rationale",
    "judge_model",
    "judge_run_at",
    "rule_version"
  ],
  "properties": {
    "finding_id": { "type": "string", "pattern": "^UAF-[0-9]{3,}$" },
    "claim_text": { "type": "string", "minLength": 1, "maxLength": 2000 },
    "section_path": { "type": "string", "minLength": 1, "description": "Hierarchical path from document root to the section containing the offending sentence (mirrors uncited_assertion.section_path)." },
    "scoped_manifest_id": {
      "type": "string",
      "pattern": "^M-[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z-[0-9a-f]{4}$",
      "description": "Points to the claim_intent_manifest.manifest_id whose MNC/NC-C set was being judged when the failure occurred. Required — no MANIFEST-MISSING sentinel admitted; UAF emission requires an active manifest scope."
    },
    "manifest_claim_id": {
      "type": ["string", "null"],
      "pattern": "^C-[0-9]{3,}$",
      "description": "When the sentence was bound to a manifest claim (sentence carries `manifest_claim_id` per §4 step 5 stream (d) NC-C judging path), points to that claim. Null when the judge call was against MNCs only (manifest-wide constraints, no claim binding). Mirrors constraint_violation.manifest_claim_id polarity."
    },
    "fault_class": {
      "enum": [
        "judge_timeout",
        "judge_api_error",
        "judge_parse_error",
        "cache_corruption",
        "retrieval_api_error",
        "retrieval_timeout",
        "retrieval_network_error"
      ],
      "description": "Same closed enum as INV-14 fault-class taxonomy on the cited path. Sourced from JudgeInvocationError.fault_class at the raise site."
    },
    "rationale": { "type": "string", "minLength": 1, "maxLength": 2000, "description": "MUST begin with the fault_class tag followed by `: ` and a free-form detail. Mirrors INV-14 rationale format. Example: `judge_timeout: judge timed out after 30s`." },
    "judge_model": { "type": "string", "minLength": 1 },
    "judge_run_at": { "type": "string", "format": "date-time" },
    "rule_version": { "const": "D4-c-v1-uaf-v1", "description": "UAF surface version. Distinguishes from `D4-c-v1` (uncited_assertion D4-c detector) and `D4-a-v1` (constraint_violation). The `-uaf-v1` suffix marks this as a separate surface, not a D4-c revision." },
    "upstream_owner_agent": {
      "enum": ["synthesis_agent", "draft_writer_agent", "report_compiler_agent", null]
    }
  }
}
```

**Cross-field invariants** (lint-enforced in `check_claim_audit_consistency.py`):
- UAF-INV-1: `finding_id` uniqueness across `uncited_audit_failures[]` in one passport.
- UAF-INV-2: `scoped_manifest_id` MUST resolve in some `claim_intent_manifests[]` entry (cross-array reference integrity).
- UAF-INV-3: When `manifest_claim_id ≠ null`, the `(scoped_manifest_id, manifest_claim_id)` pair MUST match some `claims[].claim_id` in the referenced manifest. When `manifest_claim_id = null`, the failure was against MNCs only (no claim binding required). Mirrors U-INV-4 / CV-INV-2 cross-array integrity pattern.
- UAF-INV-4: Per-(sentence, manifest) dedup. The tuple `(scoped_manifest_id, section_path, claim_text_hash)` MUST be unique across the aggregate. A sentence judged once per manifest produces at most one UAF row per (sentence, manifest). Two manifests both failing on the same sentence emit two distinct rows (legitimate per-manifest scope, mirrors CV-INV-4 cross-manifest reasoning).
- UAF-INV-5: `rationale` MUST begin with the row's own `fault_class` value followed by `":"` (and a `" "` plus free-form detail when a detail is available — the trailing space is omitted when `detail` is empty so the rationale stays `minLength: 1`-valid). Mirrors INV-14 rationale prefix requirement on the cited path; the prefix must match this row's `fault_class` field, not just any known tag. Example with detail: `"judge_timeout: judge timed out after 30s"`. Example without detail: `"judge_timeout:"` (a 14-character minimum form when the upstream `JudgeInvocationError.detail` is empty).
- UAF-INV-6: **Cross-aggregate exclusivity.** A sentence MUST NOT appear in both `uncited_audit_failures[]` AND `constraint_violations[]` for the same `(scoped_manifest_id, section_path, claim_text_hash)` — VIOLATED and audit_tool_failure are mutually exclusive verdict states at per-(sentence, manifest) level (one is a positive verdict, the other is no verdict at all). Co-existence with `uncited_assertions[]` IS permitted (D4-c detector positives and audit-time judge failure are independent signals).

## 4. Agent prompt structure: `claim_ref_alignment_audit_agent.md`

Sections (in order):

1. **Purpose & v3.8 placement** — single paragraph naming L3 audit role, dependency on v3.7.3 anchor input, audit-not-arbitration boundary.
2. **PATTERN PROTECTION (v3.6.7)** — byte-equivalent block to existing audited-agents pattern protection convention. Prevents cascading edits.
3. **Input contract** — exact passport fields read; `claim_audit_config` keys consumed (max_claims_per_paper, judge_model, gold_set_path, cache_dir).

   **Sampling behavior when citation count N > max_claims_per_paper:** the agent MUST emit a single `audit_sampling_summary` entry (one per audit run) into the passport `audit_sampling_summaries[]` aggregate, schema below. The agent selects a **stratified sample** — divide the N citations into k buckets (where k = min(max_claims_per_paper, N)) and pick one citation from each bucket in document order. Other citations are not audited but the summary entry surfaces the skip rate so users see how many citations went unaudited. No silent skipping per D3(a). When N ≤ max_claims_per_paper, no summary entry is needed (or equivalently, an entry with `audited_count == total_citation_count` may be emitted for telemetry).

   **`audit_sampling_summary` entry schema** (minimal, no separate §3.x — small enough to inline here):
   ```json
   {
     "$schema": "https://json-schema.org/draft/2020-12/schema",
     "type": "object",
     "additionalProperties": false,
     "required": ["audit_run_id", "max_claims_per_paper", "total_citation_count", "audited_count", "audited_indices", "sampling_strategy", "emitted_at"],
     "properties": {
       "audit_run_id": { "type": "string", "pattern": "^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z-[0-9a-f]{4}$" },
       "max_claims_per_paper": { "type": "integer", "minimum": 1 },
       "total_citation_count": { "type": "integer", "minimum": 0 },
       "audited_count": { "type": "integer", "minimum": 0 },
       "audited_indices": { "type": "array", "items": { "type": "integer", "minimum": 0 }, "description": "0-based document-order indices of the audited citations." },
       "sampling_strategy": { "const": "stratified_buckets_v1" },
       "emitted_at": { "type": "string", "format": "date-time" }
     }
   }
   ```

   **Sampling invariants:**
   - S-INV-1: `audited_count == |audited_indices|`.
   - S-INV-2: `audited_count ≤ max_claims_per_paper` AND `audited_count ≤ total_citation_count`.
   - S-INV-3: When `audited_count < total_citation_count`, the finalizer MUST emit a paper-level `[CLAIM-AUDIT-SAMPLED — k/N audited]` annotation in the AI Self-Reflection Report appendix.
   - S-INV-4: `audited_indices` are strictly ascending (no duplicates, document order).

   Lint rule 4c: validate `audit_sampling_summaries[]` against the inline schema + S-INV-1..S-INV-4.
4. **Audit pipeline (6 steps)**:
   - Step 1 — Anchor presence check (D1, INV-6 firm rule).
   - Step 2 — Reference retrieval (`api` → `manual_pdf` → `failed`/`not_found`). LOW-WARN on `failed` (D2 paywall). Sets `ref_retrieval_method` + carries `retrieved_excerpt` forward.
   - Step 3 — Cache lookup keyed by `(claim_text_hash, ref_slug, anchor_kind, anchor_value_hash, retrieved_excerpt_hash, active_constraints_hash, judge_model)`. The `active_constraints_hash` is SHA-256 over the JCS-encoded set of manifest constraints applicable to this claim at audit time. **Selection is scoped by `(scoped_manifest_id, claim_id)`, NOT bare `claim_id`** — per M-INV-1, cross-manifest C-001 collision is permitted, so selecting by bare claim_id would pick constraints from the wrong manifest. The set: top-level `manifest_negative_constraints[]` of the **specific** manifest whose `manifest_id == scoped_manifest_id` ∪ that manifest's `claims[].negative_constraints[]` entry whose `claim_id` matches the current claim, sorted by `constraint_id`. Lookup runs AFTER retrieval so the cached judgment is bound to the exact source text the judge will see, AND to the exact constraint set the judge would evaluate — if the user re-runs after uploading a manual PDF, correcting the corpus entry, OR adding/changing a negative constraint, the relevant hash changes and the cache miss forces fresh judging.

     **The cache stores only judge-verdict + source-bound fields, never run-local identifiers.** Cached fields: `judgment`, `audit_status`, `defect_stage`, `rationale`, `judge_model`, `judge_run_at`, `ref_retrieval_method`, `violated_constraint_id`. Excluded (must be rebuilt from current-run context on replay): `claim_id` (new manifest position), `audit_run_id` (new run), `upstream_owner_agent` (different emitting agent on a different draft), `upstream_dispute` (run-specific dispute log), `anchor_value` (already keyed but re-emitted from current marker). This separation is what allows a verdict for the same `(claim_text, ref, anchor, source-excerpt, constraint-set, judge_model)` to be reused across different drafts / manifests without misattribution.

     On hit: load cached judge-verdict + source-bound block; assemble a complete `claim_audit_result` by joining with current-run identifiers (current `claim_id`, current `audit_run_id`, current `upstream_owner_agent`). On miss: proceed to Step 4-5; write only the judge-verdict + source-bound block into the cache; emit the joined entry. The filesystem KV is `${ARS_CACHE_DIR}/claim_audit_v1/<cache_key_sha256>.json`. Cache-side metadata (mtime) lives on the filesystem, never inside the JSON body.
   - Step 4 — Passage location using anchor_value (quote = exact match; page/section/paragraph = scoped retrieval).
   - Step 5 — Judge invocation with prompt template. Output one of SUPPORTED/UNSUPPORTED/AMBIGUOUS, with rationale.
   - Step 6 — Defect_stage classification. Citation-bound results emit `claim_audit_result` entries with `defect_stage` ∈ 6 substantive categories `{retrieval_existence, metadata, source_description, citation_anchor, synthesis_overclaim, negative_constraint_violation}` plus 2 non-substantive `{not_applicable, null}`. Four out-of-band finding categories use separate entry types: (a) uncited-sentence findings emit `uncited_assertion` entries (§3.3); (b) claim-intent drift findings emit `claim_drift` entries (§3.4); (c) **cited** constraint violations (sentence carries `<!--ref:slug-->` AND judge says VIOLATED) emit `claim_audit_result` entries with `defect_stage=negative_constraint_violation`; (d) **uncited** constraint violations (no `<!--ref:slug-->` AND judge says VIOLATED against an MNC/NC rule in scope) emit `constraint_violation` entries (§3.5). (c) and (d) are the cited/uncited split routed by §4 Step 5 stream (c)/(d). Precedence rules from issue body restated in §5 finalizer integration.
5. **Manifest cross-reference (D6)** — three-set diff of `intended_claims` (manifest) vs `emitted_claims` (extracted from draft) vs `supported_claims` (post-judge SUPPORTED subset). The diff produces four streams: (a) `EMITTED_NOT_INTENDED` — emitted claims missing from manifest → `claim_drifts[]` entry with `drift_kind=EMITTED_NOT_INTENDED`, advisory LOW-WARN at finalizer. (b) `INTENDED_NOT_EMITTED` — manifest claims dropped from draft → `claim_drifts[]` entry with `drift_kind=INTENDED_NOT_EMITTED`, advisory LOW-WARN. (c) Manifest negative-constraint matches on **cited** claims (sentence has `<!--ref:slug-->`) — pass to judge via §4 negative-constraint prompt; VIOLATED outcomes emit `claim_audit_result` entries with `defect_stage=negative_constraint_violation` (judge IS invoked here, distinct from drift). (d) Manifest negative-constraint matches on **uncited** claims (sentence has no `<!--ref:slug-->` but matches MNC/NC scope) — also pass to judge via the same negative-constraint prompt; VIOLATED outcomes emit `constraint_violations[]` entries (§3.5), HIGH-WARN gate-refuse at finalizer. **`JudgeInvocationError` on this path emits `uncited_audit_failures[]` entries (§3.6) carrying the fault_class tag — MED-WARN advisory at finalizer; the pre-v3.8.2 synthetic NOT_VIOLATED substitution silently suppressed HIGH-WARN constraint checks and is fixed in v3.8.2 / #118 by this routing.** (c) and (d) BOTH escalate to HIGH-WARN on VIOLATED — explicit author MUST NOT rules block regardless of citation presence — but they use distinct entry-types to preserve the schema integrity of `claim_audit_result` (which requires `ref_slug`); the corresponding outage path uses an INV-14 row on (c) and a `uncited_audit_failures[]` entry on (d) for the same symmetric reason. (a) and (b) are pure manifest-set-diff signals never seen by the judge.
6. **Uncited-assertion detector (D4-c)** — 3-condition token rule. Pseudocode included.
7. **Output emission** — one `claim_audit_result` entry per audited citation, plus aggregate counts emitted in pipeline-orchestrator Stage 6 reflection report.
8. **Calibration mode** — opt-in flow per `claim_audit_calibration_protocol.md`. Gold-set ingestion → judge run → FNR/FPR computation → user-facing report.
9. **Error handling** — three failure surfaces with distinct semantics, so retrieval access restrictions and audit-tool outages don't collapse:
   - **Retrieval access restriction (verified paywall — HTTP 403/402, license-restricted, no full-text endpoint, reference exists but body not accessible):** emit `claim_audit_result` with `judgment=RETRIEVAL_FAILED`, `audit_status=inconclusive`, `defect_stage=not_applicable`, `ref_retrieval_method=failed`. INV-10 / D2 — LOW-WARN advisory. **NOTE:** transient API errors (5xx, timeouts, network failures) do NOT belong here — they map to `audit_tool_failure` below.
   - **Audit infrastructure / transient outage (judge timeout, judge API 5xx, retrieval API 5xx, retrieval timeout / network error, retrieval API DNS failure, cache corruption, JSON parse failure):** emit `claim_audit_result` with `judgment=RETRIEVAL_FAILED`, `audit_status=inconclusive`, `defect_stage=not_applicable`, `ref_retrieval_method=audit_tool_failure`. Per INV-14 — MED-WARN advisory at finalizer (`[CLAIM-AUDIT-TOOL-FAILURE — <fault-class>]`), surfaces the infrastructure problem distinctly from a paywall, but does NOT gate-refuse — retry on next pipeline pass is the remediation. Rationale MUST begin with a fault-class tag in `{judge_timeout, judge_api_error, judge_parse_error, cache_corruption, retrieval_api_error, retrieval_timeout, retrieval_network_error}` followed by `: <detail>`. The discriminator between `failed` and `audit_tool_failure` is permanence — a paywall is a stable property of the citation, an API 5xx is a transient property of the infrastructure.
   - **Fabricated reference (retrieval API reports not_found):** per INV-12 — `ref_retrieval_method=not_found`, `defect_stage=retrieval_existence`, `audit_status=completed`. HIGH-WARN gate-refuse.
   - **Uncited-path judge outage (v3.8.2 / #118):** when `_invoke_judge` raises `JudgeInvocationError` during D6 stream (d) constraint judging on an uncited sentence, emit an `uncited_audit_failure` entry (§3.6) carrying the fault_class tag. MED-WARN advisory at finalizer (`[CLAIM-AUDIT-TOOL-FAILURE-UNCITED — <fault-class>]`), gate passes — retry on next pipeline pass is the remediation. MUST NOT emit a synthetic `NOT_VIOLATED` verdict (silent suppression of HIGH-WARN constraint check is the bug fixed in v3.8.2). Mirrors INV-14 semantics on the cited path: judge outage is operational signal distinct from substantive non-violation, but the uncited path uses a dedicated aggregate because `claim_audit_result.ref_slug` is required.
10. **Cross-references** — Zhao 2026 §1, RubricEM Borrows 1+2, v3.7.3 anchor input contract, v3.6.7 PATTERN PROTECTION convention.

**Judge prompt template** (canonical form, embedded in agent prompt):

> Given this claim from a paper draft and this excerpt from the cited reference, does the reference support the claim?
>
> CLAIM: {claim_text}
> CITED REFERENCE EXCERPT: {retrieved_excerpt}
> ANCHOR KIND: {anchor_kind}
> ANCHOR VALUE: {anchor_value}
>
> Output ONE of:
> - SUPPORTED — the reference directly supports the claim
> - UNSUPPORTED — the reference does NOT support the claim (the cited source says something different or contradictory)
> - AMBIGUOUS — the reference is related but does not clearly support or contradict the claim
>
> Then output ONE SENTENCE rationale.
>
> Format: `JUDGMENT: <one-of>\nRATIONALE: <one sentence>`

**Negative-constraint judge prompt template** (extended form):

> Given this claim and the author's declared negative constraint, does the claim violate the constraint?
>
> CLAIM: {claim_text}
> CONSTRAINT: {constraint_rule}
>
> Output ONE of: VIOLATED, NOT_VIOLATED
> Then output ONE SENTENCE rationale.

VIOLATED → `judgment=UNSUPPORTED, defect_stage=negative_constraint_violation, violated_constraint_id={constraint_id}` per INV-8.

## 5. Orchestrator integration: `pipeline_orchestrator_agent.md` §3.6

New section "Claim-Faithfulness Audit Gate (v3.8)". Mirrors §3.5 Audit Artifact Gate structure but for claim-level audit.

**Trigger boundary:** Stage 4 → Stage 5 transition, in the same handoff slot as the v3.7.1 Cite-Time Provenance Finalizer. The audit dispatches AFTER the Cite-Time Provenance Finalizer pass (which resolves anchor-presence per v3.7.3 §3.1 and the 5-cell matrix) and BEFORE `formatter_agent` runs its hard gate at the start of Stage 5. This ordering mirrors §3.5 v3.6.7 audit gate (audit between deliverable completion and downstream consumption).

**Why not Stage 5→6:** `formatter_agent`'s terminal hard gate runs **during** Stage 5 (per orchestrator §"Cite-Time Provenance Finalizer (v3.7.1)" — formatter consumes finalizer output and refuses on `[UNVERIFIED CITATION ...]`). If the claim audit dispatches at Stage 5→6, `claim_audit_results[]` would be produced after the terminal gate has already passed; HIGH-WARN-CLAIM-NOT-SUPPORTED could not block output. The Stage 4→5 slot is the only place where (a) the draft prose with v3.7.3 anchors exists, (b) the cite finalizer has run so anchor presence is settled, and (c) the formatter hard gate has NOT yet run.

The audit agent receives:
- All in-text citations with their resolved `<!--ref:slug ...-->` + `<!--anchor:...-->` marker pairs (post-finalizer)
- The `claim_intent_manifests[]` aggregate from the writing-stage agents
- The `literature_corpus[]` aggregate (for retrieval)

**Outputs feeding formatter hard gate (same Stage 5 pass):**
- `claim_audit_results[]` array (one per audited citation) — drives the 8-row matrix annotations
- `constraint_violations[]` array (one per uncited-but-violates-MNC/NC sentence) — drives `[HIGH-WARN-CONSTRAINT-VIOLATION-UNCITED ({violated_constraint_id})]` annotation. **MUST be passed to formatter alongside `claim_audit_results[]`** — without this, uncited HIGH-WARN gate-refuse path silently disappears since no claim_audit_result row exists for uncited constraint violations (per §3.5 split). The formatter's REFUSE list per §1 deliverable 5 includes HIGH-WARN-CONSTRAINT-VIOLATION-UNCITED — this handoff is what makes that REFUSE check observable.
- `uncited_assertions[]` array — drives `[UNCITED-ASSERTION]` LOW-WARN advisory annotation (formatter renders, does NOT refuse).
- `uncited_audit_failures[]` array (v3.8.2 / #118 — one per uncited sentence × manifest where the constraint judge raised `JudgeInvocationError`) — drives `[CLAIM-AUDIT-TOOL-FAILURE-UNCITED — <fault-class>]` MED-WARN advisory annotation (formatter renders, does NOT refuse). Mirrors the cited-path INV-14 row but uses a dedicated aggregate per §3.6 because `claim_audit_result.ref_slug` is required.
- `claim_drifts[]` array — drives `[LOW-WARN-CLAIM-DRIFT — kind=...]` LOW-WARN advisory annotation (formatter renders, does NOT refuse).
- `audit_sampling_summaries[]` array — drives paper-level `[CLAIM-AUDIT-SAMPLED — k/N audited]` annotation when audited_count < total_citation_count (formatter renders in the AI Self-Reflection Report appendix; does NOT refuse).
- Per-citation/per-sentence annotations injected adjacent to the existing v3.7.1 finalizer annotations (HIGH-WARN classes block; MED/LOW-WARN advisory passes).

**Outputs feeding Stage 6 self-reflection:**
- Per-stage `defect_stage` histogram appendix (renders when ≥ 5 completed entries) — added to the existing Stage 6 AI Self-Reflection Report after gate pass

**Finalizer matrix extension (8-row):**

Existing v3.7.3 5-cell matrix (anchor presence + 4-cell trust state) gains a new finalizer pass that overlays per-citation audit annotations from `claim_audit_results[]`. The matrix discriminates the previously-conflated paywall vs anchorless cases by reading `ref_retrieval_method` alongside `(judgment, defect_stage)`. Rows are evaluated top-to-bottom, first match wins:

| `judgment` | `defect_stage` | `ref_retrieval_method` | Annotation | Severity Tier | Gate behavior |
|---|---|---|---|---|---|
| SUPPORTED | `null` | (any) | (no annotation) | — | pass |
| AMBIGUOUS | source_description / citation_anchor / synthesis_overclaim / null | (any) | `[CLAIM-AUDIT-AMBIGUOUS]` | LOW-WARN advisory | pass |
| UNSUPPORTED | source_description / metadata / citation_anchor / synthesis_overclaim | (any) | `[HIGH-WARN-CLAIM-NOT-SUPPORTED]` | HIGH-WARN | gate-refuse |
| UNSUPPORTED | negative_constraint_violation | (any) | `[HIGH-WARN-NEGATIVE-CONSTRAINT-VIOLATION ({violated_constraint_id})]` | HIGH-WARN | gate-refuse (per D4-a — explicit author rules are HIGH-WARN; drift findings emit into `claim_drifts[]` at LOW-WARN advisory tier — see below) |
| RETRIEVAL_FAILED | retrieval_existence | not_found | `[HIGH-WARN-FABRICATED-REFERENCE]` | HIGH-WARN | gate-refuse (retrieval-side detection — the cited reference does not exist in the retrieval API; fabrication is a retrieval finding, not a bibliographic-metadata finding) |
| RETRIEVAL_FAILED | not_applicable | **not_attempted** | `[HIGH-WARN-CLAIM-AUDIT-ANCHORLESS — v3.7.3 R-L3-1-A VIOLATION REACHED AUDIT]` | HIGH-WARN | gate-refuse (anchor=none should have been blocked by v3.7.3 finalizer; this row is a defense-in-depth surface against finalizer skip/stale paths) |
| RETRIEVAL_FAILED | not_applicable | **failed** | `[CLAIM-AUDIT-UNVERIFIED — REFERENCE FULL-TEXT NOT RETRIEVABLE]` | LOW-WARN advisory | pass (paywall — D2) |
| RETRIEVAL_FAILED | not_applicable | **audit_tool_failure** | `[CLAIM-AUDIT-TOOL-FAILURE — <fault-class>]` | MED-WARN advisory | pass (audit infrastructure failure after retrieval succeeded; surfaced distinctly from paywall per INV-14; retry next pipeline pass) |

**Why three rows for `(RETRIEVAL_FAILED, not_applicable)`:** anchor=none (INV-6/INV-11), paywall (INV-10), and audit-tool failure (INV-14) all emit this `(judgment, defect_stage)` pair, but mean three very different things — anchorless is a contract violation that already should have been gate-refused upstream by v3.7.3 (defense-in-depth row HIGH-WARN gate-refuse); paywall is a stable access restriction (legitimate tool/access failure, LOW-WARN advisory pass); audit_tool_failure is a transient infrastructure outage (judge timeout, retrieval 5xx, network error — MED-WARN advisory pass with retry-next-pass remediation). The `ref_retrieval_method` field discriminates them and their finalizer outcomes: `not_attempted` → HIGH-WARN gate-refuse; `failed` → LOW-WARN advisory; `audit_tool_failure` → MED-WARN advisory. INV-10 / INV-11 / INV-14 jointly enforce that these three are the only `(not_applicable)` paths AND they're mutually exclusive on `ref_retrieval_method` (each `(not_applicable)` entry MUST carry exactly one of the three method values).

**`uncited_assertion` entries** (separate aggregate `uncited_assertions[]`) emit at LOW-WARN tier with annotation `[UNCITED-ASSERTION]` next to the offending sentence. Always advisory; gate-refuse reserved for citation-level defects. See §3.3 for entry schema.

**`constraint_violation` entries** (separate aggregate `constraint_violations[]`) emit at HIGH-WARN tier with annotation `[HIGH-WARN-CONSTRAINT-VIOLATION-UNCITED ({violated_constraint_id})]` next to the offending sentence. Gate-refuse — explicit author MUST NOT rules block regardless of citation presence (parallels the gate-refuse behavior of cited constraint violations in the 8-row matrix; the entry-type split is purely a schema-integrity artifact, not a severity downgrade). The formatter hard gate MUST refuse output on this annotation alongside the four other HIGH-WARN classes (per §1 deliverable 5). See §3.5 for entry schema.

**`uncited_audit_failure` entries** (separate aggregate `uncited_audit_failures[]`, v3.8.2 / #118) emit at **MED-WARN advisory** tier with annotation `[CLAIM-AUDIT-TOOL-FAILURE-UNCITED — <fault-class>]` next to the offending sentence. Always advisory; gate passes — retry on next pipeline pass is the remediation. Mirrors INV-14 semantics on the uncited path: a transient judge outage on a constraint check is operational signal distinct from a substantive non-violation. Pre-v3.8.2 behavior synthesised a `NOT_VIOLATED` verdict on `JudgeInvocationError` and silently suppressed HIGH-WARN constraint checks; v3.8.2 routes these failures through this aggregate so the operational signal surfaces without dropping audit coverage (option 4 — re-raise and abort — was rejected for that exact coverage reason). The formatter's REFUSE list is unchanged — UAF is advisory and does not enter REFUSE. See §3.6 for entry schema.

**Why `claim_drifts[]` is separate from the 8-row matrix (per D4-a):** The decision doc rejected "manifest authority blocking" because normal drafting routinely refines claims away from manifest, and gate-refusing on drift would block valid revision passes. The §3.4 schema houses drift findings; they emit a `[LOW-WARN-CLAIM-DRIFT — kind={EMITTED_NOT_INTENDED|INTENDED_NOT_EMITTED}]` annotation next to the offending sentence (for EMITTED_NOT_INTENDED) or in the manifest-coverage appendix (for INTENDED_NOT_EMITTED). Always advisory; never gate-refusing. Source-level defects (source_description / metadata / citation_anchor / synthesis_overclaim) remain HIGH-WARN in the matrix because they indicate the prose is misrepresenting the cited source — the L3 faithfulness failure the audit exists to catch. Constraint violations remain HIGH-WARN because the author explicitly declared "MUST NOT".

**Uncited-assertion** results emit at LOW-WARN tier with annotation `[UNCITED-ASSERTION]` next to the offending sentence. Always advisory; gate-refuse reserved for citation-level defects.

**`/ars-mark-read` behavior:** Does NOT acknowledge HIGH-WARN-CLAIM-NOT-SUPPORTED or HIGH-WARN-NEGATIVE-CONSTRAINT-VIOLATION. Remediation: user fixes the prose (re-cites, drops claim, revises). Mirrors v3.7.3 R-L3-1-A asymmetry (locator is structural, not evidence-state).

**Mode flag:** Audit agent dispatch is **opt-in** per pipeline run, configurable in `academic-pipeline/SKILL.md` mode flags. Default OFF for v3.8.0; ramp-on plan deferred to post-calibration calibration evidence.

## 6. Lint: `scripts/check_claim_audit_consistency.py`

Coverage:

1. **Schema validation** — `claim_audit_result.schema.json`, `claim_intent_manifest.schema.json`, `uncited_assertion.schema.json`, `claim_drift.schema.json`, `constraint_violation.schema.json` all valid JSON Schema; sample passports validate. Inline `audit_sampling_summary` entry schema (§4 step 3) also validated.
2. **Cross-field invariants INV-1 through INV-18** — one test case per invariant, each with positive + negative fixture.
3. **Manifest invariants M-INV-1 through M-INV-4** — including M-INV-4 manifest_id uniqueness across passport (duplicate manifest_id rejected).
4. **Uncited-assertion invariants U-INV-1 through U-INV-4** — including cross-array `(scoped_manifest_id, manifest_claim_id)` integrity (uncited entry's referenced (M-*, C-*) pair must match some active manifest's claim).
4a. **Claim-drift invariants D-INV-1 through D-INV-4** — including cross-array integrity for `drift_kind=INTENDED_NOT_EMITTED` (the `(scoped_manifest_id, manifest_claim_id)` pair must match some `claim_intent_manifests[]` entry) and exclusivity rule D-INV-4 (a sentence cannot appear in both `uncited_assertions[]` and `claim_drifts[]`).
4b. **Constraint-violation invariants CV-INV-1 through CV-INV-4** — including cross-array integrity (CV-INV-2: `(scoped_manifest_id, violated_constraint_id)` MUST resolve in some active manifest entry; CV-INV-3: `manifest_claim_id` polarity must match constraint id prefix MNC/NC) and per-(manifest, sentence, constraint) dedup (CV-INV-4 — see §3.5 for the full dedup key shape `(scoped_manifest_id, section_path, claim_text_hash, violated_constraint_id)`).
4c. **Audit-sampling invariants S-INV-1 through S-INV-4** — including audited_count/audited_indices coherence (S-INV-1), cap respect (S-INV-2), finalizer annotation requirement when sampled (S-INV-3), and audited_indices ascending uniqueness (S-INV-4). Validates `audit_sampling_summaries[]` aggregate.
4d. **Uncited-audit-failure invariants UAF-INV-1 through UAF-INV-6** (v3.8.2 / #118) — schema validation against `uncited_audit_failure.schema.json`; finding_id uniqueness (UAF-INV-1); scoped_manifest_id cross-array integrity (UAF-INV-2); `(scoped_manifest_id, manifest_claim_id)` pair integrity (UAF-INV-3); per-(sentence, manifest) dedup with key `(scoped_manifest_id, section_path, claim_text_hash)` (UAF-INV-4); rationale fault_class prefix (UAF-INV-5); cross-aggregate exclusivity with `constraint_violations[]` (UAF-INV-6). Validates `uncited_audit_failures[]` aggregate.
5. **Allowed-matrix coverage** — every `(judgment, audit_status, defect_stage)` triple outside §3.1 table rejected; representative disallowed combinations (≥ 5) tested explicitly.
6. **Precedence rules** — negative_constraint_violation (HIGH-WARN claim_audit_result) > claim_drift (LOW-WARN claim_drifts[] entry) — per issue body rule 1; citation_anchor distinct from source_description (rule 2); uncited-sentence cases produce `uncited_assertions[]` entry, not a `claim_audit_result` row (rule 3 — uncited has no ref to evaluate). D-INV-4 also enforces: a sentence that's both uncited AND drifted emits only the `uncited_assertion` entry, no companion `claim_drift` entry. UAF-INV-6 (v3.8.2 / #118) enforces cross-aggregate exclusivity between `uncited_audit_failures[]` and `constraint_violations[]` — see §3.6 for the full rule.
7. **Acceptance check** — for any passport with ≥ 1 completed `claim_audit_result` whose `judgment=UNSUPPORTED`, ALL such rows must emit a `defect_stage` ≠ null AND ≠ not_applicable (100% emission per #103 acceptance criterion). AMBIGUOUS-with-null is explicitly permitted per INV-3 (judge unable to classify a related-but-unclear support level is a valid outcome); the issue body's "100% non-SUPPORTED" intent is narrower than literal reading suggests — it targets the UNSUPPORTED rows because those are the gate-refusing path, not the advisory tier.
8. **Coverage check** — sample passport with full 8-row finalizer matrix coverage (per §5); each annotation tier exercised at least once.

Lint exit codes: 0 (pass), 1 (one or more invariant violations; prints which + offending entry).

CI: invoked from `.github/workflows/spec-consistency.yml` (or matching workflow). Failure blocks merge.

## 7. TDD test plan

Tests written BEFORE production code per `superpowers:test-driven-development`. Order:

### 7.1 Schema validation tests (`tests/test_claim_audit_schema.py`)

- T-S1: Valid minimal entry validates (SUPPORTED, all required fields)
- T-S2: Each invariant INV-1..INV-18 covered by paired positive/negative fixture
- T-S3: `anchor_kind=none` entry that doesn't follow INV-6 fails lint (rationale missing prefix; `ref_retrieval_method ≠ not_attempted`)
- T-S4: Manifest M-INV-1 duplicate claim_id rejected
- T-S5: Manifest M-INV-2 dangling NC-C{n}-{m} (no parent claim) rejected
- T-S6: Manifest M-INV-3 claim-level constraint attempting to override MNC rejected
- T-S7: `uncited_assertion` U-INV-1..U-INV-4 covered by paired positive/negative fixture (rule_version literal; trigger_tokens non-empty; cross-array manifest_claim_id integrity)
- T-S8: `(judgment, audit_status, defect_stage)` allowed-matrix exhaustive coverage: each table row in §3.1 has a positive fixture, AND at least 5 representative disallowed combinations rejected (e.g., SUPPORTED + non-null defect_stage; UNSUPPORTED + null defect_stage; RETRIEVAL_FAILED + completed + not_applicable)

### 7.2 Audit-pipeline unit tests (`tests/test_claim_audit_pipeline.py`)

- T-P1: Step 1 — anchor=none input emits RETRIEVAL_FAILED/inconclusive/not_applicable + `ref_retrieval_method=not_attempted` with INV-6 rationale prefix, skips judge
- T-P2: Step 3 — cache hit (with matching `retrieved_excerpt_hash`) returns previously-judged result without invoking judge
- T-P3: Step 3 — cache miss (different `retrieved_excerpt_hash` after user uploads manual PDF) invokes judge then writes back
- T-P4: Step 2 — `ref_retrieval_method=failed` → LOW-WARN advisory path (D2 paywall)
- T-P5: Step 2 — `ref_retrieval_method=manual_pdf` accepted; `not_found` triggers `defect_stage=retrieval_existence`
- T-P6: Step 5 — judge VIOLATED → UNSUPPORTED + defect_stage=negative_constraint_violation + violated_constraint_id populated
- T-P7: Step 6 — 6 in-table defect_stage classifications each have a fixture mapping (`retrieval_existence`, `metadata`, `source_description`, `citation_anchor`, `synthesis_overclaim`, `negative_constraint_violation`). `uncited_assertion` is tested in §7.4 and `claim_drift` in a new §7.4a (both separate entry-types, not defect_stages of `claim_audit_result`); `not_applicable` is tested in T-P1 and T-P4.
- T-P8: Precedence rule 1 — claim that drifts AND violates a constraint → emits `claim_audit_result` with `defect_stage=negative_constraint_violation` (judge-evaluated, HIGH-WARN); the same claim does NOT additionally emit a `claim_drifts[]` entry — constraint violation absorbs the drift signal per D4 (a) explicit author rules > advisory drift surfaces.
- T-P9: Precedence rule 2 — citation_anchor distinct from source_description (anchor wrong, source description correct)
- T-P10: Precedence rule 3 — sentence that would be both an uncited_assertion AND a drifted manifest claim emits an `uncited_assertions[]` entry (no source-level evaluation, since there's no ref to evaluate). The same sentence may still appear in manifest diff diagnostics but does NOT produce a `claim_audit_result` row.
- T-P11: Cap sampling behavior — synthetic input with N=150 citations and `max_claims_per_paper=100` emits exactly 1 `audit_sampling_summary` entry with `audited_count=100`, `audited_indices` strictly ascending and of length 100, `sampling_strategy=stratified_buckets_v1`. Finalizer adds `[CLAIM-AUDIT-SAMPLED — 100/150 audited]` to the AI Self-Reflection Report. Variants: (a) N=50 and cap=100 → no summary entry OR summary with `audited_count == total_citation_count` (telemetry mode, finalizer adds NO sampling annotation per S-INV-3); (b) cap=0 input rejected as invalid configuration.

### 7.3 Manifest tests (`tests/test_claim_intent_manifest.py`)

- T-M1: Three-set diff — emitted ∩ intended ∩ supported, drift detection
- T-M2: Missing manifest → MANIFEST-MISSING advisory + claim-extraction-from-draft fallback, all defect_stages still emit
- T-M3: Constraint inheritance — MNC applies even when not redeclared at claim level

### 7.4 Uncited-assertion tests (`tests/test_uncited_assertion.py`)

- T-U1: Sentence with quantifier + no ref → uncited_assertion candidate
- T-U2: Definition sentence (contains "refers to") → NOT candidate
- T-U3: Methods boilerplate list → NOT candidate
- T-U4: Empirical claim ("showed X%") without ref → candidate
- T-U5: Claim in manifest but no ref → still candidate (D4-c last paragraph)

### 7.5 Finalizer integration tests (`tests/test_claim_audit_finalizer.py`)

- T-F1: 8-row matrix coverage keyed by the FULL 3-tuple (judgment, defect_stage, ref_retrieval_method) — each row maps to its specific annotation + severity tier + gate behavior. CRITICAL: `RETRIEVAL_FAILED + not_applicable` admits three distinct rows discriminated by `ref_retrieval_method` ∈ {not_attempted, failed, audit_tool_failure} — a test keyed only on (judgment, defect_stage) would let an implementation collapse these three into one and apply the wrong gate behavior. The test MUST assert each ref_retrieval_method value independently against its expected outcome:
  - T-F1a: SUPPORTED + null + any → no annotation, pass
  - T-F1b: AMBIGUOUS + {source_description, citation_anchor, synthesis_overclaim, null} + any → CLAIM-AUDIT-AMBIGUOUS, LOW-WARN advisory, pass
  - T-F1c: UNSUPPORTED + {source_description, metadata, citation_anchor, synthesis_overclaim} + any → HIGH-WARN-CLAIM-NOT-SUPPORTED, gate-refuse
  - T-F1d: UNSUPPORTED + negative_constraint_violation + any → HIGH-WARN-NEGATIVE-CONSTRAINT-VIOLATION, gate-refuse
  - T-F1e: RETRIEVAL_FAILED + retrieval_existence + not_found → HIGH-WARN-FABRICATED-REFERENCE, gate-refuse
  - T-F1f: RETRIEVAL_FAILED + not_applicable + **not_attempted** → HIGH-WARN-CLAIM-AUDIT-ANCHORLESS, **gate-refuse** (defense-in-depth; distinguishes from row T-F1g/T-F1h)
  - T-F1g: RETRIEVAL_FAILED + not_applicable + **failed** → LOW-WARN-CLAIM-AUDIT-UNVERIFIED, **pass** (paywall)
  - T-F1h: RETRIEVAL_FAILED + not_applicable + **audit_tool_failure** → MED-WARN-CLAIM-AUDIT-TOOL-FAILURE, **pass** (retry-next-pass)
- T-F2: HIGH-WARN-CLAIM-NOT-SUPPORTED triggers terminal gate refuse
- T-F3: `/ars-mark-read` does NOT clear HIGH-WARN-CLAIM-NOT-SUPPORTED (asymmetry preservation)
- T-F4: LOW-WARN-CLAIM-AUDIT-UNVERIFIED passes gate
- T-F5: Stage 6 reflection report renders histogram when ≥ 5 completed entries

### 7.6 End-to-end test (`tests/test_e2e_claim_audit.py`)

Synthetic 5-citation paper:
- Citation 1: real, SUPPORTED → no annotation
- Citation 2: real, AMBIGUOUS → LOW-WARN
- Citation 3: real but misused (source says inverse) → HIGH-WARN-CLAIM-NOT-SUPPORTED, gate refuses
- Citation 4: paywalled, retrieval fails → LOW-WARN-UNVERIFIED, passes gate
- Citation 5: violates declared negative constraint → HIGH-WARN-NEGATIVE-CONSTRAINT-VIOLATION, gate refuses

Test asserts: gate refuses output; only citations 3+5 are blockers; correcting them clears refusal.

### 7.7 Calibration mode test (`tests/test_claim_audit_calibration.py`)

Synthetic 20-tuple gold set covering alignment judgments (SUPPORTED/UNSUPPORTED/AMBIGUOUS/RETRIEVAL_FAILED) AND constraint judgments (VIOLATED/NOT_VIOLATED). Gold tuple shape per decision doc D3(c): `{tuple_kind, claim_text, ref_text_excerpt, anchor, expected_judgment, ...}` discriminated by `tuple_kind ∈ {alignment, constraint}`. For `tuple_kind=constraint`, REQUIRED fields: `constraint_under_test_id` AND (`constraint_under_test_rule_text` OR `manifest_fixture_path`). NOT_VIOLATED tuples MUST appear in the gold set (≥3 tuples; without them constraint FPR is unmeasurable). Suggested gold-set split: ~12 alignment tuples (covering 4 judgments) + ~8 constraint tuples (≥3 VIOLATED + ≥3 NOT_VIOLATED + remainder edge cases). Three-tier assertion:

- **T-C1 (threshold enforcement):** Test assert `FNR < 0.15 AND FPR < 0.10` against the synthetic gold set. Test FAILS when either threshold is exceeded. This is the unit of acceptance and aligns with reviewer-calibration convention (FNR/FPR thresholds are gates, not advisory). When the threshold is exceeded, CI fails — author must either curate a better gold set, tighten judge prompts, or update `judge_model`. (Issue body acceptance criterion + §9 acceptance bullet are binding.)
- **T-C2 (per-class FNR/FPR reporting):** Test asserts that FNR/FPR are computed AND surfaced per judgment-class (SUPPORTED vs UNSUPPORTED, AMBIGUOUS, violated-constraint) in the calibration report output. Reporting failure ≠ threshold failure — this catches calibration tooling regressions distinct from gold-set degradation.
- **T-C3 (gold-set shape integrity):** Test asserts: (a) Each tuple has a valid `tuple_kind ∈ {alignment, constraint}`. (b) `tuple_kind=alignment` tuples have `expected_judgment ∈ {SUPPORTED, UNSUPPORTED, AMBIGUOUS, RETRIEVAL_FAILED}` AND MUST NOT carry constraint fields. (c) `tuple_kind=constraint` tuples have `expected_judgment ∈ {VIOLATED, NOT_VIOLATED}` AND `constraint_under_test_id` MUST be present AND (`constraint_under_test_rule_text` OR `manifest_fixture_path`) MUST be present. (d) The gold set MUST contain ≥3 NOT_VIOLATED constraint tuples (else constraint FPR is unmeasurable and T-C1 cannot fail-on-threshold for the constraint line). Tuples violating any rule are REJECTED at calibration ingestion (lint-fail with diagnostic naming the violation). Prevents silent-skip regressions: missing rule text → judge evaluates against empty constraint → false NOT_VIOLATED → artificially low FNR; missing NOT_VIOLATED tuples → constraint FPR uncomputable → T-C1 silently bypassed.

Why three tiers: T-C2 catches infrastructure bugs (calibration script doesn't compute / doesn't write report); T-C3 catches gold-set authoring bugs (missing required rule text); T-C1 catches model/judge quality regression. All three must pass.

### 7.8 Regression test

Run existing 967+ test baseline (1107 unittest + 201 pytest adapters per session handoff). Zero regression required.

## 8. Cascade impact assessment

Files that may need touch:

| File | Why | Risk |
|---|---|---|
| `academic-pipeline/agents/pipeline_orchestrator_agent.md` | New §3.6 dispatch wiring | HIGH — already 712 lines; PATTERN PROTECTION block must stay byte-equivalent |
| `academic-paper/agents/formatter_agent.md` | Gate matrix extended to 8-row + HIGH-WARN classes | MED — 785 lines; v3.7.3 anchor logic preserved |
| `deep-research/agents/synthesis_agent.md` | New "Claim Intent Manifest Emission" sibling heading | MED — 220 lines; v3.7.3 Three-Layer heading stays |
| `deep-research/agents/report_compiler_agent.md` | Same | MED |
| `academic-paper/agents/draft_writer_agent.md` | Same | MED — 520 lines |
| `shared/contracts/passport/audit_artifact_entry.schema.json` | **NO TOUCH** (D5) | — |
| `shared/contracts/material_passport*` | No root schema exists; aggregate referenced through orchestrator | — |
| `shared/sprint_contract.schema.json` (Schema 13.1) | **NO TOUCH** (D6 zero-touch) | — |
| `scripts/check_audit_artifact_consistency.py` | **NO TOUCH** (D5 — separate lint) | — |
| `README.md` + `README.zh-TW.md` | v3.8 anchor + Zhao 2026 + RubricEM cite | LOW |
| `CHANGELOG.md` | v3.8 entry | LOW |
| `MODE_REGISTRY.md` | New mode flag for opt-in audit | LOW |

Boundary preservation lints (run as part of PR checks):
- `scripts/check_v3_6_7_pattern_protection.py` — verify PATTERN PROTECTION blocks unchanged
- `git diff main..HEAD -- shared/sprint_contract.schema.json` MUST be empty (v3.6.6 zero-touch)
- `git diff main..HEAD -- shared/contracts/passport/audit_artifact_entry.schema.json` MUST be empty (D5)

## 9. Acceptance criteria

Issue body acceptance + decision-doc-derived additions:

- [ ] Agent prompt passes ≥ 5 codex review rounds → 0 P1/P2 (new tool + IO, per harness convergence pattern)
- [ ] Schema + integration passes ≥ 1 gemini cross-model review round (docs-heavy fraction; see Codex 0.130 docs-review broken caveat — verify before invoking)
- [ ] Calibration mode tested with synthetic gold set (≥ 20 tuples) achieving FNR < 0.15 and FPR < 0.10
- [ ] End-to-end test (§7.6 above) passes
- [ ] Zero regression on existing 1107+ unittest + 201 pytest baseline
- [ ] All 18 cross-field invariants (INV-1..INV-18) + 4 manifest invariants (M-INV-1..M-INV-4) + 4 uncited-assertion invariants (U-INV-1..U-INV-4) + 4 claim-drift invariants (D-INV-1..D-INV-4) + 4 constraint-violation invariants (CV-INV-1..CV-INV-4) + 4 sampling invariants (S-INV-1..S-INV-4) covered by paired positive/negative fixture
- [ ] Allowed-matrix exhaustive test: every §3.1 table row positive + ≥5 disallowed combinations rejected
- [ ] `claim_intent_manifest` absent → `MANIFEST-MISSING` advisory + fallback flow exercised in test
- [ ] `audit_status=inconclusive` paths emit `defect_stage=not_applicable` (NOT `null`) — INV-4
- [ ] 100% of completed UNSUPPORTED findings emit a `defect_stage` ≠ null AND ≠ not_applicable (per #103 issue body acceptance criterion; AMBIGUOUS-null is permitted per INV-3 — stage accuracy deferred to #89)
- [ ] Stage 6 reflection report renders per-stage histogram when ≥ 5 completed audit results
- [ ] v3.6.6 Schema 13.1 zero-touch promise verified by git diff lint
- [ ] D5 `audit_artifact_entry.schema.json` zero-touch promise verified by git diff lint
- [ ] Precedence rules (3 rules per issue body) covered by test fixtures
- [ ] Public-repo boundary clean per personal-boundary deny list (run boundary scan before push)

## 10. Risks and open questions

The decision doc closed 8 OQs. Spec-level OQs (resolve during codex rounds, NOT before TDD):

- **S-OQ1** (codex round-1 candidate): cache eviction policy beyond manual rm. Tentative: rely on `judge_model` in cache key — model bumps naturally invalidate; users prune `${ARS_CACHE_DIR}/claim_audit_v1/` as needed.
- **S-OQ2** (codex round-1): retrieval API selection order (Semantic Scholar vs Crossref vs OpenAlex) and fallback ladder. Tentative: SS → Crossref → OpenAlex → manual_pdf, matching v3.6.x convention.
- **S-OQ3** (codex round-2): `claim_id` allocation — sequential per manifest or session-scoped UUID-prefix? Tentative: sequential per manifest (`C-001`, `C-002`...), uniqueness scope = single manifest entry. Cross-manifest collision tolerated (different agent invocations).
- **S-OQ4** (codex round-2): `audit_run_id` collision handling when two audits run within same second. Tentative: 4-hex random suffix (already in schema pattern) gives ~65k uniqueness per second; assume sufficient for ARS scale.
- **S-OQ5** (codex round-2+): manifest emission timing — exact lifecycle hook in `synthesis_agent` and `draft_writer_agent`. Tentative: emit AFTER `literature_corpus[]` consumption, BEFORE first prose block. Confirm during prompt-design rounds.

## 11. Convergence cost projection

Per session handoff harness data:
- doc-only PR = 1 round
- plumbing PR = 3-4 rounds
- new tool + IO PR = **5 rounds**
- scope-frozen follow-up = 3 rounds

#103 is **new tool + IO + new agent + 2 new schemas + new lint + 6 prompt edits**, larger than #105 (which was "new tool + IO migration"). Expected codex rounds: **5-7**.

Strategy: split into two PRs if Round-5 still has open P1/P2:
- PR-A: schemas + lint + agent prompt + tests (no orchestrator/formatter/synthesis_agent touch yet)
- PR-B: orchestrator §3.6 + finalizer 8-row + downstream agent integration

This mirrors #105 → #115 split pattern (production module first, integration follow-up).

## 12. Memory anchors

After ship, update:

- private maintainer memory (`project_ars_106_ai_disclosure_discovery`) — lesson #22 (8-OQ compressed decision-doc pattern when issue body already has frozen design)
- private maintainer memory (`feedback_codex_round_convergence_by_scope`) — new memory if not exists, record "new tool + IO + new agent" data point
- Consider new memory `feedback_audit_results_vs_audit_artifact_semantic_split.md` documenting D5 boundary

## 13. Implementation order (TDD-driven)

1. Write all 5 schema files up front (§3.1 claim_audit_result + §3.2 claim_intent_manifest + §3.3 uncited_assertion + §3.4 claim_drift + §3.5 constraint_violation) plus the inline `audit_sampling_summary` schema (§4 step 3). All five + inline are referenced by §6 schema-validation lint rule 1 + §7.1 schema tests; writing only §3.1/§3.2 first would make T-S1..T-S8 fail with "schema not found" diagnostics for the missing 3.
2. Write `tests/test_claim_audit_schema.py` — failing because schema not yet validated by lint
3. Write `scripts/check_claim_audit_consistency.py` — minimal code to pass schema tests
4. Write `tests/test_claim_audit_pipeline.py` (T-P1..T-P11) — failing, no agent yet
5. Write `claim_ref_alignment_audit_agent.md` Steps 1-6 — minimal text to pass pipeline tests via fixture-driven dispatch
6. Write `tests/test_uncited_assertion.py` + token-rule detector module
7. Write `tests/test_claim_intent_manifest.py` + emission helpers
8. Write `tests/test_claim_audit_finalizer.py` + orchestrator §3.6 + formatter 8-row extension
9. Write `tests/test_e2e_claim_audit.py` + synthetic 5-citation paper fixture
10. Write `tests/test_claim_audit_calibration.py` + calibration protocol doc
11. Regression run on full baseline; zero failures
12. `/simplify` parallel (reuse + quality + efficiency); fix findings
13. `/codex review --base=main`; iterate to 0 P1/P2
14. gemini cross-model round (verify Codex 0.130 docs-heavy caveat first per `feedback_codex_0_130_docs_review_broken.md`)
15. Public-repo boundary scan
16. Squash merge

Steps 4-5 are the highest-risk: agent prompt + pipeline are the load-bearing intersection. Plan for 2-3 codex rounds focused there.
