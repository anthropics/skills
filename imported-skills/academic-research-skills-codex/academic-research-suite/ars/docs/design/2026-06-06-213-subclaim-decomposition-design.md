# #213 — Sub-claim decomposition before citation judgment (partial-evidence trap)

**Status**: design (brainstormed 2026-06-06)
**Issue**: [#213](https://github.com/Imbad0202/academic-research-skills/issues/213) (Kim et al. 2026 META #217)
**Target agent**: `academic-pipeline/agents/claim_ref_alignment_audit_agent.md`
**Paper anchor**: Kim et al. 2026 (arXiv:2605.20668v1) §F.3.2 — the partial-evidence trap is the single largest correctness-error class in AI meta-review (41/54, 76%).

---

## Problem

The §F.3.2 failure mode: an AI judge treats a multi-part claim as a single binary check. When a cited source supports one sub-claim of a compound assertion but not another, the judge collapses the whole item to one verdict and the unsupported sub-claim is silently lost — "partial support treated as full resolution."

ARS's unified citation judge (`claim_ref_alignment_audit_agent.md:159-189`) emits exactly one verdict per citation. It has the same shape as the documented failure: compound claim in, one verdict out, no enumeration of the parts.

## Baseline correction (the issue body's premise was wrong)

The issue's acceptance assumed the current verdict set is `{SUPPORTED, UNSUPPORTED, AMBIGUOUS, VIOLATED}` and proposed a 5-class schema enum adding `PARTIAL`. First-party reading of the code shows that is not the architecture:

- **Prompt layer** (`...agent.md:161,173-177`) emits a 4-class verdict `{SUPPORTED, UNSUPPORTED, AMBIGUOUS, VIOLATED}`.
- **Schema layer** (`claim_audit_result.schema.json:51-53`) `judgment` enum is `{SUPPORTED, UNSUPPORTED, AMBIGUOUS, RETRIEVAL_FAILED}` — **no `VIOLATED`**.
- A **normalization layer** sits between them: Step 6 (`...agent.md:191-216`) maps prompt-`VIOLATED` → `judgment=UNSUPPORTED, defect_stage=negative_constraint_violation`. Prompt verdict ≠ schema judgment.
- The schema is governed by **18 cross-field invariants (INV-1..INV-18)** in `scripts/check_claim_audit_consistency.py`, including an `ALLOWED_MATRIX` of `(judgment, audit_status, defect_stage)` triples. Adding a `PARTIAL` to the schema `judgment` enum would force a new INV row, a new matrix entry, and a calibration per-class change — none of which the issue accounted for.

So the issue's "add PARTIAL to the schema enum" step is built on a wrong baseline. The **intent** (enumerate sub-claims before judging) is correct; the proposed landing is not.

## Design (chosen: B + B1 + C2)

Three decisions, made during brainstorming:

### B — `PARTIAL` lives at the prompt verdict layer only

`PARTIAL` is a new prompt-layer verdict, parallel to how `VIOLATED` already exists at the prompt layer without being a schema `judgment` value. It is **not** added to the schema `judgment` enum. This keeps the 18 INVs and the `ALLOWED_MATRIX` untouched.

The judge prompt gains a required **Step 0**: decompose `claim_text` into atomic sub-claims `1..N` and judge each independently before emitting the citation-level verdict. The prompt emits `PARTIAL` when the reference supports some sub-claims but not others — distinct from `AMBIGUOUS` (which stays "related but unclear whether supported").

### B1 — Step 6 normalizes `PARTIAL` → `judgment=UNSUPPORTED`

Rationale: the harm the trap causes is letting an unsupported sub-claim ride through as if resolved. Normalizing `PARTIAL` to `UNSUPPORTED` ensures the unsupported sub-claim trips the same HIGH-WARN gate-refuse path that a fully-unsupported claim does — partial support is never silently accepted as full resolution. This is the conservative, paper-aligned choice.

`defect_stage` for a normalized-PARTIAL row uses the existing `source_description` value — a deliberately **neutral** choice, NOT `synthesis_overclaim`. `synthesis_overclaim` carries a specific semantic ("source content correct, but the draft over-strengthens the claim", `...agent.md:208`), and a downstream consumer that reads `defect_stage` to suggest "hedge the wording" would mishandle a partial-support row whose real fix is "remove this sub-claim" or "add a second citation." Partial support is a different defect than over-strengthening. `source_description` ("source describes something different than the claim asserts across the sub-claims") is the closest neutral fit already in the UNSUPPORTED allowed-set, so **no `ALLOWED_MATRIX` / INV-2 change**.

**The machine-readable partial signal is the presence of `sub_claim_breakdown[]` itself**, not the `defect_stage` value. Consumers that need to distinguish "partial support" from "fully unsupported" read `sub_claim_breakdown != null`, a first-class structured field — they do NOT have to notice a `defect_stage` overload or scan the human-facing `rationale`. (Review correction: do not encode partial-ness by overloading an existing categorical with a divergent meaning.)

**Verdict priority:** when a claim both violates an active constraint AND is partial, `VIOLATED` wins. The prompt's existing `VIOLATED` short-circuit (`...agent.md:191`) outranks `PARTIAL`; Step 0 decomposition still runs, but the citation-level verdict is `VIOLATED`, routed to the constraint path unchanged. `PARTIAL` is only emitted when no active constraint is violated.

**Malformed-output path:** if the judge emits prompt-verdict `PARTIAL` but does not produce a valid `sub_claim_breakdown` (fewer than 2 sub-claims, or no mixed verdicts, or unparseable), the pipeline does NOT silently coerce to a bare `UNSUPPORTED` — that would recreate the invisible trap this issue exists to close. Instead it emits an `audit_status=inconclusive` row with a `[partial_breakdown_malformed]` rationale tag and surfaces it for re-run, mirroring the existing `audit_tool_failure` inconclusive path. A `PARTIAL` claim without an inspectable decomposition is treated as "the judge could not complete", not "the judge said unsupported."

### C2 — new additive optional schema field `sub_claim_breakdown[]`

The enumerate-before-judge discipline must be **auditable**, not a prompt slogan. The meta-reviewer failed precisely because the decomposition was invisible. A new optional array on `claim_audit_result` makes the decomposition a first-class, inspectable artifact:

```jsonc
"sub_claim_breakdown": {
  "type": "array",
  "items": {
    "type": "object",
    "additionalProperties": false,
    "required": ["sub_claim_text", "sub_verdict"],
    "properties": {
      "sub_claim_text": {"type": "string", "minLength": 1, "maxLength": 1000},
      "sub_verdict": {"enum": ["SUPPORTED", "UNSUPPORTED", "AMBIGUOUS"]},
      "evidence_pointer": {"type": ["string", "null"], "maxLength": 1000}
    }
  },
  "description": "Per-sub-claim decomposition (issue #213). Present iff the judge emitted prompt-verdict PARTIAL — i.e. ≥2 sub-claims with at least one SUPPORTED AND at least one non-SUPPORTED — normalized to judgment=UNSUPPORTED, defect_stage=source_description. Its presence IS the machine-readable partial-support signal (consumers read this, not defect_stage). Absent on non-decomposed single-claim verdicts and on fully-unsupported claims. Additive/optional — pre-#213 entries stay valid."
}
```

`rationale` keeps its existing one-sentence semantics (it has **no downstream parser** — verified by grep, it is human-facing only); the structured breakdown rides in its own field rather than being stuffed into the sentence.

## What changes

| Layer | File | Change |
|---|---|---|
| Prompt | `claim_ref_alignment_audit_agent.md` | Step 0 decomposition; `PARTIAL` added to prompt verdict set + output format; Step 6 normalization row for `PARTIAL → UNSUPPORTED / source_description` + emit `sub_claim_breakdown[]` |
| Prompt | `claim_ref_alignment_audit_agent.md` | (Step 6 cont.) `VIOLATED` outranks `PARTIAL`; malformed-`PARTIAL` → `audit_status=inconclusive` with `[partial_breakdown_malformed]`, not silent `UNSUPPORTED` |
| Schema | `claim_audit_result.schema.json` | Add optional `sub_claim_breakdown[]` property (additive; `additionalProperties:false` honored by declaring it) |
| Lint | `scripts/check_claim_audit_consistency.py` | Add one invariant (INV-19): when `sub_claim_breakdown` is present it has **≥2 items with ≥1 `SUPPORTED` AND ≥1 non-`SUPPORTED`** `sub_verdict` (true-partial definition — "≥1 non-SUPPORTED" alone wrongly admits an all-UNSUPPORTED breakdown), the row's `judgment` is `UNSUPPORTED`, **and `defect_stage` is `source_description`** (pins the full B1 normalization, so a future edit can't emit a breakdown on a SUPPORTED row or drift the defect_stage) |
| Calibration | `claim_audit_calibration_protocol.md` + `scripts/fixtures/claim_audit_calibration/gold_set.json` | ≥5 partial-support fixtures (compound claim, mixed sub-claim support). `expected_judgment=UNSUPPORTED` (B1). **Plus a partial-support subset metric** tracked separately from the aggregate: a partial fixture is "passed" only when the judge emits `PARTIAL` AND a well-formed `sub_claim_breakdown`, not merely a bare `UNSUPPORTED`. Without this, a judge that regresses to "stop decomposing, just say UNSUPPORTED" still satisfies `expected_judgment` and the aggregate FNR/FPR gate hides the exact regression #213 exists to catch. The aggregate gate `<0.15 / <0.10` must still hold on the extended set. |
| Tests | `scripts/test_claim_audit_schema.py`, `scripts/test_claim_audit_consistency*.py` | Positive (valid breakdown), negative (breakdown on SUPPORTED row fails INV-19), mutation (accept-all guard) |

## What does NOT change (scope guard)

- Schema `judgment` enum — untouched.
- `ALLOWED_MATRIX` / INV-1..INV-18 triples — untouched (B1 reuses the existing `UNSUPPORTED / source_description` triple).
- `VIOLATED` short-circuit (Step 6 constraint path) — untouched.
- Synthesis-layer aggregation (#214) — out of scope, sibling issue.
- Calibration threshold values (T-C1 `<0.15 / <0.10`) — unchanged gate; only the gold set grows.

## Acceptance (rewritten to match the real architecture)

- [ ] Judge prompt shows sub-claim decomposition as a required Step 0.
- [ ] `PARTIAL` exists at the prompt verdict layer; Step 6 normalizes it to `judgment=UNSUPPORTED, defect_stage=source_description` and emits `sub_claim_breakdown[]`. `VIOLATED` outranks `PARTIAL`.
- [ ] Malformed `PARTIAL` (breakdown absent / <2 sub-claims / not true-partial) → `audit_status=inconclusive` + `[partial_breakdown_malformed]`, never a silent bare `UNSUPPORTED`.
- [ ] `sub_claim_breakdown[]` is an additive optional schema field; pre-#213 entries validate unchanged. Its presence is the machine-readable partial signal.
- [ ] INV-19 pins the full B1 normalization (breakdown ⟹ `judgment=UNSUPPORTED` AND `defect_stage=source_description` AND ≥2 sub-claims with ≥1 SUPPORTED AND ≥1 non-SUPPORTED).
- [ ] Gold set gains ≥5 partial-support fixtures; aggregate FNR `<0.15` / FPR `<0.10` holds (T-C1 maintained) AND a separate partial-support subset metric requires `PARTIAL` + well-formed breakdown (not a bare `UNSUPPORTED`) to pass.
- [ ] Schema + consistency tests cover positive / negative / mutation; existing suite stays green.

## Review provenance

- **Round-1 independent review** (2026-06-06): an independent review pass over the four first-party files confirmed the core "PARTIAL out of schema enum" decision is sound, and surfaced five real defects, all adopted:
  1. `synthesis_overclaim` semantic overload → switched to the neutral `source_description` defect_stage, with the breakdown's *presence* as the partial signal (decision D1).
  2. INV-19 true-partial definition: "≥1 non-SUPPORTED" alone wrongly admits an all-UNSUPPORTED breakdown; tightened to "≥1 SUPPORTED AND ≥1 non-SUPPORTED".
  3. INV-19 also pins `defect_stage=source_description`, not just the judgment.
  4. Calibration gains a partial-support subset metric so a judge regressing to bare-`UNSUPPORTED` can't pass on `expected_judgment` alone.
  5. Malformed-`PARTIAL` takes an `inconclusive` path rather than a silent `UNSUPPORTED`; `VIOLATED` outranks `PARTIAL`.
- Confirmed the consistency lint reads the shipped schema directly, with no separate field allowlist, so the additive `sub_claim_breakdown` field is accepted once declared.

## Ship gate

Docs/schema/lint/test diff. Before merge: independent review + security review, both clean. Mutation test on the new INV-19 (a trivial accept-all replacement must FAIL, proving the invariant discriminates).
