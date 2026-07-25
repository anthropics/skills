# Re-Review Mode (Verification Review)

Re-review mode is the dedicated mode for Pipeline Stage 3', designed to **verify whether revisions address the first-round review comments**.

### How It Works

```
Input:
1. Original Revision Roadmap (Stage 3 output)
2. Revised manuscript
3. Response to Reviewers (optional)

Phase 0: Reads the Revision Roadmap, builds a checklist
Phase 1: EIC checks each item (other reviewers not activated)
Phase 2: Editorial Synthesis -> New Decision
```

### Verification Logic

```
For each item in the Revision Roadmap:

Priority 1 (Required):
  -> Check each item for corresponding changes in the revised manuscript
  -> Assess revision quality (FULLY_ADDRESSED / PARTIALLY_ADDRESSED / NOT_ADDRESSED / MADE_WORSE)
  -> All Priority 1 items must be FULLY_ADDRESSED for Accept

**Traceability Rule**: For each Priority 1 item, the reviewer MUST:
1. Read the author's claim from the Response to Reviewers
2. Navigate to the stated revision location in the manuscript
3. Independently verify the claim matches the actual change
4. If Author's Claim is empty or vague ("addressed as suggested"), mark Verified? as `🔍 Cannot verify` and flag in Quality Assessment

Priority 2 (Suggested):
  -> Check each item
  -> At least 80% should have a response
  -> NOT_ADDRESSED items require author explanation

Priority 3 (Nice to Fix):
  -> Check but does not affect Decision
```

### Commitment Ledger Verification (Kong A1 / v3.11)

This step runs **for every Schema 11 row** (any priority) that carries a non-empty `commitment_extracted` list from `revision_coach_agent` Step 3.5. It is independent of the Priority 1/2/3 Traceability Rule above — every parsed reviewer comment may produce commitments, and every commitment must be verified, regardless of the parent concern's priority.

For each commitment, verify per-commitment `fulfillment_status`:

- `fulfilled` — the `required_evidence_type` is present and substantively addresses the `commitment_text`. Verification site depends on `required_evidence_type`:
  - For `new_section` / `new_figure` / `new_table` / `new_citation` / `methods_paragraph` / `discussion_paragraph` / `prose_edit` — verify against the **revised manuscript** at `revision_location`. `prose_edit` items (typo fixes, terminology clarifications, equation formatting, citation-style corrections) are sentence- or paragraph-level changes; verify the specific text at `revision_location` rather than expecting a new structural block.
  - For `acknowledgment_only` — verify against the **Response to Reviewers (Schema 8)** instead of the manuscript diff. `acknowledgment_only` items by definition do not require manuscript changes; expecting a manuscript diff would produce false `not-fulfilled` classifications. The response letter must explicitly acknowledge or address the commitment in writing.
  - For `other` — the evidence type is intentionally underspecified (escape hatch for genuinely uncategorizable commitments). Surface a soft **`EVIDENCE_TYPE_UNSPECIFIED`** advisory (advisory only, **not** a hard block): if `revision_location` is empty, prompt the author to specify it so the re-reviewer can verify; if `revision_location` is already populated, the advisory simply flags that the evidence type was left uncategorized — verify at the stated location. This is distinct from `COMMITMENT_GAP` (which fires on missing rationale for a non-`fulfilled` status); `EVIDENCE_TYPE_UNSPECIFIED` fires whenever `required_evidence_type == other`, regardless of `fulfillment_status`.
- `partial` — required evidence exists but does not fully address the commitment (e.g., experiment run on dataset Y when reviewer asked for dataset X; 3-seed std error when 5-seed was requested with rationale provided).
- `not-fulfilled` — required evidence is absent (rationale presence is a separate axis — see `COMMITMENT_GAP` rule below).
- `explicitly-rejected-with-rationale` — author has explicitly declined to address the commitment; status name implies rationale, but `unfulfilled_rationale` is still the field that carries the actual rationale text (per Schema 11 Validation rule).

For any commitment object with `fulfillment_status` ∈ `{partial, not-fulfilled, explicitly-rejected-with-rationale}` where the object's `unfulfilled_rationale` is empty or missing, surface a **`COMMITMENT_GAP`** entry in re-review output (advisory only, **not** a hard block — author retains final responsibility per `POSITIONING.md`). This mirrors the Schema 11 Validation rule: any non-`fulfilled` status requires a rationale on the same commitment object. Because `fulfillment_status` and `unfulfilled_rationale` are nested fields of the commitment object (not separate parallel lists), there is no index-walking step and no way to pair a status with the wrong commitment — the #268 desync failure mode is structurally absent.

**A populated `residual_action` alongside one or more commitment objects with `fulfillment_status: fulfilled` is not a contradiction.** `residual_action` operates at the concern level (forward-looking: what still remains for the whole concern), while `fulfillment_status` is per-commitment (carried on each commitment object). A concern can have some commitments fully fulfilled and still carry a concern-level residual action (e.g., the core ablation was added but the concern's broader generalization claim still needs a follow-up experiment flagged in `residual_action`). Do **not** raise a gap or inconsistency flag merely because `residual_action` is non-empty while one or more commitments are `fulfilled` — see `shared/handoff_schemas.md` Schema 11 `residual_action` convention (a).

This section is the verification analog of `revision_coach_agent` Step 3.5 (Kong A1). Per-commitment lifecycle gating is what closes the Kong §7.4.3 commitment-fulfillment gap.

### New Issue Detection

```
In addition to checking old items, EIC also scans for:
- Whether content added during revision introduces new problems
- Whether newly added references are correct (but deep verification is left to Stage 4.5 integrity check)
- Whether revisions cause inconsistencies
```

### Socratic Guidance After Re-Review

```
If Re-Review Decision = Major Revision:
  -> Activate Residual Coaching (residual issue guidance)
  -> EIC guides user through Socratic dialogue:
    1. Gap analysis — "How many issues did the first round of revisions resolve? Why are the remaining ones hard to address?"
    2. Root cause diagnosis — "Is it insufficient evidence, unclear argumentation, or a structural problem?"
    3. Trade-off decisions — "Which ones can be marked as research limitations?"
    4. Action plan — Plan revision approach for each residual issue
  -> Maximum 5 rounds of dialogue
  -> User can say "just fix it" to skip guidance
```

### Re-Review Output Format

```markdown
# Verification Review Report

## Decision
[Accept / Minor Revision / Major Revision]

## Revision Response Checklist

### Priority 1 — Required Revisions

| # | Original Review Comment | Author's Claim | Response Status | Revision Location | Verified? | Quality Assessment |
|---|------------------------|---------------|-----------------|-------------------|-----------|-------------------|
| R1 | [Original text] | [What the author claims to have done in Response to Reviewers] | FULLY_ADDRESSED | Section X.X | ✅ Yes | Adequately addressed; newly added content effectively resolves the issue |
| R2 | [Original text] | [Author's stated change] | PARTIALLY_ADDRESSED | Section Y.Y | ⚠️ Partial | Partially addressed, but still missing [specific gap] |

### Priority 2 — Suggested Revisions

| # | Original Review Comment | Response Status | Notes |
|---|------------------------|-----------------|-------|
| S1 | [Original text] | FULLY_ADDRESSED | -- |
| S2 | [Original text] | NOT_ADDRESSED | Author explanation: [reason] |

### Priority 3 — Nice to Fix

| # | Original Review Comment | Response Status |
|---|------------------------|-----------------|
| N1 | [Original text] | FULLY_ADDRESSED |

## New Issues (Discovered During Revision)

| # | Type | Location | Description |
|---|------|----------|-------------|
| NEW-1 | [Type] | Section X.X | [Description] |

## Decision Rationale
[Rationale based on the checklist]

## Residual Issues (If Any)
[List unresolved items, suggest marking as Acknowledged Limitations]
```

## v3.6.2 sprint contract status

v3.6.2 introduces sprint contracts for `reviewer_full` and `reviewer_methodology_focus` only. A template for this mode will follow in a subsequent patch release. Until then, this mode runs without contract enforcement and retains its pre-v3.6.2 behaviour.
