# The 4 Checks — Full Detail

Comprehensive per-check evaluation logic for the Critic Gate, including pass evidence requirements, REQUEST_CHANGES findings (fixable issues the change author can address), REJECT findings (non-negotiable violations requiring scope-authorization escalation), and worked examples. Use this when running a check and needing the authoritative finding language, or when authoring a profile and wanting to understand which findings each check can produce.

**When to consult this file:** When evaluating a proposed change against any of the four checks, when authoring or debugging a profile that produces unexpected check behavior, when a finding's severity classification is unclear, or when a user asks "show me what each check looks like in practice."

---

## Table of Contents

1. [Check 1 — Invariant Compliance](#check-1--invariant-compliance)
2. [Check 2 — Scope Authorization](#check-2--scope-authorization)
3. [Check 3 — Detection Narrowness](#check-3--detection-narrowness)
4. [Check 4 — Regression Risk](#check-4--regression-risk)
5. [Worked Examples](#worked-examples)

---

## Check 1 — Invariant Compliance

The proposed change does not modify any element protected by the authority matrix.

### Pass evidence

The change diff has been examined against every tier of the authority matrix. No source-only content is modified. No mirror-exact content is altered (only mirrored). Free-design changes stay within the free-design tier. The evidence captures *which tier(s)* the change touched and confirms each touch was authorized.

### REQUEST_CHANGES findings (severity: minor or major)

The change touches a tier the author may not have noticed. Author should narrow scope.

**Example finding:** A change intended to fix layout (Tier 3 UI chrome) accidentally rewrites primary content (Tier 1 protected). Author re-scopes to layout only.

**Recommended action language:** "Change touches Tier 1 protected content at [specific location]. The change's stated intent is Tier 3 (UI chrome). Re-scope to leave Tier 1 content unmodified, or escalate if Tier 1 modification was intentional."

### REJECT findings (severity: blocker)

The change deliberately modifies invariant content with no scope-authorization escalation.

**Example finding:** Change author rewrites a quoted source passage because "the original wording was unclear." This is a §19.2 violation regardless of intent.

**Recommended action language:** "Change deliberately modifies Tier 1 protected content with no escalation. Cannot re-propose without human authorization for the specific modification. The 'clearer wording' rationale is not within the Critic's authority to accept — escalate to scope-authorization decision."

### Edge cases

- **Modification that is technically Tier 1 but trivially additive (e.g., adding metadata fields without changing semantic content):** Surface as `info` finding, do not auto-fail. The boundary between "addition" and "modification" depends on the matrix; if unclear, lean toward REQUEST_CHANGES with a clarifying question for the author.
- **Authority matrix tier is documented but the affected element's tier assignment is ambiguous:** Surface as REQUEST_CHANGES with a finding to disambiguate the tier in the matrix itself before re-proposing.

---

## Check 2 — Scope Authorization

The proposed change falls within the in-scope authorization for autonomous iteration. Out-of-scope changes require human escalation regardless of merit.

### Pass evidence

The change's category appears in the in-scope list (engine fix, additive evolution with narrow detection, test addition, formatting/style fix). Or: the change appears in the in-scope-with-notification list AND surfaces appropriately. No category in the out-of-scope list is touched.

### REQUEST_CHANGES findings (severity: minor)

The change is substantively in-scope but missing required surfacing.

**Example finding:** A cross-cutting refactor that didn't generate a notification entry in the change log.

**Recommended action language:** "Change is category 'cross-cutting refactor' which is in-scope-with-notification. Required surfacing entry is missing from change_log. Add the entry and re-submit."

### REJECT findings (severity: blocker)

The change is in the out-of-scope list. Cannot proceed without human authorization. The Critic does not have authority to grant exceptions.

**Example finding:** Change modifies invariant infrastructure, deletes test cases, or uses `--force` operations.

**Recommended action language:** "Change category '[name]' is in the explicit out-of-scope list per authorization. Cannot re-propose without human scope-authorization decision. The Critic Gate cannot grant exceptions to the authorization list."

### Edge cases

- **Change spans multiple categories (e.g., refactor + test addition + formatting):** Each category is evaluated independently. The verdict is the strictest of the per-category verdicts. If the test-addition portion is in-scope but the refactor portion is out-of-scope, the overall verdict is REJECT for the refactor portion.
- **Scope authorization list is incomplete or ambiguous:** Halt with `evidence_too_vague` and request specifics. Do not infer scope from context — that's the human's authorization to grant.
- **Change is a "small" out-of-scope modification (e.g., deleting one stale test the author swears is dead code):** Still REJECT. The size of the violation does not change its category; out-of-scope is binary.

---

## Check 3 — Detection Narrowness

For changes that add new code paths gated by detection criteria (the additive-evolution pattern documented in the project's methodology): the detection criterion is narrow enough that the new path only fires on the target failure shape, not on existing-passing cases.

### Pass evidence

The detection criterion is specific (named pattern, named field, named version, named state). The change author has documented which existing test cases / known-passing scenarios will NOT fire the new path. Regression-sweep evidence is included confirming existing passing cases remain unchanged.

### REQUEST_CHANGES findings (severity: major)

Detection is broader than necessary. Existing test cases might fire the new path, creating regression risk. Author tightens detection.

**Example finding:** Detection criterion is "any table with 2+ rows" when the failure shape is "tables with synthetic headers AND 2+ rows" — the latter is the narrow form.

**Recommended action language:** "Detection criterion '[broad form]' will fire on [N] existing-passing cases. Narrow to '[specific form]' to match the actual failure shape. Re-run regression sweep after narrowing."

### REJECT findings (severity: blocker)

Detection is so broad the change is effectively a non-additive modification. The fix masquerades as additive but actually changes existing behavior.

**Example finding:** The "additive" change rewrites a function that's called by all 27 existing test cases — every case now routes through the new code path, making the change non-additive in practice.

**Recommended action language:** "Detection is so broad that this change is effectively non-additive. Re-design as either (a) a properly-narrow additive fix with detection that excludes existing passing cases, or (b) an explicit non-additive change escalated to scope-authorization for review."

### When this check is skipped

This check is **skipped** for changes that are not additive-evolution pattern (e.g., bug fixes that modify a single specific function with no detection logic). Skip is recorded in output as `pass: null, skipped: true, reason: "not_additive_evolution"`.

### Edge cases

- **Change is additive but the detection criterion is implicit (no explicit gate):** Surface as REQUEST_CHANGES with a finding to make the detection explicit. Implicit detection is a maintenance hazard — it relies on the reader inferring the criterion from code structure.
- **Detection is correctly narrow but no regression sweep was run:** Surface in Check 4 (regression risk), not Check 3. The detection itself passed; the verification didn't.

---

## Check 4 — Regression Risk

The change has acceptable regression risk given the work's verification surface and the active profile's risk tolerance.

### Pass evidence

The change author has documented which verification gates were re-run (full test suite, regression sweep, smoke tests as appropriate). All gates pass. The change does not modify any contract / interface / schema that downstream code depends on, OR if it does, all dependent code has been updated and re-verified.

### REQUEST_CHANGES findings (severity: minor or major)

Verification is incomplete (e.g., unit tests pass but integration regression sweep wasn't run). Author runs the missing verification.

**Example finding:** "Unit test suite re-ran (49/49 pass) but integration regression sweep across 27 instances was not run. The change touches `extract_tables.py`, which is exercised by all 27 instances. Run full regression sweep before re-submitting."

**Recommended action language:** "Verification incomplete: [specific gate] was not re-run. The change's blast radius reaches [specific scope]; the missing verification is required to confirm no regression. Run [specific verification] and re-submit."

### REJECT findings (severity: blocker)

Verification reveals broken downstream behavior the change author intends to defer ("we'll fix the integration test next sprint"). Sleeping profiles reject this category outright. Desk profiles may accept with explicit human acknowledgment, but the Critic's role is to surface, not to authorize.

**Example finding:** "Test suite reports 3 failing tests after the change. Author claim: 'tests need updating to match new behavior; will fix in follow-up.' This is a known regression deferred — not acceptable under the active profile."

**Recommended action language:** "Change introduces [N] failing tests with stated intent to defer the fix. Cannot approve regression with deferred remediation. Either fix the failing tests as part of this change, or escalate to scope-authorization for explicit acceptance of the deferred fix."

### Edge cases

- **Change is documentation-only with no engine impact:** Skip Check 4 (mark `pass: true, evidence: "no_engine_impact"`) — there is no regression surface to evaluate.
- **Verification surface itself is broken (test suite fails to run):** Halt the entire critic with `verification_surface_broken`, surface to caller. Cannot evaluate regression risk against a broken verification surface; this is a higher-priority issue than the change being reviewed.
- **Change passes all *existing* verification but introduces a new failure mode the verification doesn't catch:** This is technically pass on Check 4 but should surface as `info` finding noting the verification gap. The change isn't blocked, but the gap should be tracked for future verification-surface improvement.

---

## Worked Examples

Three worked examples illustrating how the 4 checks combine into the verdict. Each shows the input change + authority matrix + active profile, and the resulting per-check pass/fail with finding language.

### Example 1 — Strict profile, additive engine fix, APPROVE

**Input:**
- Profile: `strict` (rejects on any major finding)
- Change: New code path in `extract_tables.py` gated on `synthetic_headers=true AND row_count >= 2`. Adds 4-line guard. Full test suite re-ran clean (49 → 49 pass). Regression sweep on 27 instances — all rebuild byte-identical except the 1 target case which now passes verification.
- Author claim: Fixes a class of failure where false-header demote logic was missing the synthetic-headers case.
- Authority matrix: 3-tier project authority (Tier 1 protected content source-only; Tier 2 structural elements mirror-exact; Tier 3 UI chrome free design).

**Output:** APPROVE.
- Invariant compliance: ✓ (extract_tables.py is engine logic, not authority-matrix-protected content)
- Scope authorization: ✓ (additive_evolution is in-scope)
- Detection narrowness: ✓ (criterion is specific to synthetic_headers + row_count threshold)
- Regression risk: ✓ (regression sweep complete, byte-identical on existing cases)

The strict profile's threshold matters: any major finding would have produced REJECT. All four checks pass cleanly, so APPROVE is the only valid verdict.

### Example 2 — Lenient profile, refactor with broad detection, REQUEST_CHANGES

**Input:**
- Profile: `lenient` (allows REQUEST_CHANGES with auto-resolution)
- Change: Refactor `bind_image_containers.py` to use new bbox-containment helper. New code path fires whenever an image is processed.
- Author claim: Reduces code duplication; identical behavior.
- Authority matrix: same 3-tier project authority.

**Output:** REQUEST_CHANGES.
- Invariant compliance: ✓
- Scope authorization: ✓ (refactor is in-scope-with-notification; notification present)
- Detection narrowness: ✗ — major finding ("New code path fires on every image; existing passing cases now route through untested code path. Either: (a) prove behavioral equivalence with deterministic test, or (b) narrow detection to specifically the case being improved.")
- Regression risk: ✓ (test suite passes)

`requires_human_escalation`: false. Author can re-propose after addressing detection.

The lenient profile's auto-resolution behavior matters here: if the author addresses the finding in the same turn (e.g., adds a deterministic equivalence test), the gate can re-evaluate without a fresh submission cycle. Strict profile would have required explicit re-submission.

### Example 3 — Any profile, deletes test cases, REJECT

**Input:**
- Profile: any
- Change: Modifies `tests/test_qa_dedupe.py`. Removes 4 test cases that "no longer reflect current behavior."
- Author claim: Tests were stale.
- Authority matrix: 3-tier project authority plus the project's documented scope-authorization lists (in-scope: additive evolution with narrow detection, refactor with notification, test addition; out-of-scope: test deletion, --force operations, schema contract changes without escalation).

**Output:** REJECT.
- Invariant compliance: ✓ (tests aren't authority-matrix-protected directly)
- Scope authorization: ✗ — blocker ("Deletion of test cases is in the out-of-scope list. Tests can be modified or expanded, never deleted, without human authorization. The 'tests are stale' claim requires a human review of WHY current behavior diverges from test expectations — that divergence may itself be the bug.")
- Detection narrowness: skipped (not applicable to test deletion)
- Regression risk: ✗ — blocker ("Removing tests reduces verification surface; condition 2 of handoff-gate methodology explicitly requires verification surface exists. Reducing it during execution undermines the gate that authorized the run.")

`requires_human_escalation`: true. Author cannot re-propose without scope-authorization decision.

This example demonstrates that profile setting doesn't matter when the change is fundamentally out-of-scope. Even the most lenient profile cannot approve test deletion if the authorization list explicitly prohibits it. The Critic is the gate; it does not have authority to grant exceptions.
