# Troubleshooting

Common failure modes and resolution guidance for the Critic Gate, organized by symptom. Use this when the gate is producing unexpected verdicts, when changes are being inappropriately approved or rejected, or when validation is failing.

**When to consult this file:** When the gate's behavior in production doesn't match expectations, when authoring or debugging a profile, or when a verdict's recommended_action language isn't producing useful author re-submissions.

---

## Table of Contents

1. [Input Validation Issues](#input-validation-issues)
2. [Verdict Behavior Issues](#verdict-behavior-issues)
3. [Profile Authoring Issues](#profile-authoring-issues)
4. [Inter-Gate Coordination](#inter-gate-coordination)

---

## Input Validation Issues

### No authority matrix provided

**Symptom:** The Critic halts with `evidence_not_provided`, refusing to evaluate the change.

**Diagnosis:** This is the most common Critic failure mode by design — and it's working correctly. The Critic cannot evaluate compliance against rules it doesn't have. Without the authority matrix, the gate has no basis for invariant-compliance checks.

**Resolution:** Provide the authority matrix in `work_context.authority_matrix` as either inline text or a file path. The matrix should enumerate tiers and specify what content/code/data belongs to each tier. If the deployment doesn't have an authority matrix yet, that's a deployment-readiness issue, not a Critic Gate bug — author the matrix before invoking the gate.

### Authority matrix is too vague

**Symptom:** The Critic halts or produces evasive findings because the authority matrix names tiers but doesn't enumerate what content belongs in each tier.

**Resolution:** Surface the specific gap. "The provided authority matrix names Tier 1, Tier 2, Tier 3 but doesn't enumerate which files / sections / data belong to each tier. The Critic cannot determine whether change X violates a tier without knowing what each tier protects." Request a more specific matrix from the deployment owner. Do not infer tier membership from context — that's a scope-authorization decision the human must make explicit.

### Change diff is too large to evaluate

**Symptom:** The change diff exceeds practical evaluation size — many hundreds of lines, many files. The Critic produces shallow findings or none at all because it cannot meaningfully examine everything.

**Resolution:** The Critic should not approve a large diff it cannot meaningfully examine. Better to REQUEST_CHANGES with the recommendation: "Diff size exceeds practical evaluation threshold (~500 lines / many files). Split into reviewable chunks of related changes; submit each chunk separately." If the deployment requires large coordinated changes, that's a workflow-design issue worth raising back to the design team — large diffs are a code-smell for autonomous execution.

### Change metadata is incomplete

**Symptom:** Author identity, diagnosis statement, claimed verification, or change category is missing from `change_metadata`.

**Resolution:** Halt with `evidence_too_vague` and request the specific missing fields. The change_metadata fields exist because the Critic uses them — author identity for audit trail, diagnosis to understand intent, verification claims to validate Check 4, category to apply the right scope-authorization logic. Don't proceed with partial metadata; the resulting verdicts will be unreliable.

---

## Verdict Behavior Issues

### Critic approves something that broke

**Symptom:** Verdict was APPROVE, change was applied, downstream behavior broke.

**Diagnosis:** Check 4 (regression risk) was nominally satisfied but the verification surface didn't actually catch the failure mode. The Critic operated correctly given the inputs; the issue is that the verification surface had a gap.

**Resolution:** This is a verification-surface issue, not a Critic issue. Update the verification surface to cover the failure mode that occurred. The Critic is only as good as the verification it can validate against. Consider whether the deployment's verification surface is genuinely sufficient for autonomous execution — if it has gaps the Critic can't see, those gaps are the real risk.

### Critic rejects valid work

**Symptom:** Verdict is REJECT for changes the human reviewer believes are correct and important.

**Diagnosis:** Most common: the change is genuinely out-of-scope per the authorization list, but the human is operating with an updated mental model that hasn't been reflected in the authorization. The Critic operates against the documented authorization, not the human's current intent.

**Resolution:** If the authorization list is genuinely outdated (the deployment owner has updated their scope expectations but not the document), update the authorization list — that's the human scope-authorization decision the Critic was correctly surfacing. If the authorization is still correct but this specific change is an exception, that's also a human scope-authorization decision: explicitly authorize the exception and document the rationale. The Critic is doing its job by surfacing rather than guessing.

### Verdict says APPROVE but findings exist

**Symptom:** The verdict is APPROVE but the JSON's `findings` array contains entries.

**Diagnosis:** This is correct behavior, not a bug. Profiles can auto-approve on certain severities (typically `info`, sometimes `minor` for lenient profiles). Auto-approval does not suppress findings — the findings still appear for audit trail.

**Resolution:** No fix needed. Audit trail matters; the findings being visible even on APPROVE allows downstream readers to see what was observed without blocking the change. If you specifically want APPROVE to mean "zero findings," configure the profile with `auto_approve_on: []` so any finding triggers REQUEST_CHANGES.

### Change author argues with the verdict

**Symptom:** Change author keeps re-submitting the same change with justification text, asking the Critic to reconsider.

**Diagnosis:** Authors sometimes treat the Critic as a debate partner. The Critic's verdict is final for the gate decision; argument is allowed and welcome, but it must take a specific form.

**Resolution:** The Critic does not re-evaluate based on author justification. Argument must take the form of either (a) modifying the change to address findings — the change itself becomes different, so re-evaluation is fresh — or (b) escalating to a human for scope-authorization decision. Justification text alone does not change the verdict. If your deployment has authors arguing repeatedly, document this rule prominently in the deployment's CLAUDE.md so authors understand the Critic's role correctly.

---

## Profile Authoring Issues

### Profile has unrouted severities

**Symptom:** The Skill validates on profile load that every severity (info, minor, major, blocker) appears in exactly one of `auto_approve_on`, `request_changes_threshold`, or `reject_on`. Misconfigured profiles fail validation with a specific message naming which severities are unrouted.

**Resolution:** Add the unrouted severity to the appropriate list. Typical defaults:
- `info` → `auto_approve_on`
- `minor` → `request_changes_threshold` (or `auto_approve_on` for lenient profiles)
- `major` → `request_changes_threshold` (or `reject_on` for strict profiles)
- `blocker` → `reject_on` (mandatory; cannot be elsewhere)

See `severity-coverage.md` for the full routing rules and three example profile patterns.

### Profile permits auto-approval but findings exist

**Symptom:** Profile is set to auto-approve on `info` findings, but the verdict still includes findings in its JSON output.

**Diagnosis:** This is correct behavior. Auto-approval means "don't block APPROVE on this severity," not "don't surface findings of this severity." Findings always appear in output; the routing only affects whether they push the verdict away from APPROVE.

**Resolution:** No fix needed. The audit trail is intentional. If your deployment wants verdicts with no findings on APPROVE, the right setting is to ensure no info findings are produced — typically by not having the checks generate them. That's a check-implementation question, not a profile question.

### Profile doesn't fit any standard pattern

**Symptom:** None of `strict`, `balanced`, or `lenient` produces the right behavior for the deployment.

**Resolution:** Author a custom profile via `rootnode-profile-builder`. The standard profiles are starting references, not deployment defaults. The right routing depends on rollback cost, verification surface, and human availability — all deployment-specific. Document in the profile description what work classes it applies to so future readers can match work to profile correctly.

---

## Inter-Gate Coordination

### Detection narrowness check on non-additive changes

**Symptom:** The Critic flags Check 3 (detection narrowness) on changes that aren't additive-evolution pattern, producing noise.

**Resolution:** Skip the check (mark `pass: null, skipped: true, reason: "not_additive_evolution"`). The check exists specifically for the additive-evolution pattern; applying it to bug fixes that modify a single function generates noise. The Critic's logic should detect non-additive changes and skip Check 3 automatically; if it isn't, the change_metadata's category field may be unset or set incorrectly.

### Critic verdict and handoff-trigger-check verdict disagree

**Symptom:** Handoff gate said PASS (work was ready to hand off to autonomous execution), Critic gate says REJECT on a specific change.

**Diagnosis:** Different gates check different things. Handoff gate runs once at the start of execution to confirm work is *ready* to be executed. Critic gate runs per-change during execution to confirm individual changes are safe.

**Resolution:** No conflict — they are complementary, not redundant. It is normal and expected for handoff to PASS and Critic to REJECT a specific change (the change author over-reached). The right interpretation: "Yes, this work was ready to hand off. AND this specific change the agent proposed exceeds the authorization granted at handoff. Author re-scopes or escalates."

### Verification surface itself is broken

**Symptom:** Critic's Check 4 cannot evaluate regression risk because the test suite or other verification gate fails to even run.

**Resolution:** Halt the entire critic with `verification_surface_broken`, surface to caller. Cannot evaluate regression risk against a broken verification surface; this is a higher-priority issue than the change being reviewed. Restore the verification surface (likely a separate human investigation) before resuming any autonomous execution. The Critic should not approve changes against a broken verification surface even if all other checks pass.
