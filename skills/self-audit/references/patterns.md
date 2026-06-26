# Self-Audit: Detailed Patterns

## Completeness patterns

### Good — explicit deferral
> "The bug is fixed. Tests will be added in a follow-up PR — tracked in #452."
✅ Complete. Both requests addressed, one deferred with tracking.

### Bad — silent omission
> "The bug is fixed. Ready to ship."
❌ Incomplete. Tests were requested, not mentioned.

### Bad — partial as full
> "The feature is done — core logic works, edge cases handled."
❌ Check edge cases. "Handled" ≠ verified.

---

## Consistency patterns

### Good — consistent rule check
First message: "We use snake_case in this project."
Last message: "Here's the updated user_profile.py"
✅ Consistent with project convention.

### Bad — contradiction
First message: "No changes needed, everything looks good."
Last message: "Edited 3 files to fix the layout."
❌ Contradiction. Either changes were needed or they weren't.

---

## Groundedness patterns

### Good — evidence-backed
> "Tests pass: 42 passed, 0 failed. Build: SUCCESS. Coverage: 87%."
✅ All claims backed by verifiable output.

### Bad — unverified
> "This should work fine in production."
❌ No evidence. "Should work" is an assumption, not a confirmation.

### Edge case — verified but output hidden
> "I tested this and it works."
⚠️ Ambiguous. Agent may have run tests but not shown output. Flag for clarification.

---

## Honesty patterns

### Good — limitations acknowledged
> "The feature is complete with one known issue: pagination is not yet implemented. This is acceptable for v1."
✅ Honest. Limitation stated clearly.

### Bad — embellishment
> "Five features done — production ready."
Checking code: 3 have TODO stubs, 1 has placeholder error handling.
❌ Embellishment. "Production ready" contradicts actual state.
