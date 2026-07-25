# Worked Example: Critic Gate Across Profiles

A single proposed change evaluated under all three example profiles to demonstrate how the same input produces different verdicts based on profile strictness. This is the most useful reference for understanding when and why profiles diverge.

The example uses a realistic engine-change shape drawn from production. The shape generalizes to any rootnode-orchestrated execution.

---

## The proposed change

**Author:** autonomous Claude Code session in production engine evolution
**Change ID:** evolution-step-41
**Category:** `additive_evolution`

**Change diff (summary):** Adds 12 lines to `extract_tables.py` to handle a new failure shape — tables with merged-cell headers spanning multiple columns. Detection criterion: `cell.colspan > 1 AND cell in row_index 0`.

**Author diagnosis:** "Tables with merged-cell headers were being incorrectly demoted to body rows by an earlier false-header-demote logic step. The new path preserves merged headers as headers."

**Author verification claim:**
- Full pytest suite re-run: 49 → 49 pass
- Regression sweep on 27 instances: all rebuild byte-identical
- Spot-check on the target failure shape: now passes verification

**Authority matrix supplied:** the project authority matrix (3 tiers; medical content source-only; section H2/TOC anchor mirror-exact; CSS/JS/UI chrome free design)

**Authorization scope:** standard the project's methodology (in-scope: additive_evolution with narrow detection; out-of-scope: test deletion, --force, schema contract changes without escalation)

---

## Critic Gate evaluation

The Skill runs the 4 checks regardless of profile. Findings emerge.

### Check 1 — Invariant Compliance

**Pass.** Change is to `extract_tables.py` (engine logic). No content classified under any tier of the authority matrix is modified. No medical content, no section anchors, no source-only material touched.

```json
"invariant_compliance": {
  "pass": true,
  "evidence": "extract_tables.py is engine logic, not authority-matrix-protected content. Diff modifies only Python parsing logic; no output content is altered.",
  "findings": []
}
```

### Check 2 — Scope Authorization

**Pass.** `additive_evolution` is in the in-scope list. No out-of-scope categories touched (no tests deleted, no `--force`, no schema contract change). Surfacing entry in change_log present (per author claim — verifiable).

```json
"scope_authorization": {
  "pass": true,
  "evidence": "Category 'additive_evolution' is in-scope per the project's methodology. No out-of-scope categories touched. change_log entry present per author submission.",
  "findings": []
}
```

### Check 3 — Detection Narrowness

**Conditional finding.** Detection criterion is `cell.colspan > 1 AND cell in row_index 0`. Examination question: how many existing test cases match this criterion?

The Critic runs the criterion against the existing test corpus mentally. Tables in the corpus with merged-cell row-0 cells are *rare but present* — a small number of the 27 guides have them. Critically, the author's regression-sweep evidence claims byte-identical rebuilds. If the new code path were firing on existing-passing cases, byte-identical would not hold.

**Resolution:** the regression-sweep evidence directly proves detection narrowness for the existing case base, even though the criterion *appears* broad. Pass with note.

```json
"detection_narrowness": {
  "pass": true,
  "evidence": "Detection criterion (cell.colspan > 1 AND cell in row_index 0) is matched by N existing tables, but author's regression sweep shows byte-identical rebuilds across all 27 guides. New code path produces same output as old path for existing cases; only new failure shape is changed.",
  "findings": [
    {
      "severity": "info",
      "category": "detection_observation",
      "description": "Detection criterion is narrow in effect (regression sweep proves it) but not narrow in form (criterion expression matches existing cases). Future maintainers should review the equivalence-of-behavior claim if extract_tables.py changes nearby logic.",
      "recommended_action": "Add a code comment noting the regression-sweep validation date and which guides were swept."
    }
  ]
}
```

### Check 4 — Regression Risk

**Pass.** Test suite green (49/49). Regression sweep across full corpus complete. No downstream contract changes (the change is internal to `extract_tables.py`; output shape and field names unchanged).

```json
"regression_risk": {
  "pass": true,
  "evidence": "Full pytest suite re-run: 49/49 pass. Regression sweep: 27/27 byte-identical. No interface changes to output structure.",
  "findings": []
}
```

### Aggregate

- 4 checks: 4 pass
- Findings: 1 info-severity finding on Check 3
- No major, no blocker, no escalation-required category

---

## Verdict by profile

### `lenient` profile

```json
{
  "verdict": "APPROVE",
  "profile_applied": "lenient",
  "summary": "All checks pass. One info-level observation on detection narrowness; profile auto-approves on info-only findings."
}
```

Reasoning: `auto_approve_on: ["clean_pass_only", "info"]` includes info, so the info finding doesn't block. The change lands. The info finding is recorded in the audit trail for future reference.

### `balanced` profile

```json
{
  "verdict": "APPROVE",
  "profile_applied": "balanced",
  "summary": "All checks pass. One info-level observation on detection narrowness; profile auto-approves on info-only findings."
}
```

Same as desk for this change. `auto_approve_on: ["clean_pass_only", "info"]` is the same. The day-job profile diverges from desk on *non-passing* findings (no auto-resolution allowed) but for a clean-pass-or-info case, both profiles produce APPROVE.

### `strict` profile

```json
{
  "verdict": "REJECT",
  "profile_applied": "strict",
  "summary": "Detection narrowness produced an info-severity finding. Sleeping profile routes info to reject_on; the change holds for Morning Brief review rather than landing under uncertainty.",
  "requires_human_escalation": false
}
```

Reasoning: `auto_approve_on: ["clean_pass_only"]` requires zero findings to auto-approve. `request_changes_threshold: []` is empty (no severity routes to REQUEST_CHANGES). `reject_on: ["info", "minor", "major", "blocker"]` includes info — so this info finding routes to REJECT. The change waits for Morning Brief.

`requires_human_escalation` is false because the underlying finding category (`detection_observation`) is not in the escalation-required list. the Morning Brief surfaces the change for review, but the change author can re-propose with the recommended action (add a code comment) without scope-authorization escalation.

This is the strict-by-default posture working as designed: at sleep, anything short of a clean pass gets routed to morning review. The Critic doesn't try to fix or auto-resolve; it surfaces and waits.

---

## Profile design note: severity coverage

This worked example almost surfaced a profile bug — initial `strict.json` had `reject_on: ["minor", "major", "blocker"]`, leaving info severity unrouted. The bug was caught during example authoring and fixed in v1.0 before delivery.

The Skill's schema now includes a `SEVERITY COVERAGE REQUIREMENT` documented in the `reject_on` field description, and the Skill validates coverage on profile load. Future profiles authored via rootnode-profile-builder should walk through each severity and confirm a route — the builder Skill should surface this as part of the interview.

---

## What this example demonstrates

1. **Same input, different verdicts by profile.** Desk and day-job approved; sleeping surfaced a configuration gap.
2. **Profile gaps are findable.** The worked example caught an ambiguous runtime path before any real change ran through the gate. This is why worked examples matter — they're cheap and they catch design issues testing real changes wouldn't.
3. **The Critic doesn't validate the diagnosis.** It didn't try to verify whether merged-cell headers were actually being demoted incorrectly. That's the change author's job and the verification surface's job. The Critic checked safety properties.
4. **Regression-sweep evidence resolves apparent detection-breadth issues.** When detection criteria look broad in form but are proven narrow by regression evidence, that's a pass — but worth recording as info so future maintainers know to re-check if nearby logic changes.
5. **Three verdicts are correct.** The middle verdict (REQUEST_CHANGES) didn't fire in this example, but the structural distinction between "fix and re-propose" and "stop, escalate to human" is what makes the gate operationally usable.

---

## Fixes applied during this example's authoring

The worked example surfaced a profile bug that was fixed in v1.0 before delivery:

1. **`strict.json`:** Added `info` to `reject_on` so all severities are routed under sleeping profile.
2. **`schema/profile.schema.json`:** Documented the SEVERITY COVERAGE REQUIREMENT in the `reject_on` field description; reject_on enum now includes `info` to support strict profiles that route info to reject.
3. **`SKILL.md`:** Added severity coverage requirement to the Important section and a troubleshooting entry for unrouted severities.

The lesson: worked examples earn their place in a Skill package precisely because they surface design issues that schema validation alone won't catch. Author them as part of the v1 build, not after.
