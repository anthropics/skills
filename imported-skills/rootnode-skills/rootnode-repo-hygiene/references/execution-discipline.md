# Execution Discipline (Phase 2 mechanics)

The full Phase 2 procedure: entry conditions, batch construction, per-batch execution with critic-gate composition, commit plan execution, post-execution verification, and the `cleanup_execution_log.md` format.

**Canonical sources:**
- `root_CC_ENVIRONMENT_GUIDE.md §5.2` — verification-before-completion iron law
- `rootnode-critic-gate` Skill (composition partner; required reading when active profile threshold is `strict`)

This file applies the canonical content to Phase 2 execution. It does not duplicate the canonical; it cites and applies.

---

## Phase 2 entry conditions

Phase 2 executes only when ALL of the following are true. Failing any condition halts Phase 2 entry; the Skill instructs the user to resolve the failing condition and retry.

**EC-1 — Authorization is file-state-grounded (D10).** Phase 2 reads `[APPROVED]` markers from the report file. Verbal authorization in chat is not a substitute. If zero markers exist in the report file, Phase 2 halts at entry.

The Skill MAY act as a text editor on the user's behalf to apply marks (the three approval forms — blanket, fragmented, conditional — documented in SKILL.md and design doc §7). When acting as an editor, the Skill produces the marked file for the user to save locally; Phase 2 then reads the saved file. There is no verbal-authorization fallback.

**EC-2 — Profile validation passes.** The active profile's JSON validates against `schema/profile.schema.json`. Required fields present: `categories`, `include_seven_layer_leak_check`, `include_commit_plan`, `critic_gate_threshold`, `remediate_routing`. If validation fails, halt and surface the schema error.

**EC-3 — Engine baseline coherence.** Phase 0's CLAUDE.md state snapshot read still matches current state. If the engine state has shifted between Phase 1 and Phase 2 (test count changed, version bumped, branches diverged), halt and instruct re-running Phase 1.

**EC-4 — Critic-gate availability when required.** If the active profile's `critic_gate_threshold` is `strict` and `rootnode-critic-gate` is not installed, halt at entry. Instruct the user to either install critic-gate or downgrade the profile threshold. Skipping a required gate by silently lowering the bar is a discipline failure.

**EC-5 — Marker placement validation.** Walk the report's `[APPROVED]` markers. Confirm each marked finding belongs to an executable category (Cat 1–10). If any marker is on a Cat 11–14 finding or 7-layer leak finding, surface a notice that those markers will be skipped (per the recommendation-only routing rule) and continue with Cat 1–10 markers only.

When all five conditions pass, Phase 2 proceeds to batch construction.

---

## Batch construction

Phase 2 groups `[APPROVED]` Cat 1–10 findings into batches. Each batch is a single category at a single confidence tier. The batches execute sequentially.

**Construction rules:**

1. **One category per batch.** Cat 1 findings batch together; Cat 2 findings batch together. No cross-category batches. This makes the verification step coherent — a Cat 1 batch verifies under Cat 1 success criteria.

2. **Confidence-tier subdivision.** Within a category, findings split by confidence: a `high`-confidence sub-batch, a `medium`-confidence sub-batch, a `low`-confidence sub-batch. Higher-confidence sub-batches execute first.

3. **Risk-tier ordering.** Within a confidence tier, low-risk findings execute first, then medium, then high. This front-loads low-blast-radius work; if execution surfaces unexpected friction, the high-risk findings haven't run yet.

4. **Skipped findings.** Cat 11–14 markers and leak markers are not added to batches (per EC-5). They appear in the closeout summary as "skipped — recommend REMEDIATE handoff."

5. **Batch ordering across categories.** Cat order: 1, 2, 3, 4, 5, 6, 7, 8, 9, 10. Categories without `[APPROVED]` markers are skipped.

**Batch metadata** (preserved through execution for the cleanup log):
- Category number
- Confidence tier
- Risk tier
- Finding IDs included
- Expected file changes (computed before execution from the recommended actions)
- Verification step (computed before execution from the category's success criteria)

---

## Per-batch execution

For each batch, Phase 2 follows the same five-step cycle.

**Step 1 — Plan submission.** Build the batch plan: findings being executed, proposed file edits, verification step that will confirm success. If `critic_gate_threshold` is `required` for this profile, submit the plan to `rootnode-critic-gate` (see "Critic-gate composition" below). If `optional`, the user MAY invoke critic-gate manually; otherwise proceed to Step 3.

**Step 2 — Critic-gate review (when applicable).** Critic-gate returns one of three verdicts:
- **APPROVE** — proceed to Step 3.
- **REQUEST_CHANGES** — adjust the batch per the critic's findings; re-submit. Cap: 3 cycles. After 3 cycles without APPROVE, halt and surface the unresolved issue to the user.
- **REJECT** — halt. Surface the rejection. The batch is not executed; the user decides whether to override (manual edit on file) or accept the halt.

**Step 3 — Execute.** Apply the file edits described in the batch plan. Execution is sequential within the batch — no parallelism. Each finding's edits complete before the next finding begins.

**Step 4 — Post-batch verification.** Run the verification step computed in batch construction. The step is category-specific (see "Per-category verification" below). If verification fails, halt. The Skill does not retry automatically — verification failure is treated as evidence the batch's assumptions were wrong.

**Step 5 — Log to `cleanup_execution_log.md`.** Append a batch entry capturing: batch metadata, critic-gate verdict (if applicable), file changes applied (path + summary), verification result, timestamp. Format detailed below.

---

## Critic-gate composition

The Skill composes with `rootnode-critic-gate` for change review during Phase 2. Composition is conditional — the Skill operates standalone if critic-gate is not installed and the profile threshold is `optional`.

**When required (`strict` threshold).** Profile `default` for `deep-audit` is `required`. Mode-router conditions (sleeping, unattended) typically map to `strict` regardless of profile. Phase 2 entry halts (EC-4) if critic-gate is not installed.

**When optional (`optional` threshold).** Profile `default` for `default` and `quick-scan` is `optional`. Critic-gate review is per-batch user choice. The Skill surfaces "critic-gate available — invoke?" before each batch when critic-gate is installed and threshold is `optional`.

**Submission format.** The Skill submits to critic-gate:
- Batch plan (findings, proposed edits, verification step)
- Engine baseline reference (Phase 0 state snapshot)
- Active profile JSON

**Verdict handling** (from Step 2 above):
- APPROVE → execute
- REQUEST_CHANGES → adjust + re-submit (3-cycle cap)
- REJECT → halt + surface to user

**Cycle cap rationale.** Three cycles is enough for the critic to surface and confirm a single class of issue but few enough that runaway loops can't develop. After three cycles without APPROVE, the issue is structural — manual user intervention is the right escalation, not more critic cycles.

---

## Per-category verification

Each category has a category-specific verification step run after the batch executes. The step is computed in batch construction and recorded in the cleanup log.

| Category | Verification step |
|---|---|
| Cat 1 | Re-run a targeted Cat 1 sub-scan over the modified files; expect zero stale-reference findings |
| Cat 2 | Validate `.claude/settings.local.json` parses; re-check the stale-removal scan; expect no surfaced removals |
| Cat 3 | Search the engine for references to the relocated archive code; expect zero |
| Cat 4 | Run the test suite; expect zero test-collection errors from removed orphans |
| Cat 5 | Re-run dependency drift scan; expect declared-vs-used parity |
| Cat 6 | Re-scan `.claude/settings*.json` and scripts for `bypassPermissions` / `--dangerously-skip-permissions`; expect only sandbox-context occurrences |
| Cat 7 | Validate `.claude/settings.json` parses; verify each hook's referenced script exists and is executable |
| Cat 8 | Validate each modified subagent definition parses; verify referenced tools and files exist |
| Cat 9 | Recount CLAUDE.md non-blank lines; re-run aspirational/conversational scans on changed sections |
| Cat 10 | Re-validate Skill frontmatter for changed Skills; verify description char count, body line count, name/folder match |

Verification failure halts Phase 2 immediately. The cleanup log records the failure; no further batches execute. The user resolves the failure and may re-invoke Phase 2 with the remaining unmarked work.

---

## Commit plan execution

Phase 1 produces a Recommended commit plan section (D7). Phase 2 executes the chosen plan after all batches complete and pass verification.

### Option A — No commits

File edits remain in the working tree. No `git add` or `git commit` is performed. Suitable for one-shot deliverables.

Phase 2 skips the commit step entirely. The cleanup log notes "Commit plan: A (no commits)."

### Option B — Engine baseline + cleanup commit

**Step 1** (one-time, typically pre-Phase-2): commit the entire engine as a baseline. The user runs this manually before Phase 2 starts; the Skill does not auto-perform Step 1 because the engine baseline scope is too large to commit without explicit user review.

**Step 2** (post-batches): commit the cleanup as a single commit. The Skill builds the commit message from the cleanup log: list of finding IDs executed grouped by category, summary line citing the report filename.

The cleanup log records Option B and the commit hash.

### Option C — Engine baseline + per-domain cleanup commits

**Step 1**: same as B (user runs manually).

**Step 2**: commit cleanup as N commits, one per domain. The Skill groups finding IDs by domain (Cat 1 = parent-vestige; Cat 2 = permissions; Cat 3–5 = stale code; Cat 6–8 = configuration; Cat 9–10 = standing context). Each commit's message lists its scope.

The cleanup log records Option C and the N commit hashes.

### Defer-to-downstream (D11)

When Phase 1 detected the deferral signals (distribution intent + interest in fresh repo, findings that downstream decisions will resolve, working tree with uncommitted structural state), Phase 1 names defer-to-downstream as the recommendation. Phase 2 accepts it.

Under defer-to-downstream:
- File edits accumulate in the working tree.
- No `git add` or `git commit` runs.
- The cleanup log serves as the audit trail in lieu of commit messages.
- A "Defer-to-downstream notice" appears at the end of the cleanup log naming the downstream decision the commit plan defers to.

---

## Post-execution verification (final sweep)

After all batches and the commit plan complete, run a final sweep:

1. **Engine baseline coherence re-check.** Re-read CLAUDE.md state sections; compare against Phase 0 baseline. Surface any drift introduced by execution.
2. **Test backstop run.** If a test command exists, run it. Record the result in the cleanup log.
3. **Skipped-findings summary.** List Cat 11–14 markers and leak markers that were skipped, grouped by recommended REMEDIATE handoff.
4. **Closeout summary.** Total findings approved, total executed, total skipped (with reason), commit plan choice, final test result, REMEDIATE recommendations summary.

---

## `cleanup_execution_log.md` format

Phase 2 writes to `output/hygiene_reports/cleanup_execution_log_{ISO8601}.md`. The file is the durable record of the Phase 2 run.

```markdown
# Cleanup Execution Log

**Report:** HYGIENE_REPORT_{ISO8601}.md
**Profile:** <profile name>
**Phase 2 start:** <ISO8601>
**Phase 2 end:** <ISO8601>
**Critic-gate:** <required | optional | not-invoked>
**Commit plan chosen:** <A | B | C | defer-to-downstream>

## Entry-condition checks
- EC-1 (file-state authorization): PASS
- EC-2 (profile validation): PASS
- EC-3 (engine baseline coherence): PASS
- EC-4 (critic-gate availability): <PASS | N/A>
- EC-5 (marker placement validation): PASS, <N> Cat 11-14/leak markers will be skipped

## Batches

### Batch 1 — Cat <N>, confidence <tier>, risk <tier>
- Findings: <list of IDs>
- Critic-gate verdict: <APPROVE | REQUEST_CHANGES (N cycles) | not-invoked>
- File changes applied:
  - <path>: <summary>
  - <path>: <summary>
- Verification: <step run> — PASS
- Timestamp: <ISO8601>

[... per-batch entries ...]

## Commit plan execution
<Option-specific section: commit hashes, scope per commit, OR defer-to-downstream notice>

## Final verification sweep
- Engine baseline coherence: <PASS | drift detected>
- Test backstop: <command> — <PASS | FAIL with output excerpt | not-run>

## Skipped findings (Cat 11-14 + 7-layer leaks)
- <list grouped by category, with REMEDIATE handoff recommendation>

## Closeout summary
- Findings approved: <N>
- Findings executed: <N>
- Findings skipped: <N> (<breakdown by reason>)
- Commit plan: <choice>
- Final test result: <PASS | FAIL | not-run>
- REMEDIATE recommendations: <count>
```

---

## Halt-on-failure discipline

The Skill halts Phase 2 immediately on:
- Entry condition failure
- Verification step failure on any batch
- Critic-gate REJECT verdict
- Critic-gate REQUEST_CHANGES exceeding 3 cycles
- Commit plan execution failure (e.g., merge conflict, permission denial — including the production-validated case where engine baseline commit hit permission denial and triggered Path 3 adaptation)

Halt is durable. The Skill does not retry automatically. Resolution is user-driven: the user addresses the failure cause (resolves a conflict, downgrades a threshold, refines a permission entry, or chooses defer-to-downstream when a commit-plan permission denial surfaces) and may re-invoke Phase 2 with the remaining unmarked findings.

The halt-on-failure discipline preserves the audit trail. Every Phase 2 invocation either completes cleanly or halts with a recorded reason — there is no silent partial completion.

---

*End of execution discipline. Verification iron law: `root_CC_ENVIRONMENT_GUIDE.md §5.2`. Critic-gate composition partner: `rootnode-critic-gate` Skill.*
