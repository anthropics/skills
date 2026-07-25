# Worked Example — End-to-End Sweep

A complete walkthrough of the Skill running on a production CC deployment. The example anonymizes the deployment but preserves the actual finding patterns, verification flow, the three approval forms in use, and the Path 3 commit-plan adaptation.

This file demonstrates the full workflow in one place. New users read this to see how the pieces compose; future maintainers read this to understand which behaviors are validated against real load.

---

## Setup

The CC deployment under audit is a research engine with the following characteristics:

- Bootstrapped from a parent project (folder copy) — inheriting JS reference modules and a parent `package.json` identity.
- Active engine in Python with a substantial test suite (450+ tests, run via pytest).
- CLAUDE.md present, ~280 lines, includes an Engine state snapshot section.
- `.claude/settings.local.json` accumulated over ~6 months of active development.
- No subagents. No MCP servers configured. Hooks present (PostToolUse for change_log; Stop for test backstop).
- Active distribution intent — maintainer planning a fresh-repo migration in the next week.

The maintainer invokes the Skill at the engine root with the `default` profile.

---

## Phase 1 — Sweep

The sweep runs Phase 0 pre-flight, then walks all 14 categories, then runs the 7-layer leak check, then produces the report.

### Phase 0 pre-flight output

```
Pre-flight inventory:
  - CLAUDE.md found (282 lines)
  - Engine state snapshot detected (test count: 451, last-shipped: 4 days ago)
  - .claude/settings.local.json found, 47 permission entries
  - .claude/settings.json found, 3 hooks configured
  - .claude/skills/ found, 8 Skills present
  - .claude/agents/ not found
  - git status: 12 modified files, 3 untracked (working tree dirty — captured as inventory, not halt)
  - Bootstrap heritage block active: 49 inherited JS files, modified_recently_threshold: 2026-04-21

Profile: default
  - Categories: 1-14
  - 7-layer leak check: enabled
  - Commit plan: enabled
  - Critic-gate threshold: optional
  - Remediate routing: enabled
  - Confidence threshold: medium-and-up
```

The pre-flight reports the bootstrap heritage block as detected and active. Cat 1 will use it for calibration.

### Cat 1 results — Stale parent-project references

The bootstrap heritage carve-out was correctly applied. The "Bootstrap heritage inventory" subsection lists the 49 inherited files at the top of Cat 1.

Three findings surfaced, all triggered by the modified-recently rule (files inherited from the parent project but modified during the current project's work period):

```
F-1.1  [risk: medium]  [confidence: high]
  File: legacy_module_alpha.js
  Issue: inherited from parent project; modified during current work period
  Evidence: last commit touching this file: 2026-04-29 (after threshold 2026-04-21)
  Recommended action: rewrite to remove parent-project import paths
```

```
F-1.2  [risk: low]  [confidence: medium]
  File: legacy_module_beta.js
  Issue: inherited from parent project; modified during current work period
  Evidence: last commit touching this file: 2026-04-25
  Recommended action: review imports; rewrite or relocate
```

```
F-1.3  [risk: medium]  [confidence: high]
  File: web/scripts/prerender-svgs.cjs
  Issue: inherited from parent project; in-engine code shells out to this
  Evidence: 3 invocations from engine scripts; engine treats this as authoritative
  Recommended action: copy to engine path; rewrite engine references; remove from inherited inventory
```

Note: F-1.3 was not explicitly enumerated in the bootstrap heritage block's `inherited_files` list, but the sweep correctly generalized the carve-out logic — the file matched the `inherited_directories` glob and the modified-recently rule fired.

### Cat 2 results — Permissions

Dual scan (D9) surfaced findings in both directions:

Stale-removal direction — 4 findings:
```
F-2.1  [direction: stale-removal]  [confidence: high]  Permission: Bash(npm test*) — 0 invocations
F-2.2  [direction: stale-removal]  [confidence: high]  Permission: Read(./old/**) — 0 invocations
F-2.3  [direction: stale-removal]  [confidence: high]  Permission: Bash(git stash*) — 0 invocations
F-2.4  [direction: stale-removal]  [confidence: high]  Permission: Bash(rm -rf*) — 0 invocations + risk-flagged
```

Missing-entry direction — 3 findings:
```
F-2.5  [direction: missing-entry]  [confidence: high]  Permission absent: Bash(python -m pytest tests/integration/*) — 5+ approval friction events
F-2.6  [direction: missing-entry]  [confidence: medium]  Permission absent: Read(.github/**) — 2 friction events
F-2.7  [direction: missing-entry]  [confidence: medium]  Permission absent: Edit(docs/**) — 2 friction events
```

### Categories 3-8 — short summary

```
Cat 3: 0 findings (no archive directories present)
Cat 4: 1 finding — F-4.1 orphaned test for retired module
Cat 5: 2 findings — F-5.1 declared-unused dependency; F-5.2 .gitignore drift on cache directory
Cat 6: 0 findings (no bypass usage)
Cat 7: 0 findings (hooks coherent)
Cat 8: 0 findings (no subagents to drift)
```

### Cat 9 results — CLAUDE.md bloat (most-cited)

CLAUDE.md is 282 lines (over 200 threshold) AND has multiple sub-signals firing.

```
F-9.1  [sub-signal: line-count]  [confidence: high]
  Lines: 282 / 200 threshold
  Recommended action: extract reference material to .claude/rules/ and Skills

F-9.2  [sub-signal: stale-state]  [confidence: high]
  Line: 47
  Evidence: "test count: 449 (current as of 2026-04-12)"; actual current count: 451
  Recommended action: update or introduce automated refresh mechanism

F-9.3  [sub-signal: stale-state]  [confidence: high]
  Line: 51
  Evidence: "Skills present: 6"; actual current count: 8
  Recommended action: update or introduce automated refresh mechanism

F-9.4  [sub-signal: stale-state]  [confidence: high]
  Line: 53
  Evidence: "last-shipped: 2026-04-08"; actual: 2026-04-30
  Recommended action: update or introduce automated refresh mechanism

F-9.5  [sub-signal: mixed-reference]  [confidence: medium]
  Lines: 88-127
  Evidence: 40-line block of "when editing pytest fixture files, ..." — file-pattern conditional content
  Recommended action: extract to .claude/rules/pytest-fixtures.md with paths: frontmatter

F-9.6  [sub-signal: stale-state]  [confidence: medium]
  Line: 178
  Evidence: "Engine version: 0.4.2"; actual current: 0.4.3
  Recommended action: update or automate

F-9.7  [sub-signal: aspirational]  [confidence: high]
  Line: 211
  Evidence: "We should add a subagent for code review when we have time"
  Recommended action: remove or convert to a tracked backlog entry

F-9.8  [sub-signal: stale-state]  [confidence: high]
  Line: 244
  Evidence: "Active focus: parser refactor"; current focus per change_log: distribution prep
  Recommended action: update
```

The 8 stale-state findings (F-9.2, F-9.3, F-9.4, F-9.6, F-9.8) plus the bloat and pattern-9 finding match the production-validation cluster: §4.14 (Stale CLAUDE.md) is the most-cited pattern in deployments that have evolved past initial configuration.

### Cat 10 results — Skills hygiene

```
F-10.1  [confidence: high]  Skill: data-loader-helper — description 1183 chars (over 1024)
F-10.2  [confidence: medium]  Skill: pytest-runner — disable-model-invocation: true with no metadata.notes
```

### Cat 11-13 (recommendation-only)

```
F-11.1: Empty directory at /tools/ (legacy)
F-12.1: CLAUDE.md missing R3 (scope authorization) section per CC_ENVIRONMENT_GUIDE.md §2.1
F-12.2: CLAUDE.md missing R4 (halt-and-escalate triggers) section
F-13.1: SHIP_MANIFEST.md absent (project in distribution stage)
```

### Cat 14 results — process-abstraction candidates

5 candidates surfaced (the production validation set). See `process-abstraction-detection.md` for full candidate-by-candidate detail. Summary by scope:

```
F-14.1: current-state-query script — methodology-generalizable, trivial, ~12 invocations/month
F-14.2: pytest permission consolidation — project-local, trivial, covered by Cat 2 findings
F-14.3: per-instance audit harness consolidation — project-local, moderate, ~4/month
F-14.4: CLAUDE.md snapshot auto-update hook — methodology-generalizable, moderate, ~10/month
F-14.5: subagent registry generator — methodology-generalizable, trivial, ~8/month
```

The maintainer flags F-14.1 + F-14.4 + F-14.5 as the high-leverage methodology-generalizable cluster (a state-query script enables a snapshot-update hook; both transfer to other CC engines).

### 7-layer leak check

```
L-1  [layer: 5]  CLAUDE.md → hooks
  Current placement: CLAUDE.md (line 156)
  Evidence: "Remember to refresh the Engine state snapshot before session close"
  Recommended extraction: Stop hook running the state-query script (F-14.1) which writes between sentinel markers in CLAUDE.md.

L-2  [layer: 2]  CLAUDE.md → .claude/rules/
  Current placement: CLAUDE.md (lines 88-127)
  Evidence: 40-line block of pytest-fixture conventions
  Recommended extraction: .claude/rules/pytest-fixtures.md with paths: ['tests/**/conftest.py', 'tests/**/fixtures/*.py']

L-3  [layer: 3]  CLAUDE.md → Skills
  Current placement: CLAUDE.md (lines 198-220)
  Evidence: 22-line "Distribution prep procedure" describing 7 sequential steps
  Recommended extraction: Skill rootnode-distribution-prep with the 7 steps as the procedure body.
```

### Routing recommendations section

```
Routing recommendations

Structural findings (Cat 11-14 + 7-layer leaks) benefit from REMEDIATE mode in
rootnode-cc-design. To act on these findings, invoke rootnode-cc-design REMEDIATE
with this report as input. To proceed without REMEDIATE, treat as recommendation-only
— Phase 2 will skip them.

Marked candidates this run:
  - F-11.1, F-12.1, F-12.2, F-13.1 (recommendation-only)
  - F-14.1, F-14.4, F-14.5 (methodology-generalizable; consider standalone build)
  - L-1, L-2, L-3 (recommend REMEDIATE)
```

### Recommended commit plan section

The maintainer's distribution intent + working-tree state + pending fresh-repo migration triggers the defer-to-downstream detection per D11.

```
Recommended commit plan

Engine state assessment:
  - Distribution intent: stated in CLAUDE.md; fresh-repo migration on next-week roadmap
  - Working tree: 12 modified files reflecting unmade structural decisions
  - Findings depending on downstream decision: F-1.x (parent-project removal — likely
    moot under fresh repo migration)

Recommendation: defer-to-downstream

Rationale: committing baseline + cleanup here would pre-commit to repo identity
defaults that the fresh-repo migration will revisit. Phase 2 should execute file
edits in working tree without git operations; the migration session handles
baseline + cleanup commit pairing in proper context.

Alternative options A/B/C remain available if maintainer disagrees with the
deferral assessment.
```

---

## Authorization marking

Total findings: 23 across 14 categories + 3 leak findings.

The maintainer reviews the report and marks via three approval forms across the same session.

### Blanket approval — Cat 2

The maintainer types into chat:

> Approve all Cat 2 findings.

The Skill confirms Cat 2 contains 7 findings (4 stale-removal, 3 missing-entry), all marked-able. Skill produces the report file with Cat 2 findings marked `[APPROVED]` and returns the file. Maintainer saves locally. The marking ledger entry at the bottom of the report records:

```
Marking ledger
  - 2026-05-04 14:32:11 — User approval form: blanket
    Categories: Cat 2
    Findings marked: F-2.1 - F-2.7 (7 findings)
    Skill action: applied [APPROVED] markers in-file
```

### Fragmented approval — Cat 1, Cat 9

The maintainer types:

> Approve F-1.3, defer F-1.1 and F-1.2 to fresh-repo migration. Approve all stale-state findings in Cat 9 (F-9.2, F-9.3, F-9.4, F-9.6, F-9.8) — these need updating regardless. Skip F-9.1 line-count for now (depends on the leak extractions). Skip F-9.5 mixed-reference (covered by L-2). Approve F-9.7 aspirational removal.

The Skill validates each finding ID exists. F-1.1 and F-1.2 marked `[DEFERRED]` per the user's intent. F-9.1 and F-9.5 left unmarked. Other named findings marked `[APPROVED]`. Marking ledger updated.

### Conditional approval — Cat 4, 5, 7, 10

The maintainer types:

> Approve all medium-and-low risk findings across remaining categories. Halt high-risk for review.

The Skill walks the remaining unmarked findings (Cat 4, 5, 7, 10), checks risk tags. None are high-risk. F-4.1, F-5.1, F-5.2, F-10.1 marked `[APPROVED]`. F-10.2 marked `[APPROVED]` (it carries `risk: low`). High-risk findings absent in this batch. Marking ledger updated.

### Recommendation-only categories — left unmarked

Cat 11-14 findings and L-1/L-2/L-3 leaks remain unmarked. The maintainer notes the REMEDIATE handoff will be a separate session.

### Final marker state

```
Cat 1: F-1.3 [APPROVED]; F-1.1, F-1.2 [DEFERRED]
Cat 2: all 7 [APPROVED]
Cat 4: F-4.1 [APPROVED]
Cat 5: F-5.1, F-5.2 [APPROVED]
Cat 7: 0 findings
Cat 9: F-9.2, F-9.3, F-9.4, F-9.6, F-9.7, F-9.8 [APPROVED]; F-9.1, F-9.5 unmarked
Cat 10: F-10.1, F-10.2 [APPROVED]
Cat 11-14: unmarked (REMEDIATE handoff intended)
Leaks L-1, L-2, L-3: unmarked (REMEDIATE handoff intended)

Total approved for execution: 18 findings (7 categories)
Total deferred: 2 findings
Total unmarked (recommendation-only routing): 11 findings + 3 leaks
```

---

## Phase 2 — Execution

The maintainer re-invokes the Skill in Phase 2 mode.

### Entry conditions

```
EC-1 (file-state authorization): PASS — 18 [APPROVED] markers detected
EC-2 (profile validation): PASS
EC-3 (engine baseline coherence): PASS — state snapshot still matches Phase 0
EC-4 (critic-gate availability): N/A — profile threshold optional
EC-5 (marker placement validation): PASS — all markers on Cat 1-10 findings;
  no recommendation-only markers to skip-with-notice
```

Phase 2 proceeds.

### Batches built

```
Batch 1: Cat 1, high-confidence, medium-risk → F-1.3
Batch 2: Cat 2, high-confidence, low-risk → F-2.1, F-2.2, F-2.3, F-2.5
Batch 3: Cat 2, medium-confidence, low-risk → F-2.6, F-2.7
Batch 4: Cat 2, high-confidence, risk-flagged → F-2.4
Batch 5: Cat 4, high-confidence, low-risk → F-4.1
Batch 6: Cat 5, medium-confidence, low-risk → F-5.1, F-5.2
Batch 7: Cat 9, high-confidence, low-risk → F-9.2, F-9.3, F-9.4, F-9.6, F-9.7, F-9.8
Batch 8: Cat 10, high-confidence, low-risk → F-10.1
Batch 9: Cat 10, medium-confidence, low-risk → F-10.2
```

### Per-batch execution (selected highlights)

Batch 4 (high-risk-flagged Cat 2 entry F-2.4 `Bash(rm -rf*)` removal): the maintainer invokes critic-gate manually before executing despite optional threshold. Critic-gate APPROVE. Removal applied. Verification: re-scan settings → 0 surfaced.

Batch 7 (Cat 9 stale-state cluster): all six findings update CLAUDE.md state snapshot values to current. Verification: recount + re-scan → state matches current. PASS.

Batch 9 (F-10.2 — Skill pytest-runner missing metadata.notes): edit applied; description re-validated; PASS.

### Commit plan execution — defer-to-downstream

Per Phase 1's defer-to-downstream recommendation, no `git add` or `git commit` runs. File edits accumulate in working tree (now ~30 modified files including the original 12 + Phase 2 changes).

The cleanup log records:

```
Commit plan: defer-to-downstream
Rationale (from Phase 1): distribution intent + fresh-repo migration on roadmap
Working tree state: ~30 modified files; HEAD unchanged
Audit trail substitute: this cleanup_execution_log
Downstream session: fresh-repo migration handles baseline + cleanup commit pairing
```

This case is the production-validated D11 path. The original Phase 2 attempt under Option B engine baseline commit hit a permission denial on the 207 MB / 883-file scope; Path 3 deferral was accepted as the right answer. The Skill internalized this as defer-to-downstream being a first-class option, not a fallback.

### Final verification sweep

```
Engine baseline coherence: PASS — Phase 0 snapshot still matches; updates applied
  to CLAUDE.md state section reflect current actual state.
Test backstop: pytest, all 451 tests passing — PASS.

Skipped findings (recommendation-only routing):
  - F-11.1, F-12.1, F-12.2, F-13.1 — recommend REMEDIATE handoff
  - F-14.1, F-14.4, F-14.5 — methodology-generalizable; consider standalone build
  - L-1, L-2, L-3 — recommend REMEDIATE handoff

Closeout:
  Findings approved: 18
  Findings executed: 18 (100%)
  Findings deferred: 2 (F-1.1, F-1.2 — fresh-repo migration)
  Findings skipped: 11 + 3 leaks (recommendation-only)
  Commit plan: defer-to-downstream
  Final test result: PASS
  REMEDIATE recommendations: 4 cat findings + 3 leaks
```

---

## What this example demonstrates

1. **Bootstrap heritage carve-out works at scale.** 49 inherited files; 0 false positives on unmodified files; 3 valid findings on modified-recently files; 1 generalization correctly caught a file outside the explicit inherited list.

2. **Cat 9 is the most-cited category in evolved deployments.** 8 of 23 findings landed in Cat 9, dominated by stale-state sub-signals — matching the production validation pattern.

3. **The three approval forms compose naturally.** Same session, same maintainer, three forms used — blanket for Cat 2 (homogeneous), fragmented for Cat 1 + Cat 9 (mixed intent), conditional for the remaining low-risk surface.

4. **Defer-to-downstream is a first-class commit-plan option.** The maintainer's distribution intent + working-tree state correctly triggered Phase 1's deferral recommendation; Phase 2 accepted it as a valid choice.

5. **Recommendation-only routing prevents structural over-reach.** 11 cat findings + 3 leaks were not executed by Phase 2; they routed to REMEDIATE. The Skill's discipline kept Phase 2 focused on tractable single-edit work.

6. **Cat 14 surfaced the high-value methodology-generalizable cluster.** F-14.1 + F-14.4 + F-14.5 form a dependency chain where the state-query script unlocks the snapshot-update hook; both transfer to other CC engines. This is exactly what process-abstraction detection is for.

---

*End of worked example. Authorization detail in design doc §7. Commit plan detail in design doc §8 + `execution-discipline.md`. Process-abstraction detail in `process-abstraction-detection.md`.*
