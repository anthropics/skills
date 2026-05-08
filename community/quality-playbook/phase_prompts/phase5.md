{skill_fallback_guide}

You are a quality engineer continuing a phase-by-phase quality playbook run. Phases 1-4 are complete.

Read these files to get context:
1. quality/PROGRESS.md - run metadata, phase status, cumulative BUG tracker
2. quality/BUGS.md - all confirmed bugs from code review and spec audit
3. quality/REQUIREMENTS.md - derived requirements
4. SKILL.md - read the Phase 5 section ("Phase 5: Post-Review Reconciliation and Closure Verification"). Also read references/requirements_pipeline.md, references/review_protocols.md, and references/spec_audit.md. Resolve SKILL.md and the references/ directory via the documented fallback list above; do NOT assume any single install layout.

Execute Phase 5: Reconciliation + TDD + Closure.

1. Run the Post-Review Reconciliation per references/requirements_pipeline.md. Update COMPLETENESS_REPORT.md.
2. Run closure verification: every BUG in the tracker must have either a regression test or an explicit exemption.
3. Write bug writeups at quality/writeups/BUG-NNN.md for EVERY confirmed bug. The canonical template is the "Bug writeup generation" section of SKILL.md (resolve via the fallback list above) — read that section before writing. Use the exact field headings listed there: **Summary, Spec reference, The code, Observable consequence, Depth judgment, The fix, The test, Related issues**. Sections 1–4, 6, 7 are required in every writeup; section 5 (Depth judgment) fires only when the consequence isn't self-evident from the immediate code; section 8 (Related issues) is included only when related bugs exist. Do NOT introduce fields that aren't in the template (no "Minimal reproduction" as a top-level field, no "Patch path:" as a top-level field — those belong inside Spec reference and The test respectively).

   **MANDATORY HYDRATION STEP.** Before writing a writeup, re-open quality/BUGS.md and locate the `### BUG-NNN:` entry for the bug you are about to write up. Every confirmed bug in BUGS.md already has the content you need — your job is to copy it into the writeup's sections, not to invent it. If a field is missing from BUGS.md, that is a reconciliation error to surface in PROGRESS.md, not a field to fabricate. Use this field map:

   | BUGS.md field              | Writeup section              | How to use it                                                                 |
   |----------------------------|------------------------------|-------------------------------------------------------------------------------|
   | Title line (### BUG-NNN:…) | Summary                      | One sentence naming the function/code path and the observable failure.        |
   | Primary requirement        | Spec reference               | `- Requirement: REQ-NNN`                                                      |
   | Spec basis                 | Spec reference               | `- Spec basis: <doc path + line range(s), semicolon-separated if multiple>` plus a ≤15-word contract quote copied verbatim from the cited lines. |
   | Location                   | The code                     | Cite `file:line` and describe what the current path does there.               |
   | Minimal reproduction       | Observable consequence       | Weave into the consequence paragraph as the triggering input.                 |
   | Expected + Actual behavior | Observable consequence       | The actual behavior is the observable failure; the expected defines the gap.  |
   | Regression test            | The test                     | `- Regression test: <function name>` — verbatim from BUGS.md.                 |
   | Patches (regression)       | The test                     | `- Regression patch: <path>` — verbatim from BUGS.md.                         |
   | Patches (fix)              | The fix + The test           | If a fix patch file exists, read it and paste the unified diff inside ```diff; also list the patch path as `- Fix patch: <path>` under The test. If no fix patch exists (confirmed-open bug), write the minimal concrete unified diff directly in The fix anyway — SKILL.md requires an inline diff in every writeup. In the no-patch case, omit the `Fix patch:` bullet from The test. |
   | Red/green logs             | The test                     | `- Red receipt: quality/results/BUG-NNN.red.log` and the matching green path. |

   **Worked example.** The BUGS.md entry for BUG-004 is:

       ### BUG-004: naive upstream timestamps crash ETA math
       - Source: Code Review
       - Severity: HIGH
       - Primary requirement: REQ-006
       - Location: bus_tracker.py:138-144
       - Spec basis: quality/REQUIREMENTS.md:163-172; quality/QUALITY.md:57-65
       - Minimal reproduction: Return a visit whose ExpectedArrivalTime is an ISO string
         without timezone information, such as 2026-04-21T12:00:00.
       - Expected behavior: The affected arrival degrades to unknown-time while the rest
         of the stop remains usable.
       - Actual behavior: datetime.fromisoformat() returns a naive datetime and
         subtracting it from datetime.now(timezone.utc) raises TypeError, aborting the
         stop/request path.
       - Regression test: quality.test_regression.TestPhase3Regressions.test_bug_004_fetch_stop_arrivals_degrades_naive_timestamps
       - Patches: quality/patches/BUG-004-regression-test.patch, quality/patches/BUG-004-fix.patch

   The hydrated writeup sections look like this (sketch — paste the real diff from the
   fix patch file into ```diff, don't make one up):

       ## Summary
       fetch_stop_arrivals() crashes the whole stop/request path when an upstream visit
       carries a naive ExpectedArrivalTime, instead of degrading that arrival to
       unknown-time.

       ## Spec reference
       - Requirement: REQ-006
       - Spec basis: quality/REQUIREMENTS.md:163-172; quality/QUALITY.md:57-65
       - Behavioral contract quote: "degrade a bad per-arrival timestamp to unknown-time instead of aborting the whole response path"

       ## The code
       At bus_tracker.py:138-144, the parser calls datetime.fromisoformat(...) on
       ExpectedArrivalTime and subtracts the result from datetime.now(timezone.utc)…

       ## Observable consequence
       When the upstream visit returns ExpectedArrivalTime="2026-04-21T12:00:00"
       (no timezone), fromisoformat() returns a naive datetime, the subtraction
       raises TypeError, and the entire stop/request path aborts rather than the
       single affected arrival degrading to unknown-time.

       ## The fix
       ```diff
       <paste the real unified diff from quality/patches/BUG-004-fix.patch here>
       ```

       ## The test
       - Regression test: quality.test_regression.TestPhase3Regressions.test_bug_004_fetch_stop_arrivals_degrades_naive_timestamps
       - Regression patch: quality/patches/BUG-004-regression-test.patch
       - Fix patch: quality/patches/BUG-004-fix.patch
       - Red receipt: quality/results/BUG-004.red.log
       - Green receipt: quality/results/BUG-004.green.log

   **Confirmation checklist (per writeup, before moving to the next bug).** (a) Every
   required section has populated content copied from BUGS.md or the patch files —
   no empty backticks, no sentinel filler like "is a confirmed code bug in ``" or
   "The affected implementation lives at ``" or "Patch path: ``". (b) The ```diff
   fence contains at least one `+` or `-` line from the actual fix patch. (c) The
   Summary names a real function or code path, not the BUG identifier. (d) No
   angle-bracket placeholders (e.g., `<...>`) remain in the final writeup — those are
   pedagogical markers from the worked example and from SKILL.md, never acceptable
   output.
4. Run the TDD red-green cycle: for each confirmed bug, run the regression test against unpatched code -> quality/results/BUG-NNN.red.log. If a fix patch exists, run against patched code -> quality/results/BUG-NNN.green.log. If the test runner is unavailable, create the log with NOT_RUN on the first line.
5. Generate sidecar JSON: quality/results/tdd-results.json and quality/results/integration-results.json (schema_version "1.1", canonical fields: id, requirement, red_phase, green_phase, verdict, fix_patch_present, writeup_path).
6. If mechanical verification artifacts exist, run quality/mechanical/verify.sh and save receipts.
7. Run terminal gate verification, write it to PROGRESS.md.

### MANDATORY CARDINALITY GATE (Lever 3, v1.5.2)

Before finalizing this phase, run the cardinality reconciliation gate against the current repo state. Locate `quality_gate.py` via the same fallback list used for SKILL.md (it sits in the same directory as SKILL.md in every install layout), then invoke it as a script — `quality_gate.py` runs `check_v1_5_2_cardinality_gate(repo_dir)` as part of its standard pass:

    python3 <resolved_quality_gate_path> .

Where `<resolved_quality_gate_path>` is the first hit when walking the documented install-location fallback list, with `SKILL.md` swapped for `quality_gate.py` (e.g., `quality_gate.py`, `.claude/skills/quality-playbook/quality_gate.py`, `.github/skills/quality_gate.py`, `.cursor/skills/quality-playbook/quality_gate.py`, `.continue/skills/quality-playbook/quality_gate.py`, `.github/skills/quality-playbook/quality_gate.py`).

If the gate output contains any line beginning with `cardinality gate:`, or reports uncovered cells, malformed cell IDs, missing consolidation rationale on multi-cell Covers, or malformed downgrade records, STOP. Fix the BUGS.md entries or the `compensation_grid_downgrades.json` file. Do NOT proceed to completion until those failure lines no longer appear.

For every pattern-tagged REQ, the Phase 5 contract is:
- Every grid cell with `"present": false` appears in either a BUG's `Covers:` list or a downgrade record.
- Every `Covers:` entry uses the canonical cell ID form `REQ-N/cell-<item>-<site>`.
- Every BUG with ≥2 `Covers:` entries has a non-empty `Consolidation rationale:` line.
- Every downgrade record has `cell_id`, `authority_ref`, `site_citation`, `reason_class` (in the enum), `falsifiable_claim` (non-empty).

The cardinality gate is blocking. It is intentionally stricter than the Phase 3 advisory self-check; the advisory check is meant to surface problems early, but Phase 5 is where they become fatal.

Mark Phase 5 complete in PROGRESS.md (use the checkbox format `- [x] Phase 5 - Reconciliation` — do NOT switch to a table).

IMPORTANT: quality_gate.py will FAIL Phase 5 if any writeup is missing a non-empty ```diff block or contains any of these sentinel phrases verbatim: "is a confirmed code bug in ``", "The affected implementation lives at ``", "Patch path: ``", "- Regression test: ``", "- Regression patch: ``". Those two checks are the hard gate. Skipping the BUGS.md hydration step above is not gate-enforced but will produce writeups that read as unpopulated stubs and fail a human review — do not skip it.
