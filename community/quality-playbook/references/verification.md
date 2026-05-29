# Verification Checklist (Phase 6: Verify)

Before declaring the quality playbook complete, check every benchmark below. If any fails, go back and fix it.

## Self-Check Benchmarks

### 1. Test Count

Calculate the heuristic target: (testable spec sections) + (QUALITY.md scenarios) + (defensive patterns from Step 5).

- **Well below target** → You likely missed spec requirements or skimmed defensive patterns. Go back and check.
- **Near target** → Review whether you tested negative cases and boundaries.
- **Above target** → Fine, as long as every test is meaningful. Don't pad to hit a number.

### 2. Scenario Coverage

Count the scenarios in QUALITY.md. Count the scenario test functions in your functional test file. The numbers must match exactly.

### 3. Cross-Variant Coverage

If the project handles N input variants, what percentage of tests exercise all N?

Count: tests that loop or parametrize over all variants / total tests.

**Heuristic: ~30%.** If well below, look for single-variant tests that should be parametrized. Common candidates: structural completeness, identity verification, required field presence, data relationships, semantic correctness. The exact percentage matters less than ensuring cross-cutting properties are tested across all variants.

### 4. Boundary and Negative Test Count

Count the defensive patterns from Step 5. Count your boundary/negative tests. The ratio should be close to 1:1. If significantly lower, write more tests targeting untested defensive patterns.

### 5. Assertion Depth

Scan your assertions. How many are presence checks vs. value checks? If more than half are presence-only (`assert x is not None`, `assert x in output`), strengthen them to check actual values.

### 6. Layer Correctness

For each test, ask: "Am I testing the *requirement* or the *mechanism*?" If any test only asserts that a specific error type is raised without also verifying pipeline output, it's testing the mechanism. Rewrite to test the outcome.

### 7. Mutation Validity

For every test that mutates a fixture, verify the mutation value is in the "Accepts" column of your Step 5b schema map. If any mutation uses a type the schema rejects, the test fails with a validation error instead of testing defensive code. Fix it.

### 8. All Tests Pass — Zero Failures AND Zero Errors

Run the test suite using the project's test runner:

- **Python:** `pytest quality/test_functional.py -v`
- **Scala:** `sbt "testOnly *FunctionalSpec"`
- **Java:** `mvn test -Dtest=FunctionalTest` or `gradle test --tests FunctionalTest`
- **TypeScript:** `npx jest functional.test.ts --verbose`
- **Go:** `go test -v` targeting the generated test file's package — use the project's existing module and package layout
- **Rust:** `cargo test` targeting the generated test — either the integration test target in `tests/` or inline `#[cfg(test)]` tests, matching the project's conventions

**Check for both failures AND errors.** Most test frameworks distinguish between test failures (assertion errors) and test errors (setup failures, missing fixtures, import/resolution errors, exceptions during initialization). Both are broken tests. A common mistake: generating tests that reference shared fixtures or helpers that don't exist. These show up as setup errors, not assertion failures — but they are just as broken.

**Expected-failure (xfail) tests do not count against this benchmark.** Regression tests in `quality/test_regression.*` use expected-failure markers (`@pytest.mark.xfail(strict=True)`, `@Disabled`, `t.Skip`, `#[ignore]`) to confirm that known bugs are still present. These tests are *supposed* to fail — that's the point. The "zero failures and zero errors" benchmark applies to `quality/test_functional.*` (the functional test suite), not to `quality/test_regression.*` (the bug confirmation suite). If your test runner reports failures from xfail-marked regression tests, that's correct behavior, not a benchmark violation. If an xfail test unexpectedly *passes*, that means the bug was fixed and the xfail marker should be removed — treat that as a finding to investigate, not a test failure.

After running, check:
- All tests passed — count must equal total test count
- Zero failures
- Zero errors/setup failures

If there are setup errors, you forgot to create the fixture/setup file or you referenced helpers that don't exist. Go back and either create them or rewrite the tests to be self-contained.

### 9. Existing Tests Unbroken

Run the project's full test suite (not just your new tests). Your new files should not break anything.

## Documentation Verification

### 10. QUALITY.md Scenarios Reference Real Code and Label Sources

Every scenario should mention actual function names, file names, or patterns that exist in the codebase. Grep for each reference to confirm it exists.

If working from non-formal requirements, verify that each scenario and test includes a requirement tag using the canonical format: `[Req: formal — README §3]`, `[Req: inferred — from validate_input() behavior]`, `[Req: user-confirmed — "must handle empty input"]`. Inferred requirements should be flagged for user review in the Phase 7 interactive session.

### 11. RUN_CODE_REVIEW.md Is Self-Contained

An AI with no prior context should be able to read it and perform a useful review. Check: does it list bootstrap files? Does it have specific focus areas? Are the guardrails present?

### 12. RUN_INTEGRATION_TESTS.md Is Executable and Field-Accurate

Every command should work. Every check should have a concrete pass/fail criterion — not "verify it looks right" but a specific expected result.

**Verify quality gates were written from a Field Reference Table, not from memory.** Check that:

1. A Field Reference Table exists in RUN_INTEGRATION_TESTS.md with a row for every field in every schema
2. **Field count check:** For each schema, count the fields in the actual schema file and count the rows in your table. If the numbers don't match, you missed fields or invented fields. The most common failure: a schema has 8 fields but the table only has 2-3 "important" ones.
3. **Character-for-character check:** Re-read each schema file now and compare every field name in your table against the file contents. `document_id` ≠ `doc_id`. `sentiment_score` ≠ `sentiment`. `classification` ≠ `category`.
4. Every type and constraint matches the schema (`float 0-1` is not `int 0-100`, `string enum` is not `integer`)

If any field name, count, or type is wrong, fix it before proceeding. The table is the foundation — if the table is wrong, every quality gate built from it is wrong.

### 13. RUN_SPEC_AUDIT.md Prompt Is Copy-Pasteable

The definitive audit prompt should work when pasted into Claude Code, Cursor, and Copilot without modification (except file reference syntax).

### 14. Structured Output Schemas Are Valid and Conformant

Verify that `RUN_TDD_TESTS.md` and `RUN_INTEGRATION_TESTS.md` both instruct the agent to produce:
- JUnit XML output using the framework's native reporter (pytest `--junitxml`, gotestsum `--junitxml`, Maven Surefire reports, `jest-junit`, `cargo2junit`)
- A sidecar JSON file (`tdd-results.json` or `integration-results.json`) in `quality/results/`

Check that each protocol's JSON schema includes all mandatory fields:
- **tdd-results.json:** `schema_version`, `skill_version`, `date`, `project`, `bugs`, `summary`. Per-bug: `id`, `requirement`, `red_phase`, `green_phase`, `verdict`, `fix_patch_present`, `writeup_path`.
- **integration-results.json:** `schema_version`, `skill_version`, `date`, `project`, `recommendation`, `groups`, `summary`, `uc_coverage`. Per-group: `group`, `name`, `use_cases`, `result`.

Verify that the protocol does NOT contain flat command-list schemas (a `"results"` or `"commands_run"` array without `"groups"` is non-conformant). Verify that verdict/result enum values use only the allowed values defined in SKILL.md (e.g., `"TDD verified"`, `"red failed"`, `"green failed"`, `"confirmed open"` for TDD verdicts; `"pass"`, `"fail"`, `"skipped"`, `"error"` for integration results; `"SHIP"`, `"FIX BEFORE MERGE"`, `"BLOCK"` for recommendations). The TDD verdict `"skipped"` is deprecated — use `"confirmed open"` with `red_phase: "fail"` and `green_phase: "skipped"` instead. The TDD summary must include a `confirmed_open` count alongside `verified`, `red_failed`, and `green_failed`.

Both sidecar JSON templates must use `schema_version: "1.1"` (v1.1 change: `verdict: "skipped"` deprecated in favor of `"confirmed open"`). Both protocols must include a **post-write validation step** instructing the agent to reopen the sidecar JSON after writing it and verify required fields, enum values, and no extra undocumented root keys.

### 15. Patch Validation Gate Is Executable

For each confirmed bug with patches, verify:
1. The `git apply --check` commands specified in the patch validation gate use the correct patch paths (`quality/patches/BUG-NNN-*.patch`)
2. The compile/syntax check command matches the project's actual build system — not a generic placeholder
3. For interpreted languages (Python, JavaScript), the gate specifies the appropriate syntax check (`python -m py_compile`, `node --check`, `pytest --collect-only`, or equivalent)
4. The gate includes a temporary worktree or stash-and-revert instruction to comply with the source boundary rule

### 16. Regression Test Skip Guards Are Present

Grep `quality/test_regression.*` for the language-appropriate skip/xfail mechanism. Every test function must have a guard:
- Python: `@pytest.mark.xfail` or `@unittest.expectedFailure`
- Go: `t.Skip(`
- Java: `@Disabled`
- Rust: `#[ignore]`
- TypeScript/JavaScript: `test.failing(`, `test.fails(`, or `it.skip(`

A regression test without a skip guard will cause unexpected failures when the test suite runs on unpatched code. Every guard must reference the bug ID (BUG-NNN format) and the fix patch path.

### 17. Integration Group Commands Pass Pre-Flight Discovery

For each integration test group command in `RUN_INTEGRATION_TESTS.md`, verify that the command discovers at least one test using the framework's dry-run mode (`pytest --collect-only`, `go test -list`, `vitest list`, `jest --listTests`, `cargo test -- --list`). A group whose command fails discovery will produce a `covered_fail` result that masks a selector bug as a code bug. If a command cannot be validated (no dry-run mode available), note the limitation.

### 18. Version Stamps Present on All Generated Files

Grep every generated Markdown file in `quality/` for the attribution line: `Generated by [Quality Playbook]`. Grep every generated code file for `Generated by Quality Playbook`. Every file must have the stamp with the correct version number. Files without stamps are not traceable to the tool and version that created them. **Exemptions:** sidecar JSON files (use `skill_version` field), JUnit XML files (framework-generated), and `.patch` files (stamp would break `git apply`). For Python files with shebang or encoding pragma, verify the stamp comes after the pragma, not before.

### 19. Enumeration Completeness Checks Performed

Verify that the code review (Pass 1 and Pass 2) performed mechanical two-list enumeration checks wherever the code uses `switch`/`case`, `match`, or if-else chains to dispatch on named constants. For each such check, the review must show: (a) the list of constants defined in headers/enums/specs, (b) the list of case labels actually present in the code, (c) any gaps. A review that claims "the whitelist covers all values" or "all cases are handled" without showing the two-list comparison is non-conformant — this is the specific hallucination pattern the check prevents.

### 20. Bug Writeups Generated for All Confirmed Bugs

For each bug in `tdd-results.json` (both `verdict: "TDD verified"` and `verdict: "confirmed open"`), verify that a corresponding `quality/writeups/BUG-NNN.md` file exists and that `tdd-results.json` has a non-null `writeup_path` for that bug. Each writeup must include: summary, spec reference, code citation, observable consequence, fix diff, and test description. A confirmed bug without a writeup is incomplete.

### 21. Triage Verification Probes Include Executable Evidence

Open the triage report (`quality/spec_audits/YYYY-MM-DD-triage.md`). For every finding that was confirmed or rejected via a verification probe, verify that the triage entry includes a test assertion (not just prose reasoning). Rejections must include a PASSING assertion proving the finding is wrong. Confirmations must include a FAILING assertion proving the bug exists. Every assertion must cite an exact line number. A triage decision based on prose reasoning alone ("lines 3527-3528 explicitly preserve X") without a mechanical assertion is non-conformant.

### 22. Enumeration Lists Extracted From Code, Not Copied From Requirements

When the code review includes an enumeration check (e.g., "case labels present in function X"), verify that the code-side list includes per-item line numbers from the actual source. If the list matches the requirements list word-for-word without line numbers, the enumeration was likely copied rather than extracted and must be redone. Also verify that the triage pre-audit spot-checks report the actual contents of cited lines ("line 3527 contains `default:`") rather than merely confirming claims ("line 3527 preserves RING_RESET").

### 23. Mechanical Verification Artifacts Exist and Pass Integrity Check

For every contract or requirement that asserts a function handles/preserves/dispatches a set of named constants (feature bits, enum values, opcode tables), verify that a corresponding `quality/mechanical/<function>_cases.txt` file exists and was generated by a non-interactive shell pipeline. Contracts that reference dispatch-function coverage without citing a mechanical artifact are non-conformant.

**Integrity check (mandatory):** Run `bash quality/mechanical/verify.sh`. This script re-executes the same extraction commands that generated each mechanical artifact and diffs the results. If ANY diff is non-empty, the artifact was tampered with — the model may have written expected output instead of capturing actual shell output. A mismatched artifact must be regenerated by re-running the extraction command (not by editing the file). This check exists because in v1.3.19, the model executed the correct awk/grep command but wrote a fabricated 9-line output (including a hallucinated `case VIRTIO_F_RING_RESET:`) to the file, when the actual command only produces 8 lines.

### 24. Source-Inspection Regression Tests Execute (No `run=False`)

Grep `quality/test_regression.*` for `run=False` (Python), `t.Skip` with a source-inspection comment, or equivalent skip mechanisms. Any regression test whose purpose is source-structure verification (string presence in function bodies, case label existence, enum extraction) must execute — it must NOT use `run=False`. These tests are safe, deterministic string-match operations. An `xfail(strict=True)` test that actually fails reports as XFAIL (expected), which is correct behavior. A source-inspection test with `run=False` is the worst possible state: the correct check exists but never fires.

### 25. Contradiction Gate Passed (Executed Evidence vs. Prose)


Verify that no executed artifact contradicts a prose artifact at closure. Specifically: (a) if any `quality/mechanical/*` file shows a constant as absent, no prose artifact (`CONTRACTS.md`, `REQUIREMENTS.md`, code review, triage) may claim it is present; (b) if any regression test with `xfail` actually fails (XFAIL), `BUGS.md` may not claim that bug is "fixed in working tree" without a commit reference; (c) if TDD traceability shows a red-phase failure, the triage may not claim the corresponding code is compliant. Any contradiction must be resolved before closure.

### 26. Version Stamp Consistency

Read the `version:` field from the SKILL.md metadata (locate SKILL.md in the skill installation directory — typically `.github/skills/SKILL.md` or `.claude/skills/quality-playbook/SKILL.md`). Check every generated artifact: PROGRESS.md's `Skill version:` field, every `> Generated by` attribution line, every code file header stamp, and every sidecar JSON `skill_version` field. Every version stamp must match the SKILL.md metadata exactly. A single mismatch is a benchmark failure. This check exists because in v1.3.21 benchmarking, 5 of 9 repos had version stamps from older skill versions due to a hardcoded template.

### 27. Mechanical Directory Conformance

If `quality/mechanical/` exists, it must contain at minimum a `verify.sh` file. An empty `quality/mechanical/` directory is non-conformant. If no dispatch-function contracts exist, the directory should not exist — instead record `Mechanical verification: NOT APPLICABLE` in PROGRESS.md. If the directory exists with extraction artifacts, `verify.sh` must include one verification block per saved file (not just one). A verify.sh that checks only one artifact when multiple exist is incomplete.

### 28. TDD Artifact Closure

If `quality/BUGS.md` contains any confirmed bugs, `quality/results/tdd-results.json` is mandatory. If any bug has a red-phase result, `quality/TDD_TRACEABILITY.md` is also mandatory. Zero-bug repos may omit both files. For repos where TDD cannot execute, tdd-results.json must exist with `verdict: "deferred"` and a `notes` field explaining why.

### 29. Triage-to-BUGS.md Sync

After spec audit triage, every finding confirmed as a code bug must appear in `quality/BUGS.md`. A triage report with confirmed code bugs and no corresponding BUGS.md entries is non-conformant. If BUGS.md does not exist when confirmed bugs exist, it must be created.

### 30. Writeups for All Confirmed Bugs

Every confirmed bug (TDD-verified or confirmed-open) must have a writeup at `quality/writeups/BUG-NNN.md`. For confirmed-open bugs without fix patches, the writeup notes the absence of fix/green-phase evidence. A run with confirmed bugs and no writeups directory is incomplete.

### 31. Phase 4 Triage File Exists

Phase 4 is not complete until a triage file exists at `quality/spec_audits/YYYY-MM-DD-triage.md`. If only auditor reports exist with no triage synthesis, Phase 4 is incomplete.

### 32. Seed Checks Executed Mechanically (Continuation Mode)

When `quality/previous_runs/` exists and Phase 0 runs, verify that `quality/SEED_CHECKS.md` was generated with one entry per unique bug from prior runs. Each seed must have a mechanical verification result (FAIL = bug still present, PASS = bug fixed) obtained by actually running the assertion — not by reading prose from the prior run. If a seed's regression test exists in a prior run, the assertion must be re-executed against the current source tree. A seed marked FAIL without executing the assertion is non-conformant. This benchmark only applies when continuation mode is active (prior runs exist).

### 33. Convergence Status Recorded in PROGRESS.md (Continuation Mode)

When Phase 0 runs, verify that PROGRESS.md contains a `## Convergence` section with: run number, seed count, net-new bug count, and a CONVERGED/NOT CONVERGED verdict. The net-new count must equal the number of bugs in BUGS.md that don't match any seed by file:line. A missing convergence section when `SEED_CHECKS.md` exists is non-conformant. This benchmark only applies when continuation mode is active.

### 34. BUGS.md Always Exists

Every completed run must produce `quality/BUGS.md`. If the run confirmed source-code bugs, BUGS.md must list them. If the run found zero source-code bugs, BUGS.md must contain a `## Summary` with a positive assertion: "No confirmed source-code bugs found" with counts of candidates evaluated and eliminated. A completed run (Phase 5 marked complete) with no BUGS.md is non-conformant. This benchmark exists because in v1.3.22 benchmarking, express completed all phases with zero source bugs but produced no BUGS.md, making it ambiguous whether the file was intentionally omitted or accidentally skipped.

### 35. Immediate Mechanical Integrity Gate (Phase 2a)

If `quality/mechanical/` exists, verify that `bash quality/mechanical/verify.sh` was executed immediately after each `*_cases.txt` was written — before any contract, requirement, or triage artifact cites the extraction. Evidence: `quality/results/mechanical-verify.log` and `quality/results/mechanical-verify.exit` exist, and the exit file contains `0`. If these receipt files are missing or the exit code is non-zero, the mechanical extraction was not verified at the point of creation. This benchmark exists because v1.3.23 deferred verification to Phase 6, allowing downstream artifacts (CONTRACTS.md, REQUIREMENTS.md, triage probes) to build on a forged extraction for the entire run before the mismatch was (not) caught.

### 36. Mechanical Artifacts Not Used as Evidence in Triage Probes

Grep all triage and verification probe files (`quality/spec_audits/*`) for `open('quality/mechanical/` or `cat quality/mechanical/`. If any probe reads a `quality/mechanical/*.txt` file as sole evidence for what a source file contains, it is circular verification and the benchmark fails. Probes must read the source file directly or re-execute the extraction pipeline. This benchmark exists because v1.3.23 Probe C validated the forged mechanical artifact instead of the source code, passing with fabricated data.

### 37. Phase 6 Mechanical Closure Uses Bash (Not Python Substitution)

If `quality/mechanical/` exists, verify that Phase 6 ran `bash quality/mechanical/verify.sh` as a literal shell command — not a Python script reading the artifact file. Evidence: `quality/results/mechanical-verify.log` contains output from the bash script (lines like "OK: ..." or "MISMATCH: ..."), not Python tracebacks or `pathlib` output. PROGRESS.md must include a `## Phase 6 Mechanical Closure` heading with the recorded stdout and exit code. This benchmark exists because v1.3.23 substituted Python `Path.read_text()` for `bash verify.sh`, creating a circular check that passed despite the artifact being fabricated.

### 38. Individual Auditor Report Artifacts Exist

If Phase 4 (spec audit) ran, verify that individual auditor report files exist at `quality/spec_audits/YYYY-MM-DD-auditor-N.md` (one per auditor), not just the triage synthesis. A single triage file without individual reports conflates discovery with reconciliation. This benchmark exists to ensure pre-reconciliation findings are preserved for independent verification.

### 39. BUGS.md Uses Canonical Heading Format

Every confirmed bug in BUGS.md must use the heading level `### BUG-NNN`. Grep for `^### BUG-` and count; grep for other bug heading patterns (`^## BUG-`, `^\*\*BUG-`, `^- BUG-`) and verify zero matches. Inconsistent heading levels cause machine-readable counts to disagree with the document.

### 40. Artifact File-Existence Gate Passed

Before Phase 5 is marked complete, verify that all required artifacts exist as files on disk — not just referenced in PROGRESS.md. Required files: EXPLORATION.md, BUGS.md, REQUIREMENTS.md, QUALITY.md, PROGRESS.md, COVERAGE_MATRIX.md, COMPLETENESS_REPORT.md, CONTRACTS.md, test_functional.* (or language-appropriate alternative: FunctionalSpec.*, FunctionalTest.*, functional.test.*), RUN_CODE_REVIEW.md, RUN_INTEGRATION_TESTS.md, RUN_SPEC_AUDIT.md, RUN_TDD_TESTS.md, and AGENTS.md (at project root). If Phase 3 ran: at least one file in code_reviews/. If Phase 4 ran: at least one auditor file and a triage file in spec_audits/. If Phase 0 or 0b ran: SEED_CHECKS.md as a standalone file. If confirmed bugs exist: tdd-results.json in results/. If any bug has a red-phase result: TDD_TRACEABILITY.md. This benchmark exists because v1.3.24 benchmarking showed express writing a terminal gate section to PROGRESS.md claiming 1 confirmed bug, but BUGS.md, code review files, and spec audit files were never written to disk.

### 41. Sidecar JSON Post-Write Validation

After `tdd-results.json` and/or `integration-results.json` are written, verify that each file contains all required keys with conformant values. For `tdd-results.json`: required root keys are `schema_version`, `skill_version`, `date`, `project`, `bugs`, `summary`. Each `bugs` entry must have `id`, `requirement`, `red_phase`, `green_phase`, `verdict`, `fix_patch_present`, `writeup_path`. The `summary` must include `confirmed_open`. For `integration-results.json`: required root keys are `schema_version`, `skill_version`, `date`, `project`, `recommendation`, `groups`, `summary`, `uc_coverage`. Both must have `schema_version: "1.1"`. A sidecar JSON with missing required keys, non-standard root keys, or invalid enum values is non-conformant. This benchmark exists because v1.3.25 benchmarking showed 6 of 8 repos with non-conformant sidecar JSON — httpx invented an alternate schema, serde used legacy shape, javalin omitted `summary` and per-bug fields, express used invalid phase values, and others used invalid verdict/result enum values.

### 42. Script-Verified Closure Gate Passed

Before Phase 5 is marked complete, `quality_gate.sh` must be executed from the project root and must exit 0. The script's full output must be saved to `quality/results/quality-gate.log`. A Phase 5 completion with no `quality-gate.log` or with a log showing FAIL results is non-conformant. This benchmark exists because v1.3.21–v1.3.25 relied entirely on model self-attestation for artifact conformance checks, and benchmarking showed persistent non-compliance (heading format, sidecar schema, use case identifiers, version stamps) that a script catches mechanically.

### 43. Canonical Use Case Identifiers Present

REQUIREMENTS.md must contain use cases labeled with canonical identifiers in the format `UC-01`, `UC-02`, etc. Grep for `UC-[0-9]` and count matches. A repo with use case content but no canonical identifiers is non-conformant. This benchmark exists because v1.3.25 benchmarking showed 7 of 8 repos with use case sections but no machine-readable identifiers — downstream tooling cannot count or cross-reference use cases without a canonical format.

### 44. Regression-Test Patches Exist for Every Confirmed Bug

For every confirmed bug (any BUG-NNN entry in BUGS.md), verify that `quality/patches/BUG-NNN-regression-test.patch` exists. A confirmed bug without a regression-test patch is incomplete — the patch is the strongest independent evidence that the bug exists. Fix patches (`BUG-NNN-fix.patch`) are optional but strongly encouraged for simple fixes. This benchmark exists because v1.3.25 and v1.3.26 benchmarking showed 4/8 repos with 0 patch files despite having confirmed bugs, and the writeups described what fixes should look like without generating actual patch files.

### 45. Writeup Inline Fix Diffs

Every writeup at `quality/writeups/BUG-NNN.md` must contain a ` ```diff ` fenced code block with the proposed fix in unified diff format. This is section 6 ("The fix") of the writeup template. A writeup that says "see patch file" or "no fix patch included" without an inline diff is incomplete — the inline diff is what makes the writeup actionable for a maintainer reading just the writeup without access to the patch directory. This benchmark exists because v1.3.27 benchmarking showed virtio producing 4 writeups with 0 inline diffs despite having fix patches in `quality/patches/`. The model wrote prose descriptions of the fix instead of pasting the actual diff.

## Quick Checklist Format

Use this as a final sign-off:

- [ ] Test count near heuristic target (spec sections + scenarios + defensive patterns)
- [ ] Scenario test count matches QUALITY.md scenario count
- [ ] Cross-variant tests ~30% of total (every cross-cutting property covered)
- [ ] Boundary tests ≈ defensive pattern count
- [ ] Majority of assertions check values, not just presence
- [ ] All tests assert outcomes, not mechanisms
- [ ] All mutations use schema-valid values
- [ ] All new tests pass (zero failures AND zero errors — check for fixture errors)
- [ ] All existing tests still pass
- [ ] QUALITY.md scenarios reference real code and include `[Req: tier — source]` tags
- [ ] If using inferred requirements: all `[Req: inferred — ...]` items are flagged for user review
- [ ] Code review protocol is self-contained
- [ ] Integration test quality gates were written from a Field Reference Table (not memory)
- [ ] Integration tests have specific pass criteria
- [ ] Spec audit prompt is copy-pasteable and uses `[Req: tier — source]` tag format
- [ ] Structured output schemas include all mandatory fields and valid enum values
- [ ] Patch validation gate uses correct commands for the project's build system
- [ ] Every regression test has a skip/xfail guard referencing the bug ID
- [ ] Integration group commands pass pre-flight discovery (dry-run finds tests)
- [ ] Every generated file has a version stamp with correct version number
- [ ] Enumeration completeness checks show two-list comparisons (not just assertions of coverage)
- [ ] Every TDD-verified bug has a writeup at `quality/writeups/BUG-NNN.md`
- [ ] Triage verification probes include test assertions (not just prose) for confirmations and rejections
- [ ] Enumeration code-side lists include per-item line numbers (not copied from requirements)
- [ ] Dispatch-function contracts cite `quality/mechanical/` artifacts (not hand-written lists)
- [ ] `bash quality/mechanical/verify.sh` passes (artifacts match re-extracted output)
- [ ] Source-inspection regression tests execute (no `run=False` for string-match tests)
- [ ] No executed artifact contradicts any prose artifact at closure (contradiction gate passed)
- [ ] All generated artifact version stamps match SKILL.md metadata version exactly
- [ ] `quality/mechanical/` is either absent (no dispatch contracts) or contains verify.sh + all extraction artifacts
- [ ] If BUGS.md has confirmed bugs: tdd-results.json exists (mandatory); TDD_TRACEABILITY.md exists if any bug has red-phase result
- [ ] Every confirmed bug in triage appears in BUGS.md (triage-to-BUGS.md sync)
- [ ] Every confirmed bug (TDD-verified or confirmed-open) has a writeup at `quality/writeups/BUG-NNN.md`
- [ ] Phase 4 has a triage file at `quality/spec_audits/YYYY-MM-DD-triage.md`
- [ ] (Continuation mode) Seed checks in `SEED_CHECKS.md` were executed mechanically, not inferred from prose
- [ ] Mechanical verification receipt files exist (`mechanical-verify.log` + `mechanical-verify.exit`) when `quality/mechanical/` exists
- [ ] No triage probe reads `quality/mechanical/*.txt` as sole evidence for source code contents
- [ ] Phase 6 mechanical closure used `bash verify.sh` (not Python substitution)
- [ ] Individual auditor reports exist at `quality/spec_audits/*-auditor-N.md` (not just triage)
- [ ] All BUGS.md bug headings use `### BUG-NNN` format
- [ ] quality/BUGS.md exists (zero-bug runs include a summary of candidates evaluated and eliminated)
- [ ] All required artifact files exist on disk before Phase 5 marked complete (not just referenced in PROGRESS.md)
- [ ] (Continuation mode) PROGRESS.md contains `## Convergence` section with net-new count and verdict
- [ ] `quality/BUGS.md` exists (zero-bug runs include a summary of candidates evaluated and eliminated)
- [ ] Sidecar JSON files (`tdd-results.json`, `integration-results.json`) contain all required keys with `schema_version: "1.1"`
- [ ] `quality_gate.sh` was executed and exited 0; output saved to `quality/results/quality-gate.log`
- [ ] REQUIREMENTS.md contains canonical use case identifiers (`UC-01`, `UC-02`, etc.)
- [ ] Every confirmed bug has `quality/patches/BUG-NNN-regression-test.patch`
- [ ] Every writeup has an inline fix diff (` ```diff ` block in section 6)
