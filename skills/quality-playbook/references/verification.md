# Verification Checklist (Phase 3)

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

If working from non-formal requirements, verify that each scenario and test includes a requirement tag using the canonical format: `[Req: formal — README §3]`, `[Req: inferred — from validate_input() behavior]`, `[Req: user-confirmed — "must handle empty input"]`. Inferred requirements should be flagged for user review in Phase 4.

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
