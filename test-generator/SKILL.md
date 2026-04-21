---
name: test-generator
description: Generate test suites for existing code. Analyzes functions for edge cases, writes tests using the project's existing framework, and runs them to verify they pass. Use when the user asks to add tests or improve test coverage.
license: Apache-2.0
---

# Test Generator

## Step 1: Identify the test framework

Check the project's existing test setup before writing anything. Don't ask the user — look at the project:

```bash
# Check for existing test files to match their patterns
find . -name "*test*" -o -name "*spec*" | grep -v node_modules | head -10

# Check config files
ls jest.config* vitest.config* pytest.ini pyproject.toml setup.cfg Cargo.toml *_test.go 2>/dev/null
```

Match the existing framework, file naming convention, and directory structure. If no tests exist yet, use: **pytest** (Python), **vitest** (JS/TS), **go test** (Go), **cargo test** (Rust), **JUnit 5** (Java).

## Step 2: Analyze the code under test

Read the source file. For each function/method, identify:

1. **Input types and valid ranges** — What does each parameter accept?
2. **Return type and possible values** — What comes back, including error cases?
3. **Side effects** — Does it write to DB, call an API, modify global state?
4. **Dependencies** — What does it import or call that needs mocking?

## Step 3: Generate edge cases

For every input parameter, systematically consider:

| Input type | Edge cases to test |
|---|---|
| String | empty `""`, single char, very long (10k+), unicode, whitespace-only, string with special chars (`<>&"'\`), null/undefined |
| Number | 0, -1, MAX_SAFE_INTEGER, NaN, Infinity, float when int expected |
| Array/List | empty `[]`, single element, very large, contains nulls, contains duplicates |
| Object/Dict | empty `{}`, missing optional keys, extra unexpected keys, nested nulls |
| Boolean | both values, plus whatever the function does when it's missing |
| File/Path | doesn't exist, empty file, no permissions, symlink, path traversal (`../`) |
| Date/Time | epoch, far future, DST boundary, leap year/second, different timezones |

Also test:
- **What happens when dependencies fail?** Mock a database call to throw, an HTTP request to timeout.
- **Concurrent access** if the function touches shared state.
- **Idempotency** — does calling it twice produce the same result?

## Step 4: Write tests

Structure tests as: one `describe`/`class` per function, one test per behavior. Each test should be:

```
[function name] + [condition] + [expected result]
```

Example: `"parseDate returns null for empty string"`, not `"test parseDate 1"`.

Keep tests independent — no test should depend on another test's side effects or execution order.

For functions with side effects, mock at the boundary (the database client, the HTTP library, the filesystem) not at internal functions. This keeps tests resilient to refactoring.

## Step 5: Run and fix

```bash
# Run only the new test file
pytest tests/test_new.py -v          # Python
npx vitest run src/new.test.ts       # JS/TS
go test -v -run TestNew ./...        # Go
```

If tests fail:
1. Read the error output
2. Determine if the test is wrong or the code has a bug
3. Fix the test if the test is wrong; report the bug to the user if the code is wrong
4. Re-run until all tests pass

Never mark a failing test as skipped to make the suite pass.

## Step 6: Check coverage

```bash
pytest --cov=src tests/ --cov-report=term-missing   # Python
npx vitest run --coverage                            # JS/TS
go test -coverprofile=coverage.out ./... && go tool cover -func=coverage.out  # Go
```

Report which lines/branches are still uncovered. Offer to write additional tests for uncovered paths, but don't pad coverage with trivial tests (testing that a constant equals itself).

## Gotchas

- Always check if the project has a test database, test fixtures, or factory functions before writing your own setup. Duplicating existing test infrastructure causes maintenance burden.
- If a function is hard to test, that's often a design signal. Note it, but write the test anyway — don't suggest a refactor unless asked.
- Watch for time-dependent tests. Use `freezegun` (Python), `vi.useFakeTimers()` (JS), or dependency injection for `time.Now()` (Go) instead of `sleep()` or real clocks.
- Don't test private/internal functions directly. Test them through the public API. If they're hard to reach, that may indicate dead code.
- Snapshot tests are tempting but brittle. Prefer explicit assertions unless the output is genuinely complex (e.g., rendered HTML, serialized ASTs).
