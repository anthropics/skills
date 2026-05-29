# Writing Functional Tests

This is the most important deliverable. The Markdown files are documentation. The functional test file is the automated safety net. Name it using the project's conventions: `test_functional.py` (Python/pytest), `FunctionalSpec.scala` (Scala/ScalaTest), `FunctionalTest.java` (Java/JUnit), `functional.test.ts` (TypeScript/Jest), `functional_test.go` (Go), etc.

## Structure: Three Test Groups

Organize tests into three logical groups using whatever structure the test framework provides — classes (Python/Java), describe blocks (TypeScript/Jest), traits (Scala), or subtests (Go):

```
Spec Requirements
    — One test per testable spec section
    — Each test's documentation cites the spec requirement

Fitness Scenarios
    — One test per QUALITY.md scenario (1:1 mapping)
    — Named to match: test_scenario_N_memorable_name (or equivalent convention)

Boundaries and Edge Cases
    — One test per defensive pattern from Step 5
    — Targets null guards, try/catch, normalization, fallbacks
```

## Test Count Heuristic

**Target = (testable spec sections) + (QUALITY.md scenarios) + (defensive patterns from Step 5)**

Example: 12 spec sections + 10 scenarios + 15 defensive patterns = 37 tests as a target.

For a medium-sized project (5–15 source files), this typically yields 35–50 functional tests. Significantly fewer suggests missed requirements or shallow exploration. Don't pad to hit a number — every test should exercise real project code and verify a meaningful property.

## Import Pattern: Match the Existing Tests

Before writing any test code, read 2–3 existing test files and identify how they import project modules. This is critical — projects handle imports differently and getting it wrong means every test fails with resolution errors.

Identify the import convention used in the project. Whatever pattern the existing tests use, copy it exactly. Do not guess or invent a different pattern.

Common patterns by language:

- **Python:** `sys.path.insert(0, "src/")` then bare imports; package imports (`from myproject.module import func`); relative imports with conftest.py path manipulation
- **Go:** Same-package tests (`package mypackage`) give access to unexported identifiers; black-box tests (`package mypackage_test`) test only exported API; internal packages may require specific import paths
- **Java:** `import com.example.project.Module;` matching the package structure; test source root must mirror main source root
- **TypeScript:** `import { func } from '../src/module'` with relative paths; path aliases from `tsconfig.json` (e.g., `@/module`)
- **Rust:** `use crate::module::function;` for unit tests in the same crate; `use myproject::module::function;` for integration tests in `tests/`
- **Scala:** `import com.example.project._` or `import com.example.project.{ClassA, ClassB}`; SBT layout mirrors `src/main/scala/` in `src/test/scala/`

## Create Test Setup BEFORE Writing Tests

Every test framework has a mechanism for shared setup. If your tests use shared fixtures or test data, you MUST create the setup file before writing tests. Test frameworks do not auto-discover fixtures from other directories.

Identify your framework's setup mechanism (fixtures, `@BeforeEach`, `beforeAll`, helper functions, builder patterns, etc.) and follow the conventions already used in the project's existing tests.

**Rule: Every fixture or test helper referenced must be defined.** If a test depends on shared setup that doesn't exist, the test will error during setup (not fail during assertion) — producing broken tests that look like they pass.

**Preferred approach across all languages:** Write tests that create their own data inline. This eliminates cross-file dependencies. Create test data directly in each test function using the framework's temporary directory support and literal data structures.

**After writing all tests, run the test suite and check for setup errors.** Setup errors (fixture not found, import failures) count as broken tests regardless of how the framework categorizes them.

## No Placeholder Tests

Every test must import and call actual project code. If a test body is `pass`, or its only assertion is `assert isinstance(errors, list)`, or it checks a trivial property like `assert hasattr(cls, 'validate')`, delete it and write a real test or drop it entirely. A test that doesn't exercise project code is worse than no test — it inflates the count and creates false confidence.

If you genuinely cannot write a meaningful test for a defensive pattern (e.g., it requires a running server or external service), note it as untestable in a comment rather than writing a placeholder.

## Read Before You Write: The Function Call Map

Before writing a single test, build a function call map. For every function you plan to test:

1. **Read the function/method signature** — not just the name, but every parameter, its type, and default value.
2. **Read the documentation** — docstrings, Javadoc, TSDoc, ScalaDoc. They often specify return types, exceptions, and edge case behavior.
3. **Read one existing test that calls it** — existing tests show you the exact calling convention, fixture shape, and assertion pattern.
4. **Read real data files** — if the function processes configs, schemas, or data files, read an actual file from the project. Your test fixtures must match this shape exactly.

**Common failure pattern:** The agent explores the architecture, understands conceptually what a function does, then writes a test call with guessed parameters. The test fails because the real function takes `(config, items_data, limit)` not `(items, seed, strategy)`. Reading the actual signature takes 5 seconds and prevents this entirely.

**Library version awareness:** Check the project's dependency manifest (`requirements.txt`, `build.sbt`, `package.json`, `pom.xml`, `build.gradle`, `Cargo.toml`) to verify what's available. Use the test framework's skip mechanism for optional dependencies (e.g., `pytest.importorskip()`, `Assumptions.assumeTrue()`, `t.Skip()`, `#[ignore]`, etc.).

## Writing Spec-Derived Tests

Walk each spec document section by section. For each section, ask: "What testable requirement does this state?" Then write a test.

Each test should:
1. **Set up** — Load a fixture, create test data, configure the system
2. **Execute** — Call the function, run the pipeline, make the request
3. **Assert specific properties** the spec requires

Each test should include a traceability annotation (via docstring, display name, or comment) citing the spec section it verifies, e.g., `[Req: formal — Design Doc §N] X should produce Y`.



## What Makes a Good Functional Test

- **Traceable** — Test name, display name, or documentation comment says which spec requirement it verifies
- **Specific** — Checks a specific property, not just "something happened"
- **Robust** — Uses real data (fixtures from the actual system), not synthetic data
- **Cross-variant** — If the project handles multiple input types, test all of them
- **Tests at the right layer** — Test the *behavior* you care about. If the requirement is "invalid data doesn't produce wrong output," test the pipeline output — don't just test that the schema validator rejects the input.

## Cross-Variant Testing Strategy

If the project handles multiple input types, cross-variant coverage is where silent bugs hide. Aim for roughly 30% of tests exercising all variants — the exact percentage matters less than ensuring every cross-cutting property is tested across all variants.

Use your framework's parametrization mechanism (e.g., `@pytest.mark.parametrize`, `@ParameterizedTest`, `test.each`, table-driven tests, iterating over cases) to run the same assertion logic across all variants.



If parametrization doesn't fit, loop explicitly within a single test.

**Which tests should be cross-variant?** Any test verifying a property that *should* hold regardless of input type: entity identity, structural properties, required links, temporal fields, domain-specific semantics.

**After writing all tests, do a cross-variant audit.** Count cross-variant tests divided by total. If below 30%, convert more.

## Anti-Patterns to Avoid

These patterns look like tests but don't catch real bugs:

- **Existence-only checks** — Finding one correct result doesn't mean all are correct. Also check count or verify comprehensively.
- **Presence-only assertions** — Asserting a value exists only proves presence, not correctness. Assert the actual value.
- **Single-variant testing** — Testing one input type and hoping others work. Use parametrization.
- **Positive-only testing** — You must test that invalid input does NOT produce bad output.
- **Incomplete negative assertions** — When testing rejection, assert ALL consequences are absent, not just one.
- **Catching exceptions instead of checking output** — Testing that code crashes in a specific way isn't testing that it handles input correctly. Test the output.

### The Exception-Catching Anti-Pattern in Detail

```python
# WRONG: tests the validation mechanism
def test_bad_value_rejected(fixture):
    fixture.field = "invalid"  # Schema rejects this!
    with pytest.raises(ValidationError):
        process(fixture)
    # Tells you nothing about output

# RIGHT: tests the requirement
def test_bad_value_not_in_output(fixture):
    fixture.field = None  # Schema accepts None for Optional
    output = process(fixture)
    assert field_property not in output  # Bad data absent
    assert expected_type in output  # Rest still works
```

The pattern is the same in every language: don't test that the validation mechanism rejects bad input — test that the system produces correct output when given edge-case input the schema accepts. The WRONG approach tests the implementation (the validator); the RIGHT approach tests the requirement (the output).



Always check your Step 5b schema map before choosing mutation values.

## Testing at the Right Layer

Ask: "What does the *spec* say should happen?" The spec says "invalid data should not appear in output" — not "validation layer should reject it." Test the spec, not the implementation.

**Exception:** When a spec explicitly mandates a specific mechanism (e.g., "must fail-fast at the schema layer"), testing that mechanism is appropriate. But this is rare.

## Fitness-to-Purpose Scenario Tests

For each scenario in QUALITY.md, write a test. This is a 1:1 mapping. Each test should include a traceability annotation citing the scenario, e.g., `[Req: formal — QUALITY.md Scenario 1]`, and be named to match the scenario's memorable name.



## Boundary and Negative Tests

One test per defensive pattern from Step 5. Each test should include a traceability annotation citing the defensive pattern, e.g., `[Req: inferred — from function_name() guard] guards against X`.

For each boundary test:
1. Mutate input to trigger the defensive code path (using a value the schema accepts)
2. Process the mutated input
3. Assert graceful handling — the result is valid despite the edge-case input



Use your Step 5b schema map when choosing mutation values. Every mutation must use a value the schema accepts.

Systematic approach:
- **Missing fields** — Optional field absent? Set to null.
- **Wrong types** — Field gets different type? Use schema-valid alternative.
- **Empty values** — Empty list? Empty string? Empty dict?
- **Boundary values** — Zero, negative, maximum, first, last.
- **Cross-module boundaries** — Module A produces unusual but valid output — does B handle it?

If you found 10+ defensive patterns but wrote only 4 boundary tests, go back and write more. Target a 1:1 ratio.
