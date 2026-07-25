---
name: "tdd-guide"
description: "Test-driven development skill for writing unit tests, generating test fixtures and mocks, analyzing coverage gaps, and guiding red-green-refactor workflows across Jest, Pytest, JUnit, Vitest, and Mocha. Use when the user asks to write tests, improve test coverage, practice TDD, generate mocks or stubs, or mentions testing frameworks like Jest, pytest, or JUnit."
---

# TDD Guide

Test-driven development skill for generating tests, analyzing coverage, and guiding red-green-refactor workflows across Jest, Pytest, JUnit, and Vitest.

---

## Workflows

### Generate Tests from Code

1. Provide source code (TypeScript, JavaScript, Python, Java)
2. Specify target framework (Jest, Pytest, JUnit, Vitest)
3. Run `test_generator.py` with requirements
4. Review generated test stubs
5. **Validation:** Tests compile and cover happy path, error cases, edge cases

### Analyze Coverage Gaps

1. Generate coverage report from test runner (`npm test -- --coverage`)
2. Run `coverage_analyzer.py` on LCOV/JSON/XML report
3. Review prioritized gaps (P0/P1/P2)
4. Generate missing tests for uncovered paths
5. **Validation:** Coverage meets target threshold (typically 80%+)

### TDD New Feature

1. Write failing test first (RED)
2. Run `tdd_workflow.py --phase red` to validate
3. Implement minimal code to pass (GREEN)
4. Run `tdd_workflow.py --phase green` to validate
5. Refactor while keeping tests green (REFACTOR)
6. **Validation:** All tests pass after each cycle

---

## Examples

### Test Generation — Input → Output (Pytest)

**Input source function (`math_utils.py`):**
```python
def divide(a: float, b: float) -> float:
    if b == 0:
        raise ValueError("Cannot divide by zero")
    return a / b
```

**Command:**
```bash
python scripts/test_generator.py --input math_utils.py --framework pytest
```

**Generated test output (`test_math_utils.py`):**
```python
import pytest
from math_utils import divide

class TestDivide:
    def test_divide_positive_numbers(self):
        assert divide(10, 2) == 5.0

    def test_divide_negative_numerator(self):
        assert divide(-10, 2) == -5.0

    def test_divide_float_result(self):
        assert divide(1, 3) == pytest.approx(0.333, rel=1e-3)

    def test_divide_by_zero_raises_value_error(self):
        with pytest.raises(ValueError, match="Cannot divide by zero"):
            divide(10, 0)

    def test_divide_zero_numerator(self):
        assert divide(0, 5) == 0.0
```

---

### Coverage Analysis — Sample P0/P1/P2 Output

**Command:**
```bash
python scripts/coverage_analyzer.py --report lcov.info --threshold 80
```

**Sample output:**
```
Coverage Report — Overall: 63% (threshold: 80%)

P0 — Critical gaps (uncovered error paths):
  auth/login.py:42-58   handle_expired_token()       0% covered
  payments/process.py:91-110  handle_payment_failure()   0% covered

P1 — High-value gaps (core logic branches):
  users/service.py:77   update_profile() — else branch  0% covered
  orders/cart.py:134    apply_discount() — zero-qty guard  0% covered

P2 — Low-risk gaps (utility / helper functions):
  utils/formatting.py:12  format_currency()            0% covered

Recommended: Generate tests for P0 items first to reach 80% threshold.
```

---

## Key Tools

| Tool | Purpose | Usage |
|------|---------|-------|
| `test_generator.py` | Generate test cases from code/requirements | `python scripts/test_generator.py --input source.py --framework pytest` |
| `coverage_analyzer.py` | Parse and analyze coverage reports | `python scripts/coverage_analyzer.py --report lcov.info --threshold 80` |
| `tdd_workflow.py` | Guide red-green-refactor cycles | `python scripts/tdd_workflow.py --phase red --test test_auth.py` |
| `fixture_generator.py` | Generate test data and mocks | `python scripts/fixture_generator.py --entity User --count 5` |

Additional scripts: `framework_adapter.py` (convert between frameworks), `metrics_calculator.py` (quality metrics), `format_detector.py` (detect language/framework), `output_formatter.py` (CLI/desktop/CI output).

---

## Input Requirements

**For Test Generation:**
- Source code (file path or pasted content)
- Target framework (Jest, Pytest, JUnit, Vitest)
- Coverage scope (unit, integration, edge cases)

**For Coverage Analysis:**
- Coverage report file (LCOV, JSON, or XML format)
- Optional: Source code for context
- Optional: Target threshold percentage

**For TDD Workflow:**
- Feature requirements or user story
- Current phase (RED, GREEN, REFACTOR)
- Test code and implementation status

---

## Spec-First Workflow

TDD is most effective when driven by a written spec. The flow:

1. **Write or receive a spec** — stored in `specs/<feature>.md`
2. **Extract acceptance criteria** — each criterion becomes one or more test cases
3. **Write failing tests (RED)** — one test per acceptance criterion
4. **Implement minimal code (GREEN)** — satisfy each test in order
5. **Refactor** — clean up while all tests stay green

### Spec Directory Convention

```
project/
├── specs/
│   ├── user-auth.md          # Feature spec with acceptance criteria
│   ├── payment-processing.md
│   └── notification-system.md
├── tests/
│   ├── test_user_auth.py     # Tests derived from specs/user-auth.md
│   ├── test_payments.py
│   └── test_notifications.py
└── src/
```

### Extracting Tests from Specs

Each acceptance criterion in a spec maps to at least one test:

| Spec Criterion | Test Case |
|---------------|-----------|
| "User can log in with valid credentials" | `test_login_valid_credentials_returns_token` |
| "Invalid password returns 401" | `test_login_invalid_password_returns_401` |
| "Account locks after 5 failed attempts" | `test_login_locks_after_five_failures` |

**Tip:** Number your acceptance criteria in the spec. Reference the number in the test docstring for traceability (`# AC-3: Account locks after 5 failed attempts`).

> **Cross-reference:** See `engineering/spec-driven-workflow` for the full spec methodology, including spec templates and review checklists.

---

## Red-Green-Refactor Examples Per Language

### TypeScript / Jest

```typescript
// test/cart.test.ts
describe("Cart", () => {
  describe("addItem", () => {
    it("should add a new item to an empty cart", () => {
      const cart = new Cart();
      cart.addItem({ id: "sku-1", name: "Widget", price: 9.99, qty: 1 });

      expect(cart.items).toHaveLength(1);
      expect(cart.items[0].id).toBe("sku-1");
    });

    it("should increment quantity when adding an existing item", () => {
      const cart = new Cart();
      cart.addItem({ id: "sku-1", name: "Widget", price: 9.99, qty: 1 });
      cart.addItem({ id: "sku-1", name: "Widget", price: 9.99, qty: 2 });

      expect(cart.items).toHaveLength(1);
      expect(cart.items[0].qty).toBe(3);
    });

    it("should throw when quantity is zero or negative", () => {
      const cart = new Cart();
      expect(() =>
        cart.addItem({ id: "sku-1", name: "Widget", price: 9.99, qty: 0 })
      ).toThrow("Quantity must be positive");
    });
  });
});
```

### Python / Pytest (Advanced Patterns)

```python
# tests/conftest.py — shared fixtures
import pytest
from app.db import create_engine, Session

@pytest.fixture(scope="session")
def db_engine():
    engine = create_engine("sqlite:///:memory:")
    yield engine
    engine.dispose()

@pytest.fixture
def db_session(db_engine):
    session = Session(bind=db_engine)
    yield session
    session.rollback()
    session.close()

# tests/test_pricing.py — parametrize for multiple cases
import pytest
from app.pricing import calculate_discount

@pytest.mark.parametrize("subtotal, expected_discount", [
    (50.0, 0.0),       # Below threshold — no discount
    (100.0, 5.0),      # 5% tier
    (250.0, 25.0),     # 10% tier
    (500.0, 75.0),     # 15% tier
])
def test_calculate_discount(subtotal, expected_discount):
    assert calculate_discount(subtotal) == pytest.approx(expected_discount)
```

### Go — Table-Driven Tests

```go
// cart_test.go
package cart

import "testing"

func TestApplyDiscount(t *testing.T) {
    tests := []struct {
        name     string
        subtotal float64
        want     float64
    }{
        {"no discount below threshold", 50.0, 0.0},
        {"5 percent tier", 100.0, 5.0},
        {"10 percent tier", 250.0, 25.0},
        {"15 percent tier", 500.0, 75.0},
        {"zero subtotal", 0.0, 0.0},
    }

    for _, tt := range tests {
        t.Run(tt.name, func(t *testing.T) {
            got := ApplyDiscount(tt.subtotal)
            if got != tt.want {
                t.Errorf("ApplyDiscount(%v) = %v, want %v", tt.subtotal, got, tt.want)
            }
        })
    }
}
```

---

## Bounded Autonomy Rules

When generating tests autonomously, follow these rules to decide when to stop and ask the user:

### Stop and Ask When

- **Ambiguous requirements** — the spec or user story has conflicting or unclear acceptance criteria
- **Missing edge cases** — you cannot determine boundary values without domain knowledge (e.g., max allowed transaction amount)
- **Test count exceeds 50** — large test suites need human review before committing; present a summary and ask which areas to prioritize
- **External dependencies unclear** — the feature relies on third-party APIs or services with undocumented behavior
- **Security-sensitive logic** — authentication, authorization, encryption, or payment flows require human sign-off on test scenarios

### Continue Autonomously When

- **Clear spec with numbered acceptance criteria** — each criterion maps directly to tests
- **Straightforward CRUD operations** — create, read, update, delete with well-defined models
- **Well-defined API contracts** — OpenAPI spec or typed interfaces available
- **Pure functions** — deterministic input/output with no side effects
- **Existing test patterns** — the codebase already has similar tests to follow

---

## Property-Based Testing

Property-based testing generates random inputs to verify invariants instead of relying on hand-picked examples. Use it when the input space is large and the expected behavior can be described as a property.

### Python — Hypothesis

```python
from hypothesis import given, strategies as st
from app.serializers import serialize, deserialize

@given(st.text())
def test_roundtrip_serialization(data):
    """Serialization followed by deserialization returns the original."""
    assert deserialize(serialize(data)) == data

@given(st.integers(), st.integers())
def test_addition_is_commutative(a, b):
    assert a + b == b + a
```

### TypeScript — fast-check

```typescript
import fc from "fast-check";
import { encode, decode } from "./codec";

test("encode/decode roundtrip", () => {
  fc.assert(
    fc.property(fc.string(), (input) => {
      expect(decode(encode(input))).toBe(input);
    })
  );
});
```

### When to Use Property-Based Over Example-Based

| Use Property-Based | Example |
|-------------------|---------|
| Data transformations | Serialize/deserialize roundtrips |
| Mathematical properties | Commutativity, associativity, idempotency |
| Encoding/decoding | Base64, URL encoding, compression |
| Sorting and filtering | Output is sorted, length preserved |
| Parser correctness | Valid input always parses without error |

---

## Mutation Testing

Mutation testing modifies your production code (creates "mutants") and checks whether your tests catch the changes. If a mutant survives (tests still pass), your tests have a gap that coverage alone cannot reveal.

### Tools

| Language | Tool | Command |
|----------|------|---------|
| TypeScript/JavaScript | **Stryker** | `npx stryker run` |
| Python | **mutmut** | `mutmut run --paths-to-mutate=src/` |
| Java | **PIT** | `mvn org.pitest:pitest-maven:mutationCoverage` |

### Why Mutation Testing Matters

- **100% line coverage != good tests** — coverage tells you code was executed, not that it was verified
- **Catches weak assertions** — tests that run code but assert nothing meaningful
- **Finds missing boundary tests** — mutants that change `<` to `<=` expose off-by-one gaps
- **Quantifiable quality metric** — mutation score (% mutants killed) is a stronger signal than coverage %

**Recommendation:** Run mutation testing on critical paths (auth, payments, data processing) even if overall coverage is high. Target 85%+ mutation score on P0 modules.

---

## Cross-References

| Skill | Relationship |
|-------|-------------|
| `engineering/spec-driven-workflow` | Spec → acceptance criteria → test extraction pipeline |
| `engineering-team/focused-fix` | Phase 5 (Verify) uses TDD to confirm the fix with a regression test |
| `engineering-team/senior-qa` | Broader QA strategy; TDD is one layer in the test pyramid |
| `engineering-team/code-reviewer` | Review generated tests for assertion quality and coverage completeness |
| `engineering-team/senior-fullstack` | Project scaffolders include testing infrastructure compatible with TDD workflows |

---

## Limitations

| Scope | Details |
|-------|---------|
| Unit test focus | Integration and E2E tests require different patterns |
| Static analysis | Cannot execute tests or measure runtime behavior |
| Language support | Best for TypeScript, JavaScript, Python, Java |
| Report formats | LCOV, JSON, XML only; other formats need conversion |
| Generated tests | Provide scaffolding; require human review for complex logic |

**When to use other tools:**
- E2E testing: Playwright, Cypress, Selenium
- Performance testing: k6, JMeter, Locust
- Security testing: OWASP ZAP, Burp Suite
