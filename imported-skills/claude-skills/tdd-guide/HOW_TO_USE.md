# How to Use the TDD Guide Skill

The TDD Guide skill helps engineering teams implement Test Driven Development with intelligent test generation, coverage analysis, and workflow guidance.

## Basic Usage

### Generate Tests from Requirements

```
@tdd-guide

I need to implement a user registration feature. Generate test cases for:
- Email validation
- Password strength checking
- Duplicate email detection

Language: TypeScript
Framework: Jest
```

### Analyze Test Coverage

```
@tdd-guide

Analyze test coverage for my authentication module.

Coverage report: coverage/lcov.info
Source code: src/auth/

Identify gaps and prioritize improvements.
```

### Get TDD Workflow Guidance

```
@tdd-guide

Guide me through TDD for implementing a shopping cart feature.

Requirements:
- Add items to cart
- Update quantities
- Calculate totals
- Apply discount codes

Framework: Pytest
```

## Example Invocations

### Example 1: Generate Tests from Code

```
@tdd-guide

Generate comprehensive tests for this function:

```typescript
export function calculateTax(amount: number, rate: number): number {
  if (amount < 0) throw new Error('Amount cannot be negative');
  if (rate < 0 || rate > 1) throw new Error('Rate must be between 0 and 1');
  return Math.round(amount * rate * 100) / 100;
}
```

Include:
- Happy path tests
- Error cases
- Boundary values
- Edge cases
```

### Example 2: Improve Coverage

```
@tdd-guide

My coverage is at 65%. Help me get to 80%.

Coverage report:
[paste LCOV or JSON coverage data]

Source files:
- src/services/payment-processor.ts
- src/services/order-validator.ts

Prioritize critical paths.
```

### Example 3: Review Test Quality

```
@tdd-guide

Review the quality of these tests:

```python
def test_login():
    result = login("user", "pass")
    assert result is not None
    assert result.status == "success"
    assert result.token != ""
    assert len(result.permissions) > 0

def test_login_fails():
    result = login("bad", "wrong")
    assert result is None
```

Suggest improvements for:
- Test isolation
- Assertion quality
- Naming conventions
- Test organization
```

### Example 4: Framework Migration

```
@tdd-guide

Convert these Jest tests to Pytest:

```javascript
describe('Calculator', () => {
  it('should add two numbers', () => {
    const result = add(2, 3);
    expect(result).toBe(5);
  });

  it('should handle negative numbers', () => {
    const result = add(-2, 3);
    expect(result).toBe(1);
  });
});
```

Maintain test structure and coverage.
```

### Example 5: Generate Test Fixtures

```
@tdd-guide

Generate realistic test fixtures for:

Entity: User
Fields:
- id (UUID)
- email (valid format)
- age (18-100)
- role (admin, user, guest)

Generate 5 fixtures with edge cases:
- Minimum age boundary
- Maximum age boundary
- Special characters in email
```

## What to Provide

### For Test Generation
- Source code (TypeScript, JavaScript, Python, or Java)
- Requirements (user stories, API specs, or business rules)
- Testing framework preference (Jest, Pytest, JUnit, Vitest)
- Specific scenarios to cover (optional)

### For Coverage Analysis
- Coverage report (LCOV, JSON, or XML format)
- Source code files (optional, for context)
- Coverage threshold target (e.g., 80%)

### For TDD Workflow
- Feature requirements
- Current phase (RED, GREEN, or REFACTOR)
- Test code and implementation (for validation)

### For Quality Review
- Existing test code
- Specific quality concerns (isolation, naming, assertions)

## What You'll Get

### Test Generation Output
- Complete test files with proper structure
- Test stubs with arrange-act-assert pattern
- Framework-specific imports and syntax
- Coverage for happy paths, errors, and edge cases

### Coverage Analysis Output
- Overall coverage summary (line, branch, function)
- Identified gaps with file/line numbers
- Prioritized recommendations (P0, P1, P2)
- Visual coverage indicators

### TDD Workflow Output
- Step-by-step guidance for current phase
- Validation of RED/GREEN/REFACTOR completion
- Refactoring suggestions
- Next steps in TDD cycle

### Quality Review Output
- Test quality score (0-100)
- Detected test smells
- Isolation and naming analysis
- Specific improvement recommendations

## Tips for Best Results

### Test Generation
1. **Be specific**: "Generate tests for password validation" is better than "generate tests"
2. **Provide context**: Include edge cases and error conditions you want covered
3. **Specify framework**: Mention Jest, Pytest, JUnit, etc., for correct syntax

### Coverage Analysis
1. **Use recent reports**: Coverage data should match current codebase
2. **Provide thresholds**: Specify your target coverage percentage
3. **Focus on critical code**: Prioritize coverage for business logic

### TDD Workflow
1. **Start with requirements**: Clear requirements lead to better tests
2. **One cycle at a time**: Complete RED-GREEN-REFACTOR before moving on
3. **Validate each phase**: Run tests and share results for accurate guidance

### Quality Review
1. **Share full context**: Include test setup/teardown and helper functions
2. **Ask specific questions**: "Is my isolation good?" gets better answers than "review this"
3. **Iterative improvement**: Implement suggestions incrementally

## Advanced Usage

### Multi-Language Projects

```
@tdd-guide

Analyze coverage across multiple languages:
- Frontend: TypeScript (Jest) - src/frontend/
- Backend: Python (Pytest) - src/backend/
- API: Java (JUnit) - src/api/

Provide unified coverage report and recommendations.
```

### CI/CD Integration

```
@tdd-guide

Generate coverage report for CI pipeline.

Input: coverage/coverage-final.json
Output format: JSON

Include:
- Pass/fail based on 80% threshold
- Changed files coverage
- Trend comparison with main branch
```

### Parameterized Test Generation

```
@tdd-guide

Generate parameterized tests for:

Function: validateEmail(email: string): boolean

Test cases:
- valid@example.com → true
- invalid.email → false
- @example.com → false
- user@domain.co.uk → true

Framework: Jest (test.each)
```

## Related Commands

- `/code-review` - Review code quality and suggest improvements
- `/test` - Run tests and analyze results
- `/refactor` - Get refactoring suggestions while keeping tests green

## Troubleshooting

**Issue**: Generated tests don't match my framework syntax
- **Solution**: Explicitly specify framework (e.g., "using Pytest" or "with Jest")

**Issue**: Coverage analysis shows 0% coverage
- **Solution**: Verify coverage report format (LCOV, JSON, XML) and try including raw content

**Issue**: TDD workflow validation fails
- **Solution**: Ensure you're providing test results (passed/failed status) along with code

**Issue**: Too many recommendations
- **Solution**: Ask for "top 3 P0 recommendations only" for focused output

## Version Support

- **Node.js**: 16+ (Jest 29+, Vitest 0.34+)
- **Python**: 3.8+ (Pytest 7+)
- **Java**: 11+ (JUnit 5.9+)
- **TypeScript**: 4.5+

## Feedback

If you encounter issues or have suggestions, please mention:
- Language and framework used
- Type of operation (generation, analysis, workflow)
- Expected vs. actual behavior
