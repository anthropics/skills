---
name: wjttc-tester
description: F1-inspired software testing expert. Tests any software with championship-grade standards and writes detailed WJTTC reports. Use when testing code, finding bugs, validating functionality, performing edge case analysis, or creating test reports. Follows F1 philosophy - when brakes must work flawlessly, so must our code.
license: Complete terms in LICENSE.txt
---

# WJTTC Championship Tester

## Philosophy

**"We break things so others never have to know they were broken."**

Apply Formula 1 engineering standards to software testing. When brakes must work flawlessly at 200mph, so must our code work flawlessly in production.

## When to Use This Skill

Activate this skill when:
- Testing new features or code changes
- Finding and documenting bugs
- Validating edge cases and error handling
- Performing regression testing
- Creating WJTTC test reports
- Reviewing code for potential failures
- Stress testing performance
- Validating data integrity
- Testing integrations and APIs
- Documenting test results

## WJTTC Testing Tiers (F1-Inspired)

### Tier 1: BRAKE SYSTEMS 🚨 (Life-Critical)
**When failure = catastrophic consequences**

**Examples:**
- File corruption or data loss
- Security vulnerabilities
- Authentication/authorization bypass
- Payment processing errors
- Data deletion without confirmation
- Backup/restore failures

**Testing Approach:**
- Zero tolerance for failures
- Test ALL edge cases
- Simulate worst-case scenarios
- Validate rollback mechanisms
- Document every failure mode

### Tier 2: ENGINE SYSTEMS ⚡ (Performance-Critical)
**When failure = poor experience or incorrect results**

**Examples:**
- API response accuracy
- Data transformation correctness
- Formula calculations
- File format compliance
- Cross-platform compatibility
- Performance benchmarks

**Testing Approach:**
- Validate core functionality
- Test with real-world data
- Measure performance metrics
- Check error handling
- Verify expected outputs

### Tier 3: AERODYNAMICS 🏁 (Polish & Edge Cases)
**When failure = minor inconvenience**

**Examples:**
- UI/UX edge cases
- Rare error message formatting
- Optional feature quirks
- Documentation accuracy
- Non-critical warnings

**Testing Approach:**
- Test common edge cases
- Validate user experience
- Check for graceful degradation
- Document known limitations

## Test Execution Process

### Step 1: Understand What to Test

**Questions to Answer:**
- What is the feature/code supposed to do?
- What are the happy path scenarios?
- What are the edge cases?
- What could go wrong?
- What data formats are expected?
- What are the performance requirements?

### Step 2: Create Test Plan

**Define:**
- Test objectives
- Test scope (what's in/out)
- Test tier (Brake/Engine/Aero)
- Test scenarios (happy + edge + error)
- Expected results
- Pass/fail criteria

### Step 3: Execute Tests

**For Each Test:**
1. Set up test environment
2. Prepare test data
3. Execute test steps
4. Observe actual results
5. Compare to expected results
6. Document outcome (pass/fail/blocked)
7. Capture errors/screenshots if failed

### Step 4: Document Results

**Create WJTTC Report** (see format below)

## Test Scenario Types

### 1. Happy Path Testing
**Test the ideal, expected flow**

```yaml
Scenario: User creates new .faf file
Given: Valid project directory with package.json
When: User runs `faf init`
Then:
  - .faf file is created
  - File contains valid YAML
  - Project metadata is detected
  - Success message is displayed
```

### 2. Edge Case Testing
**Test boundary conditions and unusual inputs**

**Examples:**
- Empty strings
- Very long strings (>1000 chars)
- Special characters (unicode, emoji, etc.)
- Null/undefined values
- Empty arrays/objects
- Maximum/minimum numeric values
- Zero/negative numbers
- Duplicate data
- Concurrent operations

### 3. Error Handling Testing
**Test that errors are handled gracefully**

**Examples:**
- File doesn't exist
- Permission denied
- Network timeout
- Invalid input format
- Missing required fields
- Malformed JSON/YAML
- Circular references
- Out of memory
- Disk full

### 4. Integration Testing
**Test interactions between components**

**Examples:**
- API calls with different responses
- Database connections
- File system operations
- External service dependencies
- Authentication flows
- Data synchronization

### 5. Performance Testing
**Test speed, memory, and scalability**

**Metrics to Test:**
- Execution time (<50ms target for FAF operations)
- Memory usage
- File size handling (small, medium, large)
- Concurrent operations
- Load handling (100, 1000, 10000 items)

### 6. Regression Testing
**Test that old functionality still works**

**After:**
- Code refactoring
- Dependency updates
- New feature additions
- Bug fixes

## WJTTC Report Format

### Standard Report Template

```yaml
---
# WJTTC Test Report
project: "project-name"
feature: "feature-being-tested"
tester: "wolfejam (via Claude)"
date: "2025-10-20"
tier: "Tier 2 - Engine Systems"
---

## Test Summary

**Objective:** [What was being tested]
**Result:** [PASS / FAIL / BLOCKED]
**Duration:** [Time taken to run tests]
**Environment:** [OS, Node version, dependencies, etc.]

## Test Statistics

- **Total Tests:** 25
- **Passed:** 23
- **Failed:** 2
- **Blocked:** 0
- **Pass Rate:** 92%

## Test Scenarios

### 1. [Scenario Name]

**Tier:** Tier 1 - Brake Systems 🚨
**Status:** ✅ PASS
**Duration:** 15ms

**Test Steps:**
1. [Step 1]
2. [Step 2]
3. [Step 3]

**Expected Result:**
[What should happen]

**Actual Result:**
[What actually happened]

**Evidence:**
```
[Code output, logs, screenshots]
```

---

### 2. [Scenario Name]

**Tier:** Tier 2 - Engine Systems ⚡
**Status:** ❌ FAIL
**Duration:** 250ms

**Test Steps:**
1. [Step 1]
2. [Step 2]

**Expected Result:**
[What should happen]

**Actual Result:**
[What actually happened - THE FAILURE]

**Error Details:**
```
Error: [Actual error message]
Stack trace: [If applicable]
```

**Root Cause:**
[Analysis of why it failed]

**Recommended Fix:**
[How to fix the issue]

---

## Edge Cases Tested

| Case | Input | Expected | Actual | Status |
|------|-------|----------|--------|--------|
| Empty string | `""` | Error message | Error message | ✅ PASS |
| Null value | `null` | Error message | Error message | ✅ PASS |
| Very long string | `"a".repeat(10000)` | Handle gracefully | Crash | ❌ FAIL |
| Unicode emoji | `"🏎️"` | Store correctly | Stored correctly | ✅ PASS |

## Performance Metrics

| Operation | Target | Actual | Status |
|-----------|--------|--------|--------|
| File read | <50ms | 18ms | ✅ PASS |
| File write | <50ms | 23ms | ✅ PASS |
| Parse YAML | <50ms | 12ms | ✅ PASS |
| Score calculation | <50ms | 8ms | ✅ PASS |

## Bugs Found

### Bug #1: [Title]
**Severity:** High (Tier 1)
**Reproducibility:** Always
**Steps to Reproduce:**
1. [Step 1]
2. [Step 2]
3. [Step 3]

**Expected:** [What should happen]
**Actual:** [What happens instead]
**Impact:** [Who is affected, how serious]
**Suggested Fix:** [How to fix it]

---

## Test Coverage

**Tested:**
- ✅ Happy path scenarios
- ✅ Edge cases (empty, null, special chars)
- ✅ Error handling
- ✅ Performance benchmarks
- ✅ Cross-platform compatibility

**Not Tested:**
- ⏸️ Concurrent file access
- ⏸️ Files >100MB
- ⏸️ Network failures (not applicable)

## Recommendations

1. **Fix Critical Issues:**
   - [Issue 1]
   - [Issue 2]

2. **Improve Error Messages:**
   - [Suggestion 1]
   - [Suggestion 2]

3. **Performance Optimization:**
   - [Suggestion 1]

4. **Additional Testing Needed:**
   - [What else to test]

## Championship Certification

**Current Status:** 🥈 Bronze (92% pass rate)

**To Reach Championship 🏆:**
- Fix 2 failing tests
- Add tests for concurrent operations
- Validate with 10,000+ item datasets

---

## Appendix

**Test Data Used:**
```yaml
# Sample test data
test_cases:
  - name: "valid-project"
    input: {...}
  - name: "empty-project"
    input: {...}
```

**Environment Details:**
- OS: macOS 14.5
- Node: v18.17.0
- Dependencies: [list]

**Test Execution Logs:**
```
[Full test output if needed]
```

---

*Tested with Championship Standards 🏎️*
*WJTTC Certified - We break things so you don't have to*
```

## Testing Best Practices

### 1. Start with Tier 1 Tests
Always test life-critical functionality first. If brakes don't work, nothing else matters.

### 2. Test with Real Data
Don't just test with perfect, sanitized data. Use:
- Real user data (anonymized)
- Production-like datasets
- Messy, imperfect inputs

### 3. Automate What You Can
```javascript
// Example: Automated test script
const testCases = [
  { input: '', expected: 'error' },
  { input: 'valid', expected: 'success' },
  { input: null, expected: 'error' },
  { input: '🏎️', expected: 'success' }
];

testCases.forEach(test => {
  const result = functionToTest(test.input);
  console.log(`Input: ${test.input}, Expected: ${test.expected}, Actual: ${result}`);
});
```

### 4. Document Every Failure
Even small failures matter. Document:
- What failed
- How to reproduce
- Why it matters
- How to fix

### 5. Think Like an Attacker
**Ask:**
- What if someone tries to break this?
- What's the worst input I can give?
- What happens if I do things in the wrong order?
- Can I bypass validation?

### 6. Test the Unhappy Paths
Don't just test success scenarios:
```yaml
# Happy path
Input: Valid email
Result: Success

# Unhappy paths
Input: Invalid email → Error message
Input: Empty string → Error message
Input: null → Error message
Input: SQL injection attempt → Sanitized/rejected
Input: XSS attempt → Sanitized/rejected
```

### 7. Measure Everything
- Execution time
- Memory usage
- File sizes
- Error rates
- Pass/fail counts

## Common Test Patterns

### Pattern 1: Arrange-Act-Assert (AAA)

```javascript
// Arrange - Set up test data
const testData = { name: 'Test', value: 123 };

// Act - Execute the code being tested
const result = processData(testData);

// Assert - Verify the result
if (result.success === true && result.value === 123) {
  console.log('✅ PASS');
} else {
  console.log('❌ FAIL');
}
```

### Pattern 2: Test Table

```javascript
const testTable = [
  { input: 0, expected: 'zero' },
  { input: 1, expected: 'one' },
  { input: -1, expected: 'error' },
  { input: null, expected: 'error' }
];

testTable.forEach(({ input, expected }) => {
  const result = numberToWord(input);
  const status = result === expected ? '✅ PASS' : '❌ FAIL';
  console.log(`${status} - Input: ${input}, Expected: ${expected}, Got: ${result}`);
});
```

### Pattern 3: Boundary Value Testing

```javascript
// Test boundaries
const boundaries = [
  { value: -1, desc: 'Below minimum' },
  { value: 0, desc: 'Minimum' },
  { value: 1, desc: 'Just above minimum' },
  { value: 99, desc: 'Just below maximum' },
  { value: 100, desc: 'Maximum' },
  { value: 101, desc: 'Above maximum' }
];
```

## Integration with WJTTC

### Report Storage

**Save reports to:**
```
/Users/wolfejam/FAF-GOLD/PLANET-FAF/WJTTC - WolfeJam Technical & Testing Center/
├── reports/
│   ├── 2025-10-20-faf-cli-tests.yaml
│   ├── 2025-10-20-mcp-server-tests.yaml
│   └── 2025-10-20-n8n-workflow-tests.yaml
└── templates/
    └── WJTC-REPORT-FORMAT.yaml
```

### Report Naming Convention

```
YYYY-MM-DD-{project}-{feature}-tests.yaml
```

**Examples:**
- `2025-10-20-faf-cli-init-command-tests.yaml`
- `2025-10-20-claude-faf-mcp-bi-sync-tests.yaml`
- `2025-10-20-n8n-workflow-http-node-tests.yaml`

### Championship Scoring

**Pass Rate to Championship Tier:**
- 🏆 **95-100%** - Championship (Gold)
- 🥇 **85-94%** - Podium (Silver)
- 🥈 **70-84%** - Points (Bronze)
- 🥉 **55-69%** - Midfield
- 🟢 **40-54%** - Backmarker
- 🟡 **25-39%** - Struggling
- 🔴 **10-24%** - Critical
- 🤍 **0-9%** - DNF (Did Not Finish)

## Quick Test Checklist

**Before releasing any code:**
- [ ] Happy path tested and passing
- [ ] Edge cases tested (empty, null, max, min)
- [ ] Error handling tested
- [ ] Performance meets targets (<50ms for FAF operations)
- [ ] Works on target platforms (macOS, Linux, Windows if applicable)
- [ ] Regression tests pass
- [ ] WJTTC report created and filed
- [ ] Critical bugs fixed (Tier 1)
- [ ] Pass rate ≥85% (Championship target)

## Example Test Execution

### Testing: faf-cli `init` command

```bash
# Test 1: Happy path
cd /tmp/test-project
faf init
# ✅ Expected: .faf file created
# ✅ Actual: .faf file created with valid YAML

# Test 2: Already exists
faf init
# ✅ Expected: Error message about existing file
# ✅ Actual: "Error: .faf file already exists"

# Test 3: No package.json
cd /tmp/empty-dir
faf init
# ✅ Expected: Still creates .faf, detects basic project info
# ✅ Actual: Created .faf with minimal structure

# Test 4: Permission denied
chmod 000 /tmp/readonly-dir
cd /tmp/readonly-dir
faf init
# ✅ Expected: Error message about permissions
# ✅ Actual: "Error: EACCES: permission denied"

# Test 5: Performance
time faf init
# ✅ Expected: <50ms
# ✅ Actual: 18ms (Championship grade!)
```

## Stress Testing

### Test with Extreme Data

```javascript
// Test with large arrays
const largeArray = Array(10000).fill(0).map((_, i) => ({ id: i }));

// Test with deeply nested objects
const deepNest = { level1: { level2: { level3: { level4: { level5: 'data' } } } } };

// Test with special characters
const specialChars = "!@#$%^&*(){}[]|\\:;\"'<>,.?/~`";

// Test with unicode
const unicode = "🏎️⚡️🏁🏆🥇🥈🥉";

// Test with very long strings
const longString = 'a'.repeat(100000);
```

---

## Skill Control

**To disable this skill temporarily:**
```bash
mv ~/.claude/skills/wjttc-tester ~/.claude/skills/wjttc-tester.disabled
```

**To re-enable:**
```bash
mv ~/.claude/skills/wjttc-tester.disabled ~/.claude/skills/wjttc-tester
```

---

*Made with 🧡 by wolfejam.dev*
*Championship Testing Standards 🏎️*
*"We break things so others never have to know they were broken."*
