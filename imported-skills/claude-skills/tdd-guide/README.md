# TDD Guide - Test Driven Development Skill

**Version**: 1.0.0
**Last Updated**: November 5, 2025
**Author**: Claude Skills Factory

A comprehensive Test Driven Development skill for Claude Code that provides intelligent test generation, coverage analysis, framework integration, and TDD workflow guidance across multiple languages and testing frameworks.

## Table of Contents

- [Overview](#overview)
- [Features](#features)
- [Installation](#installation)
- [Quick Start](#quick-start)
- [Python Modules](#python-modules)
- [Usage Examples](#usage-examples)
- [Configuration](#configuration)
- [Supported Frameworks](#supported-frameworks)
- [Output Formats](#output-formats)
- [Best Practices](#best-practices)
- [Troubleshooting](#troubleshooting)
- [Contributing](#contributing)
- [License](#license)

## Overview

The TDD Guide skill transforms how engineering teams implement Test Driven Development by providing:

- **Intelligent Test Generation**: Convert requirements into executable test cases
- **Coverage Analysis**: Parse LCOV, JSON, XML reports and identify gaps
- **Multi-Framework Support**: Jest, Pytest, JUnit, Vitest, and more
- **TDD Workflow Guidance**: Step-by-step red-green-refactor guidance
- **Quality Metrics**: Comprehensive test and code quality analysis
- **Context-Aware Output**: Optimized for Desktop, CLI, or API usage

## Features

### Test Generation (3 capabilities)
1. **Generate Test Cases from Requirements** - User stories → Test cases
2. **Create Test Stubs** - Proper scaffolding with framework patterns
3. **Generate Test Fixtures** - Realistic test data and boundary values

### TDD Workflow (3 capabilities)
1. **Red-Green-Refactor Guidance** - Phase-by-phase validation
2. **Suggest Missing Scenarios** - Identify untested edge cases
3. **Review Test Quality** - Isolation, assertions, naming analysis

### Coverage & Metrics (6 categories)
1. **Test Coverage** - Line/branch/function with gap analysis
2. **Code Complexity** - Cyclomatic/cognitive complexity
3. **Test Quality** - Assertions, isolation, naming scoring
4. **Test Data** - Boundary values, edge cases
5. **Test Execution** - Timing, slow tests, flakiness
6. **Missing Tests** - Uncovered paths and error handlers

### Framework Integration (4 capabilities)
1. **Multi-Framework Adapters** - Jest, Pytest, JUnit, Vitest, Mocha
2. **Generate Boilerplate** - Proper imports and test structure
3. **Configure Runners** - Setup and coverage configuration
4. **Framework Detection** - Automatic framework identification

## Installation

### Claude Code (Desktop)

1. **Download the skill folder**:
   ```bash
   # Option A: Clone from repository
   git clone https://github.com/your-org/tdd-guide-skill.git

   # Option B: Download ZIP and extract
   ```

2. **Install to Claude skills directory**:
   ```bash
   # Project-level (recommended for team projects)
   cp -r tdd-guide /path/to/your/project/.claude/skills/

   # User-level (available for all projects)
   cp -r tdd-guide ~/.claude/skills/
   ```

3. **Verify installation**:
   ```bash
   ls ~/.claude/skills/tdd-guide/
   # Should show: SKILL.md, *.py files, samples
   ```

### Claude Apps (Browser)

1. Use the `skill-creator` skill to import the ZIP file
2. Or manually upload files through the skills interface

### Claude API

```python
# Upload skill via API
import anthropic

client = anthropic.Anthropic(api_key="your-api-key")

# Create skill with files
skill = client.skills.create(
    name="tdd-guide",
    files=["tdd-guide/SKILL.md", "tdd-guide/*.py"]
)
```

## Quick Start

### 1. Generate Tests from Requirements

```
@tdd-guide

Generate tests for password validation function:
- Min 8 characters
- At least 1 uppercase, 1 lowercase, 1 number, 1 special char

Language: TypeScript
Framework: Jest
```

### 2. Analyze Coverage

```
@tdd-guide

Analyze coverage from: coverage/lcov.info
Target: 80% coverage
Prioritize recommendations
```

### 3. TDD Workflow

```
@tdd-guide

Guide me through TDD for implementing user authentication.

Requirements: Email/password login, session management
Framework: Pytest
```

## Python Modules

The skill includes **8 Python modules** organized by functionality:

### Core Modules (7 files)

1. **test_generator.py** (450 lines)
   - Generate test cases from requirements
   - Create test stubs with proper structure
   - Suggest missing scenarios based on code analysis
   - Support for multiple test types (unit, integration, e2e)

2. **coverage_analyzer.py** (380 lines)
   - Parse LCOV, JSON, XML coverage reports
   - Calculate line/branch/function coverage
   - Identify coverage gaps with prioritization
   - Generate actionable recommendations

3. **metrics_calculator.py** (420 lines)
   - Cyclomatic and cognitive complexity analysis
   - Test quality scoring (isolation, assertions, naming)
   - Test smell detection
   - Execution metrics analysis

4. **framework_adapter.py** (480 lines)
   - Multi-framework adapters (Jest, Pytest, JUnit, Vitest, Mocha)
   - Generate framework-specific imports and structure
   - Assertion syntax translation
   - Setup/teardown hook generation

5. **tdd_workflow.py** (380 lines)
   - Red-Green-Refactor phase guidance
   - Phase validation and progression
   - Refactoring suggestions
   - Workflow state management

6. **fixture_generator.py** (340 lines)
   - Boundary value generation
   - Edge case scenario creation
   - Mock data generation from schemas
   - Fixture file export (JSON, YAML, Python)

7. **format_detector.py** (280 lines)
   - Automatic language detection
   - Testing framework identification
   - Coverage format detection
   - Project structure analysis

### Utility Modules (1 file)

8. **output_formatter.py** (260 lines)
   - Context-aware formatting (Desktop, CLI, API)
   - Progressive disclosure
   - Token-efficient reporting
   - Summary and detailed views

### Total Lines of Code
- **Python**: ~3,400 lines
- **Documentation**: ~1,200 lines
- **Samples**: ~200 lines
- **Total**: ~4,400 lines

## Usage Examples

### Example 1: Generate Tests from User Story

**Input**:
```
@tdd-guide

User Story: As a user, I want to add items to my shopping cart

Acceptance Criteria:
- Add single item with quantity
- Update quantity if item already exists
- Validate quantity is positive
- Return updated cart total

Language: Python
Framework: Pytest
```

**Output**:
```python
import pytest
from shopping_cart import ShoppingCart

class TestShoppingCart:
    """Test suite for shopping cart functionality."""

    def test_add_single_item_successfully(self):
        """Should add single item with quantity."""
        cart = ShoppingCart()
        cart.add_item('apple', quantity=3, price=1.50)

        assert len(cart.items) == 1
        assert cart.items['apple']['quantity'] == 3
        assert cart.get_total() == 4.50

    def test_update_quantity_for_existing_item(self):
        """Should update quantity if item already exists."""
        cart = ShoppingCart()
        cart.add_item('apple', quantity=3, price=1.50)
        cart.add_item('apple', quantity=2, price=1.50)

        assert cart.items['apple']['quantity'] == 5
        assert cart.get_total() == 7.50

    def test_reject_negative_quantity(self):
        """Should validate quantity is positive."""
        cart = ShoppingCart()

        with pytest.raises(ValueError, match="Quantity must be positive"):
            cart.add_item('apple', quantity=-1, price=1.50)
```

### Example 2: Coverage Analysis with Recommendations

**Input**:
```
@tdd-guide

Analyze coverage:

[Coverage report data]
SF:src/auth/login.ts
DA:1,5
DA:2,5
DA:3,3
DA:4,0
DA:5,0
...

Target: 80% coverage
```

**Output**:
```markdown
## Coverage Summary

- Line Coverage: 65.0%
- Branch Coverage: 58.3%
- Function Coverage: 75.0%

⚠️ **65.0%** coverage (yellow) - Below 80% threshold

## Recommendations

### 🔴 Critical (P0)

1. **Error handling paths not covered**
   - Action: Add tests for authentication failure scenarios
   - File: `src/auth/login.ts`
   - Lines: 45-52, 67-70

2. **Branch coverage gap in validation**
   - Action: Test all conditional branches in input validation
   - File: `src/auth/login.ts`
   - Lines: 23-28

### 🟡 Important (P1)

1. **Edge cases missing**
   - Action: Add boundary tests for password length (7, 8, 9 chars)
   - Impact: Medium
```

### Example 3: TDD Red-Green-Refactor Guidance

**Input**:
```
@tdd-guide

Guide TDD for email validation.

Requirement: Email must contain @ and valid domain

Phase: RED (write failing test)
```

**Output**:
```markdown
## TDD Phase: RED

### Goal
Write a failing test that describes desired email validation behavior

### Steps
1. ✅ Read requirement: Email must contain @ and valid domain
2. ✅ Think about expected behavior
3. ⏳ Write test that verifies this behavior
4. ⏳ Run test and ensure it fails
5. ⏳ Verify failure reason is correct (not syntax error)

### Test Template (Jest)

```typescript
describe('EmailValidator', () => {
  it('should accept valid email format', () => {
    // Arrange
    const validator = new EmailValidator();

    // Act
    const result = validator.validate('user@example.com');

    // Assert
    expect(result).toBe(true);
  });

  it('should reject email without @ symbol', () => {
    const validator = new EmailValidator();
    const result = validator.validate('userexample.com');
    expect(result).toBe(false);
  });
});
```

### Next Steps
1. Run the test (it should fail)
2. Verify failure: "EmailValidator is not defined" or similar
3. Share test result to proceed to GREEN phase
```

### Example 4: Test Quality Review

**Input**:
```
@tdd-guide

Review test quality:

def test_user_login():
    result = login("admin", "password123")
    assert result
    assert result["status"] == "success"
    assert result["token"]
    assert result["user"]["id"] > 0
    assert result["user"]["role"] == "admin"
```

**Output**:
```markdown
## Test Quality Analysis

**Overall Score**: 62/100

### Issues Detected

1. **Assertion Roulette** (High Severity)
   - 5 assertions in single test
   - **Fix**: Split into multiple focused tests

2. **Poor Test Isolation** (Medium Severity)
   - Test depends on database state ("admin" user existing)
   - **Fix**: Use fixtures or mocks for user data

3. **Weak Assertions** (Medium Severity)
   - `assert result["token"]` just checks truthy (could be any string)
   - **Fix**: `assert len(result["token"]) > 20` or use regex

4. **Missing Naming Context** (Low Severity)
   - Test name doesn't describe what's being tested
   - **Fix**: `test_successful_login_returns_valid_token_and_user_data`

### Recommended Refactoring

```python
@pytest.fixture
def admin_user():
    return {"username": "admin", "password": "password123"}

def test_successful_login_returns_success_status(admin_user):
    """Test that valid credentials return success status."""
    result = login(admin_user["username"], admin_user["password"])
    assert result["status"] == "success"

def test_successful_login_returns_valid_jwt_token(admin_user):
    """Test that successful login returns a JWT token."""
    result = login(admin_user["username"], admin_user["password"])
    assert len(result["token"]) > 20
    assert result["token"].count('.') == 2  # JWT format

def test_successful_login_returns_user_data(admin_user):
    """Test that successful login includes user information."""
    result = login(admin_user["username"], admin_user["password"])
    assert result["user"]["id"] > 0
    assert result["user"]["role"] == "admin"
```

### Quality Improvements
- Isolation Score: 55 → 90 (with fixtures)
- Naming Quality: 40 → 85 (descriptive names)
- Test Focus: 30 → 95 (one assertion per test)
```

## Configuration

### Environment Variables

```bash
# Set preferred testing framework
export TDD_DEFAULT_FRAMEWORK="jest"

# Set coverage threshold
export TDD_COVERAGE_THRESHOLD=80

# Set output verbosity
export TDD_VERBOSE=true

# Set output format
export TDD_OUTPUT_FORMAT="markdown"  # or "json", "terminal"
```

### Skill Configuration (Optional)

Create `.tdd-guide.json` in project root:

```json
{
  "framework": "jest",
  "language": "typescript",
  "coverage_threshold": 80,
  "test_directory": "tests/",
  "quality_rules": {
    "max_assertions_per_test": 3,
    "require_descriptive_names": true,
    "enforce_isolation": true
  },
  "output": {
    "format": "markdown",
    "verbose": false,
    "max_recommendations": 10
  }
}
```

## Supported Frameworks

### JavaScript/TypeScript
- **Jest** 29+ (recommended for React, Node.js)
- **Vitest** 0.34+ (recommended for Vite projects)
- **Mocha** 10+ with Chai
- **Jasmine** 4+

### Python
- **Pytest** 7+ (recommended)
- **unittest** (Python standard library)
- **nose2** 0.12+

### Java
- **JUnit 5** 5.9+ (recommended)
- **TestNG** 7+
- **Mockito** 5+ (mocking support)

### Coverage Tools
- **Istanbul/nyc** (JavaScript)
- **c8** (JavaScript, V8 native)
- **coverage.py** (Python)
- **pytest-cov** (Python)
- **JaCoCo** (Java)
- **Cobertura** (multi-language)

## Output Formats

### Markdown (Claude Desktop)
- Rich formatting with headers, tables, code blocks
- Visual indicators (✅, ⚠️, ❌)
- Progressive disclosure (summary first, details on demand)
- Syntax highlighting for code examples

### Terminal (Claude Code CLI)
- Concise, text-based output
- Clear section separators
- Minimal formatting for readability
- Quick scanning for key information

### JSON (API/CI Integration)
- Structured data for automated processing
- Machine-readable metrics
- Suitable for CI/CD pipelines
- Easy integration with other tools

## Best Practices

### Test Generation
1. **Start with requirements** - Clear specs lead to better tests
2. **Cover the happy path first** - Then add error and edge cases
3. **One behavior per test** - Focused tests are easier to maintain
4. **Use descriptive names** - Tests are documentation

### Coverage Analysis
1. **Aim for 80%+ coverage** - Balance between safety and effort
2. **Prioritize critical paths** - Not all code needs 100% coverage
3. **Branch coverage matters** - Line coverage alone is insufficient
4. **Track trends** - Coverage should improve over time

### TDD Workflow
1. **Small iterations** - Write one test, make it pass, refactor
2. **Run tests frequently** - Fast feedback loop is essential
3. **Commit often** - Each green phase is a safe checkpoint
4. **Refactor with confidence** - Tests are your safety net

### Test Quality
1. **Isolate tests** - No shared state between tests
2. **Fast execution** - Unit tests should be <100ms each
3. **Deterministic** - Same input always produces same output
4. **Clear failures** - Good error messages save debugging time

## Troubleshooting

### Common Issues

**Issue**: Generated tests have wrong syntax for my framework
```
Solution: Explicitly specify framework
Example: "Generate tests using Pytest" or "Framework: Jest"
```

**Issue**: Coverage report not recognized
```
Solution: Verify format (LCOV, JSON, XML)
Try: Paste raw coverage data instead of file path
Check: File exists and is readable
```

**Issue**: Too many recommendations, overwhelmed
```
Solution: Ask for prioritized output
Example: "Show only P0 (critical) recommendations"
Limit: "Top 5 recommendations only"
```

**Issue**: Test quality score seems wrong
```
Check: Ensure complete test context (setup/teardown included)
Verify: Test file contains actual test code, not just stubs
Context: Quality depends on isolation, assertions, naming
```

**Issue**: Framework detection incorrect
```
Solution: Specify framework explicitly
Example: "Using JUnit 5" or "Framework: Vitest"
Check: Ensure imports are present in code
```

## File Structure

```
tdd-guide/
├── SKILL.md                          # Skill definition (YAML + documentation)
├── README.md                         # This file
├── HOW_TO_USE.md                     # Usage examples
│
├── test_generator.py                 # Test generation core
├── coverage_analyzer.py              # Coverage parsing and analysis
├── metrics_calculator.py             # Quality metrics calculation
├── framework_adapter.py              # Multi-framework support
├── tdd_workflow.py                   # Red-green-refactor guidance
├── fixture_generator.py              # Test data and fixtures
├── format_detector.py                # Automatic format detection
├── output_formatter.py               # Context-aware output
│
├── sample_input_typescript.json      # TypeScript example
├── sample_input_python.json          # Python example
├── sample_coverage_report.lcov       # LCOV coverage example
└── expected_output.json              # Expected output structure
```

## Contributing

We welcome contributions! To contribute:

1. Fork the repository
2. Create a feature branch (`git checkout -b feature/improvement`)
3. Make your changes
4. Add tests for new functionality
5. Run validation: `python -m pytest tests/`
6. Commit changes (`git commit -m "Add: feature description"`)
7. Push to branch (`git push origin feature/improvement`)
8. Open a Pull Request

### Development Setup

```bash
# Clone repository
git clone https://github.com/your-org/tdd-guide-skill.git
cd tdd-guide-skill

# Install development dependencies
pip install -r requirements-dev.txt

# Run tests
pytest tests/ -v

# Run linter
pylint *.py

# Run type checker
mypy *.py
```

## Version History

### v1.0.0 (November 5, 2025)
- Initial release
- Support for TypeScript, JavaScript, Python, Java
- Jest, Pytest, JUnit, Vitest framework adapters
- LCOV, JSON, XML coverage parsing
- TDD workflow guidance (red-green-refactor)
- Test quality metrics and analysis
- Context-aware output formatting
- Comprehensive documentation

## License

MIT License - See LICENSE file for details

## Support

- **Documentation**: See HOW_TO_USE.md for detailed examples
- **Issues**: Report bugs via GitHub issues
- **Questions**: Ask in Claude Code community forum
- **Updates**: Check repository for latest version

## Acknowledgments

Built with Claude Skills Factory toolkit, following Test Driven Development best practices and informed by:
- Kent Beck's "Test Driven Development: By Example"
- Martin Fowler's refactoring catalog
- xUnit Test Patterns by Gerard Meszaros
- Growing Object-Oriented Software, Guided by Tests

---

**Ready to improve your testing workflow?** Install the TDD Guide skill and start generating high-quality tests today!
