# Python Testing Tools - Claude Skill

A comprehensive Claude skill for writing, improving, and debugging Python tests across the full testing pyramid: unit, integration, and E2E.

## Overview

This skill provides expertise in modern Python testing tools and strategies:

**Test Framework & Plugins (8):**
- pytest, pytest-cov, pytest-xdist, pytest-randomly, pytest-mock, pytest-asyncio, pytest-timeout, pytest-benchmark

**Test Data & Mocking (3):**
- freezegun, factory_boy, Faker, responses

**Integration Testing (2):**
- Testcontainers, Playwright

**Advanced Testing (1):**
- Hypothesis

**Optional Tools (6):**
- pytest-env, pytest-depends, syrupy, locust, vcr.py, pytest-alembic

## What's Included

```
python-testing-tools/
├── SKILL.md                          # Main skill (lean, workflow-focused)
├── INSTALL.md                        # Installation instructions
├── README.md                         # This file
├── scripts/                          # Executable helper scripts
│   ├── run-tests.sh                 # Run tests with coverage
│   ├── coverage-report.sh           # Generate coverage HTML
│   └── test-performance.sh          # Run performance tests
├── references/                       # Detailed documentation
│   └── commands.md                  # Comprehensive command reference (to be created)
└── assets/                          # Template configs
    ├── pytest.ini
    ├── pyproject.toml
    ├── conftest.py
    └── justfile
```

## Design Principles

This skill follows Claude skill best practices:

### Progressive Disclosure

1. **Metadata** (~100 words): Name and description always in context
2. **SKILL.md** (<5k words): Loaded when skill triggers - lean, workflow-focused
3. **Bundled Resources** (unlimited): Loaded as needed by Claude

### Testing Focus

This skill focuses **purely on testing** (not code quality that's in python-quality-tools skill):
- Testing strategies and best practices
- Test frameworks and tools
- Coverage measurement and improvement
- Async, integration, and E2E testing
- Test data generation and mocking

### Bundled Resources Strategy

**Scripts** - Executable workflows for common testing tasks:
- Run tests with coverage reporting
- Generate HTML coverage reports
- Run performance benchmarks

**References** - Detailed command documentation:
- All testing tools with syntax, options, examples
- Testing patterns and workflows
- Troubleshooting common issues

**Assets** - Ready-to-use templates:
- pytest configuration
- Test fixtures and utilities
- Task runner recipes for testing
- Project structure examples

## Key Improvements

### 1. Added Essential Testing Tools
- **pytest-mock** - Better mocking with mocker fixture
- **pytest-asyncio** - Essential for async test support
- **pytest-timeout** - Prevent hanging tests
- **pytest-benchmark** - Performance regression testing
- **syrupy** - Snapshot/golden file testing
- **locust** - Load testing

### 2. Removed/Demoted Non-Testing Tools
- Removed Semgrep (overlaps with quality-tools)
- Removed Ruff, Pyright, Bandit (reference to python-quality-tools)
- Focused purely on testing

### 3. Comprehensive Documentation
- Full SKILL.md with all testing patterns
- Template configs for pytest, fixtures, and justfile
- Helper scripts for common workflows
- Clear testing pyramid documentation

### 4. Testing Pyramid Focus
```
        E2E (Playwright)
       /             \
    Integration Testing
    (Testcontainers, responses)
    /                 \
  Unit Tests (pytest, Hypothesis, etc.)
```

## Installation

See [INSTALL.md](INSTALL.md) for complete installation instructions.

**Quick start:**
```bash
# Create virtual environment
uv venv venv
source venv/bin/activate

# Install testing tools
uv pip install pytest pytest-cov pytest-xdist pytest-randomly \
               pytest-mock pytest-asyncio pytest-timeout pytest-benchmark \
               freezegun factory_boy faker responses \
               testcontainers playwright pytest-playwright hypothesis

# Setup Playwright
python -m playwright install --with-deps
```

## Usage Examples

**In Claude conversations:**

- "Write pytest tests for this function"
- "Create property-based tests with Hypothesis to find edge cases"
- "Test this async code with pytest-asyncio"
- "Mock the API calls in these tests"
- "Set up integration tests with real database using Testcontainers"
- "Write E2E tests for the login flow with Playwright"
- "Improve test coverage to 80%"
- "Debug why tests are flaky"

**Direct CLI usage:**

```bash
# Run all tests with coverage
./scripts/run-tests.sh

# Generate HTML coverage report
./scripts/coverage-report.sh

# Run performance benchmarks
./scripts/test-performance.sh

# Or use justfile
just test
just test-cov
just test-parallel
```

## Skill Development

This skill was improved using the `skill-creator` skill, following Anthropic's skill development best practices:

1. **Understanding** - Analyzed testing tool ecosystem for Claude Code
2. **Planning** - Added missing tools (pytest-asyncio, pytest-mock, pytest-benchmark)
3. **Implementation** - Created SKILL.md, helper scripts, and config templates
4. **Documentation** - Complete installation and usage guides

## Architecture Decisions

### Focus on Testing Pyramid
- Clear distinction between unit, integration, and E2E tests
- Tools for each level of the pyramid
- Performance and isolation best practices

### No Code Quality Tools
- Code quality tools (Ruff, Pyright, Bandit) reference python-quality-tools skill
- Avoid duplication between skills
- Clear separation of concerns

### Async-First Design
- pytest-asyncio is essential tool
- Example configurations for async testing
- Troubleshooting async issues

### Integration Testing Support
- Testcontainers for real service testing
- responses/vcr.py for HTTP mocking
- Examples with real databases

## Test Organization

Recommended project structure:

```
project/
├── src/
│   ├── models.py
│   ├── services.py
│   └── api.py
├── tests/
│   ├── conftest.py           # Shared fixtures
│   ├── unit/
│   │   ├── test_models.py
│   │   └── test_services.py
│   ├── integration/
│   │   ├── test_database.py
│   │   └── test_api.py
│   └── e2e/
│       └── test_flows.py
└── pyproject.toml
```

## Next Steps

To complete the skill:
1. Add detailed `references/commands.md` with all testing tools
2. Create `scripts/coverage-report.sh` and `scripts/test-performance.sh`
3. Add more fixture examples in `assets/conftest.py`
4. Create integration test examples

## Contributing

To improve this skill:
1. Use it with real testing tasks
2. Notice gaps or missing tools
3. Update SKILL.md, add scripts, or improve configs
4. Re-package and upload updated version

## License

This skill is provided for use with Claude. The included tools are open-source software with their own licenses.
