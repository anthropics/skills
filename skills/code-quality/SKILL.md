---
name: code-quality
description: Code quality toolkit for Python linting, formatting, testing, and accessibility checks. Use when (1) linting Python code with ruff, (2) formatting with black, (3) running tests with pytest, (4) checking accessibility, or (5) performing comprehensive code audits.
license: MIT
---

# Code Quality Skill

Comprehensive toolkit for maintaining code quality through linting, formatting, testing, and accessibility audits.

## Helper Scripts Available

- `scripts/lint.py` - Run linters (ruff, mypy, pylint)
- `scripts/format.py` - Format code (black, isort, ruff format)
- `scripts/test.py` - Run tests with coverage
- `scripts/audit.py` - Comprehensive code audit
- `scripts/a11y.py` - Accessibility checks for web content

**Always run scripts with `--help` first** to see usage.

## Quick Start

### Lint Code
```bash
# Lint current directory
python scripts/lint.py .

# Lint specific file
python scripts/lint.py myfile.py

# Auto-fix issues
python scripts/lint.py . --fix

# Show detailed output
python scripts/lint.py . --verbose
```

### Format Code
```bash
# Format with black
python scripts/format.py .

# Check formatting without changes
python scripts/format.py . --check

# Format and sort imports
python scripts/format.py . --sort-imports

# Format specific file
python scripts/format.py myfile.py
```

### Run Tests
```bash
# Run all tests
python scripts/test.py

# Run specific test file
python scripts/test.py tests/test_api.py

# Run with coverage
python scripts/test.py --coverage

# Run specific markers
python scripts/test.py --marker unit
```

### Accessibility Check
```bash
# Check HTML file
python scripts/a11y.py index.html

# Check URL
python scripts/a11y.py https://example.com

# Generate report
python scripts/a11y.py index.html --report a11y_report.md
```

## Linting (ruff)

### Default Rules
- Pyflakes (F) - Errors and potential bugs
- pycodestyle (E, W) - Style violations
- isort (I) - Import sorting
- pep8-naming (N) - Naming conventions
- Bugbear (B) - Common bugs
- Security (S) - Security issues

### Configuration
```bash
# Use specific ruleset
python scripts/lint.py . --select E,F,B

# Ignore specific rules
python scripts/lint.py . --ignore E501,W503

# Set line length
python scripts/lint.py . --line-length 100
```

### Common Issues
```bash
# E501 - Line too long
# F401 - Unused import
# F841 - Unused variable
# E402 - Module import not at top
# B006 - Mutable default argument
```

## Formatting (black)

### Options
```bash
# Preview changes
python scripts/format.py . --diff

# Set line length
python scripts/format.py . --line-length 88

# Target Python version
python scripts/format.py . --target-version py311

# Skip magic trailing comma
python scripts/format.py . --skip-magic-trailing-comma
```

### Import Sorting (isort)
```bash
# Sort imports only
python scripts/format.py . --imports-only

# Check import order
python scripts/format.py . --check-imports
```

## Testing (pytest)

### Test Markers
```python
# In tests:
@pytest.mark.unit          # Unit tests
@pytest.mark.integration   # Integration tests
@pytest.mark.e2e           # End-to-end tests
@pytest.mark.api           # API tests
@pytest.mark.slow          # Slow tests
```

### Running by Marker
```bash
python scripts/test.py --marker unit
python scripts/test.py --marker "not slow"
python scripts/test.py --marker "unit or integration"
```

### Coverage
```bash
# Generate coverage report
python scripts/test.py --coverage

# Generate HTML report
python scripts/test.py --coverage --html

# Set coverage threshold
python scripts/test.py --coverage --min-coverage 80
```

### Coverage Output
```
Name                    Stmts   Miss  Cover
-------------------------------------------
app/__init__.py            10      0   100%
app/api.py                 45      5    89%
app/models.py              30      2    93%
-------------------------------------------
TOTAL                      85      7    92%
```

## Accessibility (a11y)

### WCAG Checks
- Contrast ratios (4.5:1 for text, 3:1 for large text)
- Alt text on images
- Form labels
- Heading hierarchy
- Keyboard navigation
- ARIA attributes

### Check Levels
```bash
# WCAG 2.1 Level A (minimum)
python scripts/a11y.py index.html --level A

# WCAG 2.1 Level AA (recommended)
python scripts/a11y.py index.html --level AA

# WCAG 2.1 Level AAA (enhanced)
python scripts/a11y.py index.html --level AAA
```

### Report Format
```markdown
# Accessibility Report

## Summary
- **File**: index.html
- **Level**: WCAG 2.1 AA
- **Status**: FAIL (3 errors, 5 warnings)

## Errors (Must Fix)

### Missing alt text
- `<img src="hero.jpg">` at line 45
  - Add descriptive alt text

### Insufficient contrast
- Text color #777 on #fff background
  - Ratio: 4.48:1 (needs 4.5:1)
  - Element: `.nav-link` at line 23

## Warnings (Should Fix)

### Missing form labels
- `<input type="email">` at line 78
  - Add `<label>` or `aria-label`

## Passed Checks (15)
✓ Heading hierarchy
✓ Keyboard focus visible
✓ Lang attribute present
...
```

## Comprehensive Audit

### Full Audit
```bash
# Run all quality checks
python scripts/audit.py .

# Generate report
python scripts/audit.py . --report audit_report.md

# Set thresholds
python scripts/audit.py . --min-coverage 80 --max-issues 10
```

### Audit Report
```markdown
# Code Quality Audit

## Summary
- **Directory**: /home/coolhand/projects/myapp
- **Date**: 2024-01-15 10:30:00
- **Status**: PASS (with warnings)

## Metrics

| Check | Status | Details |
|-------|--------|---------|
| Lint (ruff) | PASS | 0 errors, 5 warnings |
| Format (black) | PASS | All files formatted |
| Tests | PASS | 45/45 tests pass |
| Coverage | WARN | 78% (target: 80%) |
| Security | PASS | No vulnerabilities |

## Recommendations
1. Increase test coverage for `api.py` (currently 65%)
2. Fix 5 lint warnings in `models.py`
3. Add type hints to public functions
```

## Configuration Files

### pyproject.toml
```toml
[tool.ruff]
line-length = 88
select = ["E", "F", "B", "I"]
ignore = ["E501"]

[tool.black]
line-length = 88
target-version = ["py311"]

[tool.pytest.ini_options]
markers = [
    "unit: Unit tests",
    "integration: Integration tests",
]
addopts = "--cov=. --cov-report=term-missing"
```

### .ruff.toml (alternative)
```toml
line-length = 88
select = ["E", "F", "B", "I", "N", "S"]
ignore = ["E501", "S101"]
```

## Pre-Commit Integration

```yaml
# .pre-commit-config.yaml
repos:
  - repo: https://github.com/astral-sh/ruff-pre-commit
    rev: v0.1.0
    hooks:
      - id: ruff
        args: [--fix]
      - id: ruff-format

  - repo: https://github.com/pre-commit/pre-commit-hooks
    hooks:
      - id: trailing-whitespace
      - id: end-of-file-fixer
```

## CI Integration

### GitHub Actions
```yaml
name: Code Quality
on: [push, pull_request]

jobs:
  quality:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - uses: actions/setup-python@v4
      - run: pip install ruff black pytest pytest-cov
      - run: ruff check .
      - run: black --check .
      - run: pytest --cov --cov-fail-under=80
```

## Best Practices

1. **Run lint before commit** - Catch issues early
2. **Auto-format on save** - Consistent style
3. **Maintain coverage** - Don't let it drop
4. **Fix warnings** - They often become errors
5. **Audit periodically** - Weekly or before releases

## Integration

Works with:
- **server-deploy**: Run quality checks before deployment
- **dream-cascade**: Lint generated code
- **datavis**: Check JavaScript/HTML accessibility

## Troubleshooting

**"Too many issues"**: Start with `--select E,F` for critical only

**"Format changes tests"**: Use `--extend-exclude tests`

**"Coverage too low"**: Focus on uncovered branches with `--cov-report=html`

**"Import errors in tests"**: Ensure `conftest.py` has proper fixtures
