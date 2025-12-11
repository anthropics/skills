---
name: python-quality-tools
description: >
  This skill should be used when working on Python projects requiring code quality improvements,
  type safety, security scanning, and dependency management. Includes 12+ essential tools
  optimized for Claude Code workflows: Ruff, Pyright, Bandit, pip-audit, uv for fast package
  management, and pre-commit for automation. For testing frameworks, see python-testing-tools.
---

# Python Quality Tools

Leverage modern Python quality tools for fast feedback, safe automation, and production-ready code. Focus on type safety, security, and clean dependencies. For testing frameworks and coverage, see the python-testing-tools skill.

## When to Use This Skill

Apply this skill when tasks involve:
- Linting and formatting Python code consistently
- Type checking for correctness and bug prevention
- Security scanning of code and dependencies
- Managing Python dependencies and virtual environments
- Setting up quality gates with pre-commit hooks
- Finding dead code or unused dependencies
- Preparing code for pull requests with comprehensive quality checks

## Tool Overview

**Essential Linting & Formatting (1):**
- **Ruff** - All-in-one: lint, format, import sort, upgrades (replaces Black/isort/Flake8/pyupgrade)

**Type Checking (1):**
- **Pyright** - Fast static type checker (language server based)

**Security (2):**
- **Bandit** - Python code security scanner (SAST)
- **pip-audit** - Dependency vulnerability scanner (CVE database)

**Code Quality (2):**
- **Vulture** - Dead code finder
- **deptry** - Dependency hygiene checker

**Dependency Management (2):**
- **uv** - Ultra-fast package installer (Rust-based, replaces pip)
- **pipdeptree** - Dependency tree visualization

**Automation (1):**
- **pre-commit** - Git hook framework

**Optional Tools (4):**
- **safety** - Alternative CVE scanner
- **Semgrep** - Custom pattern/policy rules (requires login for many features)
- **interrogate** - Docstring coverage enforcement
- **codespell** - Spell checker for code/docs

## Installation

### Essential Tools (10)
```bash
# Install uv first (package manager)
brew install uv

# Create and activate virtual environment
uv venv venv
source venv/bin/activate

# Install essential tools
uv pip install ruff pyright bandit pip-audit \
               vulture deptry pipdeptree pre-commit
```

### Optional Tools (4)
```bash
# Additional security and quality tools
uv pip install safety semgrep interrogate codespell
```

## Essential Workflows

### Pre-PR Quality Check (Complete Pipeline)

Before creating a pull request, run this complete quality check in sequence:

```bash
# Phase 1: Linting and import organization (auto-fixes safe issues)
ruff check --fix .

# Phase 2: Code formatting (consistent style)
ruff format .

# Phase 3: Type checking (correctness verification)
pyright .

# Phase 4: Security scanning (identify vulnerabilities)
bandit -q -r .
pip-audit

# Phase 5: Dependency hygiene (find unused/missing dependencies)
deptry .
pipdeptree --warn conflict
```

Or run all steps with one command:
```bash
ruff check --fix . && ruff format . && pyright . && bandit -q -r . && pip-audit && deptry .
```

**Expected workflow timing:**
- **Linting & formatting:** 1-3 seconds (fast auto-fixes)
- **Type checking:** 5-15 seconds (depends on codebase size)
- **Security scan:** 2-5 seconds (quick surface-level scan)
- **Dependency check:** 1-2 seconds (local analysis)
- **Total:** 10-30 seconds for typical projects

**When to run:**
- **During development:** Run `ruff check --fix && ruff format` frequently for feedback
- **Before committing:** Run full pipeline to catch issues before pushing
- **In CI/CD:** Fail build if any step fails (use flags like `--exit-code 1`)
- **On git hooks:** Integrate with pre-commit (see Project Setup & Automation section)

### Quick Code Quality Check

**Lint and format (safe auto-fix):**
```bash
# Check and fix issues
ruff check --fix .

# Format code
ruff format .

# Combined
ruff check --fix . && ruff format .
```

**Type check:**
```bash
# Check entire project
pyright .

# Check specific file
pyright src/app.py

# With statistics
pyright --stats .
```

### Security Scanning

**Scan code for security issues:**
```bash
# Quick security scan
bandit -r src/

# Quiet mode, recursive
bandit -q -r .

# JSON output for processing
bandit -r . -f json -o bandit-report.json
```

**Scan dependencies for vulnerabilities:**
```bash
# Scan from requirements file
pip-audit -r requirements.txt

# Scan current environment
pip-audit

# Ignore specific vulnerabilities
pip-audit --ignore-vuln VULN-ID-123

# JSON output
pip-audit --format json
```

### Dependency Management

**Visualize dependency tree:**
```bash
# Show full tree
pipdeptree

# Show only top-level
pipdeptree --depth 1

# Warn about conflicts
pipdeptree --warn conflict

# JSON output
pipdeptree --json
```

**Check dependency hygiene:**
```bash
# Find unused/missing/transitive dependencies
deptry .

# Ignore specific dependencies
deptry . --ignore DEP_001,DEP_002

# Check pyproject.toml
deptry src/ --pyproject pyproject.toml
```

### Dead Code Detection

**Find unused code:**
```bash
# Find dead code
vulture .

# Minimum confidence threshold
vulture . --min-confidence 80

# Exclude test files
vulture src/ --exclude "**/test_*.py"

# Output to file
vulture . > dead-code-report.txt
```

### Project Setup & Automation

**Bootstrap new Python project:**
```bash
# Use helper script
./scripts/setup-python-project.sh /path/to/project

# Or manually copy templates
cp assets/pyproject.toml myproject/
cp assets/.pre-commit-config.yaml myproject/
cp assets/justfile myproject/
```

**Configure Ruff in pyproject.toml:**
```toml
[tool.ruff]
line-length = 100
target-version = "py311"

[tool.ruff.lint]
select = [
    "E",   # pycodestyle errors
    "F",   # pyflakes
    "I",   # isort
    "UP",  # pyupgrade
    "B",   # flake8-bugbear
    "C4",  # flake8-comprehensions
    "S",   # bandit
]
ignore = []

[tool.ruff.format]
quote-style = "double"
indent-style = "space"
docstring-code-format = true
```

**Set up pre-commit hooks:**

Edit `.pre-commit-config.yaml`:
```yaml
repos:
  - repo: https://github.com/astral-sh/ruff-pre-commit
    rev: v0.6.9
    hooks:
      - id: ruff
        args: [--fix]
      - id: ruff-format

  - repo: https://github.com/RobertCraigie/pyright-python
    rev: v1.1.407
    hooks:
      - id: pyright

  - repo: https://github.com/PyCQA/bandit
    rev: 1.7.9
    hooks:
      - id: bandit
        args: ["-q", "-r", "."]
```

Then run:
```bash
pre-commit install
pre-commit run --all-files
```

## Bundled Resources

### Scripts (`scripts/`)

**`setup-python-project.sh`** - Bootstrap Python project with all configs
```bash
./scripts/setup-python-project.sh [project-directory]
```

**`analyze-python-code.sh`** - Run all quality checks
```bash
./scripts/analyze-python-code.sh [directory]
```

**`fix-python-code.sh`** - Auto-fix safe issues
```bash
./scripts/fix-python-code.sh [directory]
```

### Example Configs (`assets/`)

Copy these templates to projects as starting points:
- `pyproject.toml` - Ruff, deptry, and bandit configuration
- `.pre-commit-config.yaml` - Pre-commit hooks with all essential tools
- `justfile` - Task runner recipes for Python projects
- `requirements-dev.txt` - Development dependencies

### Detailed Reference (`references/`)

**`commands.md`** - Comprehensive command reference with all options, examples, and workflows. Load when deeper understanding of specific tools is needed.

To search the reference without reading the entire file:
```bash
rg -n "pytest" references/commands.md
```

## Best Practices

**Safety First:**
- Run `ruff check --fix` before committing (safe auto-fixes only)
- Always run security scans: `bandit -r . && pip-audit`
- Keep dependencies updated and scan for CVEs regularly
- Use pre-commit hooks to catch issues early

**Type Safety:**
- Start with basic Pyright settings, tighten gradually
- Add type hints to new code, gradually to existing code
- Use `pyright --stats` to track progress
- Configure in `pyproject.toml` with `[tool.pyright]`

**Dependency Hygiene:**
- Use `uv` for fast, reproducible installs
- Run `deptry .` to find unused dependencies
- Use `pipdeptree --warn conflict` to check for conflicts
- Pin dependencies in production with lock files

**Workflow Efficiency:**
- Use `just` for common tasks (see `assets/justfile`)
- Set up pre-commit hooks for automatic checks
- Use `ruff` instead of multiple tools (Black, isort, Flake8, pyupgrade)
- Leverage `uv` for 10-100x faster installs

## Verification & Testing

All tools in this skill have been tested and verified to work correctly. See [PYTHON_QUALITY_TOOLS_TEST_RESULTS.md](../../PYTHON_QUALITY_TOOLS_TEST_RESULTS.md) for comprehensive test results.

### Quick Verification

**Check that all tools are installed:**
```bash
ruff --version && pyright --version && bandit --version && \
pip-audit --version && deptry --version
```

**Run verification on a Python project:**
```bash
# Complete pre-PR quality check (see Essential Workflows section)
ruff check --fix . && ruff format . && pyright . && bandit -q -r . && pip-audit && deptry .
```

### Tool Versions Tested

| Tool | Version | Status | Notes |
|------|---------|--------|-------|
| Ruff | 0.14.3 | ✅ Working | Linting, formatting, import sorting |
| Pyright | 1.1.407 | ✅ Working | Latest version, strict type checking |
| Bandit | 1.8.6 | ✅ Working | Found 4 real security issues in test |
| pip-audit | Latest | ✅ Working | Identifies dependency vulnerabilities |
| deptry | Latest | ✅ Working | Checks dependency hygiene |
| Mypy | 1.18.2 | ✅ Working | Additional type checker option |

### What the Tests Found

✅ **Ruff** - Identified real issues:
- E501: 2 line-length violations in real code
- I001: 1 import sorting issue
- Fast execution (~0.006s per file)

✅ **Bandit** - Identified real security issues:
- B110: 4 try-except-pass anti-patterns (CWE-703)
- Proper severity classification and CWE references

✅ **pip-audit** - Dependency vulnerability scanning:
- Successfully scans current environment and requirements files
- Outputs CVE-based vulnerability reports
- Supports ignoring specific vulnerabilities

✅ **deptry** - Dependency hygiene:
- Detects unused dependencies
- Identifies missing dependencies
- Recognizes transitive dependency issues

## Troubleshooting

**Pyright can't find dependencies:**
```bash
# Ensure virtual environment is activated
source venv/bin/activate

# Verify Pyright can see installed packages
pyright --verbose

# Check Python path
pyright --pythonpath $(which python)
```

**Ruff too strict:**
```bash
# Ignore specific rules
ruff check --ignore E501,F401

# Or configure in pyproject.toml
# [tool.ruff.lint]
# ignore = ["E501", "F401"]
```

**Bandit false positives:**
```bash
# Exclude specific tests
bandit -r . --exclude tests/

# Skip specific issue
# In code: # nosec B101

# Or in pyproject.toml
# [tool.bandit]
# skips = ["B101", "B601"]
```

**deptry false positives:**
```toml
# Configure in pyproject.toml
[tool.deptry]
ignore_notebooks = true
extend_exclude = ["tests", "docs"]

[tool.deptry.per_rule_ignores]
DEP001 = ["mypy"]  # Allow unused dev tools
```

**uv installation issues:**
```bash
# Reinstall uv
brew reinstall uv

# Verify installation
uv --version

# Create fresh venv
rm -rf venv
uv venv venv
source venv/bin/activate
```
