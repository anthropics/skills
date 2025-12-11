# Installation & Usage

## Install the Skill in Claude

1. **Package the skill:**
   ```bash
   cd /path/to/python-testing-tools
   zip -r python-testing-tools.zip . -x "*.git*" -x "*.DS_Store"
   ```

2. **Upload to Claude:**
   - Open Claude Desktop or Web
   - Go to Settings → Capabilities → Skills
   - Upload the `python-testing-tools.zip` file
   - The skill will be available in all future conversations

3. **Use the skill:**
   - Start a new chat
   - When you mention tasks like "write tests for this function" or "improve test coverage", Claude will automatically load this skill
   - You can also explicitly invoke it by mentioning testing tools: "use pytest to test...", "use Hypothesis to find edge cases..."

## Install the Testing Tools (macOS/Linux)

### Essential Tools (14)
```bash
# Create and activate virtual environment
uv venv venv
source venv/bin/activate

# Install testing framework
uv pip install pytest pytest-cov pytest-xdist pytest-randomly \
               pytest-mock pytest-asyncio pytest-timeout pytest-benchmark

# Install test data & mocking
uv pip install freezegun factory_boy faker responses

# Install integration testing
uv pip install testcontainers playwright pytest-playwright

# Install advanced testing
uv pip install hypothesis

# Setup Playwright browsers
python -m playwright install --with-deps
```

### Optional Tools (6)
```bash
# Additional testing tools
uv pip install pytest-env pytest-depends syrupy locust vcrpy pytest-alembic
```

### Quick Verification
```bash
pytest --version
python -m pytest --co -q
```

## Skill Structure

```
python-testing-tools/
├── SKILL.md                          # Main skill instructions
├── INSTALL.md                        # This file
├── README.md                         # Design principles & improvements
├── scripts/                          # Helper scripts
│   ├── run-tests.sh                 # Run test suite with coverage
│   ├── coverage-report.sh           # Generate coverage report
│   └── test-performance.sh          # Run performance benchmarks
├── references/                       # Detailed documentation (to be created)
│   └── commands.md                  # Comprehensive command reference
└── assets/                          # Template config files
    ├── pytest.ini                   # pytest configuration
    ├── pyproject.toml               # Testing dependencies and config
    ├── conftest.py                  # Shared fixtures
    └── justfile                     # Task runner recipes
```

## Quick Start

After installing both the skill and testing tools:

1. **Create test directory and first test:**
   ```bash
   mkdir -p tests
   cat > tests/test_example.py <<'EOF'
   def test_addition():
       assert 2 + 2 == 4
   EOF
   ```

2. **Run tests:**
   ```bash
   pytest
   pytest --cov=src --cov-report=html
   ```

3. **Bootstrap a project:**
   ```bash
   cp assets/pytest.ini .
   cp assets/pyproject.toml .
   cp assets/conftest.py tests/
   cp assets/justfile .
   ```

## Using with Claude

Example prompts that will trigger this skill:

- "Write pytest tests for this function"
- "Improve test coverage for the User model"
- "Write property-based tests with Hypothesis to find edge cases"
- "Test this async function with pytest-asyncio"
- "Create integration tests using Testcontainers"
- "Set up E2E tests with Playwright"
- "Mock this API call in my tests"
- "Debug why my tests are flaky"
- "Generate a coverage report"
- "Test this across multiple Python versions with tox"

Claude will provide copy-pasteable test code, explain testing strategies, and suggest improvements.

## Testing Pyramid

Organize your tests by speed and complexity:

```
        E2E (Playwright)              ~5-15% of tests
       /             \
    Integration Testing               ~15-30% of tests
    (Testcontainers, responses)
    /                 \
  Unit Tests (pytest, Hypothesis)     ~70% of tests
```

## Common Workflows

### Unit Testing
```bash
pytest tests/unit/ -v
```

### Integration Testing with Real Services
```bash
pytest tests/integration/ -v
# Requires Docker for Testcontainers
```

### E2E Testing
```bash
pytest tests/e2e/ -v -m e2e
# Requires running app on localhost:3000
```

### Coverage Analysis
```bash
./scripts/coverage-report.sh
```

### Performance Testing
```bash
pytest tests/ -m benchmark --benchmark-only
```

## Updating the Skill

To update the skill after making changes:

1. Make your changes to SKILL.md, scripts, references, or assets
2. Re-package: `zip -r python-testing-tools.zip . -x "*.git*" -x "*.DS_Store"`
3. Upload the new zip file in Claude Settings → Skills
4. Start a new conversation to use the updated version

## Integration with Other Skills

This testing skill works well with:
- **python-quality-tools** - Ruff, Pyright, Bandit for code quality
- Use together for complete Python development workflow

## Resources

- [pytest documentation](https://docs.pytest.org/)
- [Hypothesis documentation](https://hypothesis.readthedocs.io/)
- [Playwright Python documentation](https://playwright.dev/python/)
- [Testcontainers Python](https://testcontainers-python.readthedocs.io/)
- [factory_boy documentation](https://factoryboy.readthedocs.io/)
- Tool documentation: See `references/commands.md` for detailed command reference
- Example configs: See `assets/` directory for ready-to-use templates
