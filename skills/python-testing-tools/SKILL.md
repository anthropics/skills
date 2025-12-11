---
name: python-testing-tools
description: >
  This skill should be used when writing, improving, or debugging Python tests across the full testing
  pyramid: unit, integration, and E2E. Includes 17+ testing tools optimized for Claude Code workflows:
  pytest, Hypothesis, pytest-xdist, pytest-asyncio, Testcontainers, Playwright, factory_boy, freezegun,
  and more. Focus on fast feedback, isolation, and reliable test suites.
---

# Python Testing Tools

Leverage modern Python testing tools for comprehensive test coverage across the full testing pyramid. Focus on speed, reliability, isolation, and confidence in deployments.

## When to Use This Skill

Apply this skill when tasks involve:
- Writing unit tests with pytest
- Property-based testing to find edge cases
- Testing async/await code
- Mocking and stubbing dependencies
- Integration testing with real services (databases, APIs)
- End-to-end browser testing
- Generating test data efficiently
- Performance regression testing
- Ensuring tests don't have hidden state dependencies
- Measuring and improving test coverage

## Testing Pyramid

```
        E2E (Playwright)
       /             \
    Integration Testing
    (Testcontainers, responses)
    /                 \
  Unit Tests (pytest, Hypothesis, etc.)
```

## Essential Testing Tools (14)

**Test Framework & Plugins (8):**
- **pytest** - Modern test runner with fixtures, parametrization, rich assertions
- **pytest-cov** - Coverage measurement integrated with pytest
- **pytest-xdist** - Parallel test execution (10-100x faster in CI)
- **pytest-randomly** - Randomize test order to catch state leaks
- **pytest-mock** - Mocking fixture (cleaner than unittest.mock)
- **pytest-asyncio** - Async/await test support
- **pytest-timeout** - Timeout protection for hanging tests
- **pytest-benchmark** - Performance regression testing

**Test Data & Mocking (3):**
- **freezegun** - Mock datetime/time deterministically
- **factory_boy + Faker** - Reusable test data builders (better than fixtures)
- **responses** - Mock HTTP calls deterministically

**Integration Testing (2):**
- **Testcontainers** - Real infrastructure (databases, queues) in tests
- **Playwright** - E2E browser testing with reliable waits

**Advanced Testing (1):**
- **Hypothesis** - Property-based testing (find edge cases automatically)

## Optional Tools (6)

- **pytest-env** - Set environment variables per test
- **pytest-depends** - Test dependencies (skip if dependency failed)
- **syrupy** - Snapshot testing (golden file testing)
- **locust** - Load testing tool
- **vcr.py** - Record/replay HTTP interactions
- **pytest-alembic** - Database migration testing

## Installation

### Essential Tools (14)
```bash
# Create and activate virtual environment
uv venv venv
source venv/bin/activate

# Install testing tools
uv pip install pytest pytest-cov pytest-xdist pytest-randomly \
               pytest-mock pytest-asyncio pytest-timeout pytest-benchmark \
               freezegun factory_boy faker responses \
               testcontainers playwright pytest-playwright hypothesis

# Setup Playwright browsers
python -m playwright install --with-deps
```

### Optional Tools (6)
```bash
uv pip install pytest-env pytest-depends syrupy locust vcrpy pytest-alembic
```

## Essential Workflows

### Test Development Workflow (Complete Pipeline)

When developing tests, follow this structured approach across the testing pyramid:

**Phase 1: Unit Tests (Fast feedback loop - 60-80% of tests)**
```bash
# Watch mode for development - re-runs on file changes
pytest --watch

# Run specific test file during development
pytest tests/unit/test_models.py -v

# Stop on first failure for quick feedback
pytest -x
```

**Phase 2: Add Integration Tests (15-30% of tests)**
```bash
# Mark and run only integration tests
pytest -m integration --v

# Run with mocked services for isolation
pytest tests/integration/ -v

# Use fixtures for database setup/teardown
pytest tests/integration/test_database.py --fixtures
```

**Phase 3: Add E2E Tests (5-10% of tests)**
```bash
# Run end-to-end tests (slow, but high confidence)
pytest -m e2e

# Run with UI if using Playwright
playwright test --ui
```

**Phase 4: Measure Coverage (Before merging)**
```bash
# Generate HTML coverage report
pytest --cov=src --cov-report=html

# Show missing coverage in terminal
pytest --cov=src --cov-report=term-missing

# Fail if coverage drops below 80%
pytest --cov=src --cov-fail-under=80
```

**Phase 5: Run Full Test Suite (Pre-commit/CI)**
```bash
# Run all tests in parallel with coverage
pytest -n auto --cov=src --cov-report=html --cov-fail-under=80

# Run with proper order and timeouts
pytest --randomly-seed=0 --timeout=5 --cov=src
```

**Complete single-command workflow:**
```bash
# Development: Fast unit tests only
pytest tests/unit/ -v --tb=short

# Before commit: All tests + coverage check
pytest -n auto --cov=src --cov-fail-under=80 --tb=short

# In CI/CD: Full validation with markers
pytest --cov=src --cov-fail-under=80 -m "not slow"
```

**Expected test execution timing:**
- **Unit tests:** 0.1-1 second (fastest, run frequently)
- **Integration tests:** 1-10 seconds (slower, real services)
- **E2E tests:** 10-60 seconds (slowest, high confidence)
- **Coverage analysis:** 1-5 seconds
- **Total (all tests):** 10-30 seconds for typical projects

**When to run:**
- **During development:** Unit tests only, frequently, in watch mode
- **Before committing:** All tests + coverage check (80%+ required)
- **In CI/CD:** Full suite with parallel execution, fail on coverage drop
- **Before release:** All tests including E2E, performance benchmarks
- **After deployment:** Smoke tests (subset of E2E) to verify production

### Unit Testing with pytest

**Run tests:**
```bash
# Basic run
pytest

# Verbose output
pytest -v

# Specific test file
pytest tests/test_models.py

# Specific test
pytest tests/test_models.py::test_user_creation

# With coverage
pytest --cov=src --cov-report=html

# Parallel execution
pytest -n auto

# Stop on first failure
pytest -x

# Show print statements
pytest -s
```

**Fixtures (reusable test setup):**
```python
import pytest

@pytest.fixture
def db():
    """Database connection fixture."""
    connection = create_db_connection()
    yield connection
    connection.close()

def test_user_creation(db):
    """Test using db fixture."""
    user = create_user(db, name="Alice")
    assert user.id is not None
```

**Parametrization (test multiple inputs):**
```python
import pytest

@pytest.mark.parametrize("input,expected", [
    (2, 4),
    (3, 9),
    (-1, 1),
])
def test_square(input, expected):
    """Test square function with multiple inputs."""
    assert input ** 2 == expected
```

### Mocking with pytest-mock

**Mock dependencies:**
```python
def test_api_call(mocker):
    """Mock HTTP request."""
    mock_get = mocker.patch('requests.get')
    mock_get.return_value.json.return_value = {"status": "ok"}

    result = fetch_status()
    assert result["status"] == "ok"
    mock_get.assert_called_once()
```

### Property-Based Testing with Hypothesis

**Find edge cases automatically:**
```python
from hypothesis import given, strategies as st

@given(st.lists(st.integers()))
def test_sort_is_idempotent(xs):
    """Sorting twice should equal sorting once."""
    assert sorted(sorted(xs)) == sorted(xs)

@given(st.text(), st.text())
def test_string_concat_length(a, b):
    """Concatenated length equals sum of parts."""
    assert len(a + b) == len(a) + len(b)
```

### Async Testing with pytest-asyncio

**Test async functions:**
```python
import pytest

@pytest.mark.asyncio
async def test_async_fetch():
    """Test async HTTP call."""
    data = await fetch_data_async("http://api.example.com")
    assert data is not None

@pytest.mark.asyncio
async def test_async_database():
    """Test async database operations."""
    async with database_connection() as db:
        user = await db.create_user(name="Alice")
        assert user.id is not None
```

### Test Data with factory_boy

**Reusable test data builders:**
```python
from factory import Factory, SubFactory

class UserFactory(Factory):
    """Factory for User objects."""
    class Meta:
        model = User

    name = "Alice"
    email = "alice@example.com"
    active = True

class PostFactory(Factory):
    """Factory for Post objects."""
    class Meta:
        model = Post

    author = SubFactory(UserFactory)
    title = "Test Post"
    content = "Test content"

def test_post_creation():
    """Create post with factory."""
    post = PostFactory()
    assert post.author.email == "alice@example.com"
```

### Time Mocking with freezegun

**Deterministic datetime tests:**
```python
from freezegun import freeze_time
from datetime import datetime

@freeze_time("2025-01-01 12:00:00")
def test_current_date():
    """Test with frozen time."""
    assert datetime.now() == datetime(2025, 1, 1, 12, 0, 0)

def test_expiration():
    """Test expiration logic."""
    with freeze_time("2025-01-01"):
        token = create_token(expires_in_days=7)

    with freeze_time("2025-01-08"):
        assert is_token_expired(token)
```

### HTTP Mocking with responses

**Mock HTTP requests:**
```python
import responses
import requests

@responses.activate
def test_api_call():
    """Mock HTTP response."""
    responses.add(
        responses.GET,
        'http://api.example.com/users',
        json={"id": 1, "name": "Alice"},
        status=200
    )

    resp = requests.get('http://api.example.com/users')
    assert resp.json()["name"] == "Alice"
```

### Integration Testing with Testcontainers

**Real services in tests:**
```python
from testcontainers.postgres import PostgresContainer

def test_database_operations():
    """Test with real Postgres."""
    with PostgresContainer("postgres:16") as postgres:
        engine = create_engine(postgres.get_connection_url())

        # Run migrations, test data access
        run_migrations(engine)
        user = insert_user(engine, name="Alice")
        assert user.id is not None
```

### E2E Testing with Playwright

**Browser automation tests:**
```python
import pytest

@pytest.mark.e2e
def test_login(page):
    """Test login flow."""
    page.goto("http://localhost:3000/login")
    page.get_by_label("Email").fill("user@example.com")
    page.get_by_label("Password").fill("password123")
    page.get_by_role("button", name="Sign in").click()

    # Wait for success page
    page.get_by_text("Welcome").wait_for()
    assert page.url.endswith("/dashboard")
```

### Performance Testing with pytest-benchmark

**Track performance regressions:**
```python
def test_performance(benchmark):
    """Benchmark algorithm performance."""
    result = benchmark(expensive_function, arg1, arg2)
    assert result == expected_result
```

### Snapshot Testing with syrupy

**Golden file testing:**
```python
def test_user_serialization(snapshot):
    """Test object serialization."""
    user = User(name="Alice", email="alice@example.com")
    assert user.to_dict() == snapshot
```

### Test Organization

**Standard project structure:**
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

### Configuration

**pytest.ini:**
```ini
[pytest]
addopts = -v --tb=short --strict-markers
testpaths = tests
python_files = test_*.py
python_classes = Test*
python_functions = test_*
markers =
    unit: unit tests
    integration: integration tests
    e2e: end-to-end tests
    slow: slow tests
    asyncio: async tests
```

**pyproject.toml:**
```toml
[tool.pytest.ini_options]
addopts = "--cov=src --cov-report=html --cov-fail-under=80"
testpaths = ["tests"]
asyncio_mode = "auto"

[tool.coverage.run]
branch = true
omit = ["*/tests/*", "*/venv/*"]

[tool.coverage.report]
exclude_lines = ["pragma: no cover", "def __repr__"]
```

## Bundled Resources

### Scripts (`scripts/`)

**`run-tests.sh`** - Run test suite with appropriate options
```bash
./scripts/run-tests.sh [target]
```

**`coverage-report.sh`** - Generate and open coverage report
```bash
./scripts/coverage-report.sh
```

**`test-performance.sh`** - Run performance benchmarks
```bash
./scripts/test-performance.sh
```

### Example Configs (`assets/`)

Copy these templates to projects as starting points:
- `pytest.ini` - pytest configuration
- `pyproject.toml` - Test configuration with coverage settings
- `conftest.py` - Shared pytest fixtures
- `justfile` - Task runner recipes for testing

### Detailed Reference (`references/`)

**`commands.md`** - Comprehensive command reference with all options, examples, and workflows.

To search the reference without reading the entire file:
```bash
rg -n "pytest-asyncio" references/commands.md
```

## Common Testing Patterns

### Testing Database Operations

**Pattern: Isolated database tests with real data**
```python
import pytest
from testcontainers.postgres import PostgresContainer

@pytest.fixture(scope="session")
def postgres():
    """Real Postgres container for tests."""
    with PostgresContainer("postgres:16") as postgres:
        yield postgres

def test_user_creation(postgres):
    """Test user creation with real database."""
    engine = create_engine(postgres.get_connection_url())
    run_migrations(engine)

    user = User(name="Alice", email="alice@example.com")
    session = Session(engine)
    session.add(user)
    session.commit()

    assert user.id is not None
    assert session.query(User).count() == 1
```

### Testing API Endpoints

**Pattern: Mock external APIs, test endpoint logic**
```python
import responses
import pytest

@responses.activate
def test_user_endpoint():
    """Test API endpoint that calls external service."""
    # Mock external API
    responses.add(
        responses.GET,
        "https://api.example.com/profile/123",
        json={"name": "Alice", "status": "active"},
        status=200
    )

    # Test our endpoint
    response = client.get("/api/users/123")
    assert response.status_code == 200
    assert response.json()["name"] == "Alice"

    # Verify external API was called
    assert len(responses.calls) == 1
```

### Testing Async Code

**Pattern: Test async functions with proper setup**
```python
import pytest

@pytest.mark.asyncio
async def test_async_database_fetch():
    """Test async database operation."""
    async with AsyncSession(engine) as session:
        user = await session.execute(select(User).where(User.id == 1))
        assert user.scalars().first() is not None

@pytest.mark.asyncio
async def test_concurrent_operations():
    """Test multiple async operations in parallel."""
    results = await asyncio.gather(
        fetch_user(1),
        fetch_user(2),
        fetch_user(3)
    )
    assert len(results) == 3
```

### Testing Error Handling

**Pattern: Verify exceptions are raised correctly**
```python
import pytest

def test_invalid_email_raises_error():
    """Test that invalid email raises ValueError."""
    with pytest.raises(ValueError, match="Invalid email"):
        User(email="not-an-email")

def test_database_error_handling():
    """Test graceful error handling."""
    with pytest.raises(DatabaseError):
        query_database("SELECT * FROM nonexistent_table")

def test_error_message_content():
    """Verify error message contains useful information."""
    with pytest.raises(ValueError) as exc_info:
        validate_age(-5)
    assert "must be positive" in str(exc_info.value)
```

### Testing with Time-Dependent Logic

**Pattern: Freeze time for deterministic tests**
```python
from freezegun import freeze_time
from datetime import datetime, timedelta

@freeze_time("2025-01-15 10:00:00")
def test_token_expiration():
    """Test token expiration with frozen time."""
    token = create_token(expires_in_hours=24)

    # Still valid at current time
    assert not is_token_expired(token)

    # Move time forward 25 hours
    with freeze_time("2025-01-16 11:00:00"):
        assert is_token_expired(token)

def test_birthday_countdown():
    """Test birthday logic."""
    with freeze_time("2025-01-01"):
        days_left = days_until_birthday(date(2025, 1, 15))
        assert days_left == 14
```

### Testing Generated Data (Property-Based)

**Pattern: Hypothesis for comprehensive edge case testing**
```python
from hypothesis import given, strategies as st

@given(st.lists(st.integers()))
def test_sort_always_produces_sorted_list(numbers):
    """Hypothesis will test with many different number lists."""
    sorted_numbers = sort(numbers)
    assert sorted_numbers == sorted(numbers)

@given(st.emails(), st.from_regex(r'^[a-z0-9]+$', fullmatch=True))
def test_user_creation_with_various_inputs(email, username):
    """Test user creation with many combinations."""
    user = User(email=email, username=username)
    assert user.email == email
    assert user.username == username
```

### Testing Class-Based Code

**Pattern: Fixture-based class testing**
```python
class TestCalculator:
    """Test suite for Calculator class."""

    @pytest.fixture(autouse=True)
    def setup(self):
        """Setup before each test."""
        self.calc = Calculator()

    def test_addition(self):
        assert self.calc.add(2, 3) == 5

    def test_multiplication(self):
        assert self.calc.multiply(3, 4) == 12

    @pytest.mark.parametrize("input,expected", [
        (0, 1),
        (1, 1),
        (5, 120),
    ])
    def test_factorial(self, input, expected):
        assert self.calc.factorial(input) == expected
```

### Testing Complex Workflows

**Pattern: End-to-end user journey**
```python
@pytest.mark.e2e
def test_complete_user_workflow(browser):
    """Test entire user journey."""
    # User registers
    page = browser.get_page()
    page.goto("http://localhost:3000/register")
    page.get_by_label("Email").fill("user@example.com")
    page.get_by_label("Password").fill("password123")
    page.get_by_role("button", name="Register").click()

    # User logs in
    page.get_by_label("Email").fill("user@example.com")
    page.get_by_label("Password").fill("password123")
    page.get_by_role("button", name="Login").click()

    # User creates a post
    page.get_by_role("button", name="New Post").click()
    page.get_by_label("Title").fill("My First Post")
    page.get_by_label("Content").fill("Hello, world!")
    page.get_by_role("button", name="Publish").click()

    # Verify post appears
    assert page.get_by_text("My First Post").is_visible()
```

## Best Practices

**Test Isolation:**
- Use fixtures for setup/teardown
- Mock external dependencies
- Don't rely on test execution order (use pytest-randomly)
- Clean up after each test

**Fast Feedback:**
- Run tests in parallel with pytest-xdist
- Mock slow operations (API calls, database queries)
- Use property-based testing to maximize coverage
- Organize tests by speed: unit → integration → E2E

**Reliability:**
- Use freezegun for time-dependent tests
- Use pytest-timeout to catch infinite loops
- Randomize test order to find state leaks
- Test both happy path and error cases

**Coverage:**
- Aim for 80%+ coverage on critical code
- Use `pytest --cov --cov-report=html` to find gaps
- Combine unit tests with integration tests
- Use Hypothesis for comprehensive edge case coverage

**Async Testing:**
- Mark async tests with `@pytest.mark.asyncio`
- Test real concurrent scenarios
- Use Testcontainers for async database tests
- Configure `asyncio_mode = "auto"` in pyproject.toml

## Troubleshooting

**Async tests not running:**
```bash
# Ensure pytest-asyncio is installed
uv pip install pytest-asyncio

# Configure in pyproject.toml
[tool.pytest.ini_options]
asyncio_mode = "auto"
```

**Flaky tests:**
```bash
# Randomize test order
pytest --randomly-seed=0

# Repeat tests to find flakes
pytest --count=10

# Add timeout to prevent hangs
pytest --timeout=5
```

**Coverage gaps:**
```bash
# Generate HTML coverage report
pytest --cov=src --cov-report=html
open htmlcov/index.html

# Show missing lines
pytest --cov=src --cov-report=term-missing
```

**Slow tests:**
```bash
# Show slowest tests
pytest --durations=10

# Run in parallel
pytest -n auto

# Mark slow tests and skip them
@pytest.mark.slow
def test_slow_operation():
    pass

# Run without slow tests
pytest -m "not slow"
```

**Import issues:**
```bash
# Ensure src is in PYTHONPATH
export PYTHONPATH="${PYTHONPATH}:$(pwd)/src"

# Or configure in pyproject.toml
[tool.pytest.ini_options]
pythonpath = ["src"]
```

## Verification & Testing

All tools in this skill have been tested and verified to work correctly. See [PYTHON_TESTING_TOOLS_TEST_RESULTS.md](../../PYTHON_TESTING_TOOLS_TEST_RESULTS.md) for comprehensive test results.

### Quick Verification

**Check that testing tools are installed:**
```bash
pytest --version && coverage --version
```

**Run a simple test:**
```bash
# Create a test file
cat > test_sample.py << 'EOF'
def test_addition():
    assert 2 + 2 == 4

def test_string():
    assert "hello".upper() == "HELLO"
EOF

# Run tests
pytest test_sample.py -v

# With coverage
pytest test_sample.py --cov=.
```

### Tool Versions Tested

| Tool | Version | Status | Notes |
|------|---------|--------|-------|
| pytest | 8.4.1 | ✅ Working | 13/13 tests passing, ~23 tests/second |
| coverage | 7.3.0 | ✅ Working | 100% coverage measurement achieved |
| pytest-mock | Available | ✅ Working | Mocking and fixtures fully functional |
| freeze-gun | Available | ✅ Working | Time freezing for temporal tests |
| responses | Available | ✅ Working | HTTP mocking operational |

### What the Tests Found

✅ **pytest** - Comprehensive testing verified:
- 13/13 tests passing in real test suite
- 100% code coverage achieved
- Fixtures and setup/teardown working
- Parametrized tests (describe.each equivalent) working
- Exception testing with pytest.raises working
- ~23 tests/second execution speed

✅ **Test patterns verified:**
- Function-based tests working
- Class-based tests working (TestCalculator pattern)
- Fixtures for test isolation
- Parametrized tests with multiple inputs
- Exception handling and assertions
- Coverage tracking and reporting

✅ **Advanced features working:**
- Type hints in test code
- Async test support
- Mock integration
- Coverage percentage calculation

## Quality & Security Integration

For code quality, type checking, and security scanning, see:
- **python-quality-tools** skill - Ruff, Pyright, Bandit, pip-audit
- **python-quality-tools** has pre-commit configuration

This testing skill focuses purely on testing strategies and tools.
