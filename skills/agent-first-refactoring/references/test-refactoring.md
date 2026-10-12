# Test Refactoring for Agent-First Development

Fast, reliable, isolated tests are the foundation of agent-first development. Agents use tests as their primary feedback loop — they run tests after every change to verify correctness. Slow or flaky tests make agents ineffective.

## Table of Contents

- [Speed Targets](#speed-targets)
- [Common Bottlenecks and Fixes](#common-bottlenecks-and-fixes)
- [Isolation Patterns](#isolation-patterns)
- [Test Organization](#test-organization)
- [Language-Specific Guidance](#language-specific-guidance)

---

## Speed Targets

| Scope | Target |
|-------|--------|
| Single unit test | < 100ms |
| Single test file | < 5s |
| Full module test suite | < 30s |
| Entire project fast suite | < 2 minutes |
| Full suite (including slow/integration) | < 10 minutes |

If a test exceeds these targets, it should be investigated and optimized or marked as `slow`.

---

## Common Bottlenecks and Fixes

### 1. Network calls in tests

**Problem**: Tests making real HTTP requests to external APIs.

**Fix**: Mock at the HTTP layer.

```python
# Before: Real network call
def test_fetch_user():
    result = api_client.get_user("123")  # Hits real API
    assert result.name == "Alice"

# After: Mocked
def test_fetch_user(httpx_mock):
    httpx_mock.add_response(json={"name": "Alice"})
    result = api_client.get_user("123")
    assert result.name == "Alice"
```

**Tools**: `responses` or `httpx_mock` (Python), `msw` or `nock` (Node.js), `httpmock` (Go).

### 2. Database access in unit tests

**Problem**: Tests hitting a real database for logic that doesn't need it.

**Fix**: Use the repository pattern — test business logic against an in-memory implementation.

```python
# Before: Hits real database
def test_deactivate_user():
    user = User.objects.create(name="Alice", active=True)
    deactivate_user(user.id)
    user.refresh_from_db()
    assert not user.active

# After: In-memory repository
def test_deactivate_user():
    repo = InMemoryUserRepo()
    repo.save(User(id="1", name="Alice", active=True))
    deactivate_user("1", repo=repo)
    assert not repo.get("1").active
```

Keep a small set of integration tests that verify the real database repository works, but test all business logic against the in-memory version.

### 3. Filesystem operations

**Problem**: Tests creating/reading real files on disk.

**Fix**: Use `tmp_path` (pytest), `os.MkdirTemp` (Go), or mock the filesystem.

```python
def test_write_report(tmp_path):
    output = tmp_path / "report.txt"
    write_report(output, data="test")
    assert output.read_text() == "test"
```

### 4. Sleep/time-based tests

**Problem**: Tests using `time.sleep()` or waiting for real time to pass.

**Fix**: Inject a clock abstraction or use time-freezing libraries.

```python
# Before
def test_token_expiry():
    token = create_token(ttl=3600)
    time.sleep(3601)  # Waits over an hour!
    assert token.is_expired()

# After
@freeze_time("2025-01-01 12:00:00")
def test_token_expiry():
    token = create_token(ttl=3600)
    with freeze_time("2025-01-01 13:00:01"):
        assert token.is_expired()
```

**Tools**: `freezegun` (Python), `jest.useFakeTimers()` (Node.js), `clockwork` (Go).

### 5. Heavy test fixtures / setUp

**Problem**: Test classes with expensive setup that runs for every test.

**Fix**: Use session-scoped or module-scoped fixtures for expensive setup. Keep per-test setup minimal.

```python
# Expensive: runs for every test
@pytest.fixture
def trained_model():
    return train_model(large_dataset)  # 10 seconds

# Better: shared across the module
@pytest.fixture(scope="module")
def trained_model():
    return train_model(large_dataset)  # 10 seconds once
```

---

## Isolation Patterns

### No shared mutable state

Tests must not depend on state left by previous tests. Each test should set up its own state and clean up after.

```python
# Bad: depends on global variable set by another test
counter = 0

def test_increment():
    global counter
    counter += 1
    assert counter == 1  # Fails if another test ran first

# Good: each test owns its state
def test_increment():
    counter = Counter(initial=0)
    counter.increment()
    assert counter.value == 1
```

### No execution order dependencies

Tests must pass regardless of execution order. Use `pytest-randomly` or equivalent to verify this.

### No port conflicts

Tests that start servers must use dynamic port allocation, not hardcoded ports.

```python
# Bad
server = start_server(port=8080)  # Conflicts with other tests

# Good
server = start_server(port=0)  # OS assigns an available port
port = server.port
```

### Deterministic randomness

If tests use random data, seed the random number generator.

---

## Test Organization

### File structure

Mirror the source structure in the test directory:

```
src/
├── auth/
│   ├── login.py
│   └── tokens.py
tests/
├── auth/
│   ├── test_login.py
│   └── test_tokens.py
```

### Naming

Test names should describe the behavior, not the implementation:

```python
# Bad
def test_process():
def test_handler():
def test_main_function():

# Good
def test_login_returns_token_for_valid_credentials():
def test_login_rejects_expired_password():
def test_rate_limiter_blocks_after_five_attempts():
```

### Markers for categorization

Tag tests by speed and dependency so agents can run the right subset:

```python
@pytest.mark.slow
def test_full_migration():
    ...

@pytest.mark.integration
def test_real_database_connection():
    ...
```

Configure fast-only execution:

```ini
# pytest.ini
[pytest]
markers =
    slow: marks tests as slow (deselect with '-m "not slow"')
    integration: marks tests that need external services
```

### Selective test execution

Ensure the test framework supports running:
- A single test: `pytest tests/test_auth.py::test_login_success`
- A single file: `pytest tests/test_auth.py`
- A directory: `pytest tests/auth/`
- By marker: `pytest -m "not slow"`

Document these commands in AGENTS.md.

---

## Language-Specific Guidance

### Python (pytest)

- Use `conftest.py` for shared fixtures at each directory level
- Use `tmp_path` for filesystem tests
- Use `monkeypatch` for environment variable and attribute mocking
- Use `pytest-xdist` for parallel execution: `pytest -n auto`
- Run `pytest --durations=10` to find slow tests

### JavaScript/TypeScript (Jest/Vitest)

- Use `describe`/`it` blocks for grouping
- Use `jest.mock()` at module level for dependency mocking
- Use `beforeEach`/`afterEach` (not `beforeAll`) for test isolation
- Configure `testTimeout` globally to catch hanging tests
- Use `--shard` for CI parallelization

### Go

- Use `t.Parallel()` for concurrent test execution
- Use `t.TempDir()` for filesystem tests
- Use `httptest.NewServer()` for HTTP mocking
- Use `-short` flag and `testing.Short()` to skip slow tests
- Use `-count=1` to disable test caching during development

### Rust

- Use `#[ignore]` attribute for slow tests, run with `--ignored`
- Use `tempfile` crate for filesystem tests
- Use `mockall` for trait-based mocking
- Use `cargo nextest` for faster parallel execution
