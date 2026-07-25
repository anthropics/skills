# CI/CD Integration Guide

Integrating test coverage and quality gates into CI pipelines.

---

## Table of Contents

- [Coverage in CI](#coverage-in-ci)
- [GitHub Actions Examples](#github-actions-examples)
- [Quality Gates](#quality-gates)
- [Trend Tracking](#trend-tracking)

---

## Coverage in CI

### Coverage Report Flow

1. Run tests with coverage enabled
2. Generate report in machine-readable format (LCOV, JSON, XML)
3. Parse report for threshold validation
4. Upload to coverage service (Codecov, Coveralls)
5. Fail build if below threshold

### Report Formats by Tool

| Tool | Command | Output Format |
|------|---------|---------------|
| Jest | `jest --coverage --coverageReporters=lcov` | LCOV |
| Pytest | `pytest --cov-report=xml` | Cobertura XML |
| JUnit/JaCoCo | `mvn jacoco:report` | JaCoCo XML |
| Vitest | `vitest --coverage` | LCOV/JSON |

---

## GitHub Actions Examples

### Node.js (Jest)

```yaml
name: Test and Coverage

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with:
          node-version: '20'

      - run: npm ci
      - run: npm test -- --coverage

      - name: Check coverage threshold
        run: |
          COVERAGE=$(cat coverage/coverage-summary.json | jq '.total.lines.pct')
          if (( $(echo "$COVERAGE < 80" | bc -l) )); then
            echo "Coverage $COVERAGE% is below 80% threshold"
            exit 1
          fi

      - uses: codecov/codecov-action@v4
        with:
          file: coverage/lcov.info
```

### Python (Pytest)

```yaml
name: Test and Coverage

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-python@v5
        with:
          python-version: '3.11'

      - run: pip install pytest pytest-cov
      - run: pytest --cov=src --cov-report=xml --cov-fail-under=80

      - uses: codecov/codecov-action@v4
        with:
          file: coverage.xml
```

### Java (Maven + JaCoCo)

```yaml
name: Test and Coverage

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-java@v4
        with:
          distribution: 'temurin'
          java-version: '17'

      - run: mvn test jacoco:check

      - uses: codecov/codecov-action@v4
        with:
          file: target/site/jacoco/jacoco.xml
```

---

## Quality Gates

### Threshold Configuration

**Jest (package.json):**
```json
{
  "jest": {
    "coverageThreshold": {
      "global": {
        "branches": 80,
        "functions": 80,
        "lines": 80,
        "statements": 80
      }
    }
  }
}
```

**Pytest (pyproject.toml):**
```toml
[tool.coverage.report]
fail_under = 80
```

**JaCoCo (pom.xml):**
```xml
<rule>
  <element>BUNDLE</element>
  <limits>
    <limit>
      <counter>LINE</counter>
      <value>COVEREDRATIO</value>
      <minimum>0.80</minimum>
    </limit>
  </limits>
</rule>
```

### PR Coverage Checks

- Block merge if coverage drops
- Show coverage diff in PR comments
- Require coverage for changed files
- Allow exceptions with justification

---

## Trend Tracking

### Metrics to Track

| Metric | Purpose | Alert Threshold |
|--------|---------|-----------------|
| Overall line coverage | Baseline health | < 80% |
| Branch coverage | Logic completeness | < 70% |
| Coverage delta | Regression detection | < -2% per PR |
| Test execution time | Performance | > 5 min |
| Flaky test count | Reliability | > 0 |

### Coverage Services

| Service | Features | Integration |
|---------|----------|-------------|
| Codecov | PR comments, badges, graphs | GitHub, GitLab, Bitbucket |
| Coveralls | History, trends, badges | GitHub, GitLab |
| SonarCloud | Full code quality suite | Multiple CI platforms |

### Badge Generation

```markdown
<!-- README.md -->
[![codecov](https://codecov.io/gh/org/repo/branch/main/graph/badge.svg)](https://codecov.io/gh/org/repo)
```
