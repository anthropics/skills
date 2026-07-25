# Senior QA Testing Engineer Skill

Production-ready quality assurance and test automation skill for React/Next.js applications.

## Tech Stack Focus

| Category | Technologies |
|----------|--------------|
| Unit/Integration | Jest, React Testing Library |
| E2E Testing | Playwright |
| Coverage Analysis | Istanbul, NYC, LCOV |
| API Mocking | MSW (Mock Service Worker) |
| Accessibility | jest-axe, @axe-core/playwright |

## Quick Start

```bash
# Generate component tests
python scripts/test_suite_generator.py src/components --include-a11y

# Analyze coverage gaps
python scripts/coverage_analyzer.py coverage/coverage-final.json --threshold 80 --strict

# Scaffold E2E tests for Next.js
python scripts/e2e_test_scaffolder.py src/app --page-objects
```

## Scripts

### test_suite_generator.py

Scans React/TypeScript components and generates Jest + React Testing Library test stubs.

**Features:**
- Detects functional, class, memo, and forwardRef components
- Generates render, interaction, and accessibility tests
- Identifies props requiring mock data
- Optional `--include-a11y` for jest-axe assertions

**Usage:**
```bash
python scripts/test_suite_generator.py <component-dir> [options]

Options:
  --scan-only       List components without generating tests
  --include-a11y    Add accessibility test assertions
  --output DIR      Output directory for test files
```

### coverage_analyzer.py

Parses Istanbul JSON or LCOV coverage reports and identifies testing gaps.

**Features:**
- Calculates line, branch, function, and statement coverage
- Identifies critical untested paths (auth, payment, API routes)
- Generates text and HTML reports
- Threshold enforcement with `--strict` flag

**Usage:**
```bash
python scripts/coverage_analyzer.py <coverage-file> [options]

Options:
  --threshold N     Minimum coverage percentage (default: 80)
  --strict          Exit with error if below threshold
  --format FORMAT   Output format: text, json, html
  --output FILE     Output file path
```

### e2e_test_scaffolder.py

Scans Next.js App Router or Pages Router directories and generates Playwright tests.

**Features:**
- Detects routes, dynamic parameters, and layouts
- Generates test files per route with navigation and content checks
- Optional Page Object Model class generation
- Generates `playwright.config.ts` and auth fixtures

**Usage:**
```bash
python scripts/e2e_test_scaffolder.py <app-dir> [options]

Options:
  --page-objects    Generate Page Object Model classes
  --output DIR      Output directory for E2E tests
  --base-url URL    Base URL for tests (default: http://localhost:3000)
```

## References

### testing_strategies.md (650 lines)

Comprehensive testing strategy guide covering:
- Test pyramid and distribution (70% unit, 20% integration, 10% E2E)
- Coverage targets by project type
- Testing types (unit, integration, E2E, visual, accessibility)
- CI/CD integration patterns
- Testing decision framework

### test_automation_patterns.md (1010 lines)

React/Next.js test automation patterns:
- Page Object Model implementation for Playwright
- Test data factories and builder patterns
- Fixture management (Playwright and Jest)
- Mocking strategies (MSW, Jest module mocking)
- Custom test utilities (`renderWithProviders`)
- Async testing patterns
- Snapshot testing guidelines

### qa_best_practices.md (965 lines)

Quality assurance best practices:
- Writing testable React code
- Test naming conventions (Describe-It pattern)
- Arrange-Act-Assert structure
- Test isolation principles
- Handling flaky tests
- Debugging failed tests
- Quality metrics and KPIs

## Workflows

### Workflow 1: New Component Testing

1. Create component in `src/components/`
2. Run `test_suite_generator.py` to generate test stub
3. Fill in test assertions based on component behavior
4. Run `npm test` to verify tests pass
5. Check coverage with `coverage_analyzer.py`

### Workflow 2: E2E Test Setup

1. Run `e2e_test_scaffolder.py` on your Next.js app directory
2. Review generated tests in `e2e/` directory
3. Customize Page Objects for complex interactions
4. Run `npx playwright test` to execute
5. Configure CI/CD with generated `playwright.config.ts`

### Workflow 3: Coverage Gap Analysis

1. Run tests with coverage: `npm test -- --coverage`
2. Analyze with `coverage_analyzer.py --strict --threshold 80`
3. Review critical untested paths in report
4. Prioritize tests for auth, payment, and API routes
5. Re-run analysis to verify improvement

## Test Pyramid Targets

| Test Type | Ratio | Focus |
|-----------|-------|-------|
| Unit | 70% | Individual functions, utilities, hooks |
| Integration | 20% | Component interactions, API calls, state |
| E2E | 10% | Critical user journeys, happy paths |

## Coverage Targets

| Project Type | Line | Branch | Function |
|--------------|------|--------|----------|
| Startup/MVP | 60% | 50% | 70% |
| Production | 80% | 70% | 85% |
| Enterprise | 90% | 85% | 95% |

## CI/CD Integration

```yaml
# .github/workflows/test.yml
jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Install dependencies
        run: npm ci
      - name: Run unit tests
        run: npm test -- --coverage
      - name: Run E2E tests
        run: npx playwright test
      - name: Upload coverage
        uses: codecov/codecov-action@v4
```

## Related Skills

- **senior-frontend** - React/Next.js component development
- **senior-fullstack** - Full application architecture
- **senior-devops** - CI/CD pipeline setup
- **code-reviewer** - Code review with testing focus

---

**Version:** 2.9.0
**Last Updated:** January 2026
**Tech Focus:** React 18+, Next.js 14+, Jest 29+, Playwright 1.40+
