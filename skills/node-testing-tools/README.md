# Node.js / TypeScript Testing Tools - Claude Skill

A comprehensive Claude skill for writing, improving, and debugging tests across the full testing pyramid: unit, integration, and E2E for Node.js and TypeScript projects.

## Overview

This skill provides expertise in modern Node.js/TypeScript testing tools and strategies:

**Test Framework & Runners (2):**
- Vitest, @vitest/coverage-v8, @vitest/ui, @vitest/environment-jsdom

**Component Testing (3):**
- @testing-library/react, @testing-library/vue, @testing-library/svelte

**API Testing (3):**
- SuperTest, node-mocks-http, MSW (Mock Service Worker)

**Integration Testing (1):**
- Testcontainers

**E2E Testing (2):**
- Playwright, Cypress

**Advanced Testing (2):**
- fast-check (property-based testing), Pact JS (contract testing)

**Code Quality & Architecture (2):**
- Knip (unused dependencies), dependency-cruiser (architecture rules)

## What's Included

```
node-testing-tools/
├── SKILL.md                          # Main skill (lean, workflow-focused)
├── INSTALL.md                        # Installation instructions
├── README.md                         # This file
├── scripts/                          # Executable helper scripts
│   ├── run-tests.sh                 # Run tests with coverage
│   ├── coverage-report.sh           # Generate coverage HTML
│   └── e2e-tests.sh                 # Run E2E tests
├── references/                       # Detailed documentation
│   └── commands.md                  # Comprehensive command reference (to be created)
└── assets/                          # Template configs
    ├── vitest.config.ts
    ├── vitest.setup.ts
    ├── package.json (template)
    ├── tsconfig.json
    ├── mocks/server.ts
    ├── justfile
    └── .dependency-cruiser.cjs
```

## Design Principles

This skill follows Claude skill best practices:

### Progressive Disclosure

1. **Metadata** (~100 words): Name and description always in context
2. **SKILL.md** (~5k words): Loaded when skill triggers - lean, workflow-focused
3. **Bundled Resources** (unlimited): Loaded as needed by Claude

### Testing Focus

This skill focuses **purely on testing** (not code quality that's in node-quality-tools skill):
- Testing strategies and best practices
- Test frameworks and tools
- Coverage measurement and improvement
- Async, integration, and E2E testing
- Test data generation and mocking
- Testing all framework types (React, Vue, Svelte)

### Bundled Resources Strategy

**Scripts** - Executable workflows for common testing tasks:
- Run tests with coverage reporting
- Generate HTML coverage reports
- Run E2E tests with recording

**References** - Detailed command documentation:
- All testing tools with syntax, options, examples
- Testing patterns and workflows
- Troubleshooting common issues

**Assets** - Ready-to-use templates:
- Vitest configuration
- Test fixtures and MSW setup
- Package.json scripts
- Task runner recipes for testing

## Key Improvements from Original

### 1. Added Essential Testing Tools

- **@testing-library/react, @testing-library/vue, @testing-library/svelte** - Framework-specific component testing
- **@vitest/ui** - Visual test explorer with live results
- **@vitest/environment-jsdom** - Browser DOM testing environment
- **MSW (Mock Service Worker)** - Modern API mocking (fetch/XHR intercept)
- **node-mocks-http** - Unit-level req/res mocking
- **fast-check** - Property-based testing for edge case discovery
- **Testcontainers** - Real service testing with Docker

### 2. Removed/Demoted Non-Testing Tools

- Removed Biome (overlaps with node-quality-tools skill - linting/formatting)
- Removed npm audit/OSV-Scanner (reference to node-quality-tools for supply-chain security)
- Focused purely on testing (not code quality)

### 3. Comprehensive Documentation

- Full SKILL.md with all testing patterns and examples
- Template configs for Vitest, MSW, TypeScript setup
- Helper scripts for common testing workflows
- Clear testing pyramid documentation
- Troubleshooting section with common issues and solutions

### 4. Testing Pyramid Focus

```
        E2E (Playwright)              ~5-10% of tests
       /             \
    Integration Testing               ~15-30% of tests
    (Testcontainers, MSW, SuperTest)
    /                 \
  Unit Tests (Vitest)                 ~60-80% of tests
```

### 5. Framework-Agnostic Component Testing

Support for React, Vue, and Svelte with Testing Library, enabling testing across modern frameworks using consistent patterns.

## Installation

See [INSTALL.md](INSTALL.md) for complete installation instructions.

**Quick start:**
```bash
# Install essential testing tools
npm i -D vitest @vitest/coverage-v8 @vitest/ui @vitest/environment-jsdom \
         @testing-library/react @testing-library/dom @testing-library/user-event \
         fast-check supertest node-mocks-http msw \
         testcontainers @playwright/test

# Setup Playwright
npx playwright install --with-deps
```

## Usage Examples

**In Claude conversations:**

- "Write Vitest tests for this React component"
- "Create integration tests with Testcontainers for my database"
- "Set up MSW mocking for this API"
- "Test this Express endpoint with SuperTest"
- "Write property-based tests with fast-check to find edge cases"
- "Write E2E tests for the checkout flow with Playwright"
- "Improve test coverage to 80%"
- "Debug why my tests are flaky"
- "Test this Vue component with Testing Library"

**Direct CLI usage:**

```bash
# Run all tests with coverage
npm test -- --coverage

# Run tests in watch mode
npm test -- --watch

# Run tests with UI
npm test -- --ui

# Run specific test file
npm test -- tests/unit/example.test.ts

# Run E2E tests
npx playwright test

# Or use justfile
just test
just test-cov
just test-watch
```

## Skill Development

This skill was improved using the skill-creator skill, following Anthropic's skill development best practices:

1. **Understanding** - Analyzed testing tool ecosystem for Node.js/TypeScript
2. **Planning** - Added missing testing libraries (Testing Library variants, MSW, node-mocks-http)
3. **Implementation** - Created SKILL.md, helper scripts, and config templates
4. **Documentation** - Complete installation and usage guides

## Architecture Decisions

### Focus on Testing Pyramid

- Clear distinction between unit, integration, and E2E tests
- Tools for each level of the pyramid
- Performance and isolation best practices

### Framework-Agnostic Components

- Use @testing-library for consistent testing patterns across React/Vue/Svelte
- Avoid framework-specific test tools
- Patterns work the same way across frameworks

### No Code Quality Tools

- Code quality tools (Biome, ESLint, Prettier) reference node-quality-tools skill
- Avoid duplication between skills
- Clear separation of concerns

### API Mocking Strategy

- MSW for integration/E2E testing (browser-compatible)
- node-mocks-http for unit-level mocking
- SuperTest for HTTP testing without port binding
- Clear guidance on when to use each

### Modern Async Support

- Vitest with async/await native support
- Testcontainers for real async database testing
- MSW with proper async request handling

### E2E Testing Focus

- Playwright as primary (cross-browser, stable, video capture)
- Cypress as alternative for interactive debugging
- Examples with realistic user flows

## Test Organization

Recommended project structure:

```
project/
├── src/
│   ├── components/
│   │   └── Button.tsx
│   ├── utils/
│   │   └── math.ts
│   ├── api/
│   │   └── client.ts
│   └── mocks/
│       └── server.ts
├── tests/
│   ├── unit/
│   │   ├── math.test.ts
│   │   └── Button.test.tsx
│   ├── integration/
│   │   ├── database.test.ts
│   │   └── api.test.ts
│   └── e2e/
│       └── checkout.test.ts
├── vitest.config.ts
├── vitest.setup.ts
├── playwright.config.ts
└── package.json
```

## Testing Strategies Covered

1. **Unit Testing** - Individual functions and components with Vitest
2. **Component Testing** - React/Vue/Svelte with Testing Library
3. **API Testing** - HTTP endpoints with SuperTest and MSW
4. **Integration Testing** - Real databases with Testcontainers
5. **E2E Testing** - User flows with Playwright
6. **Contract Testing** - Microservice compatibility with Pact
7. **Property-Based Testing** - Edge cases with fast-check
8. **Performance Testing** - Regression detection

## Next Steps

To complete the skill:
1. Add detailed `references/commands.md` with all testing tools
2. Create `scripts/coverage-report.sh` and `scripts/e2e-tests.sh`
3. Add more fixture examples in `assets/vitest.setup.ts`
4. Create integration test examples
5. Add Playwright configuration template

## Contributing

To improve this skill:
1. Use it with real testing tasks
2. Notice gaps or missing tools
3. Update SKILL.md, add scripts, or improve configs
4. Re-package and upload updated version

## License

This skill is provided for use with Claude. The included tools are open-source software with their own licenses.
