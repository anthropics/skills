# Installation & Usage

## Install the Skill in Claude

1. **Package the skill:**
   ```bash
   cd /path/to/node-testing-tools
   zip -r node-testing-tools.zip . -x "*.git*" -x "*.DS_Store" -x "node_modules/*"
   ```

2. **Upload to Claude:**
   - Open Claude Desktop or Web
   - Go to Settings → Capabilities → Skills
   - Upload the `node-testing-tools.zip` file
   - The skill will be available in all future conversations

3. **Use the skill:**
   - Start a new chat
   - When you mention tasks like "write tests for this component" or "set up Vitest", Claude will automatically load this skill
   - You can also explicitly invoke it: "use Vitest to test...", "use Playwright for E2E testing...", "use fast-check for property tests..."

## Install Testing Tools (macOS/Linux)

### Essential Tools (14)

```bash
# Create and activate virtual environment (Node.js)
node --version  # Ensure Node.js 18+ is installed

# Install testing framework & coverage
npm i -D vitest @vitest/coverage-v8 @vitest/ui @vitest/environment-jsdom

# Install component testing (framework-specific, install as needed)
npm i -D @testing-library/react @testing-library/dom @testing-library/user-event
npm i -D @testing-library/vue
npm i -D @testing-library/svelte

# Install API testing & mocking
npm i -D supertest node-mocks-http msw

# Install integration testing
npm i -D testcontainers

# Install E2E testing
npm i -D @playwright/test

# Install property-based testing
npm i -D fast-check

# Setup Playwright browsers
npx playwright install --with-deps
```

### Optional Tools (6+)

```bash
# E2E alternative (Cypress)
npm i -D cypress

# Contract testing (Pact)
npm i -D @pact-foundation/pact

# Architecture & cleanup
npm i -D knip dependency-cruiser
```

### Verify Installation

```bash
npx vitest --version
npm test -- --help
npx playwright test --version
```

## Skill Structure

```
node-testing-tools/
├── SKILL.md                          # Main skill instructions
├── INSTALL.md                        # This file
├── README.md                         # Design principles & improvements
├── scripts/                          # Helper scripts
│   ├── run-tests.sh                 # Run test suite with coverage
│   ├── coverage-report.sh           # Generate coverage report
│   └── e2e-tests.sh                 # Run E2E tests
├── references/                       # Detailed documentation
│   └── commands.md                  # Comprehensive command reference
└── assets/                          # Template config files
    ├── vitest.config.ts
    ├── vitest.setup.ts
    ├── package.json (template)
    ├── tsconfig.json
    ├── mocks/server.ts
    ├── justfile
    └── .dependency-cruiser.cjs
```

## Quick Start

After installing both the skill and testing tools:

1. **Create test directory and first test:**
   ```bash
   mkdir -p tests/unit
   cat > tests/unit/example.test.ts <<'EOF'
   import { describe, it, expect } from 'vitest';

   describe('example', () => {
     it('should pass', () => {
       expect(true).toBe(true);
     });
   });
   EOF
   ```

2. **Create vitest config:**
   ```bash
   cp assets/vitest.config.ts .
   cp assets/vitest.setup.ts .
   cp assets/tsconfig.json .
   cp assets/mocks/server.ts ./src/mocks/
   ```

3. **Add test scripts to package.json:**
   ```json
   {
     "scripts": {
       "test": "vitest -q",
       "test:watch": "vitest",
       "test:ui": "vitest --ui",
       "test:cov": "vitest run --coverage"
     }
   }
   ```

4. **Run tests:**
   ```bash
   npm test
   npm run test:cov
   ```

## Using with Claude

Example prompts that will trigger this skill:

- "Write tests for this React component"
- "Set up Vitest for my Node.js project"
- "Create integration tests with Testcontainers"
- "Write E2E tests with Playwright for this flow"
- "Use fast-check to find edge cases in this function"
- "Mock this API with MSW"
- "Test this Express endpoint with SuperTest"
- "Improve test coverage to 80%"
- "Debug why my tests are flaky"
- "Set up contract testing with Pact"

Claude will provide copy-pasteable test code, explain testing strategies, and suggest improvements.

## Testing Pyramid

Organize your tests by speed and complexity:

```
        E2E (Playwright)              ~5-10% of tests
       /             \
    Integration Testing               ~15-30% of tests
    (Testcontainers, MSW, SuperTest)
    /                 \
  Unit Tests (Vitest)                 ~60-80% of tests
```

## Common Workflows

### Unit Testing

```bash
npm test
npm test -- tests/unit/example.test.ts
npm test -- --watch
```

### Component Testing (React)

```bash
npm test -- tests/components/
npm test -- --ui
```

### Integration Testing with Real Services

```bash
npm test -- tests/integration/ -v
# Requires Docker for Testcontainers
```

### API Testing

```bash
npm test -- tests/api/
# Uses SuperTest and MSW
```

### E2E Testing

```bash
npm run test:e2e
npx playwright test
npx playwright test --ui
```

### Coverage Analysis

```bash
npm run test:cov
open coverage/index.html
```

### Performance Testing

```bash
npm test -- tests/benchmarks/ --reporter=verbose
```

## Project Structure

Recommended layout:

```
my-project/
├── src/
│   ├── components/
│   │   └── Button.tsx
│   ├── utils/
│   │   └── math.ts
│   ├── api/
│   │   └── user.ts
│   └── mocks/
│       └── server.ts
├── tests/
│   ├── conftest.ts              # Shared setup
│   ├── unit/
│   │   ├── math.test.ts
│   │   └── user.test.ts
│   ├── components/
│   │   └── Button.test.tsx
│   ├── integration/
│   │   └── database.test.ts
│   └── e2e/
│       └── login.test.ts
├── vitest.config.ts
├── vitest.setup.ts
├── playwright.config.ts
└── package.json
```

## Updating the Skill

To update the skill after making changes:

1. Make your changes to SKILL.md, scripts, references, or assets
2. Re-package: `zip -r node-testing-tools.zip . -x "*.git*" -x "*.DS_Store" -x "node_modules/*"`
3. Upload the new zip file in Claude Settings → Skills
4. Start a new conversation to use the updated version

## Integration with Other Skills

This testing skill works well with:
- **node-quality-tools** - Biome, ESLint, Prettier for code quality
- **python-testing-tools** - For Python testing if you have polyglot projects
- Use together for complete Node.js development workflow

## Resources

- [Vitest Documentation](https://vitest.dev/)
- [Testing Library Documentation](https://testing-library.com/)
- [Playwright Documentation](https://playwright.dev/)
- [MSW Documentation](https://mswjs.io/)
- [fast-check Documentation](https://fast-check.dev/)
- [SuperTest Documentation](https://github.com/visionmedia/supertest)
- [Testcontainers Documentation](https://node.testcontainers.org/)
- [Pact JavaScript Documentation](https://docs.pact.foundation/implementation_guides/javascript)
- Tool documentation: See `references/commands.md` for detailed command reference
- Example configs: See `assets/` directory for ready-to-use templates
