# Node.js/TypeScript Testing Tools - Command Reference

Comprehensive command reference for all testing tools used in node-testing-tools skill.

## Table of Contents

1. [Vitest](#vitest)
2. [Testing Library](#testing-library)
3. [SuperTest](#supertest)
4. [MSW (Mock Service Worker)](#msw)
5. [fast-check](#fast-check)
6. [Testcontainers](#testcontainers)
7. [Playwright](#playwright)
8. [Cypress](#cypress)
9. [Pact JS](#pact-js)
10. [TypeScript](#typescript)
11. [Architecture Tools](#architecture-tools)

---

## Vitest

Fast unit test framework with Jest compatibility.

### Basic Commands

```bash
# Run tests once
npm test -- --run
npx vitest run

# Run tests in watch mode (re-run on file changes)
npm test
npx vitest

# Run specific test file
npx vitest tests/unit/math.test.ts

# Run tests matching pattern
npx vitest -t "addition"
npx vitest --reporter=verbose

# Run with UI
npx vitest --ui

# Generate coverage report
npx vitest run --coverage

# Run specific test with debugging
npx vitest --inspect-brk --single-thread tests/unit/debug.test.ts
```

### Configuration

**`vitest.config.ts`:**
```typescript
import { defineConfig } from 'vitest/config';

export default defineConfig({
  test: {
    globals: true,           // use describe/it globally
    environment: 'jsdom',    // DOM environment for component tests
    coverage: {
      provider: 'v8',
      reportsDirectory: './coverage',
    },
    setupFiles: ['./vitest.setup.ts'],
  },
});
```

### Coverage Options

```bash
# Generate coverage with multiple reporters
npx vitest run --coverage --coverage.reporter=html --coverage.reporter=lcov

# Set minimum coverage threshold
npx vitest run --coverage --coverage.lines=80

# Generate coverage excluding specific files
npx vitest run --coverage --coverage.exclude="**/node_modules/**"
```

### Common Options

- `--run` - Run once, don't watch
- `--watch` - Watch mode (default in dev)
- `--ui` - Launch UI dashboard
- `--coverage` - Generate coverage report
- `--reporter=<type>` - Reporter type (default, verbose, json, etc.)
- `--threads` - Run with worker threads (default: true)
- `--inspect-brk` - Debug with Node debugger
- `-t <pattern>` - Filter by test name
- `--grep <pattern>` - Filter by pattern
- `--bail <count>` - Stop after N failures
- `--repeat <count>` - Repeat tests N times

---

## Testing Library

User-centric testing utilities for components.

### React Testing Library

```typescript
import { render, screen, within } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import { Button } from './Button';

// Render component
render(<Button>Click me</Button>);

// Query by role (preferred)
screen.getByRole('button', { name: /click me/i });
screen.getAllByRole('button');
screen.queryByRole('button'); // returns null if not found
screen.findByRole('button'); // async, waits for element

// Query by label (for form inputs)
screen.getByLabelText('Email');

// Query by placeholder
screen.getByPlaceholderText('Enter email');

// Query by test ID (last resort)
screen.getByTestId('submit-btn');

// Query by text
screen.getByText('Submit');

// Within scope
const form = screen.getByRole('form');
within(form).getByRole('button');

// User interactions
await userEvent.click(screen.getByRole('button'));
await userEvent.type(screen.getByRole('textbox'), 'text');
await userEvent.selectOptions(screen.getByRole('combobox'), 'option1');

// Waiting for async updates
await screen.findByText('Success');
await waitFor(() => {
  expect(screen.getByText('Done')).toBeInTheDocument();
});
```

### Vue Testing Library

```typescript
import { render, screen } from '@testing-library/vue';
import { mount } from 'vue';
import Button from './Button.vue';

// Render Vue component
render(Button, {
  props: { label: 'Click me' },
  slots: { default: 'Content' },
});

// Same query methods as React
screen.getByRole('button');
screen.getByText('Click me');
```

### Svelte Testing Library

```typescript
import { render, screen } from '@testing-library/svelte';
import Button from './Button.svelte';

// Render Svelte component
render(Button, { props: { label: 'Click' } });

// Same query methods
screen.getByRole('button');
```

### Query Priority (Best to Worst)

1. `getByRole()` - Most accessible, reflects how users interact
2. `getByLabelText()` - For form inputs with labels
3. `getByPlaceholderText()` - For inputs with placeholders
4. `getByText()` - For buttons, links, headings
5. `getByDisplayValue()` - For filled form fields
6. `getByTestId()` - Last resort, avoids hard-to-maintain selectors

---

## SuperTest

HTTP assertions library for testing APIs.

### Basic Usage

```typescript
import request from 'supertest';
import app from '../src/app';

// GET request
const res = await request(app)
  .get('/api/users')
  .expect(200)
  .expect('Content-Type', /json/);

// POST request with data
const res = await request(app)
  .post('/api/users')
  .send({ name: 'John', email: 'john@example.com' })
  .expect(201);

// PUT request
const res = await request(app)
  .put('/api/users/1')
  .send({ name: 'Jane' })
  .expect(200);

// DELETE request
const res = await request(app)
  .delete('/api/users/1')
  .expect(204);

// Access response body
expect(res.body).toEqual({ id: 1, name: 'Jane' });
expect(res.body.id).toBe(1);
```

### Headers and Authentication

```typescript
// Set request headers
request(app)
  .get('/api/protected')
  .set('Authorization', 'Bearer token123')
  .set('Content-Type', 'application/json')
  .expect(200);

// Check response headers
const res = await request(app).get('/api/users');
expect(res.headers['content-type']).toMatch(/json/);
```

### Query Parameters

```typescript
request(app)
  .get('/api/users')
  .query({ page: 1, limit: 10 })
  .expect(200);

request(app)
  .get('/api/users')
  .query('page=1&limit=10')
  .expect(200);
```

### File Upload

```typescript
import path from 'path';

request(app)
  .post('/api/upload')
  .attach('file', path.resolve('tests/fixtures/image.png'))
  .expect(200);
```

### Response Assertions

```typescript
const res = await request(app).get('/api/users/1');

// Response body
expect(res.body).toBeDefined();
expect(res.body.id).toBe(1);

// Status code
expect(res.status).toBe(200);
expect(res.statusCode).toBe(200);

// Headers
expect(res.headers['content-type']).toContain('application/json');

// Type checking
expect(res.type).toBe('application/json');
```

---

## MSW (Mock Service Worker)

API mocking library for both browsers and Node.js.

### Setup

```typescript
// src/mocks/server.ts
import { setupServer } from 'msw/node';
import { rest } from 'msw';

export const server = setupServer(
  rest.get('/api/user/:id', (req, res, ctx) => {
    const { id } = req.params;
    return res(
      ctx.status(200),
      ctx.json({ id, name: 'John' })
    );
  })
);

// vitest.setup.ts
beforeAll(() => server.listen());
afterEach(() => server.resetHandlers());
afterAll(() => server.close());
```

### Request Handlers

```typescript
// GET request
rest.get('/api/users', (req, res, ctx) => {
  return res(ctx.json([{ id: 1, name: 'John' }]));
});

// POST request
rest.post('/api/users', (req, res, ctx) => {
  return res(ctx.status(201), ctx.json({ id: 1, ...req.body }));
});

// Query parameters
rest.get('/api/users', (req, res, ctx) => {
  const page = req.url.searchParams.get('page');
  return res(ctx.json({ page }));
});

// Request body
rest.post('/api/users', async (req, res, ctx) => {
  const data = await req.json();
  return res(ctx.json(data));
});

// Dynamic responses
rest.get('/api/user/:id', (req, res, ctx) => {
  const { id } = req.params;
  if (id === '999') {
    return res(ctx.status(404), ctx.json({ error: 'Not found' }));
  }
  return res(ctx.json({ id, name: 'User' }));
});
```

### Response Helpers

```typescript
// JSON response
ctx.json({ id: 1, name: 'John' })

// Status code
ctx.status(201)

// Headers
ctx.set('X-Custom-Header', 'value')

// Cookie
ctx.cookie('sessionId', 'abc123', { httpOnly: true })

// Text response
ctx.text('Hello')

// Binary response
ctx.body(Buffer.from('binary'))

// Delay response
ctx.delay(1000)

// Combine multiple
ctx.status(201),
ctx.json({ id: 1 }),
ctx.set('X-Custom', 'value'),
ctx.delay(500)
```

### Override Handlers in Tests

```typescript
import { rest } from 'msw';
import { server } from '../mocks/server';

it('handles errors', async () => {
  // Override handler for this test
  server.use(
    rest.get('/api/users/:id', (req, res, ctx) => {
      return res(ctx.status(500), ctx.json({ error: 'Server error' }));
    })
  );

  const res = await fetch('/api/users/1');
  expect(res.status).toBe(500);
});
```

---

## fast-check

Property-based testing library for discovering edge cases.

### Basic Property Testing

```typescript
import fc from 'fast-check';

it('addition is commutative', () => {
  fc.assert(
    fc.property(fc.integer(), fc.integer(), (a, b) => {
      expect(add(a, b)).toBe(add(b, a));
    })
  );
});

it('string concatenation works', () => {
  fc.assert(
    fc.property(fc.string(), fc.string(), (a, b) => {
      const result = a + b;
      expect(result).toContain(a);
      expect(result).toContain(b);
    })
  );
});
```

### Generators

```typescript
// Basic types
fc.integer()                    // any integer
fc.integer({ min: 1, max: 100 })  // range
fc.nat()                        // non-negative
fc.float()                      // floating point
fc.boolean()                    // true/false
fc.string()                     // any string
fc.string({ minLength: 1, maxLength: 100 })

// Collections
fc.array(fc.integer())          // array of integers
fc.set(fc.integer())            // set of integers
fc.dictionary(fc.string(), fc.integer())  // object

// Complex
fc.record({
  id: fc.integer(),
  name: fc.string(),
  active: fc.boolean(),
})

fc.tuple(fc.integer(), fc.string())  // tuple [int, string]

fc.oneof(
  fc.integer(),
  fc.string(),
  fc.boolean()
)
```

### Shrinking

When a property fails, fast-check automatically shrinks inputs:

```typescript
// If property fails with large/complex input,
// fast-check will find minimal example that still fails
it('finds minimal failing case', () => {
  fc.assert(
    fc.property(fc.string(), (str) => {
      expect(str.length).toBeLessThan(1000); // might fail
    })
  );
  // If fails, shows minimal string that breaks it
});
```

---

## Testcontainers

Test isolation with real Docker services.

### Basic Usage

```typescript
import { GenericContainer } from 'testcontainers';
import mysql from 'mysql2/promise';

it('connects to real database', async () => {
  const container = await new GenericContainer('mysql:8')
    .withEnvironment({ MYSQL_ROOT_PASSWORD: 'test' })
    .withExposedPorts(3306)
    .start();

  const connection = await mysql.createConnection({
    host: container.getHost(),
    port: container.getMappedPort(3306),
    user: 'root',
    password: 'test',
  });

  const [result] = await connection.query('SELECT 1');
  expect(result).toBeDefined();

  await container.stop();
});
```

### Container Configuration

```typescript
const container = await new GenericContainer('postgres:15')
  // Environment variables
  .withEnvironment({
    POSTGRES_PASSWORD: 'password',
    POSTGRES_DB: 'testdb',
  })
  // Exposed ports
  .withExposedPorts(5432)
  // Volume mounts
  .withBindMounts([{
    source: '/path/to/init.sql',
    target: '/docker-entrypoint-initdb.d/init.sql',
  }])
  // Working directory
  .withWorkingDirectory('/app')
  // Command
  .withCommand(['postgres', '-c', 'log_statement=all'])
  // Labels
  .withLabels({ environment: 'test' })
  // Health check
  .withHealthCheck({
    test: ['CMD', 'pg_isready', '-U', 'postgres'],
    interval: 1000,
    timeout: 5000,
    retries: 5,
  })
  // Startup timeout
  .withStartupTimeout(60000)
  .start();

// Get connection info
const host = container.getHost();
const port = container.getMappedPort(5432);
```

### Common Containers

```typescript
// PostgreSQL
new GenericContainer('postgres:15')
  .withEnvironment({ POSTGRES_PASSWORD: 'test' })
  .withExposedPorts(5432)

// MySQL
new GenericContainer('mysql:8')
  .withEnvironment({ MYSQL_ROOT_PASSWORD: 'test' })
  .withExposedPorts(3306)

// MongoDB
new GenericContainer('mongo:6')
  .withExposedPorts(27017)

// Redis
new GenericContainer('redis:7')
  .withExposedPorts(6379)

// RabbitMQ
new GenericContainer('rabbitmq:3')
  .withEnvironment({ RABBITMQ_DEFAULT_USER: 'guest' })
  .withExposedPorts(5672, 15672)
```

---

## Playwright

End-to-end testing framework.

### Basic Test

```typescript
import { test, expect } from '@playwright/test';

test('user can login', async ({ page }) => {
  await page.goto('http://localhost:3000');
  await page.fill('input[name="email"]', 'user@example.com');
  await page.fill('input[name="password"]', 'password');
  await page.click('button[type="submit"]');

  await expect(page).toHaveURL('/dashboard');
  await expect(page.locator('h1')).toContainText('Dashboard');
});
```

### Navigation and Waiting

```typescript
// Navigate
await page.goto('http://localhost:3000');
await page.goBack();
await page.goForward();
await page.reload();

// Wait for navigation
await Promise.all([
  page.waitForNavigation(),
  page.click('a[href="/next"]'),
]);

// Wait for element
await page.waitForSelector('h1');
await page.waitForFunction(() => document.body.innerHTML.includes('loaded'));
```

### Locators

```typescript
// By role (recommended)
page.getByRole('button', { name: /submit/i })
page.getByRole('textbox', { name: /email/i })
page.getByRole('link', { name: /home/i })

// By text
page.getByText('Submit')
page.getByText(/exact match/)

// By label
page.getByLabel('Email')

// By placeholder
page.getByPlaceholder('email@example.com')

// By test ID
page.getByTestId('submit-btn')

// CSS selector
page.locator('button.primary')

// XPath
page.locator('xpath=//button[@id="submit"]')

// Combining
page.locator('form').locator('button')

// Filtering
page.locator('button').filter({ hasText: 'Submit' })
```

### Interactions

```typescript
// Click
await page.click('button');
await page.locator('button').click();

// Type
await page.fill('input[name="email"]', 'user@example.com');
await page.locator('input').type('text');

// Select option
await page.selectOption('select', 'option1');

// Check/uncheck
await page.check('input[type="checkbox"]');
await page.uncheck('input[type="checkbox"]');

// Focus
await page.focus('input');

// Blur
await page.locator('input').blur();

// Drag and drop
await page.dragAndDrop('#source', '#target');

// Multi-select
await page.click('select', { clickCount: 3 });
```

### Assertions

```typescript
// URL
await expect(page).toHaveURL('/dashboard');
await expect(page).toHaveURL(/dashboard/);

// Title
await expect(page).toHaveTitle('Dashboard');

// Visible
await expect(page.locator('h1')).toBeVisible();

// Hidden
await expect(page.locator('.hidden')).toBeHidden();

// Enabled/disabled
await expect(button).toBeEnabled();
await expect(button).toBeDisabled();

// Text content
await expect(page.locator('h1')).toContainText('Dashboard');
await expect(page.locator('h1')).toHaveText('Dashboard');

// Attribute
await expect(page.locator('input')).toHaveAttribute('type', 'email');

// Class
await expect(page.locator('button')).toHaveClass('primary');

// Count
await expect(page.locator('tr')).toHaveCount(5);

// Checked
await expect(page.locator('input[type="checkbox"]')).toBeChecked();

// Focused
await expect(page.locator('input')).toBeFocused();
```

### Configuration

```typescript
import { defineConfig, devices } from '@playwright/test';

export default defineConfig({
  testDir: './tests/e2e',
  fullyParallel: true,
  forbidOnly: !!process.env.CI,
  retries: process.env.CI ? 2 : 0,
  workers: process.env.CI ? 1 : undefined,
  reporter: 'html',
  use: {
    baseURL: 'http://localhost:3000',
    trace: 'on-first-retry',
    screenshot: 'only-on-failure',
    video: 'retain-on-failure',
  },
  webServer: {
    command: 'npm run dev',
    url: 'http://localhost:3000',
    reuseExistingServer: !process.env.CI,
  },
  projects: [
    { name: 'chromium', use: { ...devices['Desktop Chrome'] } },
    { name: 'firefox', use: { ...devices['Desktop Firefox'] } },
    { name: 'webkit', use: { ...devices['Desktop Safari'] } },
  ],
});
```

---

## Cypress

Alternative E2E testing framework.

### Basic Test

```typescript
describe('User Login', () => {
  it('should login successfully', () => {
    cy.visit('http://localhost:3000');
    cy.get('input[name="email"]').type('user@example.com');
    cy.get('input[name="password"]').type('password');
    cy.get('button[type="submit"]').click();

    cy.url().should('include', '/dashboard');
    cy.get('h1').should('contain', 'Dashboard');
  });
});
```

### Commands

```typescript
// Navigation
cy.visit('http://localhost:3000');
cy.go('back');
cy.go('forward');
cy.reload();

// Selection
cy.get('button')
cy.get('button').first()
cy.get('button').last()
cy.get('button').eq(0)
cy.contains('Submit')
cy.get('[data-testid="submit"]')

// Interaction
cy.get('input').type('text')
cy.get('button').click()
cy.get('select').select('option1')
cy.get('input[type="checkbox"]').check()
cy.get('input[type="checkbox"]').uncheck()

// Waiting
cy.get('h1', { timeout: 5000 })
cy.get('h1').should('be.visible')
```

---

## Pact JS

Contract testing for microservices.

### Consumer Test

```typescript
import { Pact } from '@pact-foundation/pact';
import { UserService } from '../src/userService';

const provider = new Pact({
  consumer: 'WebClient',
  provider: 'UserAPI',
});

describe('UserAPI contract', () => {
  it('returns user by ID', () => {
    return provider
      .addInteraction({
        state: 'user 1 exists',
        uponReceiving: 'a request for user 1',
        withRequest: {
          method: 'GET',
          path: '/users/1',
          headers: { 'Content-Type': 'application/json' },
        },
        willRespondWith: {
          status: 200,
          body: { id: 1, name: 'Alice' },
        },
      })
      .then(() => provider.verify())
      .then(() => {
        const service = new UserService(provider.mockServerUrl);
        return service.getUser(1);
      })
      .then((user) => {
        expect(user.name).toBe('Alice');
      });
  });

  afterAll(() => provider.finalize());
});
```

---

## TypeScript

Static type checking.

### Basic Commands

```bash
# Type check without emitting
tsc --noEmit

# Watch mode
tsc --watch

# Emit with declaration files
tsc --declaration

# Pretty print config
tsc --showConfig

# Specific file
tsc src/main.ts
```

### tsconfig.json Options

```json
{
  "compilerOptions": {
    "target": "ES2022",                    // Output target
    "module": "ESNext",                    // Module system
    "moduleResolution": "bundler",         // Module resolution
    "strict": true,                        // All strict checks
    "noEmit": true,                        // Don't emit files
    "jsx": "react-jsx",                    // JSX handling
    "lib": ["ES2022", "DOM"],              // Built-in types
    "skipLibCheck": true,                  // Skip type checking deps
    "esModuleInterop": true,               // ES module interop
    "resolveJsonModule": true,             // Import JSON
    "declaration": true,                   // Generate .d.ts
    "sourceMap": true,                     // Source maps
    "baseUrl": ".",                        // Base path resolution
    "paths": {
      "@/*": ["src/*"]                     // Path aliases
    }
  }
}
```

---

## Architecture Tools

### dependency-cruiser

Check dependency rules and find cycles.

```bash
# Check config
depcruise --config .dependency-cruiser.cjs src

# Generate graph
depcruise -x --output-type dot src | dot -T svg > graph.svg

# Verbose output
depcruise --verbose --config .dependency-cruiser.cjs src

# Check specific pattern
depcruise --from "^src/api" --to "^src/utils" src
```

### Knip

Find unused files, dependencies, exports.

```bash
# Find all unused
knip

# Report missing dependencies
knip --include files

# Report unused exports
knip --include unlisted

# Ignore patterns
knip --ignore "tests/**,*.config.js"

# Strict mode
knip --strict
```

---

## Tips and Patterns

### Run in CI

```bash
# Jest/Vitest in CI
npm test -- --run --reporter=verbose --coverage

# Playwright in CI
npx playwright test --reporter=github

# Set parallel workers
npm test -- --workers=4
```

### Setup and Teardown

```typescript
beforeEach(async () => {
  // Setup before each test
  await database.connect();
});

afterEach(async () => {
  // Cleanup after each test
  await database.disconnect();
});

beforeAll(async () => {
  // Setup once before all tests
  server.listen();
});

afterAll(async () => {
  // Cleanup once after all tests
  server.close();
});
```

### Debugging

```bash
# Debug with Node inspector
node --inspect-brk ./node_modules/vitest/vitest.mjs run tests/debug.test.ts

# Debug Playwright
npx playwright test --debug

# Cypress interactive
npx cypress open
```
