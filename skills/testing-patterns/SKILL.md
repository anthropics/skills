---
name: testing-patterns
description: Write effective tests across the stack—unit, integration, E2E, and visual regression. Covers testing philosophy, framework selection, mocking strategies, and CI integration. Triggers on testing, test coverage, TDD, or quality assurance requests.
---

# Testing Patterns

Build confidence through strategic testing.

## Testing Philosophy

### The Testing Trophy

```
        ╱╲
       ╱  ╲        E2E (few)
      ╱────╲
     ╱      ╲      Integration (more)
    ╱────────╲
   ╱          ╲    Unit (many, fast)
  ╱────────────╲
 ╱   Static     ╲  TypeScript, ESLint
╱────────────────╲
```

### What to Test

| Test Type | What | Why |
|-----------|------|-----|
| Static | Types, lint rules | Catch errors at write-time |
| Unit | Pure functions, utils | Fast, precise feedback |
| Integration | Component + dependencies | Test contracts |
| E2E | User flows | Confidence in real usage |

### What NOT to Test

- Implementation details (internal state, private methods)
- Third-party library internals
- Constants and configuration
- Framework code

---

## Unit Testing

### Structure: AAA Pattern

```typescript
describe('calculateTotal', () => {
  it('should apply discount to subtotal', () => {
    // Arrange
    const items = [{ price: 100 }, { price: 50 }];
    const discount = 0.1;

    // Act
    const result = calculateTotal(items, discount);

    // Assert
    expect(result).toBe(135);
  });
});
```

### Test Naming

```typescript
// Pattern: should [expected behavior] when [condition]

it('should return empty array when input is null')
it('should throw error when user is not authenticated')
it('should apply discount when coupon is valid')
```

### Testing Pure Functions

```typescript
// utils/format.ts
export function formatCurrency(cents: number): string {
  return `$${(cents / 100).toFixed(2)}`;
}

// utils/format.test.ts
describe('formatCurrency', () => {
  it('should format cents to dollar string', () => {
    expect(formatCurrency(1000)).toBe('$10.00');
    expect(formatCurrency(1)).toBe('$0.01');
    expect(formatCurrency(0)).toBe('$0.00');
  });

  it('should handle negative values', () => {
    expect(formatCurrency(-500)).toBe('$-5.00');
  });
});
```

### Edge Cases to Consider

- Empty/null/undefined inputs
- Boundary values (0, -1, MAX_INT)
- Empty arrays/objects
- Invalid types (if not using TypeScript)
- Async edge cases (race conditions, timeouts)

---

## React Component Testing

### Testing Library Philosophy

> "The more your tests resemble the way your software is used, the more confidence they can give you."

### Component Test Structure

```tsx
import { render, screen, fireEvent } from '@testing-library/react';
import { Counter } from './Counter';

describe('Counter', () => {
  it('should increment count when button clicked', async () => {
    render(<Counter initialCount={0} />);

    const button = screen.getByRole('button', { name: /increment/i });
    await fireEvent.click(button);

    expect(screen.getByText('Count: 1')).toBeInTheDocument();
  });
});
```

### Query Priority

Use queries in this order (most to least preferred):

1. `getByRole` - Accessible to everyone
2. `getByLabelText` - Form fields
3. `getByPlaceholderText` - If no label
4. `getByText` - Non-interactive content
5. `getByTestId` - Last resort

### Async Testing

```tsx
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

it('should load data after button click', async () => {
  const user = userEvent.setup();
  render(<DataLoader />);

  await user.click(screen.getByRole('button', { name: /load/i }));

  // Wait for async content
  await waitFor(() => {
    expect(screen.getByText('Data loaded')).toBeInTheDocument();
  });
});
```

### Mocking

```tsx
// Mock a module
vi.mock('./api', () => ({
  fetchUser: vi.fn(() => Promise.resolve({ name: 'Test User' })),
}));

// Mock a hook
vi.mock('./useAuth', () => ({
  useAuth: () => ({ user: { id: '1' }, isLoading: false }),
}));

// Mock fetch
global.fetch = vi.fn(() =>
  Promise.resolve({
    json: () => Promise.resolve({ data: 'test' }),
  })
);
```

---

## Integration Testing

### API Route Testing

```typescript
import { createMocks } from 'node-mocks-http';
import handler from './api/posts';

describe('/api/posts', () => {
  it('should return posts list', async () => {
    const { req, res } = createMocks({
      method: 'GET',
    });

    await handler(req, res);

    expect(res._getStatusCode()).toBe(200);
    expect(JSON.parse(res._getData())).toHaveLength(3);
  });
});
```

### Database Integration

```typescript
import { db } from '@/lib/db';

describe('User service', () => {
  beforeEach(async () => {
    await db.user.deleteMany(); // Clean state
  });

  afterAll(async () => {
    await db.$disconnect();
  });

  it('should create user with valid data', async () => {
    const user = await createUser({
      email: 'test@example.com',
      name: 'Test User'
    });

    expect(user.id).toBeDefined();
    expect(user.email).toBe('test@example.com');
  });
});
```

---

## E2E Testing

### Playwright Setup

```typescript
// e2e/auth.spec.ts
import { test, expect } from '@playwright/test';

test.describe('Authentication', () => {
  test('should allow user to sign in', async ({ page }) => {
    await page.goto('/login');

    await page.fill('[name="email"]', 'user@example.com');
    await page.fill('[name="password"]', 'testpass123'); // allow-secret
    await page.click('button[type="submit"]');

    await expect(page).toHaveURL('/dashboard');
    await expect(page.locator('h1')).toContainText('Welcome');
  });
});
```

### Page Object Pattern

```typescript
// e2e/pages/login.page.ts
export class LoginPage {
  constructor(private page: Page) {}

  async goto() {
    await this.page.goto('/login');
  }

  async login(email: string, passphrase: string) { // allow-secret
    await this.page.fill('[name="email"]', email);
    await this.page.fill('[name="password"]', passphrase); // allow-secret
    await this.page.click('button[type="submit"]');
  }
}

// e2e/auth.spec.ts
test('should login successfully', async ({ page }) => {
  const loginPage = new LoginPage(page);
  await loginPage.goto();
  await loginPage.login('user@example.com', 'testpass'); // allow-secret

  await expect(page).toHaveURL('/dashboard');
});
```

### Visual Regression

```typescript
test('homepage should match snapshot', async ({ page }) => {
  await page.goto('/');
  await expect(page).toHaveScreenshot('homepage.png');
});
```

---

## Mocking Strategies

### When to Mock

| Mock | When |
|------|------|
| External APIs | Always in unit/integration |
| Database | Sometimes (test containers vs mocks) |
| Time/Date | When testing time-dependent logic |
| Randomness | When testing deterministic output |
| Network | Always in unit tests |

### MSW (Mock Service Worker)

```typescript
// mocks/handlers.ts
import { rest } from 'msw';

export const handlers = [
  rest.get('/api/users', (req, res, ctx) => {
    return res(
      ctx.json([
        { id: 1, name: 'John' },
        { id: 2, name: 'Jane' },
      ])
    );
  }),

  rest.post('/api/users', async (req, res, ctx) => {
    const body = await req.json();
    return res(ctx.status(201), ctx.json({ id: 3, ...body }));
  }),
];
```

---

## Test Configuration

### Vitest Config

```typescript
// vitest.config.ts
import { defineConfig } from 'vitest/config';
import react from '@vitejs/plugin-react';

export default defineConfig({
  plugins: [react()],
  test: {
    environment: 'jsdom',
    globals: true,
    setupFiles: ['./test/setup.ts'],
    coverage: {
      reporter: ['text', 'html'],
      exclude: ['node_modules/', 'test/'],
    },
  },
});
```

### Test Setup

```typescript
// test/setup.ts
import '@testing-library/jest-dom';
import { server } from './mocks/server';

beforeAll(() => server.listen());
afterEach(() => server.resetHandlers());
afterAll(() => server.close());
```

---

## Coverage Strategy

### Meaningful Coverage

| Type | Target | Notes |
|------|--------|-------|
| Statements | 70-80% | Don't chase 100% |
| Branches | 70-80% | Test important paths |
| Functions | 80%+ | All public APIs |
| Lines | 70-80% | Balance with velocity |

### What High Coverage Doesn't Mean

- Tests are good
- No bugs
- Code is maintainable
- Edge cases are covered

---

## CI Integration

```yaml
# .github/workflows/test.yml
name: Test
on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with:
          node-version: '20'
          cache: 'npm'

      - run: npm ci
      - run: npm run test:coverage

      - uses: codecov/codecov-action@v3
        with:
          files: ./coverage/lcov.info
```
