# Testing Strategies for React and Next.js Applications

Comprehensive guide to test architecture, coverage targets, and CI/CD integration patterns.

---

## Table of Contents

- [The Testing Pyramid](#the-testing-pyramid)
- [Testing Types Deep Dive](#testing-types-deep-dive)
- [Coverage Targets and Thresholds](#coverage-targets-and-thresholds)
- [Test Organization Patterns](#test-organization-patterns)
- [CI/CD Integration Strategies](#cicd-integration-strategies)
- [Testing Decision Framework](#testing-decision-framework)

---

## The Testing Pyramid

The testing pyramid guides how to distribute testing effort across different test types for optimal ROI.

### Classic Pyramid Structure

```
        /\
       /  \      E2E Tests (5-10%)
      /----\     - User journey validation
     /      \    - Critical path coverage
    /--------\   Integration Tests (20-30%)
   /          \  - Component interactions
  /            \ - API integration
 /--------------\ Unit Tests (60-70%)
/                \ - Individual functions
------------------  - Isolated components
```

### React/Next.js Adapted Pyramid

For frontend applications, the pyramid shifts slightly:

| Level | Percentage | Tools | Focus |
|-------|------------|-------|-------|
| Unit | 50-60% | Jest, RTL | Pure functions, hooks, isolated components |
| Integration | 25-35% | RTL, MSW | Component trees, API calls, context |
| E2E | 10-15% | Playwright | Critical user flows, cross-page navigation |

### Why This Distribution?

**Unit tests are fast and cheap:**
- Execute in milliseconds
- Pinpoint failures precisely
- Easy to maintain
- Run on every commit

**Integration tests balance coverage and cost:**
- Test realistic scenarios
- Catch component interaction bugs
- Moderate execution time
- Run on every PR

**E2E tests are expensive but essential:**
- Validate real user experience
- Catch deployment issues
- Slow and brittle
- Run on staging/production

---

## Testing Types Deep Dive

### Unit Testing

**Purpose:** Verify individual units of code work correctly in isolation.

**What to Unit Test:**
- Pure utility functions
- Custom hooks (with renderHook)
- Individual component rendering
- State reducers
- Validation logic
- Data transformers

**Example: Testing a Pure Function**

```typescript
// utils/formatPrice.ts
export function formatPrice(cents: number, currency = 'USD'): string {
  const formatter = new Intl.NumberFormat('en-US', {
    style: 'currency',
    currency,
  });
  return formatter.format(cents / 100);
}

// utils/formatPrice.test.ts
describe('formatPrice', () => {
  it('formats cents to USD by default', () => {
    expect(formatPrice(1999)).toBe('$19.99');
  });

  it('handles zero', () => {
    expect(formatPrice(0)).toBe('$0.00');
  });

  it('supports different currencies', () => {
    expect(formatPrice(1999, 'EUR')).toContain('€');
  });

  it('handles large numbers', () => {
    expect(formatPrice(100000000)).toBe('$1,000,000.00');
  });
});
```

**Example: Testing a Custom Hook**

```typescript
// hooks/useCounter.ts
export function useCounter(initial = 0) {
  const [count, setCount] = useState(initial);
  const increment = () => setCount(c => c + 1);
  const decrement = () => setCount(c => c - 1);
  const reset = () => setCount(initial);
  return { count, increment, decrement, reset };
}

// hooks/useCounter.test.ts
import { renderHook, act } from '@testing-library/react';
import { useCounter } from './useCounter';

describe('useCounter', () => {
  it('starts with initial value', () => {
    const { result } = renderHook(() => useCounter(5));
    expect(result.current.count).toBe(5);
  });

  it('increments count', () => {
    const { result } = renderHook(() => useCounter(0));
    act(() => result.current.increment());
    expect(result.current.count).toBe(1);
  });

  it('decrements count', () => {
    const { result } = renderHook(() => useCounter(5));
    act(() => result.current.decrement());
    expect(result.current.count).toBe(4);
  });

  it('resets to initial value', () => {
    const { result } = renderHook(() => useCounter(10));
    act(() => result.current.increment());
    act(() => result.current.reset());
    expect(result.current.count).toBe(10);
  });
});
```

### Integration Testing

**Purpose:** Verify multiple units work together correctly.

**What to Integration Test:**
- Component trees with multiple children
- Components with context providers
- Form submission flows
- API call and response handling
- State management interactions
- Router-dependent components

**Example: Testing Component with API Call**

```typescript
// components/UserProfile.tsx
export function UserProfile({ userId }: { userId: string }) {
  const [user, setUser] = useState<User | null>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    fetch(`/api/users/${userId}`)
      .then(res => res.json())
      .then(data => setUser(data))
      .catch(err => setError(err.message))
      .finally(() => setLoading(false));
  }, [userId]);

  if (loading) return <div>Loading...</div>;
  if (error) return <div>Error: {error}</div>;
  return <div>{user?.name}</div>;
}

// components/UserProfile.test.tsx
import { render, screen, waitFor } from '@testing-library/react';
import { rest } from 'msw';
import { setupServer } from 'msw/node';
import { UserProfile } from './UserProfile';

const server = setupServer(
  rest.get('/api/users/:id', (req, res, ctx) => {
    return res(ctx.json({ id: req.params.id, name: 'John Doe' }));
  })
);

beforeAll(() => server.listen());
afterEach(() => server.resetHandlers());
afterAll(() => server.close());

describe('UserProfile', () => {
  it('shows loading state initially', () => {
    render(<UserProfile userId="123" />);
    expect(screen.getByText('Loading...')).toBeInTheDocument();
  });

  it('displays user name after loading', async () => {
    render(<UserProfile userId="123" />);
    await waitFor(() => {
      expect(screen.getByText('John Doe')).toBeInTheDocument();
    });
  });

  it('displays error on API failure', async () => {
    server.use(
      rest.get('/api/users/:id', (req, res, ctx) => {
        return res(ctx.status(500));
      })
    );
    render(<UserProfile userId="123" />);
    await waitFor(() => {
      expect(screen.getByText(/Error/)).toBeInTheDocument();
    });
  });
});
```

### End-to-End Testing

**Purpose:** Verify complete user flows work in a real browser environment.

**What to E2E Test:**
- Critical business flows (checkout, signup, login)
- Cross-page navigation sequences
- Authentication flows
- Third-party integrations
- Payment processing
- Form wizards

**Example: Testing Checkout Flow**

```typescript
// e2e/checkout.spec.ts
import { test, expect } from '@playwright/test';

test.describe('Checkout Flow', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
  });

  test('completes purchase successfully', async ({ page }) => {
    // Add product to cart
    await page.goto('/products/widget-pro');
    await page.getByRole('button', { name: 'Add to Cart' }).click();

    // Verify cart updated
    await expect(page.getByTestId('cart-count')).toHaveText('1');

    // Go to checkout
    await page.getByRole('link', { name: 'Checkout' }).click();

    // Fill shipping info
    await page.getByLabel('Email').fill('test@example.com');
    await page.getByLabel('Address').fill('123 Test St');
    await page.getByLabel('City').fill('Test City');
    await page.getByLabel('Zip').fill('12345');

    // Fill payment info (test card)
    await page.getByLabel('Card Number').fill('4242424242424242');
    await page.getByLabel('Expiry').fill('12/25');
    await page.getByLabel('CVC').fill('123');

    // Submit order
    await page.getByRole('button', { name: 'Place Order' }).click();

    // Verify confirmation
    await expect(page).toHaveURL(/\/orders\/\w+/);
    await expect(page.getByText('Order Confirmed')).toBeVisible();
  });

  test('shows validation errors for invalid input', async ({ page }) => {
    await page.goto('/checkout');
    await page.getByRole('button', { name: 'Place Order' }).click();

    await expect(page.getByText('Email is required')).toBeVisible();
    await expect(page.getByText('Address is required')).toBeVisible();
  });
});
```

### Visual Regression Testing

**Purpose:** Catch unintended visual changes to UI components.

**Tools:** Playwright visual comparisons, Percy, Chromatic

**Example: Visual Snapshot Test**

```typescript
// e2e/visual/components.spec.ts
import { test, expect } from '@playwright/test';

test.describe('Visual Regression', () => {
  test('button variants render correctly', async ({ page }) => {
    await page.goto('/storybook/button');
    await expect(page).toHaveScreenshot('button-variants.png');
  });

  test('responsive header', async ({ page }) => {
    // Desktop
    await page.setViewportSize({ width: 1280, height: 720 });
    await page.goto('/');
    await expect(page.locator('header')).toHaveScreenshot('header-desktop.png');

    // Mobile
    await page.setViewportSize({ width: 375, height: 667 });
    await expect(page.locator('header')).toHaveScreenshot('header-mobile.png');
  });
});
```

### Accessibility Testing

**Purpose:** Ensure application is usable by people with disabilities.

**Tools:** jest-axe, @axe-core/playwright

**Example: Automated A11y Testing**

```typescript
// Unit/Integration level with jest-axe
import { render } from '@testing-library/react';
import { axe, toHaveNoViolations } from 'jest-axe';
import { Button } from './Button';

expect.extend(toHaveNoViolations);

describe('Button accessibility', () => {
  it('has no accessibility violations', async () => {
    const { container } = render(<Button>Click me</Button>);
    const results = await axe(container);
    expect(results).toHaveNoViolations();
  });
});

// E2E level with Playwright + Axe
import { test, expect } from '@playwright/test';
import AxeBuilder from '@axe-core/playwright';

test('homepage has no a11y violations', async ({ page }) => {
  await page.goto('/');
  const results = await new AxeBuilder({ page }).analyze();
  expect(results.violations).toEqual([]);
});
```

---

## Coverage Targets and Thresholds

### Recommended Thresholds by Project Type

| Project Type | Statements | Branches | Functions | Lines |
|--------------|------------|----------|-----------|-------|
| Startup/MVP | 60% | 50% | 60% | 60% |
| Growing Product | 75% | 70% | 75% | 75% |
| Enterprise | 85% | 80% | 85% | 85% |
| Safety Critical | 95% | 90% | 95% | 95% |

### Coverage by Code Type

**High Coverage Priority (80%+):**
- Business logic
- State management
- API handlers
- Form validation
- Authentication/authorization
- Payment processing

**Medium Coverage Priority (60-80%):**
- UI components
- Utility functions
- Data transformers
- Custom hooks

**Lower Coverage Priority (40-60%):**
- Static pages
- Simple wrappers
- Configuration files
- Types/interfaces

### Jest Coverage Configuration

```javascript
// jest.config.js
module.exports = {
  collectCoverageFrom: [
    'src/**/*.{ts,tsx}',
    '!src/**/*.d.ts',
    '!src/**/*.stories.{ts,tsx}',
    '!src/**/index.{ts,tsx}', // barrel files
    '!src/types/**',
  ],
  coverageThreshold: {
    global: {
      statements: 80,
      branches: 75,
      functions: 80,
      lines: 80,
    },
    // Higher thresholds for critical paths
    './src/services/payment/': {
      statements: 95,
      branches: 90,
      functions: 95,
      lines: 95,
    },
    './src/services/auth/': {
      statements: 90,
      branches: 85,
      functions: 90,
      lines: 90,
    },
  },
  coverageReporters: ['text', 'lcov', 'html', 'json'],
};
```

---

## Test Organization Patterns

### Co-located Tests (Recommended for React)

```
src/
├── components/
│   ├── Button/
│   │   ├── Button.tsx
│   │   ├── Button.test.tsx      # Unit tests
│   │   ├── Button.stories.tsx   # Storybook
│   │   └── index.ts
│   └── Form/
│       ├── Form.tsx
│       ├── Form.test.tsx
│       └── Form.integration.test.tsx  # Integration tests
├── hooks/
│   ├── useAuth.ts
│   └── useAuth.test.ts
└── utils/
    ├── formatters.ts
    └── formatters.test.ts
```

### Separate Test Directory

```
src/
├── components/
├── hooks/
└── utils/

__tests__/
├── unit/
│   ├── components/
│   ├── hooks/
│   └── utils/
├── integration/
│   └── flows/
└── fixtures/
    ├── users.json
    └── products.json

e2e/
├── specs/
│   ├── auth.spec.ts
│   └── checkout.spec.ts
├── fixtures/
│   └── auth.ts
└── pages/      # Page Object Models
    ├── LoginPage.ts
    └── CheckoutPage.ts
```

### Test File Naming Conventions

| Pattern | Use Case |
|---------|----------|
| `*.test.ts` | Unit tests |
| `*.spec.ts` | Integration/E2E tests |
| `*.integration.test.ts` | Explicit integration tests |
| `*.e2e.spec.ts` | Explicit E2E tests |
| `*.a11y.test.ts` | Accessibility tests |
| `*.visual.spec.ts` | Visual regression tests |

---

## CI/CD Integration Strategies

### Pipeline Stages

```yaml
# .github/workflows/test.yml
name: Test Pipeline

on:
  push:
    branches: [main, dev]
  pull_request:
    branches: [main, dev]

jobs:
  unit:
    name: Unit Tests
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with:
          node-version: 20
          cache: 'npm'
      - run: npm ci
      - run: npm run test:unit -- --coverage
      - uses: codecov/codecov-action@v4
        with:
          files: coverage/lcov.info
          fail_ci_if_error: true

  integration:
    name: Integration Tests
    runs-on: ubuntu-latest
    needs: unit
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with:
          node-version: 20
          cache: 'npm'
      - run: npm ci
      - run: npm run test:integration

  e2e:
    name: E2E Tests
    runs-on: ubuntu-latest
    needs: integration
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with:
          node-version: 20
          cache: 'npm'
      - run: npm ci
      - run: npx playwright install --with-deps
      - run: npm run build
      - run: npm run test:e2e
      - uses: actions/upload-artifact@v4
        if: failure()
        with:
          name: playwright-report
          path: playwright-report/
```

### Test Splitting for Speed

```yaml
# Run E2E tests in parallel across multiple machines
e2e:
  strategy:
    matrix:
      shard: [1, 2, 3, 4]
  steps:
    - run: npx playwright test --shard=${{ matrix.shard }}/4
```

### PR Gating Rules

| Test Type | When to Run | Block Merge? |
|-----------|-------------|--------------|
| Unit | Every commit | Yes |
| Integration | Every PR | Yes |
| E2E (smoke) | Every PR | Yes |
| E2E (full) | Merge to main | No (alert only) |
| Visual | Every PR | No (review required) |
| Performance | Weekly/Release | No (alert only) |

---

## Testing Decision Framework

### When to Write Which Test

```
Is it a pure function with no side effects?
├── Yes → Unit test
└── No
    ├── Does it make API calls or use context?
    │   ├── Yes → Integration test with mocking
    │   └── No
    │       ├── Is it a critical user flow?
    │       │   ├── Yes → E2E test
    │       │   └── No → Integration test
    └── Is it UI-focused with many visual states?
        ├── Yes → Storybook + Visual test
        └── No → Component unit test
```

### Test ROI Matrix

| Test Type | Write Time | Run Time | Maintenance | Confidence |
|-----------|------------|----------|-------------|------------|
| Unit | Low | Very Fast | Low | Medium |
| Integration | Medium | Fast | Medium | High |
| E2E | High | Slow | High | Very High |
| Visual | Low | Medium | Medium | High (UI) |

### When NOT to Test

- Generated code (GraphQL types, Prisma client)
- Third-party library internals
- Implementation details (internal state, private methods)
- Simple pass-through wrappers
- Type definitions

### Red Flags in Testing Strategy

| Red Flag | Problem | Solution |
|----------|---------|----------|
| E2E tests > 30% | Slow CI, flaky tests | Push logic down to integration |
| Only unit tests | Missing interaction bugs | Add integration tests |
| Testing mocks | Not testing real behavior | Test behavior, not implementation |
| 100% coverage goal | Diminishing returns | Focus on critical paths |
| No E2E tests | Missing deployment issues | Add smoke tests for critical flows |

---

## Summary

1. **Follow the pyramid:** 60% unit, 30% integration, 10% E2E
2. **Set thresholds by risk:** Higher coverage for critical paths
3. **Co-locate tests:** Keep tests close to source code
4. **Automate in CI:** Run tests on every PR, gate merges on failure
5. **Decide wisely:** Not everything needs every type of test
