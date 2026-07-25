# QA Best Practices for React and Next.js

Guidelines for writing maintainable tests, debugging failures, and measuring test quality.

---

## Table of Contents

- [Writing Testable Code](#writing-testable-code)
- [Test Naming Conventions](#test-naming-conventions)
- [Arrange-Act-Assert Pattern](#arrange-act-assert-pattern)
- [Test Isolation Principles](#test-isolation-principles)
- [Handling Flaky Tests](#handling-flaky-tests)
- [Code Review for Testability](#code-review-for-testability)
- [Test Maintenance Strategies](#test-maintenance-strategies)
- [Debugging Failed Tests](#debugging-failed-tests)
- [Quality Metrics and KPIs](#quality-metrics-and-kpis)

---

## Writing Testable Code

Testable code is easy to understand, has clear boundaries, and minimizes dependencies.

### Dependency Injection

Instead of creating dependencies inside functions, pass them as parameters.

**Hard to Test:**

```typescript
// src/services/userService.ts
import { prisma } from '../lib/prisma';
import { sendEmail } from '../lib/email';

export async function createUser(data: UserInput) {
  const user = await prisma.user.create({ data });
  await sendEmail(user.email, 'Welcome!');
  return user;
}
```

**Easy to Test:**

```typescript
// src/services/userService.ts
export function createUserService(
  db: PrismaClient,
  emailService: EmailService
) {
  return {
    async createUser(data: UserInput) {
      const user = await db.user.create({ data });
      await emailService.send(user.email, 'Welcome!');
      return user;
    },
  };
}

// Usage in app
const userService = createUserService(prisma, emailService);

// Usage in tests
const mockDb = { user: { create: jest.fn() } };
const mockEmail = { send: jest.fn() };
const testService = createUserService(mockDb, mockEmail);
```

### Pure Functions

Pure functions are deterministic and have no side effects, making them trivial to test.

**Impure (Hard to Test):**

```typescript
function formatTimestamp() {
  const now = new Date();
  return `${now.getFullYear()}-${now.getMonth() + 1}-${now.getDate()}`;
}
```

**Pure (Easy to Test):**

```typescript
function formatTimestamp(date: Date): string {
  return `${date.getFullYear()}-${date.getMonth() + 1}-${date.getDate()}`;
}

// Test
expect(formatTimestamp(new Date('2024-03-15'))).toBe('2024-3-15');
```

### Separation of Concerns

Separate business logic from UI and I/O operations.

**Mixed Concerns (Hard to Test):**

```typescript
// Component with embedded business logic
function CheckoutForm() {
  const [total, setTotal] = useState(0);

  const handleSubmit = async (items: CartItem[]) => {
    // Business logic mixed with UI
    let sum = 0;
    for (const item of items) {
      sum += item.price * item.quantity;
      if (item.category === 'electronics') {
        sum *= 0.9; // 10% discount
      }
    }
    const tax = sum * 0.08;
    const finalTotal = sum + tax;

    // API call
    await fetch('/api/orders', {
      method: 'POST',
      body: JSON.stringify({ items, total: finalTotal }),
    });

    setTotal(finalTotal);
  };

  return <form onSubmit={handleSubmit}>...</form>;
}
```

**Separated Concerns (Easy to Test):**

```typescript
// Pure business logic (easy to unit test)
export function calculateOrderTotal(items: CartItem[]): number {
  return items.reduce((sum, item) => {
    const subtotal = item.price * item.quantity;
    const discount = item.category === 'electronics' ? 0.9 : 1;
    return sum + subtotal * discount;
  }, 0);
}

export function calculateTax(subtotal: number, rate = 0.08): number {
  return subtotal * rate;
}

// Custom hook for order logic (testable with renderHook)
export function useCheckout() {
  const [total, setTotal] = useState(0);
  const mutation = useMutation(createOrder);

  const checkout = async (items: CartItem[]) => {
    const subtotal = calculateOrderTotal(items);
    const tax = calculateTax(subtotal);
    const finalTotal = subtotal + tax;

    await mutation.mutateAsync({ items, total: finalTotal });
    setTotal(finalTotal);
  };

  return { checkout, total, isLoading: mutation.isLoading };
}

// Component (integration testable)
function CheckoutForm() {
  const { checkout, total, isLoading } = useCheckout();
  return <form onSubmit={() => checkout(items)}>...</form>;
}
```

### Component Design for Testability

| Pattern | Testability | Example |
|---------|-------------|---------|
| Props over context | High | `<Button disabled={!valid}>` |
| Callbacks over side effects | High | `onSubmit={handleSubmit}` |
| Controlled components | High | `<Input value={value} onChange={...}>` |
| Render props | Medium | `<DataProvider render={data => ...}>` |
| Internal state | Low | `const [x, setX] = useState()` |
| Global state | Low | `useGlobalStore()` |

---

## Test Naming Conventions

Good test names document expected behavior and help diagnose failures.

### Naming Patterns

**Pattern 1: should [expected behavior] when [condition]**

```typescript
describe('LoginForm', () => {
  it('should display error message when credentials are invalid', () => {});
  it('should redirect to dashboard when login succeeds', () => {});
  it('should disable submit button when form is submitting', () => {});
});
```

**Pattern 2: [method/action] [expected result]**

```typescript
describe('calculateDiscount', () => {
  it('returns 0 for orders under $50', () => {});
  it('returns 10% for orders $50-$99', () => {});
  it('returns 20% for orders $100+', () => {});
});
```

**Pattern 3: given [context], when [action], then [result]**

```typescript
describe('ShoppingCart', () => {
  it('given an empty cart, when adding an item, then cart count is 1', () => {});
  it('given items in cart, when removing all, then cart is empty', () => {});
});
```

### Describe Block Organization

```typescript
describe('UserService', () => {
  describe('createUser', () => {
    describe('with valid input', () => {
      it('creates user in database', () => {});
      it('sends welcome email', () => {});
      it('returns user with id', () => {});
    });

    describe('with invalid input', () => {
      it('throws ValidationError for missing email', () => {});
      it('throws ValidationError for invalid email format', () => {});
      it('throws ConflictError for duplicate email', () => {});
    });
  });

  describe('deleteUser', () => {
    it('removes user from database', () => {});
    it('throws NotFoundError for non-existent user', () => {});
  });
});
```

### Anti-patterns to Avoid

| Bad | Good | Why |
|-----|------|-----|
| `it('works')` | `it('returns sum of two numbers')` | Describes behavior |
| `it('test 1')` | `it('handles empty array')` | Specific scenario |
| `it('should do stuff')` | `it('should validate email format')` | Clear expectation |
| Duplicating code in name | Describing behavior | Readable output |

---

## Arrange-Act-Assert Pattern

The AAA pattern structures tests into three clear phases.

### Structure

```typescript
it('calculates total with discount', () => {
  // Arrange - Set up test data and conditions
  const items = [
    { name: 'Widget', price: 100, quantity: 2 },
    { name: 'Gadget', price: 50, quantity: 1 },
  ];
  const discountRate = 0.1;

  // Act - Execute the code being tested
  const result = calculateTotal(items, discountRate);

  // Assert - Verify the outcome
  expect(result).toBe(225); // (200 + 50) * 0.9
});
```

### Async Example

```typescript
it('fetches user profile', async () => {
  // Arrange
  const userId = '123';
  server.use(
    rest.get('/api/users/:id', (req, res, ctx) =>
      res(ctx.json({ id: userId, name: 'John' }))
    )
  );

  // Act
  render(<UserProfile userId={userId} />);

  // Assert
  await expect(screen.findByText('John')).resolves.toBeInTheDocument();
});
```

### Component Testing Example

```typescript
it('submits form with user input', async () => {
  // Arrange
  const user = userEvent.setup();
  const onSubmit = jest.fn();
  render(<ContactForm onSubmit={onSubmit} />);

  // Act
  await user.type(screen.getByLabelText('Name'), 'John Doe');
  await user.type(screen.getByLabelText('Email'), 'john@example.com');
  await user.type(screen.getByLabelText('Message'), 'Hello!');
  await user.click(screen.getByRole('button', { name: 'Send' }));

  // Assert
  expect(onSubmit).toHaveBeenCalledWith({
    name: 'John Doe',
    email: 'john@example.com',
    message: 'Hello!',
  });
});
```

### Guidelines

1. **One Act per test** - Test one behavior at a time
2. **Multiple assertions OK** - If they verify the same behavior
3. **Avoid logic in tests** - No if/else, loops in test code
4. **Setup in Arrange, not beforeEach** - Unless truly shared

---

## Test Isolation Principles

Isolated tests are independent, repeatable, and can run in any order.

### State Isolation

```typescript
describe('CartService', () => {
  let cartService: CartService;

  // Fresh instance for each test
  beforeEach(() => {
    cartService = new CartService();
  });

  it('adds item to empty cart', () => {
    cartService.addItem({ id: '1', quantity: 1 });
    expect(cartService.getItems()).toHaveLength(1);
  });

  it('starts with empty cart', () => {
    // Not affected by previous test
    expect(cartService.getItems()).toHaveLength(0);
  });
});
```

### Database Isolation

```typescript
describe('UserRepository', () => {
  beforeAll(async () => {
    // Connect to test database
    await db.connect(process.env.TEST_DATABASE_URL);
  });

  beforeEach(async () => {
    // Clean database before each test
    await db.query('TRUNCATE users CASCADE');
  });

  afterAll(async () => {
    await db.disconnect();
  });

  it('creates user', async () => {
    const user = await userRepo.create({ email: 'test@example.com' });
    expect(user.id).toBeDefined();
  });
});
```

### API Mocking Isolation

```typescript
describe('ProductList', () => {
  // Reset handlers after each test
  afterEach(() => server.resetHandlers());

  it('shows products from API', async () => {
    // Default handler returns products
    render(<ProductList />);
    await expect(screen.findByText('Widget')).resolves.toBeInTheDocument();
  });

  it('shows error on API failure', async () => {
    // Override handler for this test only
    server.use(
      rest.get('/api/products', (req, res, ctx) =>
        res(ctx.status(500))
      )
    );

    render(<ProductList />);
    await expect(screen.findByText('Error')).resolves.toBeInTheDocument();
  });

  it('shows products again', async () => {
    // Back to default handler (server.resetHandlers ran)
    render(<ProductList />);
    await expect(screen.findByText('Widget')).resolves.toBeInTheDocument();
  });
});
```

### Isolation Checklist

| Aspect | Solution |
|--------|----------|
| Global state | Reset in beforeEach |
| Timers | jest.useFakeTimers() + jest.useRealTimers() |
| DOM | RTL's cleanup (automatic) |
| Database | Truncate tables or use transactions |
| API mocks | server.resetHandlers() |
| File system | Use temp directories, clean up in afterEach |
| Environment vars | Restore in afterEach |

---

## Handling Flaky Tests

Flaky tests pass and fail intermittently without code changes.

### Common Causes and Fixes

**1. Timing Issues**

```typescript
// Flaky - race condition
it('shows loading then data', () => {
  render(<UserProfile />);
  expect(screen.getByText('Loading')).toBeInTheDocument();
  expect(screen.getByText('John')).toBeInTheDocument(); // May fail
});

// Fixed - proper async handling
it('shows loading then data', async () => {
  render(<UserProfile />);
  expect(screen.getByText('Loading')).toBeInTheDocument();
  await waitFor(() => {
    expect(screen.getByText('John')).toBeInTheDocument();
  });
});
```

**2. Non-deterministic Data**

```typescript
// Flaky - random data
it('sorts users alphabetically', () => {
  const users = [createUser(), createUser(), createUser()];
  // Names are random, order unpredictable
});

// Fixed - deterministic data
it('sorts users alphabetically', () => {
  const users = [
    createUser({ name: 'Charlie' }),
    createUser({ name: 'Alice' }),
    createUser({ name: 'Bob' }),
  ];
  const sorted = sortUsers(users);
  expect(sorted.map(u => u.name)).toEqual(['Alice', 'Bob', 'Charlie']);
});
```

**3. Test Order Dependencies**

```typescript
// Flaky - relies on previous test
describe('Counter', () => {
  const counter = new Counter(); // Shared instance!

  it('increments', () => {
    counter.increment();
    expect(counter.value).toBe(1);
  });

  it('starts at zero', () => {
    expect(counter.value).toBe(0); // Fails! Value is 1
  });
});

// Fixed - fresh instance per test
describe('Counter', () => {
  let counter: Counter;

  beforeEach(() => {
    counter = new Counter();
  });

  it('increments', () => {
    counter.increment();
    expect(counter.value).toBe(1);
  });

  it('starts at zero', () => {
    expect(counter.value).toBe(0); // Passes
  });
});
```

**4. Network/External Dependencies**

```typescript
// Flaky - real network call
it('fetches data', async () => {
  const data = await fetch('https://api.example.com/data');
  expect(data).toBeDefined();
});

// Fixed - mock the network
it('fetches data', async () => {
  server.use(
    rest.get('https://api.example.com/data', (req, res, ctx) =>
      res(ctx.json({ value: 42 }))
    )
  );

  const data = await fetchData();
  expect(data.value).toBe(42);
});
```

### Flaky Test Detection

```javascript
// jest.config.js
module.exports = {
  // Run each test multiple times to detect flakiness
  testEnvironment: 'jsdom',

  // Add reporters to track flaky tests
  reporters: [
    'default',
    ['jest-junit', { outputDirectory: './reports' }],
  ],
};

// Run tests multiple times
// npx jest --runInBand --testTimeout=10000 --repeat=5
```

### Quarantine Strategy

1. **Identify** - Track tests that fail randomly
2. **Quarantine** - Move to separate suite, run separately
3. **Fix** - Investigate and fix root cause
4. **Restore** - Move back to main suite

```typescript
// Temporarily skip flaky test
it.skip('flaky test to fix', () => {
  // TODO: Fix timing issue in #123
});

// Or run only when investigating
it.todo('investigate flaky behavior');
```

---

## Code Review for Testability

Questions to ask during code review to ensure testable code.

### Testability Checklist

**Functions and Methods:**
- [ ] Does it have a single responsibility?
- [ ] Are dependencies injected?
- [ ] Can it be tested without mocking internals?
- [ ] Does it return a value or have observable side effects?

**Components:**
- [ ] Are props descriptive and minimal?
- [ ] Can behavior be triggered via user events?
- [ ] Are loading/error states exposed?
- [ ] Can it be rendered without a full app context?

**State Management:**
- [ ] Is state minimal and derived where possible?
- [ ] Can state changes be triggered and observed?
- [ ] Are side effects separated from reducers?

### Review Comments

**Before:**
```typescript
// Hard to test - embedded dependency
function processPayment(order: Order) {
  const stripe = new Stripe(process.env.STRIPE_KEY);
  return stripe.charges.create({
    amount: order.total,
    currency: 'usd',
  });
}
```

**Review Comment:**
> Consider injecting the payment processor to improve testability:
> ```typescript
> function processPayment(order: Order, processor: PaymentProcessor) {
>   return processor.charge(order.total, 'usd');
> }
> ```
> This allows testing with a mock processor without hitting Stripe's API.

---

## Test Maintenance Strategies

Keep tests maintainable as the codebase evolves.

### Reducing Duplication

**Use helpers for common assertions:**

```typescript
// __tests__/helpers/assertions.ts
export function expectLoadingState(container: HTMLElement) {
  expect(within(container).getByRole('progressbar')).toBeInTheDocument();
}

export function expectErrorState(container: HTMLElement, message: string) {
  expect(within(container).getByRole('alert')).toHaveTextContent(message);
}

// Usage
it('shows loading state', () => {
  render(<DataList />);
  expectLoadingState(screen.getByTestId('data-list'));
});
```

**Use factory functions:**

```typescript
// Instead of repeating setup
function renderWithUser(ui: ReactElement, user = createUser()) {
  return {
    user,
    ...render(<AuthProvider user={user}>{ui}</AuthProvider>),
  };
}
```

### Updating Tests When Code Changes

**Scenario: Renaming a prop**

```typescript
// Old component
<Button onClick={handleClick} />

// New component
<Button onPress={handleClick} />

// Find and update all tests
// grep -r "onClick" __tests__/ --include="*.test.tsx"
```

**Scenario: Changing API response shape**

```typescript
// Update factory first
export function createUserResponse(overrides = {}) {
  return {
    user: {  // New nested structure
      id: '1',
      name: 'Test User',
      ...overrides,
    },
  };
}

// Tests automatically get new shape
```

### When to Delete Tests

- **Redundant coverage** - Multiple tests testing the same thing
- **Testing implementation** - Tests that break on refactor
- **Obsolete features** - Tests for removed functionality
- **Flaky beyond repair** - Tests that can't be stabilized

### Test Documentation

```typescript
/**
 * @group integration
 * @requires database
 *
 * Tests for the order processing workflow.
 * These tests require a running PostgreSQL instance.
 *
 * Setup: docker-compose up -d postgres
 */
describe('OrderProcessor', () => {
  /**
   * Verifies that orders with backordered items
   * are split into separate fulfillment batches.
   *
   * Related: JIRA-1234
   */
  it('splits orders with backordered items', () => {});
});
```

---

## Debugging Failed Tests

Techniques for investigating test failures.

### Jest Debugging

**Run single test:**
```bash
# By name pattern
npx jest -t "should validate email"

# By file
npx jest src/utils/__tests__/validation.test.ts

# Watch mode for iteration
npx jest --watch
```

**Debug with Node inspector:**
```bash
node --inspect-brk node_modules/.bin/jest --runInBand
# Open chrome://inspect in Chrome
```

**Verbose output:**
```bash
npx jest --verbose --no-coverage
```

### React Testing Library Debugging

```typescript
it('renders user profile', async () => {
  render(<UserProfile userId="123" />);

  // Print current DOM
  screen.debug();

  // Print specific element
  screen.debug(screen.getByRole('heading'));

  // Log accessible roles
  screen.logTestingPlaygroundURL(); // Opens interactive playground

  // Check what queries would match
  const element = screen.getByRole('button');
  console.log(prettyDOM(element));
});
```

### Playwright Debugging

```bash
# Debug mode - opens browser with inspector
npx playwright test --debug

# UI mode - visual test runner
npx playwright test --ui

# Headed mode - see browser
npx playwright test --headed

# Trace viewer after failure
npx playwright show-trace trace.zip
```

**Pause in test:**
```typescript
test('debug this', async ({ page }) => {
  await page.goto('/');
  await page.pause(); // Opens inspector
  await page.click('button');
});
```

### Common Failure Patterns

| Symptom | Likely Cause | Debug Approach |
|---------|--------------|----------------|
| "Unable to find element" | Wrong query or element not rendered | `screen.debug()`, check async |
| "Expected X, received Y" | Logic error or stale mock | Log intermediate values |
| "Timeout exceeded" | Slow async or missing await | Increase timeout, check promises |
| "Cannot read property of undefined" | Missing mock or setup | Check beforeEach, mock returns |
| Passes locally, fails in CI | Environment difference | Check env vars, timing |

### Investigating Flaky Failures

```typescript
// Add logging for intermittent failures
it('processes order', async () => {
  console.log('Test started at', Date.now());

  const order = await createOrder();
  console.log('Order created:', order.id);

  const result = await processOrder(order);
  console.log('Process result:', result);

  expect(result.status).toBe('completed');
});
```

---

## Quality Metrics and KPIs

Measure test suite effectiveness and track quality improvements.

### Key Metrics

**Coverage Metrics:**

| Metric | Target | Measurement |
|--------|--------|-------------|
| Line coverage | 80% | `jest --coverage` |
| Branch coverage | 75% | `jest --coverage` |
| Function coverage | 80% | `jest --coverage` |
| Critical path coverage | 95% | Custom tracking |

**Test Suite Health:**

| Metric | Target | Measurement |
|--------|--------|-------------|
| Test pass rate | 100% | CI reports |
| Flaky test rate | <1% | Track retries |
| Test execution time | <5 min | CI timing |
| Tests per component | ≥3 | Test count / components |

**Defect Metrics:**

| Metric | Target | Measurement |
|--------|--------|-------------|
| Defects found in testing | >70% | Bug tracking |
| Defects escaped to prod | <10% | Production bugs |
| Regression rate | <5% | Bugs reintroduced |
| Mean time to detect | <1 day | Bug timestamps |

### Dashboard Example

```typescript
// scripts/test-metrics.ts
import { readCoverageReport } from './utils';

const coverage = readCoverageReport('./coverage/coverage-summary.json');
const testResults = readTestReport('./reports/jest-results.json');

const metrics = {
  coverage: {
    lines: coverage.total.lines.pct,
    branches: coverage.total.branches.pct,
    functions: coverage.total.functions.pct,
  },
  tests: {
    total: testResults.numTotalTests,
    passed: testResults.numPassedTests,
    failed: testResults.numFailedTests,
    passRate: (testResults.numPassedTests / testResults.numTotalTests) * 100,
  },
  execution: {
    duration: testResults.testResults.reduce((sum, r) => sum + r.duration, 0),
  },
};

console.log('Test Metrics:', JSON.stringify(metrics, null, 2));
```

### CI Quality Gates

```yaml
# .github/workflows/quality.yml
name: Quality Gates

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4

      - run: npm ci
      - run: npm test -- --coverage

      # Coverage gate
      - name: Check coverage
        run: |
          coverage=$(jq '.total.lines.pct' coverage/coverage-summary.json)
          if (( $(echo "$coverage < 80" | bc -l) )); then
            echo "Coverage $coverage% is below 80% threshold"
            exit 1
          fi

      # Test count gate
      - name: Check test count
        run: |
          tests=$(jq '.numTotalTests' reports/test-results.json)
          if [ "$tests" -lt 100 ]; then
            echo "Test count $tests is below minimum of 100"
            exit 1
          fi
```

### Trend Tracking

Track metrics over time to identify trends:

```typescript
// Weekly metrics collection
{
  "week": "2024-W03",
  "coverage": {
    "lines": 82.4,
    "branches": 76.1,
    "trend": "+1.2%"  // vs previous week
  },
  "tests": {
    "total": 487,
    "new": 23,
    "removed": 5
  },
  "execution": {
    "avgDuration": 245,  // seconds
    "trend": "-12s"
  },
  "flaky": {
    "count": 3,
    "rate": 0.6
  }
}
```

---

## Summary

1. **Write testable code** - Inject dependencies, use pure functions, separate concerns
2. **Name tests clearly** - Describe behavior, not implementation
3. **Follow AAA pattern** - Arrange, Act, Assert for clear structure
4. **Isolate tests** - Fresh state, reset mocks, no dependencies between tests
5. **Fix flaky tests** - Handle timing, use deterministic data, mock externals
6. **Review for testability** - Check during code review, not after
7. **Maintain tests** - Reduce duplication, update with code changes
8. **Debug systematically** - Use debug tools, log strategically
9. **Measure quality** - Track coverage, pass rate, execution time
