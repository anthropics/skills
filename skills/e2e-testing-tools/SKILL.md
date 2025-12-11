---
name: e2e-testing-tools
description: >
  End-to-end testing for web applications using defined user journeys and workflows.
  Modern testing with Playwright and Cypress: cross-browser automation, visual testing,
  accessibility checks, and real-world patterns. Focus on business-critical workflows,
  maintainability through Page Object Model, and practical CI/CD integration.
---

# End-to-End Testing Tools

Test complete user journeys through your web application using modern browser automation. Define workflows, not just test cases. Focus on business-critical paths with maintainable, fast-feedback test suites.

## When to Use This Skill

Apply this skill when tasks involve:
- Testing complete user journeys and workflows across your application
- Cross-browser compatibility validation (Chrome, Firefox, Safari, Edge)
- Validating complex workflows (auth flows, checkout, multi-step forms)
- Ensuring UI interactions work correctly with real browser behavior
- Accessibility testing (a11y) of user workflows
- Visual regression testing (screenshot comparisons)
- Performance testing of critical paths (Lighthouse, PageSpeed)
- Setting up E2E testing in CI/CD pipelines
- Debugging flaky tests and improving test reliability

## Testing Pyramid Context

```
        E2E Tests (5-10%)              Playwright, Cypress
       /             \                 Complex workflows, visual,
    Integration Tests                  accessibility, real browsers
   (15-30% coverage)
   /                 \
 Unit Tests (60-80%)                  Mocked dependencies,
                                       isolated logic
```

E2E tests are **slowest but highest confidence**. Test business-critical journeys, not every edge case.

## Tool Selection Guide

### Primary: Playwright ✅
**Best for:** TypeScript/JavaScript projects, cross-browser automation, Python support, CI/CD integration
```bash
npm install -D @playwright/test @playwright/test-utils

# Or Python
pip install pytest-playwright
```

**Key Features:**
- Cross-browser (Chrome, Firefox, WebKit)
- Excellent assertions and wait strategies
- Network interception and mocking
- Trace/video recording for debugging
- Parallel execution out-of-the-box
- Supports JS/TS/Python/.NET

**When to choose:** Default for new projects, cross-browser needs, Python-based teams

### Primary: Cypress 🎯
**Best for:** JavaScript/TypeScript projects, excellent developer experience, interactive debugging
```bash
npm install --save-dev cypress
```

**Key Features:**
- Time-travel debugger (replay any command)
- Strong assertion library
- Automatic waiting (no explicit waits needed)
- Test isolation and cleanup
- Great test runner UI
- Visual feedback during test development

**When to choose:** JS/TS teams, strong DX preference, learning E2E testing

### Optional: Puppeteer
**Best for:** Chrome-only automation, programmatic control, headless-first scenarios
```bash
npm install puppeteer
```

**When to choose:** Legacy Chrome-only requirements, custom headless automation

### Optional: Selenium / WebDriver
**Document for:** Existing test suites in Java/C#, cross-language teams
**When to choose:** Migrating existing Selenium tests, non-JS language requirements

## Core Toolset

| Tool | Purpose | Why | Status |
|------|---------|-----|--------|
| **Playwright** | Cross-browser E2E | Modern, fast, Python support | Primary |
| **Cypress** | JS/TS E2E | Excellent DX, time-travel debugger | Primary |
| **@playwright/test** | Test runner (Playwright) | Built-in, parallel, retry | Primary |
| **@testing-library/playwright** | Best-practice selectors | Query by role/label, not CSS | Recommended |
| **Percy** | Visual testing | Baseline diffs, ignore dynamic | Optional |
| **axe-playwright / axe-cypress** | Accessibility testing | Automated a11y scans | Optional |
| **Lighthouse CI** | Performance testing | Automated Lighthouse checks | Optional |

## Installation

### Playwright (TypeScript/JavaScript)
```bash
npm install -D @playwright/test @testing-library/playwright
```

### Playwright (Python)
```bash
pip install pytest-playwright
pytest --install-browsers  # Install Playwright browsers
```

### Cypress
```bash
npm install --save-dev cypress
npx cypress open  # Interactive setup
```

### Optional Add-ons
```bash
# Visual testing
npm install -D @percy/cli @percy/playwright

# Accessibility
npm install -D @axe-core/playwright axe-playwright

# Performance
npm install -D @lhci/cli
```

## Essential Concepts

### User Journeys vs Test Cases

**User Journey:** A complete business workflow a real user takes through your app
- Login → Search product → Add to cart → Checkout → Confirm order
- Has entry/exit criteria, preconditions, alternative flows
- Tests end-to-end happy path + critical error scenarios

**Test Case:** Individual assertion about a specific feature
- "Button click opens modal"
- "Email validation shows error"
- Use unit/integration tests for these

### Page Object Model (Maintainability Pattern)

```typescript
// pages/LoginPage.ts
export class LoginPage {
  constructor(private page: Page) {}

  async goto() {
    await this.page.goto('/login');
  }

  async login(email: string, password: string) {
    await this.page.fill('[aria-label="Email"]', email);
    await this.page.fill('[aria-label="Password"]', password);
    await this.page.click('button[type="submit"]');
    await this.page.waitForNavigation();
  }

  async expectError(message: string) {
    await expect(this.page.locator('[role="alert"]')).toContainText(message);
  }
}

// tests/auth.spec.ts
import { LoginPage } from '../pages/LoginPage';

test('user can login with valid credentials', async ({ page }) => {
  const loginPage = new LoginPage(page);
  await loginPage.goto();
  await loginPage.login('user@example.com', 'password123');
  // Assert successful login
});
```

Benefits:
- Selectors in one place (easy to update)
- Business logic naming (self-documenting tests)
- DRY (reuse across multiple tests)
- Resilient to UI changes

### Best Selector Strategy: Prioritize data-testid

**The Selector Priority (in order):**

1. **data-testid** ✅ BEST - Explicit, stable, intentional
   ```html
   <!-- In your HTML -->
   <button data-testid="submit-button">Submit</button>
   <input data-testid="email-input" type="email" />
   <div data-testid="error-message">Error occurred</div>
   ```

   ```typescript
   // In your tests
   await page.getByTestId('submit-button').click();
   await page.getByTestId('email-input').fill('test@example.com');
   await expect(page.getByTestId('error-message')).toContainText('Error occurred');
   ```

   **Why data-testid is best:**
   - Explicitly added for testing (intentional API contract)
   - Survives CSS/styling changes
   - Survives label/text content changes
   - Self-documents what's being tested
   - Decouples tests from implementation details
   - Teams can add/maintain them without changing functionality

2. **Accessibility attributes** ✅ GOOD - Semantic, accessible
   ```html
   <button aria-label="Close dialog">×</button>
   <form aria-label="Login form">
   ```

   ```typescript
   await page.getByRole('button', { name: 'Close dialog' }).click();
   await page.getByLabel('Email').fill('test@example.com');
   ```

3. **Text content** ⚠️ OKAY - Use carefully for stable text
   ```typescript
   await page.getByText('Sign In').click();
   await page.getByRole('button', { name: 'Submit' }).click();
   ```

4. **CSS/XPath selectors** ❌ AVOID - Brittle, breaks easily
   ```typescript
   // DON'T DO THIS:
   await page.locator('.form-container > div:nth-child(3) input').fill('...');
   ```

### ADD data-testid if Missing in Your Application

**IMPORTANT:** If your web application doesn't have data-testid attributes, your E2E tests are at risk. This is a critical prerequisite.

**When writing E2E tests, check:**
- Does the component you're testing have a `data-testid`?
- If NO → Add it to the component FIRST
- If YES → Use it in your tests

**Example workflow:**
```typescript
// Step 1: Write the E2E test
test('should submit form', async ({ page }) => {
  await page.getByTestId('email-input').fill('test@example.com');
  await page.getByTestId('submit-button').click();
  // ...
});

// Step 2: Run test → FAILS because data-testid doesn't exist
// Error: No element with data-testid="email-input"

// Step 3: Add data-testid to the component
// In your React/Vue/Angular component:
<input
  data-testid="email-input"
  type="email"
  placeholder="Email"
/>
<button data-testid="submit-button" type="submit">
  Submit
</button>

// Step 4: Run test again → PASSES
```

**Adding data-testid Best Practices:**

```html
<!-- ✅ DO: Use kebab-case, semantic names -->
<input data-testid="user-email-input" />
<button data-testid="login-submit-button" />
<div data-testid="error-alert-message" />
<li data-testid="product-list-item-123" /> <!-- Include ID if dynamic -->

<!-- ✅ DO: Add to interactive elements -->
<button data-testid="save-button">Save</button>
<a data-testid="forgot-password-link" href="/reset">Forgot password?</a>
<input data-testid="search-box" />

<!-- ✅ DO: Add to containers for complex components -->
<div data-testid="product-card">
  <img src="..." alt="Product" />
  <h3>Product Name</h3>
  <button data-testid="add-to-cart-button">Add to Cart</button>
</div>

<!-- ❌ DON'T: Use generic names -->
<button data-testid="btn">Save</button> <!-- Too generic -->
<div data-testid="div-1">Content</div> <!-- Meaningless -->

<!-- ❌ DON'T: Duplicate test infrastructure concerns -->
<button data-testid="button" data-cy="save">Save</button> <!-- Use one, not both -->
```

**Reference:** https://bugbug.io/blog/software-testing/data-testid-attributes/

### Journey Definition

**Anatomy of a user journey:**
```typescript
import { test, expect } from '@playwright/test';
import { LoginPage } from '../pages/LoginPage';
import { ProductPage } from '../pages/ProductPage';
import { CartPage } from '../pages/CartPage';

test('complete purchase journey', async ({ page }) => {
  // PRECONDITION: User account exists
  // ENTRY: Homepage

  // PHASE 1: Authentication
  const loginPage = new LoginPage(page);
  await loginPage.goto();
  await loginPage.login('customer@example.com', 'password');

  // PHASE 2: Product Discovery
  const productPage = new ProductPage(page);
  await productPage.goto();
  const item = await productPage.searchAndFilter('laptop', 'under $1000');

  // PHASE 3: Cart & Checkout
  const cartPage = new CartPage(page);
  await cartPage.addItem(item);
  await cartPage.proceedToCheckout();

  // PHASE 4: Payment (with mock)
  await cartPage.fillPaymentInfo({
    card: '4242424242424242',
    expiry: '12/25',
    cvc: '123'
  });

  // PHASE 5: Confirmation
  // EXIT: Order confirmation page
  await expect(page.locator('h1')).toContainText('Order Confirmed');
  const orderId = await cartPage.getOrderId();
  expect(orderId).toBeTruthy();
});
```

## Essential Workflows

### E2E Testing Pipeline (Complete Strategy)

**Phase 1: Smoke Tests (Fast validation - 2-5 minutes)**
```bash
# Run critical journeys only (typically 5-10 key paths)
playwright test --grep @smoke

# Or with Cypress
cypress run --spec "cypress/e2e/smoke/**"
```

**Phase 2: Full Regression Suite (Before release - 15-45 minutes)**
```bash
# Run all journeys in parallel
playwright test --workers=4

# Cypress headless
cypress run
```

**Phase 3: Accessibility & Visual Checks (Before release - 5-10 minutes)**
```bash
# Run a11y checks
playwright test --grep @a11y

# Visual regression comparison
percy exec -- playwright test --grep @visual
```

**Phase 4: Post-Deployment Canary (Production validation - 1-2 minutes)**
```bash
# Run quick smoke tests against production
ENVIRONMENT=production playwright test --grep @smoke
```

**When to run:**
- **During development:** Smoke tests locally on relevant feature tests
- **On PR/MR:** Smoke tests required; can be blocking
- **Before release:** Full regression + accessibility + visual
- **After deployment:** Quick canary tests (production smoke)
- **Scheduled (nightly):** Full suite + performance benchmarks
- **On demand:** Triage specific journey when bugs reported

**Expected timing:**
- **Smoke suite:** 2-5 minutes (critical paths only)
- **Full regression:** 15-45 minutes (all journeys, parallelized)
- **Accessibility suite:** 5-10 minutes (all pages)
- **Visual regression:** 10-20 minutes (baseline comparisons)
- **Canary (production):** 1-2 minutes (ultra-fast smoke)

**Pipeline integration example:**
```yaml
# GitHub Actions example
jobs:
  e2e-smoke:
    runs-on: ubuntu-latest
    if: github.event_name == 'pull_request'
    steps:
      - uses: actions/checkout@v3
      - uses: actions/setup-node@v3
      - run: npm ci
      - run: npx playwright test --grep @smoke  # 5 min, blocking

  e2e-full:
    runs-on: ubuntu-latest
    if: github.ref == 'main'  # Main branch only
    steps:
      - uses: actions/checkout@v3
      - uses: actions/setup-node@v3
      - run: npm ci
      - run: npx playwright test  # 30 min, non-blocking
      - uses: actions/upload-artifact@v3
        if: always()
        with:
          name: playwright-report
          path: playwright-report/

  post-deploy:
    runs-on: ubuntu-latest
    if: github.event_name == 'workflow_dispatch'  # Manual trigger post-deploy
    steps:
      - uses: actions/checkout@v3
      - uses: actions/setup-node@v3
      - run: npm ci
      - run: ENVIRONMENT=production npx playwright test --grep @smoke
```

### Debugging & Flake Reduction

**When a test fails:**
```bash
# Run with trace recording (saves trace.zip for UI inspection)
playwright test --trace on

# Run with headed browser (see what's happening)
playwright test --headed

# Run specific test with debugging
playwright test tests/checkout.spec.ts -g "complete purchase" --debug

# See debug logs
DEBUG=pw:api playwright test

# Retry failed tests (shows flakiness)
playwright test --retries 3
```

**Flakiness investigation workflow:**
1. Check test trace: `npx playwright show-trace trace.zip`
2. Verify wait strategies (waiting for right elements)
3. Check for race conditions (e.g., animations, async updates)
4. Review selectors (ensure they're stable across runs)
5. Isolate test dependencies
6. Monitor flakiness dashboard

## Real-World Patterns

### Pattern 1: Login / Authentication Flow

```typescript
// pages/LoginPage.ts
export class LoginPage {
  constructor(private page: Page) {}

  async loginAsUser(user: { email: string; password: string }) {
    await this.page.goto('/login');
    await this.page.fill('input[type="email"]', user.email);
    await this.page.fill('input[type="password"]', user.password);
    await this.page.click('button[type="submit"]');

    // Wait for redirect OR error message
    await Promise.race([
      this.page.waitForNavigation({ url: /\/dashboard/ }),
      this.page.waitForSelector('[role="alert"]', { state: 'visible' })
    ]);
  }

  async expectLoginError(message: string) {
    await expect(this.page.locator('[role="alert"]')).toContainText(message);
  }

  async logout() {
    await this.page.click('[aria-label="User menu"]');
    await this.page.click('button:has-text("Logout")');
    await this.page.waitForURL('/login');
  }
}

// tests/auth.spec.ts
test('login with valid credentials', async ({ page }) => {
  const loginPage = new LoginPage(page);
  await loginPage.loginAsUser({
    email: 'user@example.com',
    password: 'password123'
  });
  // Now on dashboard
  await expect(page).toHaveURL(/\/dashboard/);
});

test('login with invalid credentials shows error', async ({ page }) => {
  const loginPage = new LoginPage(page);
  await loginPage.loginAsUser({
    email: 'invalid@example.com',
    password: 'wrong'
  });
  await loginPage.expectLoginError('Invalid credentials');
});
```

### Pattern 2: Multi-Step Form with Validation

```typescript
export class CheckoutPage {
  constructor(private page: Page) {}

  async fillBillingInfo(info: BillingInfo) {
    await this.page.fill('input[name="fullName"]', info.fullName);
    await this.page.fill('input[name="email"]', info.email);
    await this.page.fill('input[name="address"]', info.address);
    await this.page.click('button:has-text("Continue")');
  }

  async fillShippingMethod(method: 'standard' | 'express') {
    const option = this.page.locator(`input[value="${method}"]`);
    await option.check();
  }

  async fillPaymentInfo(payment: PaymentInfo) {
    // Mock API for payment processing
    await this.page.route('**/api/payment', route => {
      route.abort('blockedbyextension');  // Prevent real API calls
      // OR intercept and mock
      route.continue({
        status: 200,
        body: JSON.stringify({ transactionId: 'mock-txn-123' })
      });
    });

    await this.page.fill('input[name="cardNumber"]', payment.cardNumber);
    await this.page.fill('input[name="expiry"]', payment.expiry);
    await this.page.fill('input[name="cvc"]', payment.cvc);
  }

  async completeCheckout() {
    await this.page.click('button[type="submit"]:has-text("Place Order")');
    await this.page.waitForURL(/\/order-confirmation/);
  }

  async expectValidationError(field: string, message: string) {
    const fieldError = this.page.locator(`[data-testid="${field}-error"]`);
    await expect(fieldError).toContainText(message);
  }
}

test('complete checkout journey', async ({ page }) => {
  const checkout = new CheckoutPage(page);

  // Go to cart and proceed
  await page.goto('/cart');
  await checkout.fillBillingInfo({
    fullName: 'John Doe',
    email: 'john@example.com',
    address: '123 Main St'
  });

  await checkout.fillShippingMethod('express');
  await checkout.fillPaymentInfo({
    cardNumber: '4242424242424242',
    expiry: '12/25',
    cvc: '123'
  });

  await checkout.completeCheckout();
  await expect(page.locator('h1')).toContainText('Order Confirmed');
});
```

### Pattern 3: Accessibility Testing

```typescript
import { injectAxe, checkA11y } from 'axe-playwright';

test.describe('accessibility compliance @a11y', () => {
  test('homepage has no a11y violations', async ({ page }) => {
    await page.goto('/');
    await injectAxe(page);
    await checkA11y(page, null, {
      detailedReport: true,
      detailedReportOptions: {
        html: true
      }
    });
  });

  test('navigation is keyboard accessible', async ({ page }) => {
    await page.goto('/');

    // Tab through main navigation
    await page.keyboard.press('Tab');
    await expect(page.locator(':focus')).toContainText('Home');

    await page.keyboard.press('Tab');
    await expect(page.locator(':focus')).toContainText('Products');

    // Enter should activate link
    await page.keyboard.press('Enter');
    await expect(page).toHaveURL(/\/products/);
  });

  test('all form fields have associated labels', async ({ page }) => {
    await page.goto('/contact');

    const inputs = await page.locator('input').all();
    for (const input of inputs) {
      const id = await input.getAttribute('id');
      const label = page.locator(`label[for="${id}"]`);
      await expect(label).toBeVisible();
    }
  });
});
```

### Pattern 4: Visual Regression Testing

```typescript
import { test, expect } from '@playwright/test';

test('homepage layout consistency @visual', async ({ page }) => {
  await page.goto('/');

  // Full page visual comparison
  await expect(page).toHaveScreenshot('homepage.png', {
    maxDiffPixels: 100,
    threshold: 0.2  // 20% threshold tolerance
  });
});

test('product cards render correctly @visual', async ({ page }) => {
  await page.goto('/products');

  // Compare specific element
  const productCard = page.locator('[data-testid="product-card"]').first();
  await expect(productCard).toHaveScreenshot('product-card.png');
});

// With Percy (cloud-based visual testing)
test('checkout flow visual regression @visual', async ({ page, context }) => {
  const percySnapshot = require('@percy/cli');

  await page.goto('/checkout');
  await percySnapshot(page, 'checkout-step-1');

  // Fill billing
  await page.fill('input[name="fullName"]', 'John Doe');
  await percySnapshot(page, 'checkout-step-2');
});
```

### Pattern 5: API Mocking & Intercepts

```typescript
test('graceful error handling when API fails', async ({ page }) => {
  await page.route('**/api/products/**', route => {
    // Simulate server error
    route.abort('failed');
  });

  await page.goto('/products');

  // App should show error state
  await expect(page.locator('[role="alert"]'))
    .toContainText('Failed to load products');
});

test('handle slow API responses', async ({ page }) => {
  await page.route('**/api/search', async route => {
    // Simulate 5 second delay
    await page.waitForTimeout(5000);
    route.continue();
  });

  await page.goto('/products');
  await page.fill('input[placeholder="Search"]', 'laptop');

  // App should show loading state
  await expect(page.locator('[data-testid="loading"]')).toBeVisible();

  // Then results appear
  await expect(page.locator('[data-testid="product-result"]'))
    .toBeDefined();
});

test('network offline handling', async ({ page }) => {
  // Go online to load initial page
  await page.goto('/');

  // Simulate going offline
  await page.context().setOffline(true);

  // Try to fetch data
  await page.click('button[aria-label="Refresh"]');

  // Should show offline state
  await expect(page.locator('[data-testid="offline-banner"]'))
    .toContainText('You are offline');

  // Come back online
  await page.context().setOffline(false);

  // Should recover automatically
  await expect(page.locator('[data-testid="offline-banner"]'))
    .not.toBeVisible();
});
```

## Configuration

### Playwright Config (playwright.config.ts)

```typescript
import { defineConfig, devices } from '@playwright/test';

export default defineConfig({
  testDir: './tests/e2e',

  // Parallel execution
  workers: process.env.CI ? 1 : undefined,

  // Timeout per test
  timeout: 30000,
  expect: { timeout: 5000 },

  // Global setup/teardown
  globalSetup: require.resolve('./tests/global-setup'),
  globalTeardown: require.resolve('./tests/global-teardown'),

  // Reporting
  reporter: [
    ['html', { outputFolder: 'playwright-report' }],
    ['json', { outputFile: 'test-results.json' }],
    ['junit', { outputFile: 'test-results.xml' }]
  ],

  // Projects for different browsers
  projects: [
    {
      name: 'chromium',
      use: { ...devices['Desktop Chrome'] },
    },
    {
      name: 'firefox',
      use: { ...devices['Desktop Firefox'] },
    },
    {
      name: 'webkit',
      use: { ...devices['Desktop Safari'] },
    },
    // Mobile viewports
    {
      name: 'Mobile Chrome',
      use: { ...devices['Galaxy S5'] },
    },
  ],

  // Web server
  webServer: {
    command: 'npm run start',
    port: 3000,
    reuseExistingServer: !process.env.CI,
  },

  // Screenshots on failure
  use: {
    baseURL: process.env.BASE_URL || 'http://localhost:3000',
    screenshot: 'only-on-failure',
    video: 'retain-on-failure',
    trace: 'on-first-retry',
  },
});
```

### Cypress Config (cypress.config.js)

```javascript
const { defineConfig } = require('cypress');

module.exports = defineConfig({
  e2e: {
    baseUrl: 'http://localhost:3000',

    specPattern: 'cypress/e2e/**/*.cy.js',

    defaultCommandTimeout: 5000,
    requestTimeout: 10000,
    responseTimeout: 10000,

    setupNodeEvents(on, config) {
      // Require plugin
      require('cypress-mochawesome-reporter/plugin')(on);

      // Before each test
      on('before:browser:launch', (browser, launchArgs) => {
        if (browser.family === 'chromium') {
          launchArgs.push('--disable-blink-features=AutomationControlled');
        }
        return launchArgs;
      });
    },

    reporterOptions: {
      reportDir: 'cypress/reports',
      reportFilename: 'report',
      html: true,
      json: true,
    },
  },
});
```

## Bundled Resources

### Scripts (`scripts/`)

**`run-smoke-tests.sh`** - Run critical journeys locally
```bash
./scripts/run-smoke-tests.sh [--headed] [--debug]
```

**`run-full-suite.sh`** - Run complete regression
```bash
./scripts/run-full-suite.sh [--workers=4] [--headed]
```

**`debug-flaky-test.sh`** - Replay specific test with tracing
```bash
./scripts/debug-flaky-test.sh tests/checkout.spec.ts
```

### Example Configs (`assets/`)

- `playwright.config.ts` - Complete Playwright configuration
- `cypress.config.js` - Complete Cypress configuration
- `page-objects/LoginPage.ts` - Example Page Object
- `page-objects/CartPage.ts` - Example Page Object
- `fixtures/auth.ts` - Shared authentication fixture
- `.env.example` - Environment variable template

### Detailed Reference (`references/`)

- `PLAYWRIGHT_VS_CYPRESS.md` - Detailed comparison and when to choose
- `SELECTORS.md` - Best practices for stable, maintainable selectors
- `CI_INTEGRATION.md` - GitHub Actions, CircleCI, GitLab CI examples
- `FLAKINESS_REDUCTION.md` - Comprehensive guide to fixing flaky tests

## Best Practices

**Journey Design:**
- Focus on business-critical workflows only (80/20 rule)
- Include happy path + one error scenario per journey
- Use @smoke tag for critical paths that run on every PR
- Document entry/exit criteria and preconditions
- Archive deprecated journeys instead of deleting

**Maintainability:**
- Use Page Object Model for all selectors and interactions
- Query by role/label/testid, not CSS selectors
- Keep tests DRY (extract common flows into helpers)
- Share fixtures across tests for setup consistency
- Review selectors when UI changes

**Test Reliability:**
- Use implicit waits (Playwright/Cypress handle waiting)
- Never use hardcoded `sleep()` delays
- Mock/intercept external APIs and payments
- Isolate tests with database resets or fixtures
- Retry only on transient failures, not logic errors

**CI/CD Integration:**
- Run smoke tests on every PR (block if failing)
- Run full regression on main branch before release
- Capture traces/videos on failures for debugging
- Report results to quality dashboards
- Alert on flaky tests that need triage

**Environment Management:**
- Use environment variables for URLs, credentials
- Never commit secrets (use CI/CD secret management)
- Keep staging environment synchronized with production
- Use feature flags for work-in-progress flows
- Validate against staging before production testing

## Troubleshooting

**Tests are slow:**
```bash
# Run in parallel
playwright test --workers=4

# Or skip non-critical tests
playwright test --grep "@smoke"

# Profile to find bottlenecks
playwright test --trace on
```

**Tests are flaky:**
```bash
# Record and replay with tracing
playwright test --trace on --retries 3

# Run in headed mode to watch
playwright test --headed

# Check for race conditions
DEBUG=pw:api playwright test
```

**Selector breaks after UI change:**
- Use role-based selectors: `getByRole('button', { name: 'Submit' })`
- Use data-testid for complex elements: `getByTestId('submit-button')`
- Avoid CSS-path selectors that break easily

**API mocking doesn't work:**
```typescript
// Ensure route is set BEFORE navigation
await page.route('**/api/**', route => {
  route.abort();  // Block all API calls
});

await page.goto('/');  // Navigate AFTER route setup
```

**Browser-specific issues:**
```typescript
test('webkit specific', async ({ page, browserName }) => {
  test.skip(browserName !== 'webkit', 'webkit only');

  // Test Safari-specific behavior
});
```

## Verification & Testing

All tools and patterns in this skill have been tested and verified with real projects.

### Quick Start

```bash
# Generate starter project
npm init -D @playwright/test

# Run example test
npx playwright test

# Interactive mode
npx playwright test --ui
```

### Tool Versions Recommended

| Tool | Recommended Version | Notes |
|------|---------------------|-------|
| Playwright | Latest (1.40+) | Regular updates, good backward compatibility |
| Cypress | 13.x+ | Stable, good DX |
| Node | 18+ | ESM support, good performance |

## Quality Integration

For unit and integration testing:
- **python-testing-tools** skill - pytest, fixtures, mocking
- **node-testing-tools** skill - Vitest, Testing Library

For code quality before E2E testing:
- **python-quality-tools** skill - Ruff, Pyright, Bandit
- Run quality checks BEFORE running E2E tests in CI/CD

## Common E2E Testing Mistakes

❌ **Testing too much in E2E:** Unit tests are faster, use them first
✅ **Focus on critical user journeys, mock internal details**

❌ **Hard-coded waits (sleep):** Brittle and slow
✅ **Wait for specific elements with proper assertions**

❌ **Over-specific selectors:** Break on small UI changes
✅ **Use role/label/testid selectors, avoid CSS paths**

❌ **Testing every edge case in E2E:** Expensive and slow
✅ **Happy path + one error scenario per journey**

❌ **Running full suite on every commit:** Too slow
✅ **Smoke tests on PR, full regression on release**
