# Playwright vs Cypress: Detailed Comparison

## At a Glance

| Feature | Playwright | Cypress |
|---------|-----------|---------|
| **Primary Language** | TypeScript/JavaScript | JavaScript |
| **Browser Support** | Chrome, Firefox, WebKit, Edge | Chrome, Firefox, Edge, Safari (beta) |
| **Python Support** | ✅ Full | ❌ No |
| **Cross-browser** | ✅ True multi-browser | ⚠️ Separate instances |
| **Speed** | ⚡ Very Fast | ⚡ Fast |
| **DX (Developer Experience)** | 📊 Good tooling | 🎯 Excellent |
| **Time-Travel Debugging** | ⚠️ Limited | ✅ Excellent |
| **API Mocking** | ✅ Native | ⚠️ Plugin-based |
| **Parallel Execution** | ✅ Built-in | ⚠️ Requires plugins |
| **CI/CD Integration** | ✅ Excellent | ✅ Excellent |
| **Mobile Testing** | ✅ Mobile emulation | ❌ Limited |
| **Cost of Tools** | Free & Open Source | Free & Open Source (premium cloud) |

## Playwright

### When to Choose Playwright

✅ **Pick Playwright if:**
- You need cross-browser testing (Chrome, Firefox, Safari)
- Your team uses Python or C# alongside JavaScript
- You need to scale to parallel workers across multiple machines
- You want built-in API mocking and network interception
- You need mobile/tablet emulation
- You want to test multiple browser contexts in parallel
- You prefer a modern async-first architecture

### Strengths

**1. True Cross-Browser Support**
```typescript
// Single test runs in Chrome, Firefox, WebKit
export const chromiumConfig = {
  name: 'chromium',
  use: { ...devices['Desktop Chrome'] },
};
```

**2. Python Support** (Unique!)
```python
# Same test written in Python
from playwright.sync_api import sync_playwright

with sync_playwright() as p:
    browser = p.chromium.launch()
    page = browser.new_page()
    page.goto("https://example.com")
    page.click("button")
```

**3. Network Interception (Powerful)**
```typescript
// Mock any API call
await page.route('**/api/**', route => {
  route.abort('failed');  // Simulate network failure
  // OR
  route.continue({
    status: 200,
    body: JSON.stringify({ /* mock data */ })
  });
});
```

**4. Parallel Execution**
```bash
# Built-in, no plugins needed
playwright test --workers=8
```

**5. Trace Recording (Debugging)**
```bash
# Records all actions, network, DOM snapshots
playwright test --trace on
npx playwright show-trace trace.zip  # Replay in UI
```

### Weaknesses

- **Steeper learning curve** - More options, more configuration
- **Less interactive debugging** - No time-travel debugger like Cypress
- **Newer ecosystem** - Fewer third-party plugins than Cypress
- **Visual comparison** - Requires paid Percy or homebrew solutions

### Popular for:

- Enterprise applications needing cross-browser validation
- Python teams that test JavaScript frontends
- Mobile-responsive testing
- API-driven E2E testing

---

## Cypress

### When to Choose Cypress

✅ **Pick Cypress if:**
- Your team is JavaScript/TypeScript only
- You value excellent developer experience
- You want interactive, visual debugging
- You're just starting with E2E testing (lower barrier to entry)
- You like the time-travel debugger for troubleshooting
- You prefer convention over configuration
- Your app is browser-based (no mobile native)

### Strengths

**1. Time-Travel Debugger**
```typescript
// Click to any command in the test and see:
// - DOM at that point
// - Network calls
// - Console logs
// - Exact state
cy.get('button').click();  // Step back in time to any point
```

**2. Excellent DX (Developer Experience)**
```typescript
// Automatic waiting - no explicit waits needed
cy.get('button').click();  // Waits for element automatically
cy.contains('Success').should('be.visible');  // Auto-waits
```

**3. Interactive Mode**
```bash
# Watch your tests run, pause, inspect, resume
cypress open

# Click commands in the UI to debug interactively
```

**4. Great Documentation & Community**
- Official docs are excellent
- Massive community and Stack Overflow answers
- Easier for beginners

**5. Built-in Assertions**
```typescript
// Rich assertion library (Chai)
cy.get('input').should('have.value', 'expected');
cy.get('.error').should('be.visible');
cy.get('button').should('be.disabled');
```

### Weaknesses

- **No Python support** - JavaScript/TypeScript only
- **Cross-browser limited** - Multiple browser runners, not unified
- **Mobile testing weak** - Limited mobile emulation
- **Parallel execution** - Requires paying for Dashboard
- **iFrame challenges** - Historically difficult, improved recently

### Popular for:

- JavaScript/React/Vue teams
- Learning E2E testing for the first time
- Interactive debugging in development
- Rapid test development

---

## Detailed Feature Comparison

### Language Support

**Playwright:**
```typescript
// TypeScript/JavaScript/Python/.NET
import { test } from '@playwright/test';

test('example', async ({ page }) => {
  await page.goto('http://example.com');
});
```

```python
# Python (unique advantage)
from playwright.sync_api import sync_playwright

with sync_playwright() as p:
    browser = p.chromium.launch()
    page = browser.new_page()
    page.goto('http://example.com')
```

**Cypress:**
```typescript
// JavaScript/TypeScript ONLY
describe('example', () => {
  it('works', () => {
    cy.visit('http://example.com');
    cy.get('button').click();
  });
});
```

### Setup Complexity

**Playwright:**
- More initial setup required
- More configuration options
- More flexible = more decisions needed

**Cypress:**
- Minimal setup (`npm install cypress && npx cypress open`)
- Convention over configuration
- Easier for beginners

### Selectors & Queries

**Playwright:**
```typescript
// Modern query APIs (recommended)
page.getByRole('button', { name: 'Submit' });
page.getByLabel('Email');
page.getByPlaceholder('Enter email');
page.getByTestId('submit-btn');
page.getByText('Sign In');

// Legacy locators (also works)
page.locator('button');
page.locator('css=button');
page.locator('xpath=//button');
```

**Cypress:**
```typescript
// jQuery-style selectors
cy.get('button');
cy.get('[data-testid="submit"]');
cy.contains('Sign In');
cy.get('input').parent();
```

### Waiting & Retry Logic

**Playwright:**
```typescript
// Implicit, configurable globally
export default defineConfig({
  use: { timeout: 30000 }
});

// Explicit waits when needed
await page.waitForSelector('[data-testid="modal"]');
await page.waitForFunction(() => {
  return window.isLoaded === true;
});
```

**Cypress:**
```typescript
// Automatic waiting built-in
cy.get('button')  // Waits up to 4 seconds
  .should('be.visible')  // Retries until visible
  .click();

// Explicit wait
cy.get('[data-testid="modal"]', { timeout: 10000 });
```

### Screenshots & Videos

**Playwright:**
```typescript
// Screenshots
await page.screenshot({ path: 'screenshot.png' });

// Videos (configured in config)
use: { video: 'retain-on-failure' }

// Traces (most powerful)
export default defineConfig({
  use: { trace: 'on-first-retry' }
});
```

**Cypress:**
```typescript
// Screenshots (automatic on failure)
// Use cypress/screenshots/

// Videos (automatic on run)
// Use cypress/videos/

// No built-in trace, but plugins available
```

### Parallel Execution

**Playwright:**
```bash
# Built-in, works without plugins
playwright test --workers=8

# Sharding across machines
playwright test --shard=1/4  # Run 1 of 4 shards
```

**Cypress:**
```bash
# Free: Sequential only
cypress run

# Parallel: Requires paid Cypress Cloud
# OR free with custom solutions like Knapsack Pro
```

### Cost

**Playwright:**
- ✅ Completely free
- Open source, self-hosted, all features free

**Cypress:**
- ✅ Test runner: Free
- ⚠️ Dashboard (parallel, advanced reporting): Paid
- Cloud recording/artifact storage: Paid

---

## Decision Matrix

| Scenario | Playwright | Cypress |
|----------|-----------|---------|
| New to E2E testing | - | ✅ Easier start |
| Python/C# team | ✅ | - |
| React SPA | ✅ | ✅ |
| Cross-browser testing | ✅ | ⚠️ More work |
| Mobile responsive | ✅ | - |
| API testing in E2E | ✅ | ⚠️ |
| Interactive debugging | - | ✅ |
| Parallel execution (free) | ✅ | - |
| Small team | - | ✅ |
| Enterprise scale | ✅ | ⚠️ |

---

## Migration Path

### From Cypress to Playwright

```typescript
// Cypress
describe('login', () => {
  it('works', () => {
    cy.visit('/login');
    cy.get('[data-testid="email"]').type('user@example.com');
    cy.get('[data-testid="password"]').type('password');
    cy.get('button').click();
    cy.url().should('include', '/dashboard');
  });
});

// Playwright (equivalent)
import { test, expect } from '@playwright/test';

test('login', async ({ page }) => {
  await page.goto('/login');
  await page.getByTestId('email').fill('user@example.com');
  await page.getByTestId('password').fill('password');
  await page.locator('button').click();
  await expect(page).toHaveURL(/\/dashboard/);
});
```

### From Playwright to Cypress

```typescript
// Playwright
test('login', async ({ page }) => {
  await page.goto('/login');
  await page.getByTestId('email').fill('user@example.com');
  await page.getByTestId('password').fill('password');
  await page.click('button');
  await expect(page).toHaveURL('/dashboard');
});

// Cypress (equivalent)
describe('login', () => {
  it('works', () => {
    cy.visit('/login');
    cy.get('[data-testid="email"]').type('user@example.com');
    cy.get('[data-testid="password"]').type('password');
    cy.get('button').click();
    cy.url().should('include', '/dashboard');
  });
});
```

---

## Recommendation Summary

**Choose Playwright if:**
- You need production-grade cross-browser testing
- Your team includes Python developers
- You're testing at scale (large test suites)
- You need maximum flexibility

**Choose Cypress if:**
- Your team is JavaScript-focused
- You're starting with E2E testing
- Interactive debugging is a priority
- You want the easiest learning curve

**Can't decide?** Playwright is the safer long-term choice. It scales better and supports more languages, but has a steeper learning curve initially.
