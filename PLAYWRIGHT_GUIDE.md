# Playwright Testing Setup Guide

## Installation

All dependencies are defined in `package.json`. Install them with:

```bash
npm install
```

This installs Playwright and the test runner.

## Running Tests

### Basic Commands

```bash
# Run all tests
npm test

# Run tests in UI mode (interactive)
npm run test:ui

# Run tests in headed mode (see browser)
npm run test:headed

# Run tests in debug mode (step through)
npm run test:debug

# Run tests on specific browser
npm run test:chrome
npm run test:firefox
npm run test:webkit
```

### Advanced Usage

```bash
# Run specific test file
npx playwright test tests/example.spec.ts

# Run tests matching a pattern
npx playwright test --grep "form interaction"

# Run single test
npx playwright test -g "example: check README"

# View test report
npx playwright show-report
```

## Project Structure

```
.
├── playwright.config.ts       # Playwright configuration
├── package.json               # Dependencies and scripts
├── tests/
│   └── example.spec.ts        # Example tests
└── .playwright/               # Playwright cache (auto-generated)
```

## Writing Tests

### Basic Test Structure

```typescript
import { test, expect } from '@playwright/test';

test('test description', async ({ page }) => {
  await page.goto('http://localhost:3000');
  await page.wait_for_load_state('networkidle');
  
  // Your test logic here
  expect(await page.title()).toBeTruthy();
});
```

### Key Patterns from webapp-testing Skill

#### 1. Testing Local Web Applications

Use the `with_server.py` helper script for managing server lifecycle:

```bash
python scripts/with_server.py --server "npm run dev" --port 3000 -- npm test
```

#### 2. Reconnaissance-Then-Action Pattern

```typescript
// 1. Navigate and wait for content to load
await page.goto('http://localhost:3000');
await page.wait_for_load_state('networkidle');

// 2. Inspect and identify selectors
const screenshot = await page.screenshot();
const elements = await page.locator('button').all();

// 3. Execute actions with discovered selectors
await page.click('button:text("Submit")');
```

#### 3. Common Selectors

```typescript
// Text content
page.locator('text=Click me')

// Role (accessible)
page.locator('role=button')

// CSS selectors
page.locator('.button-class')

// Attributes
page.locator('[data-testid="submit"]')

// XPath
page.locator('xpath=//button[@type="submit"]')
```

### Testing Strategies

#### Static HTML Testing

```typescript
import { test, expect } from '@playwright/test';

test('test static HTML', async () => {
  const filePath = 'file://' + process.cwd() + '/index.html';
  // Use page.goto(filePath) to test local HTML files
});
```

#### Dynamic Web App Testing

```typescript
test('test dynamic app', async ({ page }) => {
  await page.goto('http://localhost:3000');
  
  // CRITICAL: Wait for JavaScript to execute
  await page.wait_for_load_state('networkidle');
  
  // Now inspect and interact
  const content = await page.content();
  await page.click('button');
});
```

#### Form Testing

```typescript
test('form submission', async ({ page }) => {
  await page.goto('http://localhost:3000/form');
  await page.fill('input[name="email"]', 'test@example.com');
  await page.click('button[type="submit"]');
  await expect(page.locator('.success')).toBeVisible();
});
```

## Common Issues & Solutions

### ❌ Tests fail on dynamic content

✅ Always use `page.wait_for_load_state('networkidle')` on dynamic apps

### ❌ Can't find elements

✅ Take a screenshot first: `await page.screenshot();`
✅ Use the browser DevTools with `--debug` flag

### ❌ Server not running

✅ Use `with_server.py` helper to manage server lifecycle

### ❌ Tests timeout

✅ Increase timeout: `test.setTimeout(30000);`
✅ Ensure proper waits before interactions

## CI/CD Integration

The `playwright.config.ts` includes CI detection. In CI environments:

- Tests run with retries enabled
- Tests run on a single worker
- Tests capture traces on first retry

## Debugging

### Interactive UI Mode

```bash
npm run test:ui
```

This opens an interactive interface where you can step through tests.

### Headed Mode with DevTools

```bash
npm run test:debug
```

This launches the browser with DevTools open for inspection.

### Console & Network Logs

```typescript
page.on('console', msg => console.log(msg.text()));
page.on('response', response => console.log(response.status()));
```

## Resources

- [Playwright Documentation](https://playwright.dev)
- [Playwright Test API](https://playwright.dev/docs/api/class-test)
- [Locators & Selectors](https://playwright.dev/docs/locators)
- [Best Practices](https://playwright.dev/docs/best-practices)
