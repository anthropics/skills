---
name: Playwright Browser Automation
description: Complete browser automation with Playwright. Auto-detects dev servers, integrates with project tests OR runs ad-hoc scripts. Test pages, fill forms, take screenshots, check responsive design, validate UX, test login flows, check links, automate any browser task.
version: 5.0.0
author: Claude Assistant
tags: [testing, automation, browser, e2e, playwright, web-testing]
---

# Playwright Browser Automation

This skill provides **two complementary modes** for browser automation:

1. **Project Mode** - Run/create tests using the project's existing Playwright setup
2. **Ad-hoc Mode** - Quick dynamic scripts for investigation and prototyping

## Decision Tree: Which Mode to Use?

```
Is there an existing tests/e2e/ or tests/ directory with *.spec.ts files?
├── YES: Does the project have Playwright installed (check package.json)?
│   ├── YES: Use PROJECT MODE (preferred for established tests)
│   └── NO: Use AD-HOC MODE with skill's Playwright
└── NO: Use AD-HOC MODE

What's your goal?
├── Run existing E2E tests → PROJECT MODE: `npx playwright test`
├── Investigate a bug/UI issue → AD-HOC MODE: Quick script to /tmp/
├── Prototype a new test → AD-HOC MODE first, then convert to project test
├── Take a quick screenshot → AD-HOC MODE: Inline or simple script
└── Add permanent test coverage → PROJECT MODE: Create proper .spec.ts file
```

---

## PROJECT MODE: Using Project's Playwright

**When to use:** The project has Playwright installed and you want to:
- Run existing E2E tests
- Add new permanent test coverage
- Use project's `playwright.config.ts` settings

### Step 1: Detect Project Playwright Setup

```bash
# Check if project has Playwright
ls package.json && grep -l "playwright" package.json
ls playwright.config.ts 2>/dev/null || ls playwright.config.js 2>/dev/null

# Check for existing tests
ls tests/e2e/*.spec.ts 2>/dev/null || ls tests/*.spec.ts 2>/dev/null
```

### Step 2: Run Existing Tests

```bash
# Run all E2E tests
cd <project> && npx playwright test

# Run specific test file
cd <project> && npx playwright test tests/e2e/network-tabs.spec.ts

# Run tests matching pattern
cd <project> && npx playwright test -g "login"

# Run with visible browser
cd <project> && npx playwright test --headed

# Run with UI mode (interactive)
cd <project> && npx playwright test --ui
```

### Step 3: Create New Project Test

When you've prototyped something in ad-hoc mode and want to make it permanent:

```typescript
// tests/e2e/new-feature.spec.ts
import { test, expect } from '@playwright/test'

test.describe('New Feature', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/feature')
  })

  test('should display correctly', async ({ page }) => {
    await expect(page.getByTestId('feature-container')).toBeVisible()
    await expect(page.getByRole('heading')).toHaveText('Feature Title')
  })

  test('should handle user interaction', async ({ page }) => {
    await page.getByRole('button', { name: 'Submit' }).click()
    await expect(page.getByText('Success')).toBeVisible()
  })
})
```

---

## AD-HOC MODE: Dynamic Scripts for Investigation

**When to use:**
- Investigating a bug or UI issue
- Prototyping before writing a permanent test
- Quick one-off automation (screenshots, form filling)
- Project doesn't have Playwright installed

### Option A: Use Project's Playwright (Recommended if available)

If the project has Playwright in `node_modules`, use it directly:

```bash
# Quick script using project's Playwright
NODE_PATH=<project>/node_modules node /tmp/playwright-test-*.js
```

Example script:
```javascript
// /tmp/playwright-investigate.js
const { chromium } = require('playwright');

const TARGET_URL = 'http://localhost:3000';

(async () => {
  const browser = await chromium.launch({ headless: false, slowMo: 50 });
  const page = await browser.newPage();

  try {
    await page.goto(`${TARGET_URL}/problem-page`);

    // Investigate the issue
    console.log('Page title:', await page.title());
    console.log('URL:', page.url());

    // Check for specific elements
    const errorVisible = await page.locator('.error-message').isVisible();
    console.log('Error visible:', errorVisible);

    // Take screenshot for analysis
    await page.screenshot({ path: '/tmp/investigate.png', fullPage: true });
    console.log('Screenshot saved to /tmp/investigate.png');

  } catch (error) {
    console.error('Error:', error.message);
    await page.screenshot({ path: '/tmp/error-state.png' });
  } finally {
    await browser.close();
  }
})();
```

Execute:
```bash
NODE_PATH=<project>/node_modules node /tmp/playwright-investigate.js
```

### Option B: Use Skill's Playwright

If project doesn't have Playwright, use this skill's installation:

```bash
# First time setup (only once)
cd $SKILL_DIR && npm run setup

# Execute script
cd $SKILL_DIR && node run.js /tmp/playwright-test-*.js
```

**Path Resolution:** Replace `$SKILL_DIR` with actual path:
- Global: `~/.claude/skills/playwright-skill`
- Plugin: `~/.claude/plugins/marketplaces/playwright-skill/skills/playwright-skill`

---

## Workflow: Prototype to Production

A common workflow is to **investigate with ad-hoc scripts**, then **convert to project tests**:

### Phase 1: Investigate the Problem

```javascript
// /tmp/playwright-debug-login.js
const { chromium } = require('playwright');

(async () => {
  const browser = await chromium.launch({ headless: false, slowMo: 100 });
  const page = await browser.newPage();

  await page.goto('http://localhost:3000/login');

  // Try different scenarios to understand the bug
  await page.fill('[data-testid="email-input"]', 'test@example.com');
  await page.fill('[data-testid="password-input"]', 'wrongpassword');
  await page.click('[data-testid="submit-btn"]');

  // Wait and observe
  await page.waitForTimeout(2000);

  // Check what happened
  const errorText = await page.locator('.error-message').textContent();
  console.log('Error message:', errorText);

  await page.screenshot({ path: '/tmp/login-error.png' });
  await browser.close();
})();
```

### Phase 2: Refine Until Working

Iterate on the script, adding assertions and edge cases.

### Phase 3: Convert to Project Test

```typescript
// tests/e2e/login.spec.ts
import { test, expect } from '@playwright/test'

test.describe('Login', () => {
  test('should show error for invalid credentials', async ({ page }) => {
    await page.goto('/login')

    await page.getByTestId('email-input').fill('test@example.com')
    await page.getByTestId('password-input').fill('wrongpassword')
    await page.getByTestId('submit-btn').click()

    await expect(page.locator('.error-message')).toHaveText('Invalid credentials')
  })

  test('should redirect to dashboard on success', async ({ page }) => {
    await page.goto('/login')

    await page.getByTestId('email-input').fill('valid@example.com')
    await page.getByTestId('password-input').fill('correctpassword')
    await page.getByTestId('submit-btn').click()

    await expect(page).toHaveURL(/.*dashboard/)
  })
})
```

---

## Quick Reference

### Auto-Detect Dev Servers

```bash
# Using skill helper
cd $SKILL_DIR && node -e "require('./lib/helpers').detectDevServers().then(s => console.log(JSON.stringify(s)))"

# Or manually check common ports
lsof -i :3000 -i :3001 -i :5173 -i :8080 | grep LISTEN
```

### Common Ad-hoc Patterns

**Take Screenshot:**
```javascript
const { chromium } = require('playwright');
(async () => {
  const browser = await chromium.launch({ headless: false });
  const page = await browser.newPage();
  await page.goto('http://localhost:3000');
  await page.screenshot({ path: '/tmp/screenshot.png', fullPage: true });
  console.log('Saved to /tmp/screenshot.png');
  await browser.close();
})();
```

**Test Responsive Design:**
```javascript
const viewports = [
  { name: 'desktop', width: 1920, height: 1080 },
  { name: 'tablet', width: 768, height: 1024 },
  { name: 'mobile', width: 375, height: 667 }
];

for (const vp of viewports) {
  await page.setViewportSize({ width: vp.width, height: vp.height });
  await page.screenshot({ path: `/tmp/${vp.name}.png` });
}
```

**Fill Form:**
```javascript
await page.fill('input[name="email"]', 'test@example.com');
await page.fill('input[name="password"]', 'password123');
await page.click('button[type="submit"]');
await page.waitForURL('**/dashboard');
```

**Check Element State:**
```javascript
const isVisible = await page.locator('.error').isVisible();
const text = await page.locator('h1').textContent();
const count = await page.locator('li').count();
console.log({ isVisible, text, count });
```

### Project Test Commands

```bash
# Run all tests
npx playwright test

# Run specific file
npx playwright test tests/e2e/auth.spec.ts

# Run with pattern
npx playwright test -g "should login"

# Visual mode
npx playwright test --headed
npx playwright test --ui

# Debug mode
npx playwright test --debug

# Generate HTML report
npx playwright test --reporter=html
npx playwright show-report
```

---

## Tips

### General
- **Visible browser by default** - Use `headless: false` for debugging
- **Slow motion** - Use `slowMo: 100` to see what's happening
- **Wait strategies** - Prefer `waitForSelector`, `waitForURL` over `waitForTimeout`
- **Error handling** - Always use try-catch for robust scripts

### Project Mode
- **Use data-testid** - More reliable than CSS selectors
- **Use locators** - `page.getByTestId()`, `page.getByRole()`, `page.getByText()`
- **Use expect** - Proper assertions with retries built-in
- **Check baseURL** - Use relative paths if `playwright.config.ts` sets baseURL

### Ad-hoc Mode
- **Write to /tmp/** - Scripts auto-cleaned by OS
- **Parameterize URLs** - Use `TARGET_URL` constant at top
- **Console logging** - Output progress and findings
- **Save screenshots** - Visual evidence in /tmp/

---

## Troubleshooting

**Module not found with NODE_PATH:**
```bash
# Verify node_modules exists
ls <project>/node_modules/playwright

# Use full path
NODE_PATH=/full/path/to/project/node_modules node /tmp/script.js
```

**Playwright not installed in skill:**
```bash
cd $SKILL_DIR && npm run setup
```

**Tests won't run:**
```bash
# Check Playwright is installed
npx playwright --version

# Install browsers
npx playwright install chromium
```

**Element not found:**
```javascript
// Add explicit wait
await page.waitForSelector('.element', { timeout: 10000 });

// Or use locator with expect (auto-waits)
await expect(page.locator('.element')).toBeVisible();
```

---

## Summary

| Scenario | Mode | Command |
|----------|------|---------|
| Run existing tests | Project | `npx playwright test` |
| Add permanent test | Project | Create `tests/e2e/*.spec.ts` |
| Investigate bug | Ad-hoc | Script to `/tmp/`, run with `NODE_PATH` |
| Quick screenshot | Ad-hoc | Simple script, `NODE_PATH` execution |
| Prototype new test | Ad-hoc → Project | Start in `/tmp/`, then convert |
| No Playwright in project | Ad-hoc | Use skill's Playwright via `run.js` |
