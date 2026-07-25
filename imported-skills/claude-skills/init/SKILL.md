---
name: "init"
description: >-
  Set up Playwright in a project. Use when user says "set up playwright",
  "add e2e tests", "configure playwright", "testing setup", "init playwright",
  or "add test infrastructure".
---

# Initialize Playwright Project

Set up a production-ready Playwright testing environment. Detect the framework, generate config, folder structure, example test, and CI workflow.

## Steps

### 1. Analyze the Project

Use the `Explore` subagent to scan the project:

- Check `package.json` for framework (React, Next.js, Vue, Angular, Svelte)
- Check for `tsconfig.json` → use TypeScript; otherwise JavaScript
- Check if Playwright is already installed (`@playwright/test` in dependencies)
- Check for existing test directories (`tests/`, `e2e/`, `__tests__/`)
- Check for existing CI config (`.github/workflows/`, `.gitlab-ci.yml`)

### 2. Install Playwright

If not already installed:

```bash
npm init playwright@latest -- --quiet
```

Or if the user prefers manual setup:

```bash
npm install -D @playwright/test
npx playwright install --with-deps chromium
```

### 3. Generate `playwright.config.ts`

Adapt to the detected framework:

**Next.js:**
```typescript
import { defineConfig, devices } from '@playwright/test';

export default defineConfig({
  testDir: './e2e',
  fullyParallel: true,
  forbidOnly: !!process.env.CI,
  retries: process.env.CI ? 2 : 0,
  workers: process.env.CI ? 1 : undefined,
  reporter: [
    ['html', { open: 'never' }],
    ['list'],
  ],
  use: {
    baseURL: 'http://localhost:3000',
    trace: 'on-first-retry',
    screenshot: 'only-on-failure',
  },
  projects: [
    { name: "chromium", use: { ...devices['Desktop Chrome'] } },
    { name: "firefox", use: { ...devices['Desktop Firefox'] } },
    { name: "webkit", use: { ...devices['Desktop Safari'] } },
  ],
  webServer: {
    command: 'npm run dev',
    url: 'http://localhost:3000',
    reuseExistingServer: !process.env.CI,
  },
});
```

**React (Vite):**
- Change `baseURL` to `http://localhost:5173`
- Change `webServer.command` to `npm run dev`

**Vue/Nuxt:**
- Change `baseURL` to `http://localhost:3000`
- Change `webServer.command` to `npm run dev`

**Angular:**
- Change `baseURL` to `http://localhost:4200`
- Change `webServer.command` to `npm run start`

**No framework detected:**
- Omit `webServer` block
- Set `baseURL` from user input or leave as placeholder

### 4. Create Folder Structure

```
e2e/
├── fixtures/
│   └── index.ts          # Custom fixtures
├── pages/
│   └── .gitkeep          # Page object models
├── test-data/
│   └── .gitkeep          # Test data files
└── example.spec.ts       # First example test
```

### 5. Generate Example Test

```typescript
import { test, expect } from '@playwright/test';

test.describe('Homepage', () => {
  test('should load successfully', async ({ page }) => {
    await page.goto('/');
    await expect(page).toHaveTitle(/.+/);
  });

  test('should have visible navigation', async ({ page }) => {
    await page.goto('/');
    await expect(page.getByRole('navigation')).toBeVisible();
  });
});
```

### 6. Generate CI Workflow

If `.github/workflows/` exists, create `playwright.yml`:

```yaml
name: "playwright-tests"

on:
  push:
    branches: [main, dev]
  pull_request:
    branches: [main, dev]

jobs:
  test:
    timeout-minutes: 60
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with:
          node-version: lts/*
      - name: "install-dependencies"
        run: npm ci
      - name: "install-playwright-browsers"
        run: npx playwright install --with-deps
      - name: "run-playwright-tests"
        run: npx playwright test
      - uses: actions/upload-artifact@v4
        if: ${{ !cancelled() }}
        with:
          name: "playwright-report"
          path: playwright-report/
          retention-days: 30
```

If `.gitlab-ci.yml` exists, add a Playwright stage instead.

### 7. Update `.gitignore`

Append if not already present:

```
/test-results/
/playwright-report/
/blob-report/
/playwright/.cache/
```

### 8. Add npm Scripts

Add to `package.json` scripts:

```json
{
  "test:e2e": "playwright test",
  "test:e2e:ui": "playwright test --ui",
  "test:e2e:debug": "playwright test --debug"
}
```

### 9. Verify Setup

Run the example test:

```bash
npx playwright test
```

Report the result. If it fails, diagnose and fix before completing.

## Output

Confirm what was created:
- Config file path and key settings
- Test directory and example test
- CI workflow (if applicable)
- npm scripts added
- How to run: `npx playwright test` or `npm run test:e2e`
