# Fixtures Reference

## What Are Fixtures

Fixtures provide setup/teardown for each test. They replace `beforeEach`/`afterEach` for shared state and are composable, type-safe, and lazy (only run when used).

## Creating Custom Fixtures

```typescript
// fixtures.ts
import { test as base, expect } from '@playwright/test';

// Define fixture types
type MyFixtures = {
  authenticatedPage: Page;
  testUser: { email: string; password: string };
  apiClient: APIRequestContext;
};

export const test = base.extend<MyFixtures>({
  // Simple value fixture
  testUser: async ({}, use) => {
    await use({
      email: `test-${Date.now()}@example.com`,
      password: 'Test123!',
    });
  },

  // Fixture with setup and teardown
  authenticatedPage: async ({ page, testUser }, use) => {
    // Setup: log in
    await page.goto('/login');
    await page.getByLabel('Email').fill(testUser.email);
    await page.getByLabel('Password').fill(testUser.password);
    await page.getByRole('button', { name: 'Sign in' }).click();
    await expect(page).toHaveURL('/dashboard');

    // Provide the authenticated page to the test
    await use(page);

    // Teardown: clean up (optional)
    await page.goto('/logout');
  },

  // API client fixture
  apiClient: async ({ playwright }, use) => {
    const context = await playwright.request.newContext({
      baseURL: 'http://localhost:3000',
      extraHTTPHeaders: {
        Authorization: `Bearer ${process.env.API_TOKEN}`,
      },
    });
    await use(context);
    await context.dispose();
  },
});

export { expect };
```

## Using Fixtures in Tests

```typescript
import { test, expect } from './fixtures';

test('should show dashboard for logged in user', async ({ authenticatedPage }) => {
  // authenticatedPage is already logged in
  await expect(authenticatedPage.getByRole('heading', { name: 'Dashboard' })).toBeVisible();
});

test('should create item via API', async ({ apiClient }) => {
  const response = await apiClient.post('/api/items', {
    data: { name: 'Test Item' },
  });
  expect(response.ok()).toBeTruthy();
});
```

## Shared Auth State (storageState)

For performance, authenticate once and reuse:

```typescript
// auth.setup.ts
import { test as setup } from '@playwright/test';

setup('authenticate', async ({ page }) => {
  await page.goto('/login');
  await page.getByLabel('Email').fill('admin@example.com');
  await page.getByLabel('Password').fill('password');
  await page.getByRole('button', { name: 'Sign in' }).click();
  await page.waitForURL('/dashboard');
  await page.context().storageState({ path: '.auth/user.json' });
});
```

```typescript
// playwright.config.ts
export default defineConfig({
  projects: [
    { name: 'setup', testMatch: /.*\.setup\.ts/ },
    {
      name: 'chromium',
      use: {
        storageState: '.auth/user.json',
      },
      dependencies: ['setup'],
    },
  ],
});
```

## When to Use What

| Need | Use |
|---|---|
| Shared login state | `storageState` + setup project |
| Per-test data creation | Custom fixture with API calls |
| Reusable page helpers | Custom fixture returning page |
| Test data cleanup | Fixture teardown (after `use()`) |
| Config values | Simple value fixture |
