# Logout Template

Tests logout from navigation, session cleanup, and redirect behaviour.

## Prerequisites
- Authenticated session (use `storageState` or login fixture)
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Logout', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  // Happy path: logout via nav menu
  test('logs out from user menu', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.getByRole('button', { name: /user menu/i }).click();
    await page.getByRole('menuitem', { name: /sign out/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/login');
    await expect(page.getByRole('heading', { name: /sign in/i })).toBeVisible();
  });

  // Happy path: session cookies cleared
  test('clears session cookie on logout', async ({ page, context }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.getByRole('button', { name: /user menu/i }).click();
    await page.getByRole('menuitem', { name: /sign out/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/login');
    const cookies = await context.cookies();
    const session = cookies.find(c => c.name === '{{sessionCookieName}}');
    expect(session).toBeUndefined();
  });

  // Happy path: accessing protected page after logout redirects
  test('redirects to login when accessing protected page after logout', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.getByRole('button', { name: /user menu/i }).click();
    await page.getByRole('menuitem', { name: /sign out/i }).click();
    await page.goto('{{baseUrl}}/dashboard');
    await expect(page).toHaveURL(/\/login/);
  });

  // Error case: double logout (stale session)
  test('handles logout gracefully when session already expired', async ({ page, context }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await context.clearCookies();
    await page.getByRole('button', { name: /user menu/i }).click();
    await page.getByRole('menuitem', { name: /sign out/i }).click();
    await expect(page).toHaveURL(/\/login/);
  });

  // Edge case: logout from multiple tabs
  test('invalidates session across tabs', async ({ page, context }) => {
    const tab2 = await context.newPage();
    await page.goto('{{baseUrl}}/dashboard');
    await tab2.goto('{{baseUrl}}/dashboard');
    await page.getByRole('button', { name: /user menu/i }).click();
    await page.getByRole('menuitem', { name: /sign out/i }).click();
    await tab2.reload();
    await expect(tab2).toHaveURL(/\/login/);
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Logout', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test('logs out from user menu', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.getByRole('button', { name: /user menu/i }).click();
    await page.getByRole('menuitem', { name: /sign out/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/login');
  });

  test('clears session cookie on logout', async ({ page, context }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.getByRole('button', { name: /user menu/i }).click();
    await page.getByRole('menuitem', { name: /sign out/i }).click();
    const cookies = await context.cookies();
    expect(cookies.find(c => c.name === '{{sessionCookieName}}')).toBeUndefined();
  });

  test('redirects protected page to login after logout', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.getByRole('button', { name: /user menu/i }).click();
    await page.getByRole('menuitem', { name: /sign out/i }).click();
    await page.goto('{{baseUrl}}/dashboard');
    await expect(page).toHaveURL(/\/login/);
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Happy path | Nav menu → sign out → login page |
| Cookie cleanup | Session cookie removed after logout |
| Protected redirect | Accessing /dashboard after logout → /login |
| Stale session | Already-expired session handled gracefully |
| Multi-tab | Logout invalidates other open tabs |
