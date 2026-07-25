# Session Timeout Template

Tests auto-logout after inactivity and session refresh behaviour.

## Prerequisites
- Authenticated session via `{{authStorageStatePath}}`
- Session timeout configured to `{{sessionTimeoutMs}}` ms in test env
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Session Timeout', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  // Happy path: session refresh on activity
  test('refreshes session on user activity', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.clock.install();
    // Advance to just before timeout
    await page.clock.fastForward({{sessionTimeoutMs}} - 5000);
    await page.getByRole('button', { name: /any interactive element/i }).click();
    // Advance past original timeout — session should still be valid
    await page.clock.fastForward(10_000);
    await expect(page.getByRole('heading', { name: /dashboard/i })).toBeVisible();
  });

  // Happy path: warning dialog shown before logout
  test('shows session-expiry warning before auto-logout', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.clock.install();
    await page.clock.fastForward({{sessionTimeoutMs}} - {{warningLeadMs}});
    await expect(page.getByRole('dialog', { name: /session.*expiring/i })).toBeVisible();
    await expect(page.getByRole('button', { name: /stay signed in/i })).toBeVisible();
  });

  // Happy path: extend session from warning dialog
  test('extends session when "stay signed in" clicked', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.clock.install();
    await page.clock.fastForward({{sessionTimeoutMs}} - {{warningLeadMs}});
    await page.getByRole('button', { name: /stay signed in/i }).click();
    await expect(page.getByRole('dialog', { name: /session.*expiring/i })).toBeHidden();
    await expect(page.getByRole('heading', { name: /dashboard/i })).toBeVisible();
  });

  // Error case: auto-logout after inactivity
  test('redirects to login after session timeout', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.clock.install();
    await page.clock.fastForward({{sessionTimeoutMs}} + 1000);
    await expect(page).toHaveURL(/\/login/);
    await expect(page.getByText(/session.*expired|signed out/i)).toBeVisible();
  });

  // Edge case: API calls return 401 after timeout
  test('shows re-auth prompt when API returns 401', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.route('{{baseUrl}}/api/**', route =>
      route.fulfill({ status: 401, body: JSON.stringify({ error: 'Unauthorized' }) })
    );
    await page.getByRole('button', { name: /refresh|reload/i }).click();
    await expect(page.getByRole('dialog', { name: /session.*expired/i })).toBeVisible();
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Session Timeout', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test('shows warning before auto-logout', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.clock.install();
    await page.clock.fastForward({{sessionTimeoutMs}} - {{warningLeadMs}});
    await expect(page.getByRole('dialog', { name: /session.*expiring/i })).toBeVisible();
  });

  test('auto-logs out after inactivity', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.clock.install();
    await page.clock.fastForward({{sessionTimeoutMs}} + 1000);
    await expect(page).toHaveURL(/\/login/);
  });

  test('extends session on "stay signed in"', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.clock.install();
    await page.clock.fastForward({{sessionTimeoutMs}} - {{warningLeadMs}});
    await page.getByRole('button', { name: /stay signed in/i }).click();
    await expect(page.getByRole('dialog', { name: /session.*expiring/i })).toBeHidden();
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Session refresh | Activity before timeout resets the clock |
| Warning dialog | Shown N ms before timeout |
| Extend session | "Stay signed in" dismisses warning |
| Auto-logout | Inactivity past timeout → /login |
| 401 from API | Re-auth dialog shown when backend rejects request |
