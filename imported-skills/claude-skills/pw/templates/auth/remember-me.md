# Remember Me Template

Tests persistent login cookie behaviour and expiry.

## Prerequisites
- Valid account: `{{username}}` / `{{password}}`
- `{{sessionCookieName}}` cookie used for auth
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Remember Me', () => {
  // Happy path: cookie is long-lived when remember me is checked
  test('sets persistent cookie when remember me is checked', async ({ page, context }) => {
    await page.goto('{{baseUrl}}/login');
    await page.getByRole('textbox', { name: /email/i }).fill('{{username}}');
    await page.getByRole('textbox', { name: /password/i }).fill('{{password}}');
    await page.getByRole('checkbox', { name: /remember me/i }).check();
    await page.getByRole('button', { name: /sign in/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/dashboard');
    const cookies = await context.cookies();
    const session = cookies.find(c => c.name === '{{sessionCookieName}}');
    // Cookie should expire > 7 days from now
    expect(session?.expires).toBeGreaterThan(Date.now() / 1000 + 7 * 86400);
  });

  // Happy path: session cookie (no remember me) is session-scoped
  test('sets session-scoped cookie when remember me is unchecked', async ({ page, context }) => {
    await page.goto('{{baseUrl}}/login');
    await page.getByRole('textbox', { name: /email/i }).fill('{{username}}');
    await page.getByRole('textbox', { name: /password/i }).fill('{{password}}');
    const checkbox = page.getByRole('checkbox', { name: /remember me/i });
    if (await checkbox.isChecked()) await checkbox.uncheck();
    await page.getByRole('button', { name: /sign in/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/dashboard');
    const cookies = await context.cookies();
    const session = cookies.find(c => c.name === '{{sessionCookieName}}');
    // Session cookie: expires = -1 (browser session only)
    expect(session?.expires).toBeLessThanOrEqual(0);
  });

  // Happy path: persistent login survives page reload
  test('stays logged in across browser restart with remember me', async ({ page, context }) => {
    await page.goto('{{baseUrl}}/login');
    await page.getByRole('textbox', { name: /email/i }).fill('{{username}}');
    await page.getByRole('textbox', { name: /password/i }).fill('{{password}}');
    await page.getByRole('checkbox', { name: /remember me/i }).check();
    await page.getByRole('button', { name: /sign in/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/dashboard');
    // Simulate new browser session by closing & reopening page (cookies persist)
    await page.close();
    const newPage = await context.newPage();
    await newPage.goto('{{baseUrl}}/dashboard');
    await expect(newPage).toHaveURL('{{baseUrl}}/dashboard');
    await expect(newPage.getByRole('heading', { name: /dashboard/i })).toBeVisible();
  });

  // Error case: expired persistent cookie redirects to login
  test('redirects to login when persistent cookie has expired', async ({ page, context }) => {
    await context.addCookies([{
      name: '{{sessionCookieName}}',
      value: '{{expiredCookieValue}}',
      domain: '{{cookieDomain}}',
      path: '/',
      expires: Math.floor(Date.now() / 1000) - 1, // already expired
    }]);
    await page.goto('{{baseUrl}}/dashboard');
    await expect(page).toHaveURL(/\/login/);
  });

  // Edge case: remember me checkbox state is preserved on validation error
  test('retains remember me checkbox state after failed login', async ({ page }) => {
    await page.goto('{{baseUrl}}/login');
    await page.getByRole('checkbox', { name: /remember me/i }).check();
    await page.getByRole('textbox', { name: /email/i }).fill('{{username}}');
    await page.getByRole('textbox', { name: /password/i }).fill('wrong');
    await page.getByRole('button', { name: /sign in/i }).click();
    await expect(page.getByRole('alert')).toContainText(/invalid/i);
    await expect(page.getByRole('checkbox', { name: /remember me/i })).toBeChecked();
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Remember Me', () => {
  test('sets persistent cookie when remember me is checked', async ({ page, context }) => {
    await page.goto('{{baseUrl}}/login');
    await page.getByRole('textbox', { name: /email/i }).fill('{{username}}');
    await page.getByRole('textbox', { name: /password/i }).fill('{{password}}');
    await page.getByRole('checkbox', { name: /remember me/i }).check();
    await page.getByRole('button', { name: /sign in/i }).click();
    const cookies = await context.cookies();
    const session = cookies.find(c => c.name === '{{sessionCookieName}}');
    expect(session?.expires).toBeGreaterThan(Date.now() / 1000 + 7 * 86400);
  });

  test('sets session cookie when remember me is unchecked', async ({ page, context }) => {
    await page.goto('{{baseUrl}}/login');
    await page.getByRole('textbox', { name: /email/i }).fill('{{username}}');
    await page.getByRole('textbox', { name: /password/i }).fill('{{password}}');
    await page.getByRole('button', { name: /sign in/i }).click();
    const cookies = await context.cookies();
    const session = cookies.find(c => c.name === '{{sessionCookieName}}');
    expect(session?.expires).toBeLessThanOrEqual(0);
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Persistent cookie | Remember me → long-lived cookie (>7 days) |
| Session cookie | No remember me → session-scoped cookie |
| Survives reload | Persistent cookie keeps user logged in across restart |
| Expired cookie | Stale cookie → redirect to /login |
| Checkbox retained | State preserved after failed login attempt |
