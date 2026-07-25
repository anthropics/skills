# Login Template

Tests email/password login, social login, and remember me functionality.

## Prerequisites
- Valid user account: `{{username}}` / `{{password}}`
- Social provider configured (Google/GitHub)
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Login', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/login');
  });

  // Happy path: email/password login
  test('logs in with valid credentials', async ({ page }) => {
    await page.getByRole('textbox', { name: /email/i }).fill('{{username}}');
    await page.getByRole('textbox', { name: /password/i }).fill('{{password}}');
    await page.getByRole('button', { name: /sign in/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/dashboard');
    await expect(page.getByRole('heading', { name: /dashboard/i })).toBeVisible();
  });

  // Happy path: remember me
  test('persists session with remember me checked', async ({ page, context }) => {
    await page.getByRole('textbox', { name: /email/i }).fill('{{username}}');
    await page.getByRole('textbox', { name: /password/i }).fill('{{password}}');
    await page.getByRole('checkbox', { name: /remember me/i }).check();
    await page.getByRole('button', { name: /sign in/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/dashboard');
    const cookies = await context.cookies();
    const session = cookies.find(c => c.name === '{{sessionCookieName}}');
    expect(session?.expires).toBeGreaterThan(Date.now() / 1000 + 86400);
  });

  // Happy path: social login
  test('redirects to social provider', async ({ page }) => {
    await page.getByRole('button', { name: /continue with google/i }).click();
    await expect(page).toHaveURL(/accounts\.google\.com/);
  });

  // Error case: invalid credentials
  test('shows error for wrong password', async ({ page }) => {
    await page.getByRole('textbox', { name: /email/i }).fill('{{username}}');
    await page.getByRole('textbox', { name: /password/i }).fill('wrong-password');
    await page.getByRole('button', { name: /sign in/i }).click();
    await expect(page.getByRole('alert')).toContainText(/invalid.*credentials/i);
    await expect(page).toHaveURL('{{baseUrl}}/login');
  });

  // Edge case: empty fields
  test('shows validation for empty submission', async ({ page }) => {
    await page.getByRole('button', { name: /sign in/i }).click();
    await expect(page.getByRole('textbox', { name: /email/i })).toBeFocused();
    await expect(page.getByText(/email is required/i)).toBeVisible();
  });

  // Edge case: locked account
  test('shows account locked message after multiple failures', async ({ page }) => {
    for (let i = 0; i < {{lockoutAttempts}}; i++) {
      await page.getByRole('textbox', { name: /email/i }).fill('{{username}}');
      await page.getByRole('textbox', { name: /password/i }).fill('wrong');
      await page.getByRole('button', { name: /sign in/i }).click();
    }
    await expect(page.getByRole('alert')).toContainText(/account.*locked/i);
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Login', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/login');
  });

  test('logs in with valid credentials', async ({ page }) => {
    await page.getByRole('textbox', { name: /email/i }).fill('{{username}}');
    await page.getByRole('textbox', { name: /password/i }).fill('{{password}}');
    await page.getByRole('button', { name: /sign in/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/dashboard');
    await expect(page.getByRole('heading', { name: /dashboard/i })).toBeVisible();
  });

  test('shows error for wrong password', async ({ page }) => {
    await page.getByRole('textbox', { name: /email/i }).fill('{{username}}');
    await page.getByRole('textbox', { name: /password/i }).fill('wrong-password');
    await page.getByRole('button', { name: /sign in/i }).click();
    await expect(page.getByRole('alert')).toContainText(/invalid.*credentials/i);
  });

  test('shows validation for empty submission', async ({ page }) => {
    await page.getByRole('button', { name: /sign in/i }).click();
    await expect(page.getByText(/email is required/i)).toBeVisible();
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Happy path | Valid credentials → dashboard redirect |
| Remember me | Long-lived cookie set |
| Social login | OAuth redirect to provider |
| Wrong password | Alert with error message |
| Empty form | Inline validation shown |
| Locked account | Lockout message after N failures |
