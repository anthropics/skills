# Registration Template

Tests signup form submission, validation, and post-registration flow.

## Prerequisites
- Unique test email for each run: `{{newUserEmail}}`
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

const uniqueEmail = `test+${Date.now()}@example.com`;

test.describe('Registration', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/register');
  });

  // Happy path: successful registration
  test('registers new user with valid data', async ({ page }) => {
    await page.getByRole('textbox', { name: /first name/i }).fill('{{firstName}}');
    await page.getByRole('textbox', { name: /last name/i }).fill('{{lastName}}');
    await page.getByRole('textbox', { name: /email/i }).fill(uniqueEmail);
    await page.getByRole('textbox', { name: /^password$/i }).fill('{{newPassword}}');
    await page.getByRole('textbox', { name: /confirm.*password/i }).fill('{{newPassword}}');
    await page.getByRole('checkbox', { name: /terms/i }).check();
    await page.getByRole('button', { name: /sign up|register|create account/i }).click();
    await expect(page).toHaveURL(/\/verify-email|\/dashboard|\/onboarding/);
  });

  // Happy path: success message or redirect
  test('shows confirmation after registration', async ({ page }) => {
    await page.getByRole('textbox', { name: /email/i }).fill(uniqueEmail);
    await page.getByRole('textbox', { name: /^password$/i }).fill('{{newPassword}}');
    await page.getByRole('checkbox', { name: /terms/i }).check();
    await page.getByRole('button', { name: /sign up|register/i }).click();
    await expect(page.getByText(/check your email|account created|welcome/i)).toBeVisible();
  });

  // Error case: email already registered
  test('shows error for already registered email', async ({ page }) => {
    await page.getByRole('textbox', { name: /email/i }).fill('{{existingUserEmail}}');
    await page.getByRole('textbox', { name: /^password$/i }).fill('{{newPassword}}');
    await page.getByRole('checkbox', { name: /terms/i }).check();
    await page.getByRole('button', { name: /sign up|register/i }).click();
    await expect(page.getByRole('alert')).toContainText(/already.*registered|email.*taken/i);
  });

  // Error case: terms not accepted
  test('blocks registration if terms not accepted', async ({ page }) => {
    await page.getByRole('textbox', { name: /email/i }).fill(uniqueEmail);
    await page.getByRole('textbox', { name: /^password$/i }).fill('{{newPassword}}');
    await page.getByRole('button', { name: /sign up|register/i }).click();
    await expect(page.getByText(/accept.*terms|terms.*required/i)).toBeVisible();
  });

  // Error case: weak password
  test('shows error for weak password', async ({ page }) => {
    await page.getByRole('textbox', { name: /^password$/i }).fill('123');
    await page.getByRole('textbox', { name: /^password$/i }).blur();
    await expect(page.getByText(/at least \d+ characters|too weak/i)).toBeVisible();
  });

  // Error case: passwords mismatch
  test('shows error when passwords do not match', async ({ page }) => {
    await page.getByRole('textbox', { name: /^password$/i }).fill('{{newPassword}}');
    await page.getByRole('textbox', { name: /confirm.*password/i }).fill('different');
    await page.getByRole('textbox', { name: /confirm.*password/i }).blur();
    await expect(page.getByText(/do not match/i)).toBeVisible();
  });

  // Edge case: already logged-in user redirected
  test('redirects to dashboard when already authenticated', async ({ page, context }) => {
    await context.addCookies([{ name: '{{sessionCookieName}}', value: '{{validSession}}', domain: '{{cookieDomain}}', path: '/' }]);
    await page.goto('{{baseUrl}}/register');
    await expect(page).toHaveURL('{{baseUrl}}/dashboard');
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Registration', () => {
  test('registers with valid data', async ({ page }) => {
    const email = `test+${Date.now()}@example.com`;
    await page.goto('{{baseUrl}}/register');
    await page.getByRole('textbox', { name: /email/i }).fill(email);
    await page.getByRole('textbox', { name: /^password$/i }).fill('{{newPassword}}');
    await page.getByRole('checkbox', { name: /terms/i }).check();
    await page.getByRole('button', { name: /sign up|register/i }).click();
    await expect(page).toHaveURL(/\/verify-email|\/dashboard|\/onboarding/);
  });

  test('shows error for existing email', async ({ page }) => {
    await page.goto('{{baseUrl}}/register');
    await page.getByRole('textbox', { name: /email/i }).fill('{{existingUserEmail}}');
    await page.getByRole('textbox', { name: /^password$/i }).fill('{{newPassword}}');
    await page.getByRole('checkbox', { name: /terms/i }).check();
    await page.getByRole('button', { name: /sign up|register/i }).click();
    await expect(page.getByRole('alert')).toContainText(/already.*registered/i);
  });

  test('requires terms acceptance', async ({ page }) => {
    await page.goto('{{baseUrl}}/register');
    await page.getByRole('textbox', { name: /email/i }).fill(`t${Date.now()}@example.com`);
    await page.getByRole('textbox', { name: /^password$/i }).fill('{{newPassword}}');
    await page.getByRole('button', { name: /sign up|register/i }).click();
    await expect(page.getByText(/accept.*terms/i)).toBeVisible();
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Valid registration | All fields → redirect or success message |
| Confirmation | Email check or welcome shown |
| Existing email | Error alert |
| Terms not accepted | Validation error |
| Weak password | Strength error on blur |
| Password mismatch | Confirm error |
| Already authed | Redirected to dashboard |
