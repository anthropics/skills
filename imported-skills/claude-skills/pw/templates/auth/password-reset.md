# Password Reset Template

Tests reset request, setting a new password, and expired link handling.

## Prerequisites
- Account with email: `{{username}}`
- Reset link / token available in test environment (`{{resetToken}}`)
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Password Reset', () => {
  // Happy path: request reset email
  test('sends reset email for known address', async ({ page }) => {
    await page.goto('{{baseUrl}}/forgot-password');
    await page.getByRole('textbox', { name: /email/i }).fill('{{username}}');
    await page.getByRole('button', { name: /send reset/i }).click();
    await expect(page.getByRole('alert')).toContainText(/check your email/i);
  });

  // Happy path: set new password via reset link
  test('sets new password with valid reset token', async ({ page }) => {
    await page.goto('{{baseUrl}}/reset-password?token={{resetToken}}');
    await expect(page.getByRole('heading', { name: /set.*new password/i })).toBeVisible();
    await page.getByRole('textbox', { name: /^new password$/i }).fill('{{newPassword}}');
    await page.getByRole('textbox', { name: /confirm password/i }).fill('{{newPassword}}');
    await page.getByRole('button', { name: /reset password/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/login');
    await expect(page.getByRole('alert')).toContainText(/password.*updated/i);
  });

  // Happy path: login with new password
  test('can log in with updated password', async ({ page }) => {
    await page.goto('{{baseUrl}}/login');
    await page.getByRole('textbox', { name: /email/i }).fill('{{username}}');
    await page.getByRole('textbox', { name: /password/i }).fill('{{newPassword}}');
    await page.getByRole('button', { name: /sign in/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/dashboard');
  });

  // Error case: expired reset link
  test('shows error for expired reset token', async ({ page }) => {
    await page.goto('{{baseUrl}}/reset-password?token={{expiredResetToken}}');
    await expect(page.getByRole('alert')).toContainText(/link.*expired|token.*invalid/i);
    await expect(page.getByRole('link', { name: /request new link/i })).toBeVisible();
  });

  // Error case: unknown email
  test('shows generic message for unknown email (anti-enumeration)', async ({ page }) => {
    await page.goto('{{baseUrl}}/forgot-password');
    await page.getByRole('textbox', { name: /email/i }).fill('unknown@example.com');
    await page.getByRole('button', { name: /send reset/i }).click();
    // Should NOT reveal whether email exists
    await expect(page.getByRole('alert')).toContainText(/check your email/i);
  });

  // Error case: passwords do not match
  test('validates that passwords match', async ({ page }) => {
    await page.goto('{{baseUrl}}/reset-password?token={{resetToken}}');
    await page.getByRole('textbox', { name: /^new password$/i }).fill('{{newPassword}}');
    await page.getByRole('textbox', { name: /confirm password/i }).fill('different-password');
    await page.getByRole('button', { name: /reset password/i }).click();
    await expect(page.getByText(/passwords.*do not match/i)).toBeVisible();
  });

  // Edge case: weak password rejected
  test('rejects password that does not meet strength requirements', async ({ page }) => {
    await page.goto('{{baseUrl}}/reset-password?token={{resetToken}}');
    await page.getByRole('textbox', { name: /^new password$/i }).fill('123');
    await page.getByRole('textbox', { name: /confirm password/i }).fill('123');
    await page.getByRole('button', { name: /reset password/i }).click();
    await expect(page.getByText(/password.*too weak|must be at least/i)).toBeVisible();
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Password Reset', () => {
  test('sends reset email for known address', async ({ page }) => {
    await page.goto('{{baseUrl}}/forgot-password');
    await page.getByRole('textbox', { name: /email/i }).fill('{{username}}');
    await page.getByRole('button', { name: /send reset/i }).click();
    await expect(page.getByRole('alert')).toContainText(/check your email/i);
  });

  test('sets new password with valid reset token', async ({ page }) => {
    await page.goto('{{baseUrl}}/reset-password?token={{resetToken}}');
    await page.getByRole('textbox', { name: /^new password$/i }).fill('{{newPassword}}');
    await page.getByRole('textbox', { name: /confirm password/i }).fill('{{newPassword}}');
    await page.getByRole('button', { name: /reset password/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/login');
  });

  test('shows error for expired reset token', async ({ page }) => {
    await page.goto('{{baseUrl}}/reset-password?token={{expiredResetToken}}');
    await expect(page.getByRole('alert')).toContainText(/link.*expired|token.*invalid/i);
  });

  test('validates passwords match', async ({ page }) => {
    await page.goto('{{baseUrl}}/reset-password?token={{resetToken}}');
    await page.getByRole('textbox', { name: /^new password$/i }).fill('{{newPassword}}');
    await page.getByRole('textbox', { name: /confirm password/i }).fill('other');
    await page.getByRole('button', { name: /reset password/i }).click();
    await expect(page.getByText(/passwords.*do not match/i)).toBeVisible();
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Request reset | Known email → check email message |
| Set new password | Valid token → new password set → login page |
| Login with new pw | Updated credentials accepted |
| Expired token | Error + "request new link" shown |
| Unknown email | Generic response (anti-enumeration) |
| Passwords mismatch | Inline validation error |
| Weak password | Strength requirement error |
