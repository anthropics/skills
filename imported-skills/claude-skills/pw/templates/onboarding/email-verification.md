# Email Verification Template

Tests email verification link, resend flow, and expired token handling.

## Prerequisites
- Registered but unverified account: `{{unverifiedEmail}}`
- Valid token: `{{verificationToken}}`
- Expired token: `{{expiredVerificationToken}}`
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Email Verification', () => {
  // Happy path: valid verification link
  test('verifies email with valid token', async ({ page }) => {
    await page.goto('{{baseUrl}}/verify-email?token={{verificationToken}}');
    await expect(page.getByRole('heading', { name: /email verified|verified/i })).toBeVisible();
    await expect(page.getByRole('link', { name: /continue|go to dashboard/i })).toBeVisible();
  });

  // Happy path: continues to app after verification
  test('redirects to dashboard after clicking continue', async ({ page }) => {
    await page.goto('{{baseUrl}}/verify-email?token={{verificationToken}}');
    await page.getByRole('link', { name: /continue|go to dashboard/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/dashboard');
  });

  // Happy path: resend verification email
  test('resends verification email', async ({ page }) => {
    await page.goto('{{baseUrl}}/verify-email/resend');
    await page.getByRole('textbox', { name: /email/i }).fill('{{unverifiedEmail}}');
    await page.getByRole('button', { name: /resend/i }).click();
    await expect(page.getByRole('alert')).toContainText(/sent|check your email/i);
  });

  // Happy path: verification prompt on login for unverified user
  test('shows verification prompt when unverified user logs in', async ({ page }) => {
    await page.goto('{{baseUrl}}/login');
    await page.getByRole('textbox', { name: /email/i }).fill('{{unverifiedEmail}}');
    await page.getByRole('textbox', { name: /password/i }).fill('{{password}}');
    await page.getByRole('button', { name: /sign in/i }).click();
    await expect(page.getByText(/verify.*email|check.*inbox/i)).toBeVisible();
    await expect(page.getByRole('button', { name: /resend.*verification/i })).toBeVisible();
  });

  // Error case: expired token
  test('shows error for expired verification token', async ({ page }) => {
    await page.goto('{{baseUrl}}/verify-email?token={{expiredVerificationToken}}');
    await expect(page.getByRole('heading', { name: /link.*expired|verification.*failed/i })).toBeVisible();
    await expect(page.getByRole('link', { name: /resend|request new/i })).toBeVisible();
  });

  // Error case: invalid token
  test('shows error for invalid verification token', async ({ page }) => {
    await page.goto('{{baseUrl}}/verify-email?token=invalid-token-xyz');
    await expect(page.getByRole('heading', { name: /invalid|failed/i })).toBeVisible();
  });

  // Edge case: already verified user hitting link
  test('shows already verified message for used token', async ({ page }) => {
    await page.goto('{{baseUrl}}/verify-email?token={{usedVerificationToken}}');
    await expect(page.getByText(/already verified|email.*confirmed/i)).toBeVisible();
    await expect(page.getByRole('link', { name: /sign in/i })).toBeVisible();
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Email Verification', () => {
  test('verifies email with valid token', async ({ page }) => {
    await page.goto('{{baseUrl}}/verify-email?token={{verificationToken}}');
    await expect(page.getByRole('heading', { name: /email verified/i })).toBeVisible();
  });

  test('shows error for expired token', async ({ page }) => {
    await page.goto('{{baseUrl}}/verify-email?token={{expiredVerificationToken}}');
    await expect(page.getByRole('heading', { name: /link.*expired/i })).toBeVisible();
    await expect(page.getByRole('link', { name: /resend|request new/i })).toBeVisible();
  });

  test('resends verification email', async ({ page }) => {
    await page.goto('{{baseUrl}}/verify-email/resend');
    await page.getByRole('textbox', { name: /email/i }).fill('{{unverifiedEmail}}');
    await page.getByRole('button', { name: /resend/i }).click();
    await expect(page.getByRole('alert')).toContainText(/sent/i);
  });

  test('shows verification prompt on login for unverified user', async ({ page }) => {
    await page.goto('{{baseUrl}}/login');
    await page.getByRole('textbox', { name: /email/i }).fill('{{unverifiedEmail}}');
    await page.getByRole('textbox', { name: /password/i }).fill('{{password}}');
    await page.getByRole('button', { name: /sign in/i }).click();
    await expect(page.getByText(/verify.*email/i)).toBeVisible();
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Valid token | Email verified heading + continue link |
| Continue CTA | Navigates to dashboard |
| Resend | Sends new email, success alert |
| Login prompt | Unverified login shows resend button |
| Expired token | Error heading + resend link |
| Invalid token | Generic error heading |
| Already verified | "Already verified" with login link |
