# SSO Template

Tests SSO redirect flow, IdP callback handling, and attribute mapping.

## Prerequisites
- SSO provider configured (SAML / OIDC) at `{{ssoProviderUrl}}`
- Test IdP with user `{{ssoUsername}}`
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect, Page } from '@playwright/test';

async function completeSsoLogin(page: Page, username: string): Promise<void> {
  // Fill IdP login form — adapt selectors to your provider
  await page.getByRole('textbox', { name: /username/i }).fill(username);
  await page.getByRole('button', { name: /login/i }).click();
}

test.describe('SSO', () => {
  // Happy path: SSO redirect and callback
  test('redirects to IdP and returns authenticated', async ({ page }) => {
    await page.goto('{{baseUrl}}/login');
    await page.getByRole('button', { name: /sign in with sso/i }).click();
    await expect(page).toHaveURL(/{{ssoProviderDomain}}/);
    await completeSsoLogin(page, '{{ssoUsername}}');
    await expect(page).toHaveURL('{{baseUrl}}/dashboard');
    await expect(page.getByRole('heading', { name: /dashboard/i })).toBeVisible();
  });

  // Happy path: SSO with domain hint
  test('pre-fills organisation domain and redirects', async ({ page }) => {
    await page.goto('{{baseUrl}}/login');
    await page.getByRole('textbox', { name: /work email/i }).fill('{{ssoUsername}}');
    await page.getByRole('button', { name: /continue/i }).click();
    await expect(page).toHaveURL(/{{ssoProviderDomain}}/);
  });

  // Happy path: attributes mapped to user profile
  test('maps SSO attributes to user profile', async ({ page }) => {
    await page.goto('{{baseUrl}}/login');
    await page.getByRole('button', { name: /sign in with sso/i }).click();
    await completeSsoLogin(page, '{{ssoUsername}}');
    await page.goto('{{baseUrl}}/settings/profile');
    await expect(page.getByRole('textbox', { name: /email/i })).toHaveValue('{{ssoUsername}}');
  });

  // Error case: IdP returns error
  test('shows error page when IdP returns error response', async ({ page }) => {
    await page.goto('{{baseUrl}}/auth/callback?error=access_denied&error_description=User+denied+access');
    await expect(page.getByRole('alert')).toContainText(/access denied/i);
    await expect(page.getByRole('link', { name: /back to login/i })).toBeVisible();
  });

  // Error case: invalid callback state
  test('rejects callback with invalid state parameter', async ({ page }) => {
    await page.goto('{{baseUrl}}/auth/callback?code=valid_code&state=tampered_state');
    await expect(page.getByRole('alert')).toContainText(/invalid.*state|authentication failed/i);
  });

  // Edge case: SSO user first login provisions account
  test('provisions new account on first SSO login', async ({ page }) => {
    await page.goto('{{baseUrl}}/login');
    await page.getByRole('button', { name: /sign in with sso/i }).click();
    await completeSsoLogin(page, '{{newSsoUsername}}');
    await expect(page).toHaveURL(/{{baseUrl}}\/(dashboard|onboarding)/);
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

async function completeSsoLogin(page, username) {
  await page.getByRole('textbox', { name: /username/i }).fill(username);
  await page.getByRole('button', { name: /login/i }).click();
}

test.describe('SSO', () => {
  test('redirects to IdP and returns authenticated', async ({ page }) => {
    await page.goto('{{baseUrl}}/login');
    await page.getByRole('button', { name: /sign in with sso/i }).click();
    await expect(page).toHaveURL(/{{ssoProviderDomain}}/);
    await completeSsoLogin(page, '{{ssoUsername}}');
    await expect(page).toHaveURL('{{baseUrl}}/dashboard');
  });

  test('shows error when IdP returns access_denied', async ({ page }) => {
    await page.goto('{{baseUrl}}/auth/callback?error=access_denied');
    await expect(page.getByRole('alert')).toContainText(/access denied/i);
  });

  test('rejects tampered state parameter', async ({ page }) => {
    await page.goto('{{baseUrl}}/auth/callback?code=abc&state=tampered');
    await expect(page.getByRole('alert')).toContainText(/invalid.*state|authentication failed/i);
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Happy path | SSO button → IdP → callback → dashboard |
| Domain hint | Email triggers org-specific IdP redirect |
| Attribute mapping | SSO profile fields populate user record |
| IdP error | access_denied → error page with back link |
| Invalid state | CSRF protection rejects tampered callback |
| First login | Auto-provisions account on initial SSO |
