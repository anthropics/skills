# MFA Template

Tests 2FA TOTP code entry, backup codes, and MFA enrollment flow.

## Prerequisites
- MFA-enabled account: `{{mfaUsername}}` / `{{mfaPassword}}`
- TOTP secret for generating codes: `{{totpSecret}}`
- Backup code: `{{backupCode}}`
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';
import { authenticator } from 'otplib'; // npm i otplib

test.describe('MFA', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/login');
    await page.getByRole('textbox', { name: /email/i }).fill('{{mfaUsername}}');
    await page.getByRole('textbox', { name: /password/i }).fill('{{mfaPassword}}');
    await page.getByRole('button', { name: /sign in/i }).click();
    await expect(page).toHaveURL(/\/mfa|\/two-factor/);
  });

  // Happy path: valid TOTP code
  test('accepts valid TOTP code', async ({ page }) => {
    const token = authenticator.generate('{{totpSecret}}');
    await page.getByRole('textbox', { name: /code|token/i }).fill(token);
    await page.getByRole('button', { name: /verify/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/dashboard');
  });

  // Happy path: backup code
  test('accepts backup code', async ({ page }) => {
    await page.getByRole('link', { name: /use backup code/i }).click();
    await page.getByRole('textbox', { name: /backup code/i }).fill('{{backupCode}}');
    await page.getByRole('button', { name: /verify/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/dashboard');
    // Backup code consumed — warning shown
    await expect(page.getByRole('alert')).toContainText(/backup code used/i);
  });

  // Error case: wrong TOTP code
  test('rejects invalid TOTP code', async ({ page }) => {
    await page.getByRole('textbox', { name: /code|token/i }).fill('000000');
    await page.getByRole('button', { name: /verify/i }).click();
    await expect(page.getByRole('alert')).toContainText(/invalid.*code/i);
    await expect(page).toHaveURL(/\/mfa|\/two-factor/);
  });

  // Error case: expired code (simulate by providing code + 1 step)
  test('rejects expired TOTP code', async ({ page }) => {
    const expiredToken = authenticator.generate('{{totpSecret}}');
    // Advance time simulation via clock if supported, else use a fixed stale code
    await page.getByRole('textbox', { name: /code|token/i }).fill(expiredToken);
    await page.clock.fastForward(60_000); // advance 60s past TOTP window
    await page.getByRole('button', { name: /verify/i }).click();
    await expect(page.getByRole('alert')).toContainText(/expired|invalid.*code/i);
  });

  // Edge case: MFA enrollment for new user
  test('enrolls MFA via QR code scan', async ({ page: enrollPage }) => {
    await enrollPage.goto('{{baseUrl}}/settings/security');
    await enrollPage.getByRole('button', { name: /enable.*two-factor/i }).click();
    await expect(enrollPage.getByRole('img', { name: /qr code/i })).toBeVisible();
    await expect(enrollPage.getByText(/scan.*authenticator/i)).toBeVisible();
    // User scans QR → enters token
    const token = authenticator.generate('{{totpSecret}}');
    await enrollPage.getByRole('textbox', { name: /verification code/i }).fill(token);
    await enrollPage.getByRole('button', { name: /activate/i }).click();
    await expect(enrollPage.getByRole('heading', { name: /backup codes/i })).toBeVisible();
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');
const { authenticator } = require('otplib');

test.describe('MFA', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/login');
    await page.getByRole('textbox', { name: /email/i }).fill('{{mfaUsername}}');
    await page.getByRole('textbox', { name: /password/i }).fill('{{mfaPassword}}');
    await page.getByRole('button', { name: /sign in/i }).click();
    await expect(page).toHaveURL(/\/mfa|\/two-factor/);
  });

  test('accepts valid TOTP code', async ({ page }) => {
    const token = authenticator.generate('{{totpSecret}}');
    await page.getByRole('textbox', { name: /code|token/i }).fill(token);
    await page.getByRole('button', { name: /verify/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/dashboard');
  });

  test('accepts backup code', async ({ page }) => {
    await page.getByRole('link', { name: /use backup code/i }).click();
    await page.getByRole('textbox', { name: /backup code/i }).fill('{{backupCode}}');
    await page.getByRole('button', { name: /verify/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/dashboard');
  });

  test('rejects invalid TOTP code', async ({ page }) => {
    await page.getByRole('textbox', { name: /code|token/i }).fill('000000');
    await page.getByRole('button', { name: /verify/i }).click();
    await expect(page.getByRole('alert')).toContainText(/invalid.*code/i);
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Valid TOTP | Correct time-based code → dashboard |
| Backup code | Single-use backup code accepted; warning shown |
| Invalid code | Wrong code → alert, stays on MFA page |
| Expired code | Clock-advanced token rejected |
| MFA enrollment | QR shown → token verified → backup codes displayed |
