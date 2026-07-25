# Password Change Template

Tests current password verification, new password validation, and success flow.

## Prerequisites
- Authenticated session via `{{authStorageStatePath}}`
- Current password: `{{currentPassword}}`
- New password: `{{newPassword}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Password Change', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/settings/security');
  });

  // Happy path: successful password change
  test('changes password with valid inputs', async ({ page }) => {
    await page.getByRole('textbox', { name: /current password/i }).fill('{{currentPassword}}');
    await page.getByRole('textbox', { name: /^new password$/i }).fill('{{newPassword}}');
    await page.getByRole('textbox', { name: /confirm.*password/i }).fill('{{newPassword}}');
    await page.getByRole('button', { name: /change.*password|update password/i }).click();
    await expect(page.getByRole('alert')).toContainText(/password.*changed|updated successfully/i);
  });

  // Happy path: can log in with new password
  test('new password accepted on next login', async ({ page, context }) => {
    // Change password
    await page.getByRole('textbox', { name: /current password/i }).fill('{{currentPassword}}');
    await page.getByRole('textbox', { name: /^new password$/i }).fill('{{newPassword}}');
    await page.getByRole('textbox', { name: /confirm.*password/i }).fill('{{newPassword}}');
    await page.getByRole('button', { name: /change.*password/i }).click();
    await expect(page.getByRole('alert')).toContainText(/changed/i);
    // Log out and back in
    await page.getByRole('button', { name: /user menu/i }).click();
    await page.getByRole('menuitem', { name: /sign out/i }).click();
    await page.getByRole('textbox', { name: /email/i }).fill('{{username}}');
    await page.getByRole('textbox', { name: /password/i }).fill('{{newPassword}}');
    await page.getByRole('button', { name: /sign in/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/dashboard');
  });

  // Error case: wrong current password
  test('shows error when current password is wrong', async ({ page }) => {
    await page.getByRole('textbox', { name: /current password/i }).fill('wrong-password');
    await page.getByRole('textbox', { name: /^new password$/i }).fill('{{newPassword}}');
    await page.getByRole('textbox', { name: /confirm.*password/i }).fill('{{newPassword}}');
    await page.getByRole('button', { name: /change.*password/i }).click();
    await expect(page.getByRole('alert')).toContainText(/current password.*incorrect|wrong password/i);
  });

  // Error case: new passwords do not match
  test('shows error when confirmation does not match', async ({ page }) => {
    await page.getByRole('textbox', { name: /current password/i }).fill('{{currentPassword}}');
    await page.getByRole('textbox', { name: /^new password$/i }).fill('{{newPassword}}');
    await page.getByRole('textbox', { name: /confirm.*password/i }).fill('mismatch');
    await page.getByRole('button', { name: /change.*password/i }).click();
    await expect(page.getByText(/passwords.*do not match/i)).toBeVisible();
  });

  // Error case: new password too weak
  test('shows strength error for weak new password', async ({ page }) => {
    await page.getByRole('textbox', { name: /current password/i }).fill('{{currentPassword}}');
    await page.getByRole('textbox', { name: /^new password$/i }).fill('123');
    await page.getByRole('textbox', { name: /^new password$/i }).blur();
    await expect(page.getByText(/too weak|at least \d+ characters/i)).toBeVisible();
  });

  // Error case: new password same as current
  test('shows error when new password matches current', async ({ page }) => {
    await page.getByRole('textbox', { name: /current password/i }).fill('{{currentPassword}}');
    await page.getByRole('textbox', { name: /^new password$/i }).fill('{{currentPassword}}');
    await page.getByRole('textbox', { name: /confirm.*password/i }).fill('{{currentPassword}}');
    await page.getByRole('button', { name: /change.*password/i }).click();
    await expect(page.getByText(/same as.*current|choose.*different/i)).toBeVisible();
  });

  // Edge case: password strength meter updates on input
  test('strength meter reacts to new password input', async ({ page }) => {
    await page.getByRole('textbox', { name: /^new password$/i }).fill('weak');
    await expect(page.getByRole('meter', { name: /strength/i })).toHaveAttribute('aria-valuenow', '1');
    await page.getByRole('textbox', { name: /^new password$/i }).fill('Str0ng!Pass#2026');
    await expect(page.getByRole('meter', { name: /strength/i })).toHaveAttribute('aria-valuenow', '4');
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Password Change', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test('changes password with valid inputs', async ({ page }) => {
    await page.goto('{{baseUrl}}/settings/security');
    await page.getByRole('textbox', { name: /current password/i }).fill('{{currentPassword}}');
    await page.getByRole('textbox', { name: /^new password$/i }).fill('{{newPassword}}');
    await page.getByRole('textbox', { name: /confirm.*password/i }).fill('{{newPassword}}');
    await page.getByRole('button', { name: /change.*password/i }).click();
    await expect(page.getByRole('alert')).toContainText(/changed|updated/i);
  });

  test('shows error for wrong current password', async ({ page }) => {
    await page.goto('{{baseUrl}}/settings/security');
    await page.getByRole('textbox', { name: /current password/i }).fill('wrong');
    await page.getByRole('textbox', { name: /^new password$/i }).fill('{{newPassword}}');
    await page.getByRole('textbox', { name: /confirm.*password/i }).fill('{{newPassword}}');
    await page.getByRole('button', { name: /change.*password/i }).click();
    await expect(page.getByRole('alert')).toContainText(/incorrect|wrong/i);
  });

  test('shows mismatch error', async ({ page }) => {
    await page.goto('{{baseUrl}}/settings/security');
    await page.getByRole('textbox', { name: /current password/i }).fill('{{currentPassword}}');
    await page.getByRole('textbox', { name: /^new password$/i }).fill('{{newPassword}}');
    await page.getByRole('textbox', { name: /confirm.*password/i }).fill('nope');
    await page.getByRole('button', { name: /change.*password/i }).click();
    await expect(page.getByText(/do not match/i)).toBeVisible();
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Success | All fields valid → success alert |
| Login with new pw | New password accepted at login |
| Wrong current | Incorrect current → error alert |
| Mismatch | Confirm ≠ new → validation error |
| Weak password | Short password → strength error |
| Same as current | Reuse blocked with error |
| Strength meter | Meter aria-valuenow updates on input |
