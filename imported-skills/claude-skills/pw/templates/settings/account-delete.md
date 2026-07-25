# Account Delete Template

Tests account deletion flow with confirmation and data warning.

## Prerequisites
- Authenticated session via `{{authStorageStatePath}}`
- Disposable test account (deletion is irreversible)
- Settings at `{{baseUrl}}/settings/account`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Account Delete', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/settings/account');
  });

  // Happy path: delete button opens confirmation
  test('clicking delete account shows confirmation dialog', async ({ page }) => {
    await page.getByRole('button', { name: /delete.*account/i }).click();
    const dialog = page.getByRole('dialog', { name: /delete account/i });
    await expect(dialog).toBeVisible();
    await expect(dialog).toContainText(/irreversible|cannot be undone/i);
    await expect(dialog).toContainText(/{{dataWarningText}}/i);
  });

  // Happy path: cancel preserves account
  test('cancel keeps account intact', async ({ page }) => {
    await page.getByRole('button', { name: /delete.*account/i }).click();
    await page.getByRole('dialog').getByRole('button', { name: /cancel/i }).click();
    await expect(page.getByRole('dialog')).toBeHidden();
    await expect(page).toHaveURL('{{baseUrl}}/settings/account');
  });

  // Happy path: type-to-confirm gates deletion
  test('confirm button disabled until account email typed', async ({ page }) => {
    await page.getByRole('button', { name: /delete.*account/i }).click();
    const dialog = page.getByRole('dialog');
    const confirmBtn = dialog.getByRole('button', { name: /delete.*account|confirm/i });
    await expect(confirmBtn).toBeDisabled();
    await dialog.getByRole('textbox', { name: /type.*email/i }).fill('{{username}}');
    await expect(confirmBtn).toBeEnabled();
  });

  // Happy path: successful deletion redirects to login
  test('deletes account and redirects to login', async ({ page }) => {
    await page.getByRole('button', { name: /delete.*account/i }).click();
    const dialog = page.getByRole('dialog');
    await dialog.getByRole('textbox', { name: /type.*email/i }).fill('{{username}}');
    await dialog.getByRole('button', { name: /delete.*account|confirm/i }).click();
    await expect(page).toHaveURL(/\/login/);
    await expect(page.getByText(/account.*deleted|successfully deleted/i)).toBeVisible();
  });

  // Error case: wrong email in confirmation box
  test('shows error when wrong email typed in confirmation', async ({ page }) => {
    await page.getByRole('button', { name: /delete.*account/i }).click();
    const dialog = page.getByRole('dialog');
    await dialog.getByRole('textbox', { name: /type.*email/i }).fill('wrong@email.com');
    const confirmBtn = dialog.getByRole('button', { name: /delete.*account|confirm/i });
    await expect(confirmBtn).toBeDisabled();
    await expect(dialog.getByText(/does not match/i)).toBeVisible();
  });

  // Error case: deletion fails server-side
  test('shows error when account deletion fails', async ({ page }) => {
    await page.route('{{baseUrl}}/api/account', route =>
      route.fulfill({ status: 500, body: JSON.stringify({ error: 'Deletion failed' }) })
    );
    await page.getByRole('button', { name: /delete.*account/i }).click();
    const dialog = page.getByRole('dialog');
    await dialog.getByRole('textbox', { name: /type.*email/i }).fill('{{username}}');
    await dialog.getByRole('button', { name: /confirm/i }).click();
    await expect(page.getByRole('alert')).toContainText(/failed|error/i);
    await expect(page).toHaveURL('{{baseUrl}}/settings/account');
  });

  // Edge case: data export offered before deletion
  test('shows data export option in deletion dialog', async ({ page }) => {
    await page.getByRole('button', { name: /delete.*account/i }).click();
    await expect(page.getByRole('link', { name: /export.*data|download.*data/i })).toBeVisible();
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Account Delete', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test('shows confirmation dialog on delete', async ({ page }) => {
    await page.goto('{{baseUrl}}/settings/account');
    await page.getByRole('button', { name: /delete.*account/i }).click();
    await expect(page.getByRole('dialog', { name: /delete account/i })).toBeVisible();
    await expect(page.getByRole('dialog')).toContainText(/irreversible/i);
  });

  test('confirm button disabled until email typed', async ({ page }) => {
    await page.goto('{{baseUrl}}/settings/account');
    await page.getByRole('button', { name: /delete.*account/i }).click();
    const dialog = page.getByRole('dialog');
    await expect(dialog.getByRole('button', { name: /confirm/i })).toBeDisabled();
    await dialog.getByRole('textbox', { name: /type.*email/i }).fill('{{username}}');
    await expect(dialog.getByRole('button', { name: /confirm/i })).toBeEnabled();
  });

  test('cancel preserves account', async ({ page }) => {
    await page.goto('{{baseUrl}}/settings/account');
    await page.getByRole('button', { name: /delete.*account/i }).click();
    await page.getByRole('dialog').getByRole('button', { name: /cancel/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/settings/account');
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Dialog opens | Delete button → confirmation with warning |
| Cancel | Dialog closed, account preserved |
| Type-to-confirm | Button enabled only with correct email |
| Successful delete | Account deleted → /login |
| Wrong email | Input mismatch → button stays disabled |
| Server error | Deletion fails → error alert |
| Data export | Export link offered in dialog |
