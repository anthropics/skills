# Profile Update Template

Tests updating name, email, and avatar in user profile settings.

## Prerequisites
- Authenticated session via `{{authStorageStatePath}}`
- Current name: `{{currentName}}`, email: `{{currentEmail}}`
- Test avatar image: `{{avatarFilePath}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Profile Update', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/settings/profile');
  });

  // Happy path: update display name
  test('updates display name', async ({ page }) => {
    const nameField = page.getByRole('textbox', { name: /display name|full name/i });
    await nameField.clear();
    await nameField.fill('{{newName}}');
    await page.getByRole('button', { name: /save|update/i }).click();
    await expect(page.getByRole('alert')).toContainText(/profile updated|saved/i);
    await expect(page.getByRole('textbox', { name: /display name|full name/i })).toHaveValue('{{newName}}');
  });

  // Happy path: update email
  test('updates email address', async ({ page }) => {
    const emailField = page.getByRole('textbox', { name: /email/i });
    await emailField.clear();
    await emailField.fill('{{newEmail}}');
    await page.getByRole('button', { name: /save|update/i }).click();
    await expect(page.getByRole('alert')).toContainText(/verification.*sent|email updated/i);
  });

  // Happy path: upload avatar
  test('uploads new avatar image', async ({ page }) => {
    await page.getByRole('button', { name: /change.*avatar|upload.*photo/i }).click();
    await page.locator('input[type="file"]').setInputFiles('{{avatarFilePath}}');
    await expect(page.getByRole('img', { name: /avatar preview/i })).toBeVisible();
    await page.getByRole('button', { name: /save|apply/i }).click();
    await expect(page.getByRole('alert')).toContainText(/avatar updated|photo saved/i);
  });

  // Happy path: avatar crop dialog
  test('shows crop dialog after avatar upload', async ({ page }) => {
    await page.locator('input[type="file"]').setInputFiles('{{avatarFilePath}}');
    await expect(page.getByRole('dialog', { name: /crop/i })).toBeVisible();
    await page.getByRole('button', { name: /apply crop/i }).click();
    await expect(page.getByRole('dialog', { name: /crop/i })).toBeHidden();
  });

  // Error case: invalid email format
  test('shows error for invalid email format', async ({ page }) => {
    await page.getByRole('textbox', { name: /email/i }).clear();
    await page.getByRole('textbox', { name: /email/i }).fill('bad-email');
    await page.getByRole('button', { name: /save|update/i }).click();
    await expect(page.getByText(/valid.*email/i)).toBeVisible();
  });

  // Error case: email already taken
  test('shows error when email is already in use', async ({ page }) => {
    await page.getByRole('textbox', { name: /email/i }).clear();
    await page.getByRole('textbox', { name: /email/i }).fill('{{takenEmail}}');
    await page.getByRole('button', { name: /save|update/i }).click();
    await expect(page.getByRole('alert')).toContainText(/already in use|taken/i);
  });

  // Edge case: name reflected in nav after update
  test('nav shows updated name after save', async ({ page }) => {
    const nameField = page.getByRole('textbox', { name: /display name|full name/i });
    await nameField.clear();
    await nameField.fill('{{newName}}');
    await page.getByRole('button', { name: /save|update/i }).click();
    await expect(page.getByRole('navigation').getByText('{{newName}}')).toBeVisible();
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Profile Update', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test('updates display name', async ({ page }) => {
    await page.goto('{{baseUrl}}/settings/profile');
    await page.getByRole('textbox', { name: /display name|full name/i }).clear();
    await page.getByRole('textbox', { name: /display name|full name/i }).fill('{{newName}}');
    await page.getByRole('button', { name: /save|update/i }).click();
    await expect(page.getByRole('alert')).toContainText(/profile updated|saved/i);
  });

  test('shows error for invalid email', async ({ page }) => {
    await page.goto('{{baseUrl}}/settings/profile');
    await page.getByRole('textbox', { name: /email/i }).fill('bad-email');
    await page.getByRole('button', { name: /save|update/i }).click();
    await expect(page.getByText(/valid.*email/i)).toBeVisible();
  });

  test('uploads avatar image', async ({ page }) => {
    await page.goto('{{baseUrl}}/settings/profile');
    await page.locator('input[type="file"]').setInputFiles('{{avatarFilePath}}');
    await page.getByRole('button', { name: /save|apply/i }).click();
    await expect(page.getByRole('alert')).toContainText(/avatar updated/i);
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Name update | Name saved, field reflects new value |
| Email update | Email saved, verification notice shown |
| Avatar upload | Image uploaded, success alert |
| Crop dialog | Cropper shown, apply saves |
| Invalid email | Format error shown |
| Taken email | Duplicate error shown |
| Nav update | Navigation reflects new name |
