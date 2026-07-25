# Form Validation Template

Tests required fields, format validation, and inline error messages.

## Prerequisites
- Form at `{{baseUrl}}/{{formPath}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Form Validation', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/{{formPath}}');
  });

  // Happy path: all errors resolved on re-submit
  test('clears errors when valid data entered', async ({ page }) => {
    await page.getByRole('button', { name: /submit/i }).click();
    await expect(page.getByText(/required/i)).toBeVisible();
    await page.getByRole('textbox', { name: /{{requiredField}}/i }).fill('{{validValue}}');
    await page.getByRole('button', { name: /submit/i }).click();
    await expect(page.getByText(/required/i)).toBeHidden();
  });

  // Error case: required fields
  test('shows required error for each empty required field', async ({ page }) => {
    await page.getByRole('button', { name: /submit/i }).click();
    const requiredErrors = page.getByText(/is required|required field/i);
    await expect(requiredErrors.first()).toBeVisible();
  });

  // Error case: invalid email format
  test('shows error for invalid email format', async ({ page }) => {
    await page.getByRole('textbox', { name: /email/i }).fill('bad@');
    await page.getByRole('textbox', { name: /email/i }).blur();
    await expect(page.getByText(/valid.*email|enter.*valid email/i)).toBeVisible();
  });

  // Error case: invalid phone format
  test('shows error for invalid phone number', async ({ page }) => {
    await page.getByRole('textbox', { name: /phone/i }).fill('123');
    await page.getByRole('textbox', { name: /phone/i }).blur();
    await expect(page.getByText(/valid.*phone|invalid phone/i)).toBeVisible();
  });

  // Error case: password too short
  test('shows error when password is too short', async ({ page }) => {
    await page.getByRole('textbox', { name: /^password$/i }).fill('abc');
    await page.getByRole('textbox', { name: /^password$/i }).blur();
    await expect(page.getByText(/at least \d+ characters/i)).toBeVisible();
  });

  // Error case: passwords do not match
  test('shows error when confirm password does not match', async ({ page }) => {
    await page.getByRole('textbox', { name: /^password$/i }).fill('{{validPassword}}');
    await page.getByRole('textbox', { name: /confirm password/i }).fill('different');
    await page.getByRole('textbox', { name: /confirm password/i }).blur();
    await expect(page.getByText(/passwords.*do not match/i)).toBeVisible();
  });

  // Error case: inline error on blur (not on submit)
  test('shows inline error on blur for invalid value', async ({ page }) => {
    await page.getByRole('textbox', { name: /email/i }).fill('invalid');
    await page.getByRole('textbox', { name: /email/i }).blur();
    // Error shown immediately, not waiting for submit
    await expect(page.getByText(/valid.*email/i)).toBeVisible();
  });

  // Error case: field-level errors tied to field via aria-describedby
  test('error message is associated with field via aria', async ({ page }) => {
    await page.getByRole('button', { name: /submit/i }).click();
    const emailField = page.getByRole('textbox', { name: /email/i });
    const errorId = await emailField.getAttribute('aria-describedby');
    expect(errorId).toBeTruthy();
    await expect(page.locator(`#${errorId}`)).toBeVisible();
  });

  // Edge case: field max-length validation
  test('shows error when input exceeds max length', async ({ page }) => {
    await page.getByRole('textbox', { name: /{{field}}/i }).fill('A'.repeat({{maxLength}} + 1));
    await page.getByRole('textbox', { name: /{{field}}/i }).blur();
    await expect(page.getByText(/max.*{{maxLength}}|too long/i)).toBeVisible();
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Form Validation', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/{{formPath}}');
  });

  test('shows required errors on empty submit', async ({ page }) => {
    await page.getByRole('button', { name: /submit/i }).click();
    await expect(page.getByText(/is required|required field/i).first()).toBeVisible();
  });

  test('shows error for invalid email on blur', async ({ page }) => {
    await page.getByRole('textbox', { name: /email/i }).fill('bad@');
    await page.getByRole('textbox', { name: /email/i }).blur();
    await expect(page.getByText(/valid.*email/i)).toBeVisible();
  });

  test('passwords mismatch error shown', async ({ page }) => {
    await page.getByRole('textbox', { name: /^password$/i }).fill('{{validPassword}}');
    await page.getByRole('textbox', { name: /confirm password/i }).fill('other');
    await page.getByRole('textbox', { name: /confirm password/i }).blur();
    await expect(page.getByText(/do not match/i)).toBeVisible();
  });

  test('clears errors when valid data entered', async ({ page }) => {
    await page.getByRole('button', { name: /submit/i }).click();
    await page.getByRole('textbox', { name: /{{requiredField}}/i }).fill('{{validValue}}');
    await page.getByRole('button', { name: /submit/i }).click();
    await expect(page.getByText(/required/i)).toBeHidden();
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Error cleared | Valid input → errors removed on next submit |
| Required fields | Empty submit → at least one required error |
| Email format | Blur with bad email → inline error |
| Phone format | Invalid phone → inline error |
| Password length | Too short → character count error |
| Password match | Mismatch → confirmation error |
| Blur validation | Error shown on blur, not just submit |
| aria-describedby | Error programmatically linked to field |
| Max length | Exceeded length → error shown |
