# Single-Step Form Template

Tests simple form submission with success and validation scenarios.

## Prerequisites
- Authenticated session via `{{authStorageStatePath}}`
- Form at `{{baseUrl}}/{{formPath}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Single-Step Form — {{formName}}', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/{{formPath}}');
  });

  // Happy path: successful submission
  test('submits form with valid data', async ({ page }) => {
    await page.getByRole('textbox', { name: /{{field1Label}}/i }).fill('{{field1Value}}');
    await page.getByRole('textbox', { name: /{{field2Label}}/i }).fill('{{field2Value}}');
    await page.getByRole('combobox', { name: /{{field3Label}}/i }).selectOption('{{field3Value}}');
    await page.getByRole('button', { name: /submit|save/i }).click();
    await expect(page.getByRole('alert')).toContainText(/submitted|saved successfully/i);
  });

  // Happy path: success redirect
  test('redirects to success page after submission', async ({ page }) => {
    await page.getByRole('textbox', { name: /{{field1Label}}/i }).fill('{{field1Value}}');
    await page.getByRole('button', { name: /submit|save/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/{{successPath}}');
  });

  // Happy path: reset clears form
  test('reset button clears all fields', async ({ page }) => {
    await page.getByRole('textbox', { name: /{{field1Label}}/i }).fill('some value');
    await page.getByRole('button', { name: /reset|clear/i }).click();
    await expect(page.getByRole('textbox', { name: /{{field1Label}}/i })).toHaveValue('');
  });

  // Error case: required field missing
  test('shows required field error', async ({ page }) => {
    await page.getByRole('button', { name: /submit|save/i }).click();
    await expect(page.getByText(/{{field1Label}}.*required|required/i)).toBeVisible();
    await expect(page.getByRole('textbox', { name: /{{field1Label}}/i })).toBeFocused();
  });

  // Error case: invalid email format
  test('shows format error for invalid email', async ({ page }) => {
    await page.getByRole('textbox', { name: /email/i }).fill('not-an-email');
    await page.getByRole('button', { name: /submit|save/i }).click();
    await expect(page.getByText(/valid.*email|invalid.*email/i)).toBeVisible();
  });

  // Error case: server error on submit
  test('shows generic error when server returns 500', async ({ page }) => {
    await page.route('{{baseUrl}}/api/{{formEndpoint}}', route =>
      route.fulfill({ status: 500, body: JSON.stringify({ error: 'Server Error' }) })
    );
    await page.getByRole('textbox', { name: /{{field1Label}}/i }).fill('{{field1Value}}');
    await page.getByRole('button', { name: /submit|save/i }).click();
    await expect(page.getByRole('alert')).toContainText(/error|something went wrong/i);
  });

  // Edge case: double submit prevented
  test('disables submit button after first click', async ({ page }) => {
    await page.getByRole('textbox', { name: /{{field1Label}}/i }).fill('{{field1Value}}');
    const btn = page.getByRole('button', { name: /submit|save/i });
    await btn.click();
    await expect(btn).toBeDisabled();
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Single-Step Form — {{formName}}', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/{{formPath}}');
  });

  test('submits form with valid data', async ({ page }) => {
    await page.getByRole('textbox', { name: /{{field1Label}}/i }).fill('{{field1Value}}');
    await page.getByRole('textbox', { name: /{{field2Label}}/i }).fill('{{field2Value}}');
    await page.getByRole('button', { name: /submit|save/i }).click();
    await expect(page.getByRole('alert')).toContainText(/submitted|saved/i);
  });

  test('shows required error for empty submission', async ({ page }) => {
    await page.getByRole('button', { name: /submit|save/i }).click();
    await expect(page.getByText(/required/i)).toBeVisible();
  });

  test('disables submit after click (prevents double submit)', async ({ page }) => {
    await page.getByRole('textbox', { name: /{{field1Label}}/i }).fill('{{field1Value}}');
    const btn = page.getByRole('button', { name: /submit|save/i });
    await btn.click();
    await expect(btn).toBeDisabled();
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Valid submit | All fields filled → success message |
| Success redirect | Navigates to success URL |
| Reset | All fields cleared |
| Required field | Empty submit → first error focused |
| Invalid email | Format error shown |
| Server 500 | Generic error alert |
| Double submit | Button disabled after first click |
