# Multi-Step Form (Wizard) Template

Tests wizard step navigation, validation per step, and final submission.

## Prerequisites
- Form wizard at `{{baseUrl}}/{{wizardPath}}`
- Steps: Step 1 (personal), Step 2 (details), Step 3 (review)

---

## TypeScript

```typescript
import { test, expect, Page } from '@playwright/test';

async function completeStep1(page: Page): Promise<void> {
  await page.getByRole('textbox', { name: /first name/i }).fill('{{firstName}}');
  await page.getByRole('textbox', { name: /last name/i }).fill('{{lastName}}');
  await page.getByRole('textbox', { name: /email/i }).fill('{{email}}');
  await page.getByRole('button', { name: /next/i }).click();
}

async function completeStep2(page: Page): Promise<void> {
  await page.getByRole('combobox', { name: /{{step2Field}}/i }).selectOption('{{step2Value}}');
  await page.getByRole('textbox', { name: /{{step2TextField}}/i }).fill('{{step2TextValue}}');
  await page.getByRole('button', { name: /next/i }).click();
}

test.describe('Multi-Step Form', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/{{wizardPath}}');
  });

  // Happy path: complete all steps
  test('completes all wizard steps and submits', async ({ page }) => {
    await expect(page.getByText(/step 1/i)).toBeVisible();
    await completeStep1(page);
    await expect(page.getByText(/step 2/i)).toBeVisible();
    await completeStep2(page);
    await expect(page.getByText(/review|step 3/i)).toBeVisible();
    // Review page shows entered data
    await expect(page.getByText('{{firstName}}')).toBeVisible();
    await page.getByRole('button', { name: /submit|finish/i }).click();
    await expect(page).toHaveURL(/\/{{successPath}}/);
  });

  // Happy path: step indicator updates
  test('step indicator reflects current step', async ({ page }) => {
    const step1 = page.getByRole('listitem', { name: /step 1/i });
    await expect(step1).toHaveAttribute('aria-current', 'step');
    await completeStep1(page);
    const step2 = page.getByRole('listitem', { name: /step 2/i });
    await expect(step2).toHaveAttribute('aria-current', 'step');
  });

  // Happy path: back navigation
  test('navigates back to previous step without losing data', async ({ page }) => {
    await completeStep1(page);
    await page.getByRole('button', { name: /back|previous/i }).click();
    await expect(page.getByRole('textbox', { name: /first name/i })).toHaveValue('{{firstName}}');
  });

  // Happy path: completed steps accessible via indicator
  test('clicking completed step in indicator navigates back', async ({ page }) => {
    await completeStep1(page);
    await page.getByRole('button', { name: /step 1/i }).click();
    await expect(page.getByRole('textbox', { name: /first name/i })).toBeVisible();
  });

  // Error case: cannot proceed with invalid step 1 data
  test('stays on step 1 when required field missing', async ({ page }) => {
    await page.getByRole('button', { name: /next/i }).click();
    await expect(page.getByText(/first name.*required|required/i)).toBeVisible();
    await expect(page.getByText(/step 1/i)).toBeVisible();
  });

  // Error case: future step not accessible directly
  test('cannot access step 3 without completing step 2', async ({ page }) => {
    await expect(page.getByRole('button', { name: /step 3/i })).toBeDisabled();
  });

  // Edge case: browser back button handled
  test('browser back from step 2 returns to step 1 with data', async ({ page }) => {
    await completeStep1(page);
    await page.goBack();
    await expect(page.getByRole('textbox', { name: /first name/i })).toHaveValue('{{firstName}}');
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Multi-Step Form', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/{{wizardPath}}');
  });

  test('completes all wizard steps and submits', async ({ page }) => {
    await page.getByRole('textbox', { name: /first name/i }).fill('{{firstName}}');
    await page.getByRole('textbox', { name: /email/i }).fill('{{email}}');
    await page.getByRole('button', { name: /next/i }).click();
    await page.getByRole('combobox', { name: /{{step2Field}}/i }).selectOption('{{step2Value}}');
    await page.getByRole('button', { name: /next/i }).click();
    await page.getByRole('button', { name: /submit|finish/i }).click();
    await expect(page).toHaveURL(/\/{{successPath}}/);
  });

  test('stays on step 1 when required field missing', async ({ page }) => {
    await page.getByRole('button', { name: /next/i }).click();
    await expect(page.getByText(/required/i)).toBeVisible();
  });

  test('navigates back without losing data', async ({ page }) => {
    await page.getByRole('textbox', { name: /first name/i }).fill('{{firstName}}');
    await page.getByRole('textbox', { name: /email/i }).fill('{{email}}');
    await page.getByRole('button', { name: /next/i }).click();
    await page.getByRole('button', { name: /back|previous/i }).click();
    await expect(page.getByRole('textbox', { name: /first name/i })).toHaveValue('{{firstName}}');
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Full completion | All steps filled → submit → success URL |
| Step indicator | aria-current updates per step |
| Back navigation | Data preserved on back |
| Completed step click | Step indicator link works |
| Validation | Required field blocks Next |
| Locked future step | Step 3 button disabled until step 2 done |
| Browser back | History navigation preserves data |
