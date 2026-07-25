# First-Time Setup Template

Tests initial configuration wizard and profile completion after registration.

## Prerequisites
- Newly registered session via `{{newUserStorageStatePath}}`
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('First-Time Setup', () => {
  test.use({ storageState: '{{newUserStorageStatePath}}' });

  // Happy path: setup wizard shown on first login
  test('shows setup wizard on first login', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await expect(page).toHaveURL(/\/setup|\/onboarding/);
    await expect(page.getByRole('heading', { name: /set up.*account|get started/i })).toBeVisible();
  });

  // Happy path: complete organisation setup step
  test('completes organisation details step', async ({ page }) => {
    await page.goto('{{baseUrl}}/setup');
    await page.getByRole('textbox', { name: /organisation.*name|company/i }).fill('{{orgName}}');
    await page.getByRole('combobox', { name: /industry/i }).selectOption('{{industry}}');
    await page.getByRole('spinbutton', { name: /team size/i }).fill('{{teamSize}}');
    await page.getByRole('button', { name: /next|continue/i }).click();
    await expect(page.getByText(/step 2|preferences/i)).toBeVisible();
  });

  // Happy path: complete preferences step
  test('completes preferences step', async ({ page }) => {
    await page.goto('{{baseUrl}}/setup/preferences');
    await page.getByRole('combobox', { name: /timezone/i }).selectOption('{{timezone}}');
    await page.getByRole('combobox', { name: /language/i }).selectOption('{{language}}');
    await page.getByRole('button', { name: /next|continue/i }).click();
    await expect(page.getByText(/step 3|invite|done/i)).toBeVisible();
  });

  // Happy path: full wizard completion redirects to dashboard
  test('completes all setup steps and lands on dashboard', async ({ page }) => {
    await page.goto('{{baseUrl}}/setup');
    // Step 1
    await page.getByRole('textbox', { name: /organisation.*name/i }).fill('{{orgName}}');
    await page.getByRole('button', { name: /next/i }).click();
    // Step 2
    await page.getByRole('combobox', { name: /timezone/i }).selectOption('{{timezone}}');
    await page.getByRole('button', { name: /next/i }).click();
    // Final step
    await page.getByRole('button', { name: /finish|go to dashboard/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/dashboard');
  });

  // Happy path: setup completion percentage shown
  test('progress indicator updates on each step', async ({ page }) => {
    await page.goto('{{baseUrl}}/setup');
    await expect(page.getByRole('progressbar')).toHaveAttribute('aria-valuenow', '0');
    await page.getByRole('textbox', { name: /organisation.*name/i }).fill('{{orgName}}');
    await page.getByRole('button', { name: /next/i }).click();
    await expect(page.getByRole('progressbar')).not.toHaveAttribute('aria-valuenow', '0');
  });

  // Error case: required setup field missing
  test('shows validation when required field missing', async ({ page }) => {
    await page.goto('{{baseUrl}}/setup');
    await page.getByRole('button', { name: /next/i }).click();
    await expect(page.getByText(/organisation.*required|required/i)).toBeVisible();
  });

  // Edge case: setup not required on subsequent login
  test('skips setup on second login', async ({ page }) => {
    // Complete setup
    await page.goto('{{baseUrl}}/setup');
    await page.getByRole('textbox', { name: /organisation.*name/i }).fill('{{orgName}}');
    await page.getByRole('button', { name: /next/i }).click();
    await page.getByRole('button', { name: /finish/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/dashboard');
    // Reload — setup not re-triggered
    await page.reload();
    await expect(page).toHaveURL('{{baseUrl}}/dashboard');
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('First-Time Setup', () => {
  test.use({ storageState: '{{newUserStorageStatePath}}' });

  test('redirects to setup wizard on first login', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await expect(page).toHaveURL(/\/setup|\/onboarding/);
  });

  test('shows validation for missing required field', async ({ page }) => {
    await page.goto('{{baseUrl}}/setup');
    await page.getByRole('button', { name: /next/i }).click();
    await expect(page.getByText(/required/i)).toBeVisible();
  });

  test('completes setup and lands on dashboard', async ({ page }) => {
    await page.goto('{{baseUrl}}/setup');
    await page.getByRole('textbox', { name: /organisation.*name/i }).fill('{{orgName}}');
    await page.getByRole('button', { name: /next/i }).click();
    await page.getByRole('button', { name: /finish|go to dashboard/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/dashboard');
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Setup on first login | Redirected to /setup wizard |
| Org details step | Company name + industry filled |
| Preferences step | Timezone + language selected |
| Full completion | All steps → dashboard |
| Progress bar | Progressbar value updates per step |
| Required field | Empty step blocked with error |
| Skip on re-login | Setup not triggered again |
