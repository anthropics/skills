# Welcome Tour Template

Tests step-by-step onboarding tour, skip, and completion behaviour.

## Prerequisites
- Newly registered session (first login) via `{{newUserStorageStatePath}}`
- Tour has `{{tourStepCount}}` steps
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Welcome Tour', () => {
  test.use({ storageState: '{{newUserStorageStatePath}}' });

  // Happy path: tour shown on first login
  test('shows welcome tour on first login', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await expect(page.getByRole('dialog', { name: /welcome|tour/i })).toBeVisible();
    await expect(page.getByText(/step 1 of {{tourStepCount}}/i)).toBeVisible();
  });

  // Happy path: advance through all steps
  test('advances through all tour steps', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    for (let i = 1; i <= {{tourStepCount}}; i++) {
      await expect(page.getByText(new RegExp(`step ${i} of {{tourStepCount}}`, 'i'))).toBeVisible();
      if (i < {{tourStepCount}}) {
        await page.getByRole('button', { name: /next/i }).click();
      } else {
        await page.getByRole('button', { name: /finish|done|get started/i }).click();
      }
    }
    await expect(page.getByRole('dialog', { name: /welcome|tour/i })).toBeHidden();
  });

  // Happy path: back navigation within tour
  test('navigates back to previous step', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.getByRole('button', { name: /next/i }).click();
    await expect(page.getByText(/step 2 of {{tourStepCount}}/i)).toBeVisible();
    await page.getByRole('button', { name: /back|previous/i }).click();
    await expect(page.getByText(/step 1 of {{tourStepCount}}/i)).toBeVisible();
  });

  // Happy path: skip tour
  test('skips tour and dismisses overlay', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.getByRole('button', { name: /skip.*tour|skip/i }).click();
    await expect(page.getByRole('dialog', { name: /welcome|tour/i })).toBeHidden();
    await expect(page.getByRole('heading', { name: /dashboard/i })).toBeVisible();
  });

  // Happy path: tour not shown on subsequent logins
  test('tour not shown on second login', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    // Complete or skip tour
    await page.getByRole('button', { name: /skip.*tour|skip/i }).click();
    // Simulate re-login by reloading
    await page.reload();
    await expect(page.getByRole('dialog', { name: /welcome|tour/i })).toBeHidden();
  });

  // Happy path: tooltip highlights correct element
  test('tour tooltip highlights the correct UI element', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    const tooltip = page.getByRole('tooltip').or(page.getByRole('dialog', { name: /tour/i }));
    await expect(tooltip).toBeVisible();
    const targetEl = page.getByRole('{{tourStep1TargetRole}}', { name: /{{tourStep1TargetName}}/i });
    await expect(targetEl).toBeVisible();
  });

  // Edge case: close button (×) dismisses tour
  test('× button dismisses tour', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.getByRole('dialog', { name: /welcome|tour/i })
      .getByRole('button', { name: /close|×/i }).click();
    await expect(page.getByRole('dialog', { name: /welcome|tour/i })).toBeHidden();
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Welcome Tour', () => {
  test.use({ storageState: '{{newUserStorageStatePath}}' });

  test('shows welcome tour on first login', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await expect(page.getByRole('dialog', { name: /welcome|tour/i })).toBeVisible();
  });

  test('skips tour on button click', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.getByRole('button', { name: /skip/i }).click();
    await expect(page.getByRole('dialog', { name: /tour/i })).toBeHidden();
  });

  test('advances through all steps to completion', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    for (let i = 1; i < {{tourStepCount}}; i++) {
      await page.getByRole('button', { name: /next/i }).click();
    }
    await page.getByRole('button', { name: /finish|done|get started/i }).click();
    await expect(page.getByRole('dialog', { name: /tour/i })).toBeHidden();
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Tour on first login | Dialog shown with step 1 of N |
| Full completion | All steps advanced → tour dismissed |
| Back navigation | Previous step accessible |
| Skip tour | Dismissed immediately |
| Not shown again | Tour absent on subsequent visits |
| Tooltip target | Tour highlights correct element |
| Close button | × closes tour |
