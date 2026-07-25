# Conditional Fields Template

Tests show/hide fields based on selection and correct validation of visible fields only.

## Prerequisites
- Form at `{{baseUrl}}/{{formPath}}`
- Trigger field: `{{triggerField}}` (e.g. country, type selector)
- Conditional field shown when value is `{{triggerValue}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Conditional Fields', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/{{formPath}}');
  });

  // Happy path: conditional field shown on trigger
  test('shows conditional field when trigger value selected', async ({ page }) => {
    await expect(page.getByRole('textbox', { name: /{{conditionalFieldLabel}}/i })).toBeHidden();
    await page.getByRole('combobox', { name: /{{triggerField}}/i }).selectOption('{{triggerValue}}');
    await expect(page.getByRole('textbox', { name: /{{conditionalFieldLabel}}/i })).toBeVisible();
  });

  // Happy path: conditional field hidden when trigger changes
  test('hides conditional field when trigger changes back', async ({ page }) => {
    await page.getByRole('combobox', { name: /{{triggerField}}/i }).selectOption('{{triggerValue}}');
    await expect(page.getByRole('textbox', { name: /{{conditionalFieldLabel}}/i })).toBeVisible();
    await page.getByRole('combobox', { name: /{{triggerField}}/i }).selectOption('{{nonTriggerValue}}');
    await expect(page.getByRole('textbox', { name: /{{conditionalFieldLabel}}/i })).toBeHidden();
  });

  // Happy path: form submits with conditional field filled
  test('submits form when conditional field is shown and filled', async ({ page }) => {
    await page.getByRole('combobox', { name: /{{triggerField}}/i }).selectOption('{{triggerValue}}');
    await page.getByRole('textbox', { name: /{{conditionalFieldLabel}}/i }).fill('{{conditionalFieldValue}}');
    await page.getByRole('button', { name: /submit/i }).click();
    await expect(page.getByRole('alert')).toContainText(/submitted|saved/i);
  });

  // Error case: conditional field required when visible
  test('validates conditional field when it is visible', async ({ page }) => {
    await page.getByRole('combobox', { name: /{{triggerField}}/i }).selectOption('{{triggerValue}}');
    await page.getByRole('button', { name: /submit/i }).click();
    await expect(page.getByText(/{{conditionalFieldLabel}}.*required/i)).toBeVisible();
  });

  // Error case: hidden field not validated
  test('does not validate conditional field when hidden', async ({ page }) => {
    await page.getByRole('combobox', { name: /{{triggerField}}/i }).selectOption('{{nonTriggerValue}}');
    await page.getByRole('button', { name: /submit/i }).click();
    await expect(page.getByText(/{{conditionalFieldLabel}}.*required/i)).toBeHidden();
  });

  // Edge case: conditional field value cleared when hidden
  test('clears conditional field value when field is hidden', async ({ page }) => {
    await page.getByRole('combobox', { name: /{{triggerField}}/i }).selectOption('{{triggerValue}}');
    await page.getByRole('textbox', { name: /{{conditionalFieldLabel}}/i }).fill('some value');
    await page.getByRole('combobox', { name: /{{triggerField}}/i }).selectOption('{{nonTriggerValue}}');
    // Re-show and verify value is cleared
    await page.getByRole('combobox', { name: /{{triggerField}}/i }).selectOption('{{triggerValue}}');
    await expect(page.getByRole('textbox', { name: /{{conditionalFieldLabel}}/i })).toHaveValue('');
  });

  // Edge case: radio trigger shows/hides field
  test('shows field based on radio button selection', async ({ page }) => {
    await page.getByRole('radio', { name: '{{radioTriggerLabel}}' }).check();
    await expect(page.getByRole('textbox', { name: /{{conditionalFieldLabel}}/i })).toBeVisible();
    await page.getByRole('radio', { name: '{{radioOtherLabel}}' }).check();
    await expect(page.getByRole('textbox', { name: /{{conditionalFieldLabel}}/i })).toBeHidden();
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Conditional Fields', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/{{formPath}}');
  });

  test('shows conditional field when trigger selected', async ({ page }) => {
    await expect(page.getByRole('textbox', { name: /{{conditionalFieldLabel}}/i })).toBeHidden();
    await page.getByRole('combobox', { name: /{{triggerField}}/i }).selectOption('{{triggerValue}}');
    await expect(page.getByRole('textbox', { name: /{{conditionalFieldLabel}}/i })).toBeVisible();
  });

  test('validates visible conditional field on submit', async ({ page }) => {
    await page.getByRole('combobox', { name: /{{triggerField}}/i }).selectOption('{{triggerValue}}');
    await page.getByRole('button', { name: /submit/i }).click();
    await expect(page.getByText(/{{conditionalFieldLabel}}.*required/i)).toBeVisible();
  });

  test('does not validate hidden conditional field', async ({ page }) => {
    await page.getByRole('combobox', { name: /{{triggerField}}/i }).selectOption('{{nonTriggerValue}}');
    await page.getByRole('button', { name: /submit/i }).click();
    await expect(page.getByText(/{{conditionalFieldLabel}}.*required/i)).toBeHidden();
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Show on trigger | Selecting value reveals hidden field |
| Hide on change | Changing back hides field again |
| Submit with field | Visible field filled → success |
| Validate visible | Visible empty field → required error |
| Skip hidden | Hidden field not validated |
| Clear on hide | Value cleared when field hidden |
| Radio trigger | Radio button controls field visibility |
