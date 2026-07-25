# Create Entity Template

Tests creating a new entity via form submission.

## Prerequisites
- Authenticated session via `{{authStorageStatePath}}`
- Entity type: `{{entityName}}` (e.g. "Project", "Product", "User")
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Create {{entityName}}', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s/new');
  });

  // Happy path: create with valid data
  test('creates {{entityName}} with valid data', async ({ page }) => {
    await page.getByRole('textbox', { name: /name/i }).fill('{{testEntityName}}');
    await page.getByRole('textbox', { name: /description/i }).fill('{{testEntityDescription}}');
    await page.getByRole('combobox', { name: /category/i }).selectOption('{{testEntityCategory}}');
    await page.getByRole('button', { name: /create|save/i }).click();
    await expect(page).toHaveURL(/\/{{entityName}}s\/\d+/);
    await expect(page.getByRole('heading', { name: '{{testEntityName}}' })).toBeVisible();
    await expect(page.getByRole('alert')).toContainText(/created successfully/i);
  });

  // Happy path: create and add another
  test('clears form after "save and add another"', async ({ page }) => {
    await page.getByRole('textbox', { name: /name/i }).fill('{{testEntityName}}');
    await page.getByRole('button', { name: /save and add another/i }).click();
    await expect(page.getByRole('textbox', { name: /name/i })).toHaveValue('');
    await expect(page.getByRole('alert')).toContainText(/created successfully/i);
  });

  // Error case: required fields missing
  test('shows validation errors for empty required fields', async ({ page }) => {
    await page.getByRole('button', { name: /create|save/i }).click();
    await expect(page.getByText(/name is required/i)).toBeVisible();
    await expect(page).toHaveURL('{{baseUrl}}/{{entityName}}s/new');
  });

  // Error case: duplicate name
  test('shows error when entity name already exists', async ({ page }) => {
    await page.getByRole('textbox', { name: /name/i }).fill('{{existingEntityName}}');
    await page.getByRole('button', { name: /create|save/i }).click();
    await expect(page.getByRole('alert')).toContainText(/already exists|duplicate/i);
  });

  // Edge case: max length enforcement
  test('enforces max length on name field', async ({ page }) => {
    const longName = 'A'.repeat({{maxNameLength}} + 1);
    await page.getByRole('textbox', { name: /name/i }).fill(longName);
    const actualValue = await page.getByRole('textbox', { name: /name/i }).inputValue();
    expect(actualValue.length).toBeLessThanOrEqual({{maxNameLength}});
  });

  // Edge case: cancel navigates away without saving
  test('cancel navigates back without creating', async ({ page }) => {
    await page.getByRole('textbox', { name: /name/i }).fill('should-not-save');
    await page.getByRole('button', { name: /cancel/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/{{entityName}}s');
    await expect(page.getByRole('cell', { name: 'should-not-save' })).toBeHidden();
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Create {{entityName}}', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s/new');
  });

  test('creates entity with valid data', async ({ page }) => {
    await page.getByRole('textbox', { name: /name/i }).fill('{{testEntityName}}');
    await page.getByRole('textbox', { name: /description/i }).fill('{{testEntityDescription}}');
    await page.getByRole('button', { name: /create|save/i }).click();
    await expect(page).toHaveURL(/\/{{entityName}}s\/\d+/);
    await expect(page.getByRole('alert')).toContainText(/created successfully/i);
  });

  test('shows validation errors for empty form', async ({ page }) => {
    await page.getByRole('button', { name: /create|save/i }).click();
    await expect(page.getByText(/name is required/i)).toBeVisible();
  });

  test('cancel navigates back without saving', async ({ page }) => {
    await page.getByRole('textbox', { name: /name/i }).fill('not-saved');
    await page.getByRole('button', { name: /cancel/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/{{entityName}}s');
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Happy path | Valid form → entity created → detail page |
| Save and add | Form cleared, ready for next entry |
| Required fields | Empty submit → inline validation |
| Duplicate name | Server error shown |
| Max length | Input truncated at field max |
| Cancel | No entity created, returns to list |
