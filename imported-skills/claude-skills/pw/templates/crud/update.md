# Update Entity Template

Tests editing an entity via form and inline edit interactions.

## Prerequisites
- Authenticated session via `{{authStorageStatePath}}`
- Existing entity ID: `{{entityId}}`, name: `{{originalEntityName}}`
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Update {{entityName}}', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  // Happy path: edit via form
  test('updates entity via edit form', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s/{{entityId}}/edit');
    const nameField = page.getByRole('textbox', { name: /name/i });
    await nameField.clear();
    await nameField.fill('{{updatedEntityName}}');
    await page.getByRole('button', { name: /save|update/i }).click();
    await expect(page).toHaveURL(`{{baseUrl}}/{{entityName}}s/{{entityId}}`);
    await expect(page.getByRole('heading', { name: '{{updatedEntityName}}' })).toBeVisible();
    await expect(page.getByRole('alert')).toContainText(/updated successfully/i);
  });

  // Happy path: inline edit
  test('updates name via inline edit', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s/{{entityId}}');
    await page.getByRole('button', { name: /edit name/i }).click();
    const inlineInput = page.getByRole('textbox', { name: /name/i });
    await inlineInput.clear();
    await inlineInput.fill('{{updatedEntityName}}');
    await inlineInput.press('Enter');
    await expect(page.getByRole('heading', { name: '{{updatedEntityName}}' })).toBeVisible();
  });

  // Happy path: edit then navigate away — unsaved changes warning
  test('warns before discarding unsaved changes', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s/{{entityId}}/edit');
    await page.getByRole('textbox', { name: /name/i }).fill('unsaved-change');
    await page.getByRole('link', { name: /cancel|back/i }).click();
    await expect(page.getByRole('dialog', { name: /unsaved changes/i })).toBeVisible();
    await page.getByRole('button', { name: /discard/i }).click();
    await expect(page).toHaveURL(`{{baseUrl}}/{{entityName}}s/{{entityId}}`);
    await expect(page.getByRole('heading', { name: '{{originalEntityName}}' })).toBeVisible();
  });

  // Error case: clearing required field
  test('shows validation error when required field is cleared', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s/{{entityId}}/edit');
    await page.getByRole('textbox', { name: /name/i }).clear();
    await page.getByRole('button', { name: /save|update/i }).click();
    await expect(page.getByText(/name is required/i)).toBeVisible();
    await expect(page).toHaveURL(`{{baseUrl}}/{{entityName}}s/{{entityId}}/edit`);
  });

  // Error case: conflict (optimistic update failure)
  test('handles concurrent edit conflict gracefully', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s/{{entityId}}/edit');
    // Simulate another user modifying the record
    await page.request.put(`{{baseUrl}}/api/{{entityName}}s/{{entityId}}`, {
      data: { name: 'modified-by-other', version: 999 },
    });
    await page.getByRole('textbox', { name: /name/i }).fill('my-change');
    await page.getByRole('button', { name: /save|update/i }).click();
    await expect(page.getByRole('alert')).toContainText(/conflict|modified by another/i);
  });

  // Edge case: inline edit cancelled with Escape
  test('cancels inline edit on Escape key', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s/{{entityId}}');
    await page.getByRole('button', { name: /edit name/i }).click();
    await page.getByRole('textbox', { name: /name/i }).fill('should-not-save');
    await page.keyboard.press('Escape');
    await expect(page.getByRole('heading', { name: '{{originalEntityName}}' })).toBeVisible();
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Update {{entityName}}', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test('updates entity via edit form', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s/{{entityId}}/edit');
    await page.getByRole('textbox', { name: /name/i }).clear();
    await page.getByRole('textbox', { name: /name/i }).fill('{{updatedEntityName}}');
    await page.getByRole('button', { name: /save|update/i }).click();
    await expect(page.getByRole('heading', { name: '{{updatedEntityName}}' })).toBeVisible();
  });

  test('shows validation error when required field cleared', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s/{{entityId}}/edit');
    await page.getByRole('textbox', { name: /name/i }).clear();
    await page.getByRole('button', { name: /save|update/i }).click();
    await expect(page.getByText(/name is required/i)).toBeVisible();
  });

  test('cancels inline edit on Escape', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s/{{entityId}}');
    await page.getByRole('button', { name: /edit name/i }).click();
    await page.getByRole('textbox', { name: /name/i }).fill('nope');
    await page.keyboard.press('Escape');
    await expect(page.getByRole('heading', { name: '{{originalEntityName}}' })).toBeVisible();
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Edit form | Full edit form → save → detail page |
| Inline edit | Click field → type → Enter to save |
| Unsaved changes | Navigation shows discard confirmation |
| Required field | Cleared required field → validation |
| Conflict | Concurrent edit → conflict error |
| Escape cancel | Inline edit cancelled, original value restored |
