# Delete Entity Template

Tests deletion with confirmation dialog and post-delete behaviour.

## Prerequisites
- Authenticated session via `{{authStorageStatePath}}`
- Entity to delete: ID `{{entityId}}`, name `{{entityName}}`
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Delete {{entityName}}', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  // Happy path: delete from detail page
  test('deletes entity after confirming dialog', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s/{{entityId}}');
    await page.getByRole('button', { name: /delete/i }).click();
    const dialog = page.getByRole('dialog', { name: /delete|confirm/i });
    await expect(dialog).toBeVisible();
    await expect(dialog).toContainText('{{entityName}}');
    await dialog.getByRole('button', { name: /delete|confirm/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/{{entityName}}s');
    await expect(page.getByRole('alert')).toContainText(/deleted successfully/i);
    await expect(page.getByRole('link', { name: '{{entityName}}' })).toBeHidden();
  });

  // Happy path: delete from list view
  test('deletes entity from list row action', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s');
    const row = page.getByRole('row', { name: new RegExp('{{entityName}}') });
    await row.getByRole('button', { name: /delete/i }).click();
    await page.getByRole('dialog').getByRole('button', { name: /confirm|delete/i }).click();
    await expect(row).toBeHidden();
  });

  // Error case: cancel deletion
  test('does not delete when cancel is clicked in dialog', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s/{{entityId}}');
    await page.getByRole('button', { name: /delete/i }).click();
    await page.getByRole('dialog').getByRole('button', { name: /cancel/i }).click();
    await expect(page.getByRole('dialog')).toBeHidden();
    await expect(page).toHaveURL(`{{baseUrl}}/{{entityName}}s/{{entityId}}`);
    await expect(page.getByRole('heading', { name: '{{entityName}}' })).toBeVisible();
  });

  // Error case: delete entity with dependents
  test('shows error when entity has dependent records', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s/{{entityWithDependentsId}}');
    await page.getByRole('button', { name: /delete/i }).click();
    await page.getByRole('dialog').getByRole('button', { name: /confirm|delete/i }).click();
    await expect(page.getByRole('alert')).toContainText(/cannot delete|has dependents/i);
    await expect(page).toHaveURL(`{{baseUrl}}/{{entityName}}s/{{entityWithDependentsId}}`);
  });

  // Edge case: confirmation dialog requires typing entity name
  test('requires typing entity name to confirm deletion', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s/{{entityId}}');
    await page.getByRole('button', { name: /delete/i }).click();
    const confirmBtn = page.getByRole('dialog').getByRole('button', { name: /confirm|delete/i });
    await expect(confirmBtn).toBeDisabled();
    await page.getByRole('textbox', { name: /type.*to confirm/i }).fill('{{entityName}}');
    await expect(confirmBtn).toBeEnabled();
    await confirmBtn.click();
    await expect(page).toHaveURL('{{baseUrl}}/{{entityName}}s');
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Delete {{entityName}}', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test('deletes entity after confirming dialog', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s/{{entityId}}');
    await page.getByRole('button', { name: /delete/i }).click();
    await page.getByRole('dialog').getByRole('button', { name: /confirm|delete/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/{{entityName}}s');
    await expect(page.getByRole('alert')).toContainText(/deleted successfully/i);
  });

  test('does not delete when cancel clicked', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s/{{entityId}}');
    await page.getByRole('button', { name: /delete/i }).click();
    await page.getByRole('dialog').getByRole('button', { name: /cancel/i }).click();
    await expect(page.getByRole('heading', { name: '{{entityName}}' })).toBeVisible();
  });

  test('shows error for entity with dependents', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s/{{entityWithDependentsId}}');
    await page.getByRole('button', { name: /delete/i }).click();
    await page.getByRole('dialog').getByRole('button', { name: /confirm|delete/i }).click();
    await expect(page.getByRole('alert')).toContainText(/cannot delete/i);
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Delete confirmed | Dialog confirmed → entity removed → list page |
| Delete from list | Row action → confirm → row removed |
| Cancel deletion | Dialog cancelled → entity intact |
| Dependent error | Entity with children → deletion blocked |
| Type-to-confirm | Confirm button disabled until name typed |
