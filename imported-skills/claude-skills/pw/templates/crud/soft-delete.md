# Soft Delete (Archive/Restore) Template

Tests archiving an entity, viewing archived items, and restoring them.

## Prerequisites
- Authenticated session via `{{authStorageStatePath}}`
- Active entity: ID `{{entityId}}`, name `{{entityName}}`
- Archived entity: ID `{{archivedEntityId}}`
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Soft Delete — Archive & Restore', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  // Happy path: archive entity
  test('archives entity and removes from active list', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s/{{entityId}}');
    await page.getByRole('button', { name: /archive/i }).click();
    await page.getByRole('dialog').getByRole('button', { name: /archive|confirm/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/{{entityName}}s');
    await expect(page.getByRole('alert')).toContainText(/archived/i);
    await expect(page.getByRole('link', { name: '{{entityName}}' })).toBeHidden();
  });

  // Happy path: archived entity appears in archived view
  test('archived entity visible in archived list', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s?status=archived');
    await expect(page.getByRole('link', { name: '{{entityName}}' })).toBeVisible();
  });

  // Happy path: restore archived entity
  test('restores archived entity to active list', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s?status=archived');
    const row = page.getByRole('row', { name: new RegExp('{{entityName}}') });
    await row.getByRole('button', { name: /restore/i }).click();
    await expect(page.getByRole('alert')).toContainText(/restored/i);
    await expect(row).toBeHidden();

    await page.goto('{{baseUrl}}/{{entityName}}s');
    await expect(page.getByRole('link', { name: '{{entityName}}' })).toBeVisible();
  });

  // Happy path: active list does not show archived by default
  test('active list does not include archived entities', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s');
    await expect(page.getByRole('link', { name: /{{archivedEntityName}}/i })).toBeHidden();
  });

  // Error case: archived entity cannot be edited
  test('archived entity edit button is disabled', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s/{{archivedEntityId}}');
    await expect(page.getByRole('button', { name: /edit/i })).toBeDisabled();
    await expect(page.getByText(/archived/i)).toBeVisible();
  });

  // Edge case: permanently delete archived entity
  test('permanently deletes archived entity', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s/{{archivedEntityId}}');
    await page.getByRole('button', { name: /delete permanently/i }).click();
    await page.getByRole('dialog').getByRole('button', { name: /delete permanently/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/{{entityName}}s?status=archived');
    await expect(page.getByRole('link', { name: '{{archivedEntityName}}' })).toBeHidden();
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Soft Delete — Archive & Restore', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test('archives entity and removes from active list', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s/{{entityId}}');
    await page.getByRole('button', { name: /archive/i }).click();
    await page.getByRole('dialog').getByRole('button', { name: /archive|confirm/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/{{entityName}}s');
    await expect(page.getByRole('link', { name: '{{entityName}}' })).toBeHidden();
  });

  test('restores archived entity to active list', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s?status=archived');
    await page.getByRole('row', { name: new RegExp('{{entityName}}') })
      .getByRole('button', { name: /restore/i }).click();
    await expect(page.getByRole('alert')).toContainText(/restored/i);
  });

  test('archived entity edit button is disabled', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s/{{archivedEntityId}}');
    await expect(page.getByRole('button', { name: /edit/i })).toBeDisabled();
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Archive | Entity moved to archived list, removed from active |
| Archived list | Archived items visible with status=archived filter |
| Restore | Archived entity returned to active list |
| Active list clean | Archived items hidden from default view |
| Edit disabled | Archived entity cannot be edited |
| Permanent delete | Hard-delete of archived entity |
