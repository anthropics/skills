# Bulk Operations Template

Tests selecting multiple items and performing bulk delete/update actions.

## Prerequisites
- Authenticated session via `{{authStorageStatePath}}`
- At least `{{minItemCount}}` entities seeded in list
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Bulk Operations', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s');
  });

  // Happy path: select all and bulk delete
  test('selects all and bulk deletes', async ({ page }) => {
    await page.getByRole('checkbox', { name: /select all/i }).check();
    const checkboxes = page.getByRole('row').filter({ hasNot: page.getByRole('columnheader') })
      .getByRole('checkbox');
    await expect(checkboxes.first()).toBeChecked();

    await page.getByRole('button', { name: /bulk delete/i }).click();
    await page.getByRole('dialog').getByRole('button', { name: /confirm/i }).click();
    await expect(page.getByRole('alert')).toContainText(/deleted/i);
    await expect(page.getByRole('row').filter({ hasNot: page.getByRole('columnheader') }))
      .toHaveCount(0);
  });

  // Happy path: select specific rows and bulk update status
  test('updates status of selected rows', async ({ page }) => {
    const rows = page.getByRole('row').filter({ hasNot: page.getByRole('columnheader') });
    await rows.nth(0).getByRole('checkbox').check();
    await rows.nth(1).getByRole('checkbox').check();
    await expect(page.getByText(/2 selected/i)).toBeVisible();

    await page.getByRole('button', { name: /bulk actions/i }).click();
    await page.getByRole('menuitem', { name: /mark as active/i }).click();
    await expect(page.getByRole('alert')).toContainText(/2.*updated/i);
  });

  // Happy path: toolbar appears only when items selected
  test('shows bulk action toolbar only when items are selected', async ({ page }) => {
    await expect(page.getByRole('toolbar', { name: /bulk actions/i })).toBeHidden();
    await page.getByRole('row').nth(1).getByRole('checkbox').check();
    await expect(page.getByRole('toolbar', { name: /bulk actions/i })).toBeVisible();
  });

  // Happy path: deselect all clears toolbar
  test('hides toolbar after deselecting all', async ({ page }) => {
    await page.getByRole('checkbox', { name: /select all/i }).check();
    await page.getByRole('checkbox', { name: /select all/i }).uncheck();
    await expect(page.getByRole('toolbar', { name: /bulk actions/i })).toBeHidden();
  });

  // Error case: bulk delete requires confirmation
  test('requires confirmation before bulk delete', async ({ page }) => {
    await page.getByRole('checkbox', { name: /select all/i }).check();
    await page.getByRole('button', { name: /bulk delete/i }).click();
    await expect(page.getByRole('dialog', { name: /confirm/i })).toBeVisible();
    await page.getByRole('button', { name: /cancel/i }).click();
    const rowCount = await page.getByRole('row').filter({ hasNot: page.getByRole('columnheader') }).count();
    expect(rowCount).toBeGreaterThan(0);
  });

  // Edge case: select all across pages
  test('shows "select all across pages" option when applicable', async ({ page }) => {
    await page.getByRole('checkbox', { name: /select all/i }).check();
    const crossPage = page.getByRole('button', { name: /select all.*across pages/i });
    if (await crossPage.isVisible()) {
      await crossPage.click();
      await expect(page.getByText(/all.*selected/i)).toBeVisible();
    }
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Bulk Operations', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s');
  });

  test('shows bulk action toolbar when items selected', async ({ page }) => {
    await expect(page.getByRole('toolbar', { name: /bulk actions/i })).toBeHidden();
    await page.getByRole('row').nth(1).getByRole('checkbox').check();
    await expect(page.getByRole('toolbar', { name: /bulk actions/i })).toBeVisible();
  });

  test('selects all and bulk deletes', async ({ page }) => {
    await page.getByRole('checkbox', { name: /select all/i }).check();
    await page.getByRole('button', { name: /bulk delete/i }).click();
    await page.getByRole('dialog').getByRole('button', { name: /confirm/i }).click();
    await expect(page.getByRole('alert')).toContainText(/deleted/i);
  });

  test('requires confirmation before bulk delete', async ({ page }) => {
    await page.getByRole('checkbox', { name: /select all/i }).check();
    await page.getByRole('button', { name: /bulk delete/i }).click();
    await expect(page.getByRole('dialog', { name: /confirm/i })).toBeVisible();
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Select all + delete | All rows selected → confirmed delete → empty list |
| Partial select + update | N rows selected → status updated → success |
| Toolbar visibility | Appears on select, hides on deselect |
| Deselect all | Select all → uncheck → toolbar gone |
| Confirmation required | Bulk delete shows dialog first |
| Cross-page select | Select-all-pages option shown on multi-page lists |
