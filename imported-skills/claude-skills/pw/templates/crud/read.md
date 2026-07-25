# Read Entity Template

Tests viewing entity details and list view with correct data display.

## Prerequisites
- Authenticated session via `{{authStorageStatePath}}`
- Seeded entity with ID `{{entityId}}` and name `{{entityName}}`
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Read {{entityName}}', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  // Happy path: detail page
  test('displays entity details correctly', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s/{{entityId}}');
    await expect(page.getByRole('heading', { name: '{{expectedTitle}}' })).toBeVisible();
    await expect(page.getByText('{{expectedField}}')).toBeVisible();
    await expect(page.getByText('{{expectedCategory}}')).toBeVisible();
  });

  // Happy path: list view shows all items
  test('displays list of entities', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s');
    await expect(page.getByRole('table')).toBeVisible();
    const rows = page.getByRole('row').filter({ hasNot: page.getByRole('columnheader') });
    await expect(rows).toHaveCount({{expectedItemCount}});
  });

  // Happy path: list item links to detail
  test('clicking list item navigates to detail page', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s');
    await page.getByRole('link', { name: '{{expectedTitle}}' }).click();
    await expect(page).toHaveURL(`{{baseUrl}}/{{entityName}}s/{{entityId}}`);
  });

  // Happy path: breadcrumb navigation
  test('breadcrumb shows correct path', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s/{{entityId}}');
    await expect(page.getByRole('navigation', { name: /breadcrumb/i })).toContainText('{{entityName}}s');
    await expect(page.getByRole('navigation', { name: /breadcrumb/i })).toContainText('{{expectedTitle}}');
  });

  // Error case: non-existent entity shows 404
  test('shows 404 for non-existent entity', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s/999999');
    await expect(page.getByRole('heading', { name: /404|not found/i })).toBeVisible();
  });

  // Edge case: loading state resolves to data
  test('shows data after loading completes', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s/{{entityId}}');
    // Skeleton/spinner should be gone, data visible
    await expect(page.getByTestId('skeleton')).toBeHidden();
    await expect(page.getByRole('heading', { name: '{{expectedTitle}}' })).toBeVisible();
  });

  // Edge case: empty list state
  test('shows empty state when no entities exist', async ({ page }) => {
    // Assumes a fresh context or filter that returns no results
    await page.goto('{{baseUrl}}/{{entityName}}s?filter={{emptyFilter}}');
    await expect(page.getByText(/no {{entityName}}s found/i)).toBeVisible();
    await expect(page.getByRole('button', { name: /create|add/i })).toBeVisible();
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Read {{entityName}}', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test('displays entity details correctly', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s/{{entityId}}');
    await expect(page.getByRole('heading', { name: '{{expectedTitle}}' })).toBeVisible();
    await expect(page.getByText('{{expectedField}}')).toBeVisible();
  });

  test('displays list of entities with correct count', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s');
    const rows = page.getByRole('row').filter({ hasNot: page.getByRole('columnheader') });
    await expect(rows).toHaveCount({{expectedItemCount}});
  });

  test('shows 404 for non-existent entity', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s/999999');
    await expect(page.getByRole('heading', { name: /404|not found/i })).toBeVisible();
  });

  test('shows empty state when list is empty', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s?filter={{emptyFilter}}');
    await expect(page.getByText(/no {{entityName}}s found/i)).toBeVisible();
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Detail view | Entity fields rendered correctly |
| List view | Correct row count in table |
| List → detail | Clicking row/link navigates correctly |
| Breadcrumb | Path reflects current location |
| 404 | Non-existent ID shows not-found page |
| Loading → data | Skeleton hidden, data visible after load |
| Empty list | No-results state with call to action |
