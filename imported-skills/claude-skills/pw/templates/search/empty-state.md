# Empty State Template

Tests no-results messaging and clear-filters behaviour.

## Prerequisites
- App running at `{{baseUrl}}`
- Query that returns no results: `{{emptySearchQuery}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Empty State', () => {
  // Happy path: no results message
  test('shows no-results message for unmatched query', async ({ page }) => {
    await page.goto('{{baseUrl}}/search?q={{emptySearchQuery}}');
    await expect(page.getByRole('heading', { name: /no results|nothing found/i })).toBeVisible();
    await expect(page.getByText(/try.*different|adjust.*search/i)).toBeVisible();
  });

  // Happy path: clear filters CTA shown in empty state
  test('shows "clear filters" button when filters applied with no results', async ({ page }) => {
    await page.goto('{{baseUrl}}/search?q={{searchQuery}}&category={{nonExistentCategory}}');
    await expect(page.getByText(/no results/i)).toBeVisible();
    await expect(page.getByRole('button', { name: /clear.*filter/i })).toBeVisible();
  });

  // Happy path: clearing filters restores results
  test('clearing filters from empty state restores results', async ({ page }) => {
    await page.goto('{{baseUrl}}/search?q={{searchQuery}}&category={{nonExistentCategory}}');
    await page.getByRole('button', { name: /clear.*filter/i }).click();
    await expect(page.getByRole('listitem').first()).toBeVisible();
    await expect(page.getByText(/no results/i)).toBeHidden();
  });

  // Happy path: search suggestions shown in empty state
  test('shows related search suggestions', async ({ page }) => {
    await page.goto('{{baseUrl}}/search?q={{emptySearchQuery}}');
    const suggestions = page.getByRole('list', { name: /suggestions|similar/i });
    if (await suggestions.isVisible()) {
      await expect(suggestions.getByRole('listitem').first()).toBeVisible();
    }
  });

  // Happy path: empty list view (not search)
  test('shows empty state on entity list with no data', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s?filter={{emptyFilter}}');
    await expect(page.getByText(/no {{entityName}}s|empty/i)).toBeVisible();
    await expect(page.getByRole('button', { name: /create|add new/i })).toBeVisible();
  });

  // Error case: network error shows error state not empty state
  test('distinguishes network error from no-results', async ({ page }) => {
    await page.route('{{baseUrl}}/api/search*', route => route.abort('failed'));
    await page.goto('{{baseUrl}}/search?q={{searchQuery}}');
    await expect(page.getByText(/error|something went wrong/i)).toBeVisible();
    await expect(page.getByText(/no results/i)).toBeHidden();
  });

  // Edge case: empty state after removing last item
  test('shows empty state after deleting last item in list', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s');
    const row = page.getByRole('row').filter({ hasNot: page.getByRole('columnheader') }).last();
    await row.getByRole('button', { name: /delete/i }).click();
    await page.getByRole('dialog').getByRole('button', { name: /confirm/i }).click();
    await expect(page.getByText(/no {{entityName}}s|empty/i)).toBeVisible();
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Empty State', () => {
  test('shows no-results message for unmatched query', async ({ page }) => {
    await page.goto('{{baseUrl}}/search?q={{emptySearchQuery}}');
    await expect(page.getByRole('heading', { name: /no results|nothing found/i })).toBeVisible();
  });

  test('shows clear-filters button in no-results state', async ({ page }) => {
    await page.goto('{{baseUrl}}/search?q={{searchQuery}}&category={{nonExistentCategory}}');
    await expect(page.getByRole('button', { name: /clear.*filter/i })).toBeVisible();
  });

  test('clearing filters restores results', async ({ page }) => {
    await page.goto('{{baseUrl}}/search?q={{searchQuery}}&category={{nonExistentCategory}}');
    await page.getByRole('button', { name: /clear.*filter/i }).click();
    await expect(page.getByRole('listitem').first()).toBeVisible();
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| No-results query | Heading + suggestion text shown |
| Filter no-results | Clear-filters CTA displayed |
| Clear filters | Removes filter, results return |
| Search suggestions | Related terms listed when available |
| Empty list view | Entity list empty state with create CTA |
| Network error | Error state distinct from no-results |
| Last item deleted | Empty state shown after deletion |
