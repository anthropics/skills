# Pagination Template

Tests page navigation, items-per-page selector, and URL state.

## Prerequisites
- Search results for `{{searchQuery}}` spanning multiple pages
- At least `{{totalItemCount}}` items total
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Pagination', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/search?q={{searchQuery}}');
  });

  // Happy path: navigate to next page
  test('navigates to next page and updates URL', async ({ page }) => {
    const firstItem = await page.getByRole('listitem').first().textContent();
    await page.getByRole('button', { name: /next page/i }).click();
    await expect(page).toHaveURL(/page=2/);
    await expect(page.getByRole('listitem').first()).not.toHaveText(firstItem!);
  });

  // Happy path: navigate to previous page
  test('navigates to previous page', async ({ page }) => {
    await page.goto('{{baseUrl}}/search?q={{searchQuery}}&page=2');
    const secondPageFirst = await page.getByRole('listitem').first().textContent();
    await page.getByRole('button', { name: /previous page/i }).click();
    await expect(page).toHaveURL(/page=1/);
    await expect(page.getByRole('listitem').first()).not.toHaveText(secondPageFirst!);
  });

  // Happy path: jump to specific page
  test('jumps to specific page number', async ({ page }) => {
    await page.getByRole('button', { name: '3' }).click();
    await expect(page).toHaveURL(/page=3/);
    await expect(page.getByRole('button', { name: '3' })).toHaveAttribute('aria-current', 'page');
  });

  // Happy path: items per page selector
  test('changes items per page', async ({ page }) => {
    await page.getByRole('combobox', { name: /per page/i }).selectOption('50');
    await expect(page).toHaveURL(/per_page=50/);
    const items = page.getByRole('listitem');
    await expect(items).toHaveCount(Math.min(50, {{totalItemCount}}));
  });

  // Happy path: page info text
  test('shows correct page info text', async ({ page }) => {
    await expect(page.getByText(/showing \d+.+of\s+{{totalItemCount}}/i)).toBeVisible();
  });

  // Error case: first page has no previous button
  test('previous page button disabled on first page', async ({ page }) => {
    await expect(page.getByRole('button', { name: /previous page/i })).toBeDisabled();
  });

  // Error case: last page has no next button
  test('next page button disabled on last page', async ({ page }) => {
    const lastPage = Math.ceil({{totalItemCount}} / {{defaultPageSize}});
    await page.goto(`{{baseUrl}}/search?q={{searchQuery}}&page=${lastPage}`);
    await expect(page.getByRole('button', { name: /next page/i })).toBeDisabled();
  });

  // Edge case: out-of-range page redirects to last page
  test('out-of-range page parameter redirects gracefully', async ({ page }) => {
    await page.goto('{{baseUrl}}/search?q={{searchQuery}}&page=99999');
    await expect(page.getByRole('listitem').first()).toBeVisible();
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Pagination', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/search?q={{searchQuery}}');
  });

  test('navigates to next page', async ({ page }) => {
    await page.getByRole('button', { name: /next page/i }).click();
    await expect(page).toHaveURL(/page=2/);
  });

  test('previous page disabled on first page', async ({ page }) => {
    await expect(page.getByRole('button', { name: /previous page/i })).toBeDisabled();
  });

  test('next page disabled on last page', async ({ page }) => {
    const last = Math.ceil({{totalItemCount}} / {{defaultPageSize}});
    await page.goto(`{{baseUrl}}/search?q={{searchQuery}}&page=${last}`);
    await expect(page.getByRole('button', { name: /next page/i })).toBeDisabled();
  });

  test('changes items per page', async ({ page }) => {
    await page.getByRole('combobox', { name: /per page/i }).selectOption('50');
    await expect(page).toHaveURL(/per_page=50/);
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Next page | Items change, URL updates page=2 |
| Previous page | Back to page 1 |
| Jump to page | Clicking page number sets aria-current |
| Items per page | Selector changes count of visible items |
| Page info | "Showing X-Y of N" text |
| First page prev | Previous button disabled |
| Last page next | Next button disabled |
| Out-of-range | Graceful fallback |
