# Basic Search Template

Tests search input, query submission, and results display.

## Prerequisites
- At least one indexed item matching `{{searchQuery}}`
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Basic Search', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}');
  });

  // Happy path: search returns results
  test('displays results for valid search query', async ({ page }) => {
    await page.getByRole('searchbox', { name: /search/i }).fill('{{searchQuery}}');
    await page.getByRole('button', { name: /search/i }).click();
    await expect(page).toHaveURL(/[?&]q={{searchQuery}}/);
    await expect(page.getByRole('list', { name: /results/i })).toBeVisible();
    const results = page.getByRole('listitem').filter({ hasText: /{{searchQuery}}/i });
    await expect(results.first()).toBeVisible();
  });

  // Happy path: search via Enter key
  test('submits search on Enter key', async ({ page }) => {
    await page.getByRole('searchbox', { name: /search/i }).fill('{{searchQuery}}');
    await page.keyboard.press('Enter');
    await expect(page).toHaveURL(/[?&]q=/);
    await expect(page.getByRole('list', { name: /results/i })).toBeVisible();
  });

  // Happy path: result count shown
  test('shows result count in heading', async ({ page }) => {
    await page.getByRole('searchbox', { name: /search/i }).fill('{{searchQuery}}');
    await page.getByRole('button', { name: /search/i }).click();
    await expect(page.getByText(/\d+\s+results? for/i)).toBeVisible();
  });

  // Happy path: clicking result navigates to detail
  test('clicking result navigates to detail page', async ({ page }) => {
    await page.getByRole('searchbox', { name: /search/i }).fill('{{searchQuery}}');
    await page.getByRole('button', { name: /search/i }).click();
    await page.getByRole('listitem').first().getByRole('link').click();
    await expect(page).toHaveURL(/\/{{entityName}}s\/\d+/);
  });

  // Happy path: query pre-filled from URL
  test('pre-fills search box from URL query param', async ({ page }) => {
    await page.goto(`{{baseUrl}}/search?q={{searchQuery}}`);
    await expect(page.getByRole('searchbox', { name: /search/i })).toHaveValue('{{searchQuery}}');
  });

  // Error case: no results
  test('shows no-results message for unmatched query', async ({ page }) => {
    await page.getByRole('searchbox', { name: /search/i }).fill('xyzzy-no-match-12345');
    await page.getByRole('button', { name: /search/i }).click();
    await expect(page.getByText(/no results|nothing found/i)).toBeVisible();
  });

  // Edge case: special characters handled safely
  test('handles special characters in query', async ({ page }) => {
    await page.getByRole('searchbox', { name: /search/i }).fill('<script>alert(1)</script>');
    await page.getByRole('button', { name: /search/i }).click();
    await expect(page.getByRole('alert')).toBeHidden();
    await expect(page.getByText(/no results/i)).toBeVisible();
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Basic Search', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}');
  });

  test('displays results for valid query', async ({ page }) => {
    await page.getByRole('searchbox', { name: /search/i }).fill('{{searchQuery}}');
    await page.getByRole('button', { name: /search/i }).click();
    await expect(page.getByRole('list', { name: /results/i })).toBeVisible();
  });

  test('shows no-results for unmatched query', async ({ page }) => {
    await page.getByRole('searchbox', { name: /search/i }).fill('xyzzy-no-match');
    await page.getByRole('button', { name: /search/i }).click();
    await expect(page.getByText(/no results|nothing found/i)).toBeVisible();
  });

  test('submits on Enter key', async ({ page }) => {
    await page.getByRole('searchbox', { name: /search/i }).fill('{{searchQuery}}');
    await page.keyboard.press('Enter');
    await expect(page).toHaveURL(/[?&]q=/);
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Valid query | Results list visible, count shown |
| Enter key | Search submitted without clicking button |
| Result count | Heading shows N results for query |
| Result click | Navigates to entity detail |
| URL pre-fill | Query param populates search box |
| No results | Empty state message |
| Special chars | XSS input handled, no script execution |
