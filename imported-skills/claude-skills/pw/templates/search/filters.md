# Search Filters Template

Tests category filter, price range, and checkbox filters.

## Prerequisites
- Search results available for `{{searchQuery}}`
- Category `{{filterCategory}}` with items
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Search Filters', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/search?q={{searchQuery}}');
  });

  // Happy path: category filter
  test('filters results by category', async ({ page }) => {
    await page.getByRole('checkbox', { name: '{{filterCategory}}' }).check();
    await expect(page).toHaveURL(/category={{filterCategory}}/);
    const results = page.getByRole('listitem');
    await expect(results.first()).toContainText('{{filterCategory}}');
    const count = await results.count();
    expect(count).toBeGreaterThan(0);
  });

  // Happy path: price range filter
  test('filters results by price range', async ({ page }) => {
    const minInput = page.getByRole('spinbutton', { name: /min.*price/i });
    const maxInput = page.getByRole('spinbutton', { name: /max.*price/i });
    await minInput.fill('{{minPrice}}');
    await maxInput.fill('{{maxPrice}}');
    await page.getByRole('button', { name: /apply|filter/i }).click();
    await expect(page).toHaveURL(/min_price={{minPrice}}/);
    // Verify no results exceed max price
    const prices = page.getByTestId('item-price');
    const priceCount = await prices.count();
    for (let i = 0; i < priceCount; i++) {
      const text = await prices.nth(i).textContent() ?? '';
      const value = parseFloat(text.replace(/[^0-9.]/g, ''));
      expect(value).toBeLessThanOrEqual({{maxPrice}});
    }
  });

  // Happy path: multiple checkboxes combine filters
  test('applies multiple checkbox filters simultaneously', async ({ page }) => {
    await page.getByRole('checkbox', { name: '{{filterOption1}}' }).check();
    await page.getByRole('checkbox', { name: '{{filterOption2}}' }).check();
    await expect(page).toHaveURL(/{{filterParam1}}.*{{filterParam2}}|{{filterParam2}}.*{{filterParam1}}/);
  });

  // Happy path: active filters shown as chips
  test('shows active filter chips', async ({ page }) => {
    await page.getByRole('checkbox', { name: '{{filterCategory}}' }).check();
    await expect(page.getByRole('button', { name: /remove.*{{filterCategory}}/i })).toBeVisible();
  });

  // Happy path: clear individual filter chip
  test('removes filter by clicking chip close', async ({ page }) => {
    await page.getByRole('checkbox', { name: '{{filterCategory}}' }).check();
    await page.getByRole('button', { name: /remove.*{{filterCategory}}/i }).click();
    await expect(page.getByRole('checkbox', { name: '{{filterCategory}}' })).not.toBeChecked();
  });

  // Happy path: clear all filters
  test('clears all filters', async ({ page }) => {
    await page.getByRole('checkbox', { name: '{{filterCategory}}' }).check();
    await page.getByRole('button', { name: /clear all filters/i }).click();
    await expect(page.getByRole('checkbox', { name: '{{filterCategory}}' })).not.toBeChecked();
    await expect(page).not.toHaveURL(/category=/);
  });

  // Error case: no results for filter combination
  test('shows empty state when filters yield no results', async ({ page }) => {
    await page.getByRole('spinbutton', { name: /min.*price/i }).fill('999999');
    await page.getByRole('button', { name: /apply|filter/i }).click();
    await expect(page.getByText(/no results/i)).toBeVisible();
    await expect(page.getByRole('button', { name: /clear.*filter/i })).toBeVisible();
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Search Filters', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/search?q={{searchQuery}}');
  });

  test('filters results by category', async ({ page }) => {
    await page.getByRole('checkbox', { name: '{{filterCategory}}' }).check();
    await expect(page).toHaveURL(/category={{filterCategory}}/);
    await expect(page.getByRole('listitem').first()).toBeVisible();
  });

  test('shows active filter chips', async ({ page }) => {
    await page.getByRole('checkbox', { name: '{{filterCategory}}' }).check();
    await expect(page.getByRole('button', { name: /remove.*{{filterCategory}}/i })).toBeVisible();
  });

  test('clears all filters', async ({ page }) => {
    await page.getByRole('checkbox', { name: '{{filterCategory}}' }).check();
    await page.getByRole('button', { name: /clear all filters/i }).click();
    await expect(page.getByRole('checkbox', { name: '{{filterCategory}}' })).not.toBeChecked();
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Category filter | Checkbox → results scoped to category |
| Price range | Min/max filter applied, prices verified |
| Multi-filter | Multiple checkboxes combine in URL |
| Filter chips | Active filters shown as removable chips |
| Remove chip | Chip close → filter unchecked |
| Clear all | All filters removed at once |
| No-results combo | Filter combination yields empty state |
