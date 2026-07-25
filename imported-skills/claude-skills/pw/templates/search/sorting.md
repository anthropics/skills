# Search Sorting Template

Tests sorting results by name, date, and price.

## Prerequisites
- Search results for `{{searchQuery}}` with multiple items
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Search Sorting', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/search?q={{searchQuery}}');
  });

  // Happy path: sort by name A-Z
  test('sorts results alphabetically A-Z', async ({ page }) => {
    await page.getByRole('combobox', { name: /sort by/i }).selectOption('name_asc');
    await expect(page).toHaveURL(/sort=name_asc/);
    const names = page.getByTestId('result-name');
    const first = await names.first().textContent();
    const second = await names.nth(1).textContent();
    expect(first!.localeCompare(second!)).toBeLessThanOrEqual(0);
  });

  // Happy path: sort by name Z-A
  test('sorts results alphabetically Z-A', async ({ page }) => {
    await page.getByRole('combobox', { name: /sort by/i }).selectOption('name_desc');
    const names = page.getByTestId('result-name');
    const first = await names.first().textContent();
    const second = await names.nth(1).textContent();
    expect(first!.localeCompare(second!)).toBeGreaterThanOrEqual(0);
  });

  // Happy path: sort by date newest
  test('sorts results by newest date first', async ({ page }) => {
    await page.getByRole('combobox', { name: /sort by/i }).selectOption('date_desc');
    await expect(page).toHaveURL(/sort=date_desc/);
    const dates = page.getByTestId('result-date');
    const firstDate = new Date(await dates.first().getAttribute('datetime') ?? '');
    const secondDate = new Date(await dates.nth(1).getAttribute('datetime') ?? '');
    expect(firstDate.getTime()).toBeGreaterThanOrEqual(secondDate.getTime());
  });

  // Happy path: sort by price low-high
  test('sorts by price low to high', async ({ page }) => {
    await page.getByRole('combobox', { name: /sort by/i }).selectOption('price_asc');
    const prices = page.getByTestId('result-price');
    const firstText = await prices.first().textContent() ?? '';
    const secondText = await prices.nth(1).textContent() ?? '';
    const first = parseFloat(firstText.replace(/[^0-9.]/g, ''));
    const second = parseFloat(secondText.replace(/[^0-9.]/g, ''));
    expect(first).toBeLessThanOrEqual(second);
  });

  // Happy path: sort by price high-low
  test('sorts by price high to low', async ({ page }) => {
    await page.getByRole('combobox', { name: /sort by/i }).selectOption('price_desc');
    const prices = page.getByTestId('result-price');
    const firstText = await prices.first().textContent() ?? '';
    const secondText = await prices.nth(1).textContent() ?? '';
    const first = parseFloat(firstText.replace(/[^0-9.]/g, ''));
    const second = parseFloat(secondText.replace(/[^0-9.]/g, ''));
    expect(first).toBeGreaterThanOrEqual(second);
  });

  // Happy path: sort persists with filters
  test('sort selection persists when filter applied', async ({ page }) => {
    await page.getByRole('combobox', { name: /sort by/i }).selectOption('price_asc');
    await page.getByRole('checkbox', { name: '{{filterCategory}}' }).check();
    await expect(page).toHaveURL(/sort=price_asc/);
    await expect(page.getByRole('combobox', { name: /sort by/i })).toHaveValue('price_asc');
  });

  // Edge case: default sort is relevance
  test('default sort is relevance', async ({ page }) => {
    await expect(page.getByRole('combobox', { name: /sort by/i })).toHaveValue('relevance');
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Search Sorting', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/search?q={{searchQuery}}');
  });

  test('sorts alphabetically A-Z', async ({ page }) => {
    await page.getByRole('combobox', { name: /sort by/i }).selectOption('name_asc');
    await expect(page).toHaveURL(/sort=name_asc/);
    const names = page.getByTestId('result-name');
    const first = await names.first().textContent();
    const second = await names.nth(1).textContent();
    expect(first.localeCompare(second)).toBeLessThanOrEqual(0);
  });

  test('sorts by price low to high', async ({ page }) => {
    await page.getByRole('combobox', { name: /sort by/i }).selectOption('price_asc');
    const prices = page.getByTestId('result-price');
    const a = parseFloat((await prices.first().textContent()).replace(/[^0-9.]/g, ''));
    const b = parseFloat((await prices.nth(1).textContent()).replace(/[^0-9.]/g, ''));
    expect(a).toBeLessThanOrEqual(b);
  });

  test('default sort is relevance', async ({ page }) => {
    await expect(page.getByRole('combobox', { name: /sort by/i })).toHaveValue('relevance');
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Name A-Z | First result ≤ second alphabetically |
| Name Z-A | First result ≥ second alphabetically |
| Date newest | Dates in descending order |
| Price low-high | Prices in ascending order |
| Price high-low | Prices in descending order |
| Sort + filter | Sort param persists when filter applied |
| Default sort | Relevance selected by default |
