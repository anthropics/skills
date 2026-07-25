# Update Cart Quantity Template

Tests increasing, decreasing, and removing items from cart.

## Prerequisites
- Cart with at least one item: `{{productName}}` (quantity 2)
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Update Cart Quantity', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/cart');
    // Assumes cart is pre-populated via storageState or API setup
  });

  // Happy path: increase quantity
  test('increases item quantity', async ({ page }) => {
    const row = page.getByRole('row', { name: new RegExp('{{productName}}') });
    await row.getByRole('button', { name: /increase|plus|\+/i }).click();
    await expect(row.getByRole('spinbutton', { name: /quantity/i })).toHaveValue('3');
    await expect(page.getByRole('region', { name: /order summary/i })).toContainText('{{updatedTotal}}');
  });

  // Happy path: decrease quantity
  test('decreases item quantity', async ({ page }) => {
    const row = page.getByRole('row', { name: new RegExp('{{productName}}') });
    await row.getByRole('button', { name: /decrease|minus|−/i }).click();
    await expect(row.getByRole('spinbutton', { name: /quantity/i })).toHaveValue('1');
  });

  // Happy path: type quantity directly
  test('updates quantity by typing in field', async ({ page }) => {
    const row = page.getByRole('row', { name: new RegExp('{{productName}}') });
    const qtyInput = row.getByRole('spinbutton', { name: /quantity/i });
    await qtyInput.fill('5');
    await qtyInput.press('Tab');
    await expect(qtyInput).toHaveValue('5');
  });

  // Happy path: remove item with remove button
  test('removes item from cart', async ({ page }) => {
    const row = page.getByRole('row', { name: new RegExp('{{productName}}') });
    await row.getByRole('button', { name: /remove|delete/i }).click();
    await expect(row).toBeHidden();
    await expect(page.getByText(/cart is empty/i)).toBeVisible();
  });

  // Happy path: decrease to 0 removes item
  test('removing to quantity 0 removes item', async ({ page }) => {
    const row = page.getByRole('row', { name: new RegExp('{{productName}}') });
    await row.getByRole('button', { name: /decrease|minus/i }).click(); // from 2 to 1
    await row.getByRole('button', { name: /decrease|minus/i }).click(); // should trigger remove
    await expect(row).toBeHidden();
  });

  // Error case: quantity cannot go below 1 via decrease button
  test('decrease button disabled at minimum quantity', async ({ page }) => {
    const row = page.getByRole('row').nth(1);
    const qty = row.getByRole('spinbutton', { name: /quantity/i });
    await qty.fill('1');
    await qty.press('Tab');
    await expect(row.getByRole('button', { name: /decrease|minus/i })).toBeDisabled();
  });

  // Edge case: quantity clamped to stock limit
  test('quantity capped at available stock', async ({ page }) => {
    const row = page.getByRole('row', { name: new RegExp('{{productName}}') });
    const qtyInput = row.getByRole('spinbutton', { name: /quantity/i });
    await qtyInput.fill('{{overStockQuantity}}');
    await qtyInput.press('Tab');
    await expect(qtyInput).toHaveValue('{{maxStock}}');
    await expect(page.getByRole('alert')).toContainText(/max.*available|stock limit/i);
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Update Cart Quantity', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/cart');
  });

  test('increases item quantity', async ({ page }) => {
    const row = page.getByRole('row', { name: new RegExp('{{productName}}') });
    await row.getByRole('button', { name: /increase|plus|\+/i }).click();
    await expect(row.getByRole('spinbutton', { name: /quantity/i })).toHaveValue('3');
  });

  test('removes item from cart', async ({ page }) => {
    await page.getByRole('row', { name: new RegExp('{{productName}}') })
      .getByRole('button', { name: /remove|delete/i }).click();
    await expect(page.getByText(/cart is empty/i)).toBeVisible();
  });

  test('decrease button disabled at quantity 1', async ({ page }) => {
    const row = page.getByRole('row').nth(1);
    await row.getByRole('spinbutton', { name: /quantity/i }).fill('1');
    await row.getByRole('spinbutton', { name: /quantity/i }).press('Tab');
    await expect(row.getByRole('button', { name: /decrease|minus/i })).toBeDisabled();
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Increase | +1 → quantity updates, total recalculates |
| Decrease | -1 → quantity updates |
| Type directly | Manual quantity input accepted on blur/tab |
| Remove button | Item removed, empty-cart message shown |
| Decrease to 0 | Triggers item removal |
| Min quantity | Decrease button disabled at 1 |
| Stock cap | Input clamped to available stock |
