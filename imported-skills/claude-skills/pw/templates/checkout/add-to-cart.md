# Add to Cart Template

Tests adding items to cart and quantity updates.

## Prerequisites
- Authenticated (or guest) session
- Product: ID `{{productId}}`, name `{{productName}}`, price `{{productPrice}}`
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Add to Cart', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/products/{{productId}}');
  });

  // Happy path: add single item
  test('adds product to cart', async ({ page }) => {
    await page.getByRole('button', { name: /add to cart/i }).click();
    await expect(page.getByRole('status', { name: /cart/i })).toContainText('1');
    await expect(page.getByRole('alert')).toContainText(/added to cart/i);
  });

  // Happy path: add multiple items increments count
  test('increments cart count on repeated add', async ({ page }) => {
    await page.getByRole('button', { name: /add to cart/i }).click();
    await page.getByRole('button', { name: /add to cart/i }).click();
    await expect(page.getByRole('status', { name: /cart/i })).toContainText('2');
  });

  // Happy path: add with quantity selector
  test('adds specified quantity to cart', async ({ page }) => {
    await page.getByRole('spinbutton', { name: /quantity/i }).fill('3');
    await page.getByRole('button', { name: /add to cart/i }).click();
    await expect(page.getByRole('status', { name: /cart/i })).toContainText('3');
  });

  // Happy path: cart persists on navigation
  test('cart persists after navigating away', async ({ page }) => {
    await page.getByRole('button', { name: /add to cart/i }).click();
    await page.goto('{{baseUrl}}/products');
    await expect(page.getByRole('status', { name: /cart/i })).toContainText('1');
  });

  // Error case: out of stock product cannot be added
  test('add to cart button disabled for out-of-stock product', async ({ page }) => {
    await page.goto('{{baseUrl}}/products/{{outOfStockProductId}}');
    await expect(page.getByRole('button', { name: /add to cart/i })).toBeDisabled();
    await expect(page.getByText(/out of stock/i)).toBeVisible();
  });

  // Error case: quantity exceeds stock
  test('shows error when quantity exceeds available stock', async ({ page }) => {
    await page.getByRole('spinbutton', { name: /quantity/i }).fill('{{overStockQuantity}}');
    await page.getByRole('button', { name: /add to cart/i }).click();
    await expect(page.getByRole('alert')).toContainText(/only.*available|exceeds.*stock/i);
  });

  // Edge case: cart opens after add
  test('cart drawer opens after adding item', async ({ page }) => {
    await page.getByRole('button', { name: /add to cart/i }).click();
    await expect(page.getByRole('dialog', { name: /cart/i })).toBeVisible();
    await expect(page.getByRole('dialog').getByText('{{productName}}')).toBeVisible();
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Add to Cart', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/products/{{productId}}');
  });

  test('adds product to cart', async ({ page }) => {
    await page.getByRole('button', { name: /add to cart/i }).click();
    await expect(page.getByRole('status', { name: /cart/i })).toContainText('1');
  });

  test('add to cart disabled for out-of-stock', async ({ page }) => {
    await page.goto('{{baseUrl}}/products/{{outOfStockProductId}}');
    await expect(page.getByRole('button', { name: /add to cart/i })).toBeDisabled();
  });

  test('cart persists after navigation', async ({ page }) => {
    await page.getByRole('button', { name: /add to cart/i }).click();
    await page.goto('{{baseUrl}}/products');
    await expect(page.getByRole('status', { name: /cart/i })).toContainText('1');
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Single add | Product added, cart count = 1 |
| Repeated add | Cart count increments |
| Quantity selector | Specified quantity added |
| Persist on nav | Cart count survives page change |
| Out of stock | Button disabled, label shown |
| Quantity exceeds stock | Error alert |
| Cart drawer | Slide-in cart opens showing added item |
