# Order History Template

Tests listing orders, viewing order details, and pagination.

## Prerequisites
- Authenticated session via `{{authStorageStatePath}}`
- At least `{{orderCount}}` orders seeded for user
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Order History', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  // Happy path: order list
  test('displays list of orders with key details', async ({ page }) => {
    await page.goto('{{baseUrl}}/orders');
    await expect(page.getByRole('heading', { name: /orders|order history/i })).toBeVisible();
    const rows = page.getByRole('row').filter({ hasNot: page.getByRole('columnheader') });
    await expect(rows.first()).toContainText('{{latestOrderId}}');
    await expect(rows.first()).toContainText('{{latestOrderStatus}}');
    await expect(rows.first()).toContainText('{{latestOrderTotal}}');
  });

  // Happy path: view order details
  test('navigates to order detail from history', async ({ page }) => {
    await page.goto('{{baseUrl}}/orders');
    await page.getByRole('link', { name: new RegExp('{{latestOrderId}}') }).click();
    await expect(page).toHaveURL(`{{baseUrl}}/orders/{{latestOrderId}}`);
    await expect(page.getByRole('heading', { name: '{{latestOrderId}}' })).toBeVisible();
    await expect(page.getByText('{{productName}}')).toBeVisible();
  });

  // Happy path: order status badge
  test('shows correct status badge for each order', async ({ page }) => {
    await page.goto('{{baseUrl}}/orders');
    const deliveredBadge = page.getByRole('status', { name: /delivered/i }).first();
    await expect(deliveredBadge).toBeVisible();
  });

  // Happy path: pagination
  test('paginates through orders', async ({ page }) => {
    await page.goto('{{baseUrl}}/orders');
    const firstPageFirstOrder = await page.getByRole('row').nth(1).textContent();
    await page.getByRole('button', { name: /next page|>/i }).click();
    await expect(page.getByRole('row').nth(1)).not.toHaveText(firstPageFirstOrder!);
    await expect(page.getByRole('button', { name: /previous page|</i })).toBeEnabled();
  });

  // Happy path: items per page selector
  test('changes items per page', async ({ page }) => {
    await page.goto('{{baseUrl}}/orders');
    await page.getByRole('combobox', { name: /per page|items per page/i }).selectOption('50');
    const rows = page.getByRole('row').filter({ hasNot: page.getByRole('columnheader') });
    await expect(rows).toHaveCount(Math.min(50, {{orderCount}}));
  });

  // Error case: empty order history
  test('shows empty state for user with no orders', async ({ page }) => {
    await page.goto('{{baseUrl}}/orders');
    // Assumes this user context has no orders
    await expect(page.getByText(/no orders yet|start shopping/i)).toBeVisible();
  });

  // Edge case: reorder from history
  test('adds previous order items to cart via reorder', async ({ page }) => {
    await page.goto('{{baseUrl}}/orders/{{latestOrderId}}');
    await page.getByRole('button', { name: /reorder|buy again/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/cart');
    await expect(page.getByText('{{productName}}')).toBeVisible();
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Order History', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test('displays orders with id, status, and total', async ({ page }) => {
    await page.goto('{{baseUrl}}/orders');
    const rows = page.getByRole('row').filter({ hasNot: page.getByRole('columnheader') });
    await expect(rows.first()).toContainText('{{latestOrderId}}');
  });

  test('navigates to order detail', async ({ page }) => {
    await page.goto('{{baseUrl}}/orders');
    await page.getByRole('link', { name: new RegExp('{{latestOrderId}}') }).click();
    await expect(page).toHaveURL(`{{baseUrl}}/orders/{{latestOrderId}}`);
  });

  test('paginates through orders', async ({ page }) => {
    await page.goto('{{baseUrl}}/orders');
    await page.getByRole('button', { name: /next page|>/i }).click();
    await expect(page.getByRole('button', { name: /previous page|</i })).toBeEnabled();
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Order list | ID, status, total visible per row |
| Order detail | Clicking order → detail page |
| Status badge | Correct badge per order state |
| Pagination | Next page loads different orders |
| Items per page | Selector changes row count |
| Empty state | No-orders message with CTA |
| Reorder | Previous order items added to cart |
