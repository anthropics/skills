# Order Confirmation Template

Tests the success page and order details after checkout.

## Prerequisites
- Completed order with ID `{{orderId}}`
- Authenticated session via `{{authStorageStatePath}}`
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Order Confirmation', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  // Happy path: confirmation page content
  test('shows order confirmation with correct details', async ({ page }) => {
    await page.goto('{{baseUrl}}/order-confirmation/{{orderId}}');
    await expect(page.getByRole('heading', { name: /order confirmed|thank you/i })).toBeVisible();
    await expect(page.getByText('{{orderId}}')).toBeVisible();
    await expect(page.getByText('{{productName}}')).toBeVisible();
    await expect(page.getByText('{{orderTotal}}')).toBeVisible();
  });

  // Happy path: confirmation email notice
  test('shows confirmation email notice', async ({ page }) => {
    await page.goto('{{baseUrl}}/order-confirmation/{{orderId}}');
    await expect(page.getByText(/confirmation.*sent to|email.*{{username}}/i)).toBeVisible();
  });

  // Happy path: billing and shipping details shown
  test('displays shipping address on confirmation page', async ({ page }) => {
    await page.goto('{{baseUrl}}/order-confirmation/{{orderId}}');
    await expect(page.getByText('{{shippingAddress}}')).toBeVisible();
    await expect(page.getByText('{{billingAddress}}')).toBeVisible();
  });

  // Happy path: CTA navigates to order history
  test('"view your orders" link navigates to order history', async ({ page }) => {
    await page.goto('{{baseUrl}}/order-confirmation/{{orderId}}');
    await page.getByRole('link', { name: /view.*orders|my orders/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/orders');
  });

  // Happy path: continue shopping CTA
  test('"continue shopping" returns to products', async ({ page }) => {
    await page.goto('{{baseUrl}}/order-confirmation/{{orderId}}');
    await page.getByRole('link', { name: /continue shopping/i }).click();
    await expect(page).toHaveURL('{{baseUrl}}/products');
  });

  // Error case: accessing another user's order shows 403
  test('cannot access another user\'s confirmation page', async ({ page }) => {
    await page.goto('{{baseUrl}}/order-confirmation/{{otherUsersOrderId}}');
    await expect(page).toHaveURL(/\/403|\/dashboard/);
  });

  // Edge case: cart is empty after successful checkout
  test('cart is empty after order confirmed', async ({ page }) => {
    await page.goto('{{baseUrl}}/order-confirmation/{{orderId}}');
    await expect(page.getByRole('status', { name: /cart/i })).toContainText('0');
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Order Confirmation', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test('shows order id and total on confirmation', async ({ page }) => {
    await page.goto('{{baseUrl}}/order-confirmation/{{orderId}}');
    await expect(page.getByRole('heading', { name: /order confirmed|thank you/i })).toBeVisible();
    await expect(page.getByText('{{orderId}}')).toBeVisible();
    await expect(page.getByText('{{orderTotal}}')).toBeVisible();
  });

  test('cart is empty after checkout', async ({ page }) => {
    await page.goto('{{baseUrl}}/order-confirmation/{{orderId}}');
    await expect(page.getByRole('status', { name: /cart/i })).toContainText('0');
  });

  test('cannot access another user\'s order', async ({ page }) => {
    await page.goto('{{baseUrl}}/order-confirmation/{{otherUsersOrderId}}');
    await expect(page).toHaveURL(/\/403|\/dashboard/);
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Confirmation content | Order ID, product, total visible |
| Email notice | Confirmation email address shown |
| Shipping/billing | Addresses displayed |
| View orders CTA | Navigates to /orders |
| Continue shopping | Returns to /products |
| Unauthorized | Other user's order → 403 |
| Cart cleared | Cart count = 0 after checkout |
