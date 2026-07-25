# Apply Coupon Template

Tests valid coupon code, invalid code, and expired coupon handling.

## Prerequisites
- Cart with items totalling `{{cartTotal}}`
- Valid coupon: `{{validCouponCode}}` ({{discountPercent}}% off)
- Expired coupon: `{{expiredCouponCode}}`
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Apply Coupon', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/cart');
  });

  // Happy path: valid coupon applied
  test('applies valid coupon and shows discount', async ({ page }) => {
    await page.getByRole('textbox', { name: /coupon|promo code/i }).fill('{{validCouponCode}}');
    await page.getByRole('button', { name: /apply/i }).click();
    await expect(page.getByText(/{{discountPercent}}%.*off|discount applied/i)).toBeVisible();
    await expect(page.getByText('{{discountedTotal}}')).toBeVisible();
    await expect(page.getByRole('button', { name: /remove coupon/i })).toBeVisible();
  });

  // Happy path: percentage discount calculated correctly
  test('calculates discount amount correctly', async ({ page }) => {
    await page.getByRole('textbox', { name: /coupon|promo code/i }).fill('{{validCouponCode}}');
    await page.getByRole('button', { name: /apply/i }).click();
    const discountLine = page.getByRole('row', { name: /discount/i });
    await expect(discountLine).toContainText('-{{discountAmount}}');
  });

  // Happy path: remove applied coupon
  test('removes applied coupon and restores original total', async ({ page }) => {
    await page.getByRole('textbox', { name: /coupon|promo code/i }).fill('{{validCouponCode}}');
    await page.getByRole('button', { name: /apply/i }).click();
    await page.getByRole('button', { name: /remove coupon/i }).click();
    await expect(page.getByText('{{cartTotal}}')).toBeVisible();
    await expect(page.getByRole('button', { name: /remove coupon/i })).toBeHidden();
  });

  // Error case: invalid coupon code
  test('shows error for invalid coupon code', async ({ page }) => {
    await page.getByRole('textbox', { name: /coupon|promo code/i }).fill('INVALID123');
    await page.getByRole('button', { name: /apply/i }).click();
    await expect(page.getByRole('alert')).toContainText(/invalid.*coupon|code not found/i);
    await expect(page.getByText('{{cartTotal}}')).toBeVisible();
  });

  // Error case: expired coupon
  test('shows error for expired coupon', async ({ page }) => {
    await page.getByRole('textbox', { name: /coupon|promo code/i }).fill('{{expiredCouponCode}}');
    await page.getByRole('button', { name: /apply/i }).click();
    await expect(page.getByRole('alert')).toContainText(/expired|no longer valid/i);
  });

  // Error case: coupon not applicable to cart items
  test('shows error when coupon excludes cart products', async ({ page }) => {
    await page.getByRole('textbox', { name: /coupon|promo code/i }).fill('{{categoryRestrictedCoupon}}');
    await page.getByRole('button', { name: /apply/i }).click();
    await expect(page.getByRole('alert')).toContainText(/not applicable|excluded/i);
  });

  // Edge case: empty coupon field
  test('apply button disabled when coupon field is empty', async ({ page }) => {
    const applyBtn = page.getByRole('button', { name: /apply/i });
    await expect(applyBtn).toBeDisabled();
    await page.getByRole('textbox', { name: /coupon|promo code/i }).fill('X');
    await expect(applyBtn).toBeEnabled();
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Apply Coupon', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/cart');
  });

  test('applies valid coupon and shows discount', async ({ page }) => {
    await page.getByRole('textbox', { name: /coupon|promo code/i }).fill('{{validCouponCode}}');
    await page.getByRole('button', { name: /apply/i }).click();
    await expect(page.getByText(/discount applied/i)).toBeVisible();
    await expect(page.getByText('{{discountedTotal}}')).toBeVisible();
  });

  test('shows error for invalid coupon', async ({ page }) => {
    await page.getByRole('textbox', { name: /coupon|promo code/i }).fill('INVALID123');
    await page.getByRole('button', { name: /apply/i }).click();
    await expect(page.getByRole('alert')).toContainText(/invalid.*coupon/i);
  });

  test('shows error for expired coupon', async ({ page }) => {
    await page.getByRole('textbox', { name: /coupon|promo code/i }).fill('{{expiredCouponCode}}');
    await page.getByRole('button', { name: /apply/i }).click();
    await expect(page.getByRole('alert')).toContainText(/expired/i);
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Valid coupon | Discount applied, total updated |
| Discount calculation | Discount line shows correct amount |
| Remove coupon | Original total restored |
| Invalid code | Error alert, total unchanged |
| Expired coupon | Expiry error shown |
| Category restriction | Coupon not applicable error |
| Empty field | Apply button disabled |
