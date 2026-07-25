# Payment Template

Tests card form entry, validation, and payment processing.

## Prerequisites
- Cart with items, shipping filled
- Test card numbers: `{{testCardNumber}}` (success), `{{declinedCardNumber}}` (decline)
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect, Page } from '@playwright/test';

async function fillCardForm(page: Page, card: {
  number: string; expiry: string; cvc: string; name: string;
}): Promise<void> {
  // Stripe/Braintree iframes — adapt frame locator to your provider
  const cardFrame = page.frameLocator('[data-testid="card-number-frame"]');
  await cardFrame.getByRole('textbox', { name: /card number/i }).fill(card.number);
  const expiryFrame = page.frameLocator('[data-testid="expiry-frame"]');
  await expiryFrame.getByRole('textbox', { name: /expiry/i }).fill(card.expiry);
  const cvcFrame = page.frameLocator('[data-testid="cvc-frame"]');
  await cvcFrame.getByRole('textbox', { name: /cvc|cvv/i }).fill(card.cvc);
  await page.getByRole('textbox', { name: /cardholder name/i }).fill(card.name);
}

test.describe('Payment', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/checkout/payment');
  });

  // Happy path: successful payment
  test('completes payment with valid card', async ({ page }) => {
    await fillCardForm(page, {
      number: '{{testCardNumber}}',
      expiry: '12/28',
      cvc: '123',
      name: '{{cardholderName}}',
    });
    await page.getByRole('button', { name: /pay|place order/i }).click();
    await expect(page).toHaveURL(/\/order-confirmation|\/success/);
    await expect(page.getByRole('heading', { name: /order confirmed|thank you/i })).toBeVisible();
  });

  // Happy path: processing state shown
  test('shows processing state while payment is pending', async ({ page }) => {
    await fillCardForm(page, {
      number: '{{testCardNumber}}',
      expiry: '12/28',
      cvc: '123',
      name: '{{cardholderName}}',
    });
    const payBtn = page.getByRole('button', { name: /pay|place order/i });
    await payBtn.click();
    await expect(payBtn).toBeDisabled();
    await expect(page.getByText(/processing|please wait/i)).toBeVisible();
  });

  // Error case: declined card
  test('shows decline error for rejected card', async ({ page }) => {
    await fillCardForm(page, {
      number: '{{declinedCardNumber}}',
      expiry: '12/28',
      cvc: '123',
      name: '{{cardholderName}}',
    });
    await page.getByRole('button', { name: /pay|place order/i }).click();
    await expect(page.getByRole('alert')).toContainText(/declined|card.*not accepted/i);
    await expect(page).toHaveURL(/\/checkout\/payment/);
  });

  // Error case: invalid card number format
  test('shows inline error for invalid card number', async ({ page }) => {
    const cardFrame = page.frameLocator('[data-testid="card-number-frame"]');
    await cardFrame.getByRole('textbox', { name: /card number/i }).fill('1234');
    await page.getByRole('button', { name: /pay|place order/i }).click();
    await expect(page.getByText(/invalid.*card number/i)).toBeVisible();
  });

  // Error case: expired card
  test('shows error for expired card', async ({ page }) => {
    await fillCardForm(page, {
      number: '{{testCardNumber}}',
      expiry: '01/20',
      cvc: '123',
      name: '{{cardholderName}}',
    });
    await page.getByRole('button', { name: /pay|place order/i }).click();
    await expect(page.getByRole('alert')).toContainText(/expired|invalid.*expiry/i);
  });

  // Edge case: 3DS authentication required
  test('handles 3DS challenge and completes payment', async ({ page }) => {
    await fillCardForm(page, {
      number: '{{threeDsCardNumber}}',
      expiry: '12/28',
      cvc: '123',
      name: '{{cardholderName}}',
    });
    await page.getByRole('button', { name: /pay|place order/i }).click();
    // 3DS modal appears
    const challengeFrame = page.frameLocator('[data-testid="3ds-challenge-frame"]');
    await challengeFrame.getByRole('button', { name: /complete authentication/i }).click();
    await expect(page).toHaveURL(/\/order-confirmation|\/success/);
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Payment', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/checkout/payment');
  });

  test('completes payment with valid card', async ({ page }) => {
    const cardFrame = page.frameLocator('[data-testid="card-number-frame"]');
    await cardFrame.getByRole('textbox', { name: /card number/i }).fill('{{testCardNumber}}');
    await page.getByRole('button', { name: /pay|place order/i }).click();
    await expect(page).toHaveURL(/\/order-confirmation/);
  });

  test('shows decline error for rejected card', async ({ page }) => {
    const cardFrame = page.frameLocator('[data-testid="card-number-frame"]');
    await cardFrame.getByRole('textbox', { name: /card number/i }).fill('{{declinedCardNumber}}');
    await page.getByRole('button', { name: /pay|place order/i }).click();
    await expect(page.getByRole('alert')).toContainText(/declined/i);
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Successful payment | Valid test card → order confirmation |
| Processing state | Button disabled + spinner during processing |
| Declined card | Error alert, stays on payment page |
| Invalid card number | Inline validation from provider |
| Expired card | Expiry error |
| 3DS challenge | Modal completed, payment succeeds |
