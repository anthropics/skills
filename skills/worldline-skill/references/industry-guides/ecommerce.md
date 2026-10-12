# E-commerce Payment Integration

Standard online retail with immediate fulfillment or physical goods shipping.

## Recommended Payment Flow

```
Digital Goods: Direct Sale (authorize + capture immediately)
Physical Goods: Final Authorization → Capture at shipping
```

## Integration Method: Hosted Checkout

Recommended for most e-commerce sites. Lowest PCI scope (SAQ-A).

```javascript
const checkout = await client.hostedCheckout.createHostedCheckout(merchantId, {
  order: {
    amountOfMoney: { amount: 4999, currencyCode: "EUR" },
    customer: {
      merchantCustomerId: customerId,
      billingAddress: {
        street: "123 Main St",
        city: "Amsterdam",
        countryCode: "NL",
        zip: "1011AB"
      }
    },
    references: { merchantReference: `order-${orderId}` }
  },
  hostedCheckoutSpecificInput: {
    returnUrl: "https://shop.example.com/checkout/complete",
    showResultPage: false, // Handle result on your site
    paymentProductFilters: {
      restrictTo: {
        products: [1, 3, 117, 125, 302, 840] // Visa, MC, iDEAL, PayPal, Apple Pay, Klarna
      }
    }
  }
});

// Redirect customer to:
const redirectUrl = `https://payment.preprod.direct.worldline-solutions.com/hostedcheckout/${checkout.hostedCheckoutId}`;
```

## Digital Goods: Direct Sale

For immediate delivery (downloads, subscriptions, credits).

```javascript
const payment = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 999, currencyCode: "EUR" },
    references: { merchantReference: `digital-${orderId}` }
  },
  cardPaymentMethodSpecificInput: {
    authorizationMode: "SALE", // Immediate capture
    card: {
      cardNumber: "4111111111111111",
      expiryDate: "1225",
      cvv: "123",
      cardholderName: "John Doe"
    },
    threeDSecure: {
      redirectionData: {
        returnUrl: "https://shop.example.com/3ds/complete"
      }
    }
  }
});
```

## Physical Goods: Authorize, Then Capture

For shipped items - capture only when shipping.

```javascript
// At checkout
const auth = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 7999, currencyCode: "EUR" },
    references: { merchantReference: `order-${orderId}` }
  },
  cardPaymentMethodSpecificInput: {
    authorizationMode: "FINAL_AUTHORIZATION", // 7-day hold
    card: cardDetails
  }
});

// Store paymentId with order

// At shipping
await client.payments.capturePayment(merchantId, paymentId, {
  amount: 7999,
  isFinal: true
});
```

## One-Click Checkout (Returning Customers)

Store tokens for faster checkout.

```javascript
// Initial purchase - tokenize
const payment = await client.payments.createPayment(merchantId, {
  order: { amountOfMoney: { amount: 2999, currencyCode: "EUR" } },
  cardPaymentMethodSpecificInput: {
    card: cardDetails,
    tokenize: true // Request token
  }
});

const token = payment.payment.paymentOutput.cardPaymentMethodSpecificOutput.token;

// Future purchases - use token
const repeat = await client.payments.createPayment(merchantId, {
  order: { amountOfMoney: { amount: 3999, currencyCode: "EUR" } },
  cardPaymentMethodSpecificInput: {
    token: token,
    unscheduledCardOnFileRequestor: "cardholderInitiated",
    unscheduledCardOnFileSequenceIndicator: "subsequent"
  }
});
```

## Handling Partial Shipments

When order ships in multiple packages.

```javascript
// Original auth for €100
const auth = await client.payments.createPayment(merchantId, {
  order: { amountOfMoney: { amount: 10000, currencyCode: "EUR" } },
  cardPaymentMethodSpecificInput: {
    authorizationMode: "PRE_AUTHORIZATION", // Use pre-auth for partial captures
    card: cardDetails
  }
});

// Ship first package - €60
await client.payments.capturePayment(merchantId, paymentId, {
  amount: 6000,
  isFinal: false // More to come
});

// Ship second package - €40
await client.payments.capturePayment(merchantId, paymentId, {
  amount: 4000,
  isFinal: true
});
```

## Order Modifications

### Cancel Before Shipping
```javascript
await client.payments.cancelPayment(merchantId, paymentId);
```

### Partial Order Cancellation
```javascript
// Auth was for €100, customer cancelled €30 worth
await client.payments.capturePayment(merchantId, paymentId, {
  amount: 7000, // Only capture €70
  isFinal: true
});
```

### Refund After Capture
```javascript
// Full refund
await client.payments.refundPayment(merchantId, paymentId, {
  amountOfMoney: { amount: 7999, currencyCode: "EUR" }
});

// Partial refund (1 item returned)
await client.payments.refundPayment(merchantId, paymentId, {
  amountOfMoney: { amount: 2999, currencyCode: "EUR" }
});
```

## Payment Methods by Country

| Country | Recommended Methods |
|---------|-------------------|
| Netherlands | iDEAL, Cards, Klarna |
| Germany | SEPA, Cards, Klarna, PayPal |
| France | Cartes Bancaires, Oney |
| Belgium | Bancontact, Cards |
| Poland | Przelewy24, BLIK |
| Austria | EPS, Cards |
| Switzerland | TWINT, Cards |

## Best Practices

1. **Offer local payment methods** - Increases conversion
2. **Use Hosted Checkout** - Simplest PCI compliance
3. **3DS for all card payments** - Required in EU (SCA)
4. **Capture at shipping** - For physical goods
5. **Direct sale for digital** - No capture needed
6. **Store tokens with consent** - For one-click checkout
7. **Handle webhooks** - Don't rely on redirect alone

## Checkout Optimization

### Reduce Abandonment
- Show payment methods early
- Offer express checkout (Apple Pay, Google Pay)
- Remember payment methods for returning customers

### Mobile Optimization
- Use Apple Pay / Google Pay
- Hosted Checkout is mobile-responsive
- Test on real devices

## Status Codes

| Status | Meaning | Next Step |
|--------|---------|-----------|
| PENDING_APPROVAL | 3DS required | Wait for customer |
| PENDING_CAPTURE | Authorized | Capture when ready |
| CAPTURED | Complete | Done |
| CANCELLED | Voided | Order cancelled |
| REJECTED | Failed | Retry or ask for new card |
