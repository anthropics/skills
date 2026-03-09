# Authorization Types

Worldline Direct supports three authorization modes that determine how and when funds are captured.

## Overview

| Type | Hold Period | Partial Capture | Use Case |
|------|-------------|-----------------|----------|
| **Pre-Authorization** | Up to 30 days | Yes | Car rental, hotels, variable amounts |
| **Final Authorization** | 7 days | No (full only) | Standard e-commerce |
| **Direct Sale** | Immediate | N/A | Digital goods, subscriptions |

## Pre-Authorization

Blocks funds for up to 30 days. Allows multiple partial captures.

### When to Use
- Car rental (deposit + actual rental)
- Hotels (reservation + incidentals)
- Any scenario where final amount is unknown

### Example

```javascript
// Create pre-authorization
const auth = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 100000, currencyCode: "EUR" }, // €1000
    references: { merchantReference: `auth-${orderId}` }
  },
  cardPaymentMethodSpecificInput: {
    authorizationMode: "PRE_AUTHORIZATION",
    card: cardDetails
  }
});

// Payment status: PENDING_CAPTURE

// Later: Capture partial amount
await client.payments.capturePayment(merchantId, paymentId, {
  amount: 75000, // €750
  isFinal: false // More captures possible
});

// Even later: Capture additional amount
await client.payments.capturePayment(merchantId, paymentId, {
  amount: 15000, // €150
  isFinal: true // No more captures
});

// Total captured: €900 (less than authorized €1000)
// Remaining €100 is automatically released
```

### Key Points
- Maximum hold period: 30 days
- Can capture less than authorized
- Multiple partial captures allowed
- Unused amount automatically released
- Set `isFinal: true` on last capture

## Final Authorization

Blocks funds for 7 days. Only full capture is allowed.

### When to Use
- Standard e-commerce
- Physical goods shipped together
- Known final amount at checkout

### Example

```javascript
// Create final authorization
const auth = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 4999, currencyCode: "EUR" },
    references: { merchantReference: `order-${orderId}` }
  },
  cardPaymentMethodSpecificInput: {
    authorizationMode: "FINAL_AUTHORIZATION",
    card: cardDetails
  }
});

// Payment status: PENDING_CAPTURE

// At shipping: Full capture
await client.payments.capturePayment(merchantId, paymentId, {
  isFinal: true
  // Amount not specified = full authorized amount
});
```

### Key Points
- Maximum hold period: 7 days
- Must capture full amount
- Single capture only
- Cancel if order is cancelled

## Direct Sale

Authorizes and captures in one step.

### When to Use
- Digital goods (immediate delivery)
- Subscriptions
- Services rendered immediately
- No fulfillment delay

### Example

```javascript
// Direct sale - immediate capture
const payment = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 999, currencyCode: "EUR" },
    references: { merchantReference: `digital-${orderId}` }
  },
  cardPaymentMethodSpecificInput: {
    authorizationMode: "SALE",
    card: cardDetails
  }
});

// Payment status: CAPTURED (immediately)
// Funds are collected, no further action needed
```

### Key Points
- Funds captured immediately
- No separate capture step
- No hold period
- Refund if needed

## Hosted Checkout Configuration

Set authorization mode in hosted checkout:

```javascript
const checkout = await client.hostedCheckout.createHostedCheckout(merchantId, {
  order: { amountOfMoney: { amount: 10000, currencyCode: "EUR" } },
  hostedCheckoutSpecificInput: {
    returnUrl: "https://...",
    cardPaymentMethodSpecificInput: {
      authorizationMode: "PRE_AUTHORIZATION" // or FINAL_AUTHORIZATION, SALE
    }
  }
});
```

## Comparison: When to Use Each

| Scenario | Recommended Mode |
|----------|------------------|
| Digital download | SALE |
| SaaS subscription | SALE |
| Physical goods, ship same day | SALE |
| Physical goods, ship in 1-7 days | FINAL_AUTHORIZATION |
| Marketplace, ship in 7+ days | PRE_AUTHORIZATION |
| Car rental | PRE_AUTHORIZATION |
| Hotel booking | PRE_AUTHORIZATION |
| Restaurant (tips) | SALE |
| Pre-order (release in weeks) | PRE_AUTHORIZATION |

## Cancellation

Before capture, you can cancel any authorization:

```javascript
await client.payments.cancelPayment(merchantId, paymentId);
// Funds are released to cardholder
```

## Partial Cancellation (Pre-Auth Only)

```javascript
// Authorized €1000, want to reduce to €600
await client.payments.cancelPayment(merchantId, paymentId, {
  amount: 40000, // Cancel €400
  isFinal: false
});
// €600 still available to capture
```

## Status Flow

### Pre-Authorization
```
PENDING_CAPTURE → CAPTURE_REQUESTED → CAPTURED
              ↓
           CANCELLED
```

### Final Authorization
```
PENDING_CAPTURE → CAPTURED
              ↓
           CANCELLED
```

### Direct Sale
```
CAPTURED (immediate)
```

## Timeouts and Expiration

| Mode | Hold Period | What Happens on Expiry |
|------|-------------|----------------------|
| Pre-Auth | 30 days | Auth expires, funds released |
| Final Auth | 7 days | Auth expires, funds released |
| Sale | N/A | Already captured |

**Important**: The actual hold period may vary by:
- Card network (Visa, Mastercard, etc.)
- Issuing bank
- Card type (credit vs debit)
- Region

Always capture within a reasonable timeframe.

## Error Handling

```javascript
try {
  await client.payments.capturePayment(merchantId, paymentId, {
    amount: 10000,
    isFinal: true
  });
} catch (error) {
  if (error.statusCode === 400) {
    // Invalid request (e.g., amount exceeds authorization)
    console.error("Capture failed:", error.body?.errors);
  } else if (error.statusCode === 409) {
    // Authorization expired or already captured
    console.error("Authorization no longer valid");
  }
}
```

## Best Practices

1. **Choose the right mode** - Match your business flow
2. **Capture promptly** - Don't wait until last day
3. **Handle expiration** - Re-authorize if needed
4. **Use unique references** - Track captures per auth
5. **Monitor status** - Implement webhooks
6. **Cancel unused auths** - Don't leave funds blocked
