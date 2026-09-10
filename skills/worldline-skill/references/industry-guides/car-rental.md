# Car Rental Payment Integration

Car rental businesses have unique payment requirements: deposits, variable final amounts, and potential post-rental charges.

## Recommended Payment Flow

```
1. Booking: Pre-authorize estimated rental cost + deposit
2. Pickup: Verify card, optionally increase authorization
3. Return: Capture actual rental amount
4. Post-rental: MIT for damages, fuel, tolls, fines
```

## Key Features to Implement

### Pre-Authorization (30-day hold)
Use `authorizationMode: "PRE_AUTHORIZATION"` to block funds for up to 30 days.

```javascript
const response = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 50000, currencyCode: "EUR" }, // €500 deposit
    customer: { merchantCustomerId: "rental-123" }
  },
  cardPaymentMethodSpecificInput: {
    authorizationMode: "PRE_AUTHORIZATION",
    card: { ... }
  }
});
```

### Partial Capture
Capture less than the authorized amount when the actual rental cost is lower.

```javascript
await client.payments.capturePayment(merchantId, paymentId, {
  amount: 35000, // €350 actual rental cost
  isFinal: true
});
```

### Card-on-File for Post-Rental Charges
Store the card token for potential damage charges, fuel fees, or traffic fines.

```javascript
// Store token during initial transaction
const token = response.payment.paymentOutput.cardPaymentMethodSpecificOutput.token;

// Later: Charge for damages (MIT - Merchant Initiated)
await client.payments.createPayment(merchantId, {
  order: { amountOfMoney: { amount: 15000, currencyCode: "EUR" } },
  cardPaymentMethodSpecificInput: {
    token: token,
    unscheduledCardOnFileRequestor: "merchantInitiated",
    unscheduledCardOnFileSequenceIndicator: "subsequent"
  }
});
```

### No-Show Fees
Charge customers who don't pick up their reservation using MIT.

```javascript
await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 5000, currencyCode: "EUR" },
    references: { merchantReference: "noshow-booking-456" }
  },
  cardPaymentMethodSpecificInput: {
    token: storedToken,
    unscheduledCardOnFileRequestor: "merchantInitiated"
  }
});
```

## Complete Flow Example

```javascript
// 1. At booking - Pre-authorize deposit
const booking = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 100000, currencyCode: "EUR" }, // €1000
    references: { merchantReference: `booking-${bookingId}` }
  },
  cardPaymentMethodSpecificInput: {
    authorizationMode: "PRE_AUTHORIZATION",
    card: cardDetails,
    // Store for future charges
    tokenize: true
  }
});

const paymentId = booking.payment.id;
const token = booking.payment.paymentOutput.cardPaymentMethodSpecificOutput.token;

// 2. At return - Capture actual amount
await client.payments.capturePayment(merchantId, paymentId, {
  amount: 75000, // €750 actual rental
  isFinal: false // Keep open for potential extras
});

// 3. Post-rental - Additional capture for fuel
await client.payments.capturePayment(merchantId, paymentId, {
  amount: 5000, // €50 fuel charge
  isFinal: true
});

// 4. Much later - Damage charge via MIT
await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 20000, currencyCode: "EUR" },
    references: { merchantReference: `damage-${bookingId}` }
  },
  cardPaymentMethodSpecificInput: {
    token: token,
    unscheduledCardOnFileRequestor: "merchantInitiated",
    unscheduledCardOnFileSequenceIndicator: "subsequent"
  }
});
```

## Best Practices

1. **Always pre-authorize** - Never do direct sale for rentals
2. **Store tokens** - Required for post-rental charges
3. **Use meaningful references** - Include booking ID in merchantReference
4. **Partial captures** - Never capture more than authorized
5. **Document MIT usage** - Keep records of why charges were made
6. **Communicate clearly** - Inform customers about deposit and potential charges

## Status Codes to Handle

| Status | Meaning | Action |
|--------|---------|--------|
| PENDING_CAPTURE | Authorization successful | Ready for capture |
| CAPTURED | Funds collected | Complete |
| CANCELLED | Authorization voided | No charge possible |
| AUTHORIZATION_REQUESTED | Processing | Wait and check status |

## Common Issues

### Authorization Expired
Pre-authorizations expire after 30 days. For longer rentals, capture and re-authorize.

### Insufficient Funds on Return
Capture what's available, then use MIT for the remainder with a new authorization.

### Card Declined for MIT
Contact customer for new payment method - MIT charges can fail if card was cancelled.
