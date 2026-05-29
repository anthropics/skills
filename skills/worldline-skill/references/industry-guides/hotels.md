# Hotel & Lodging Payment Integration

Hotels need flexible payment handling for reservations, check-in deposits, and variable charges.

## Recommended Payment Flow

```
1. Booking: Pre-authorize room rate or store card
2. Check-in: Verify card, pre-auth for incidentals
3. During stay: Track minibar, room service, spa
4. Check-out: Capture total amount
5. Post-checkout: MIT for damages, missing items
```

## Key Features to Implement

### Pre-Authorization at Booking
Hold funds for the reservation period.

```javascript
const booking = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 30000, currencyCode: "EUR" }, // €300/night
    references: { merchantReference: `reservation-${confirmationNumber}` }
  },
  cardPaymentMethodSpecificInput: {
    authorizationMode: "PRE_AUTHORIZATION",
    card: cardDetails,
    tokenize: true // Store for extras
  }
});
```

### Incidentals Authorization at Check-in
Additional hold for potential extras.

```javascript
const incidentalAuth = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 20000, currencyCode: "EUR" }, // €200 incidentals
    references: { merchantReference: `incidentals-${confirmationNumber}` }
  },
  cardPaymentMethodSpecificInput: {
    authorizationMode: "PRE_AUTHORIZATION",
    token: storedToken,
    unscheduledCardOnFileRequestor: "cardholderInitiated"
  }
});
```

### Variable Capture at Checkout
Capture the actual stay amount plus extras.

```javascript
// Capture room charges
await client.payments.capturePayment(merchantId, roomPaymentId, {
  amount: 90000, // €900 for 3 nights
  isFinal: true
});

// Capture incidentals (minibar, etc.)
await client.payments.capturePayment(merchantId, incidentalsPaymentId, {
  amount: 4500, // €45 minibar
  isFinal: true
});
```

### No-Show Charges
Charge for no-shows using MIT.

```javascript
await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 30000, currencyCode: "EUR" }, // 1 night penalty
    references: { merchantReference: `noshow-${confirmationNumber}` }
  },
  cardPaymentMethodSpecificInput: {
    token: storedToken,
    unscheduledCardOnFileRequestor: "merchantInitiated",
    unscheduledCardOnFileSequenceIndicator: "subsequent"
  }
});
```

## Complete Flow Example

```javascript
// 1. Booking - Store card and optionally pre-authorize
const reservation = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 15000, currencyCode: "EUR" }, // 1 night deposit
    customer: { merchantCustomerId: `guest-${guestId}` },
    references: { merchantReference: `booking-${confirmationNumber}` }
  },
  cardPaymentMethodSpecificInput: {
    authorizationMode: "PRE_AUTHORIZATION",
    card: cardDetails,
    tokenize: true
  }
});

const token = reservation.payment.paymentOutput.cardPaymentMethodSpecificOutput.token;

// 2. Check-in - Pre-auth for full stay + incidentals
const stayAuth = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 65000, currencyCode: "EUR" }, // Stay + extras
    references: { merchantReference: `stay-${confirmationNumber}` }
  },
  cardPaymentMethodSpecificInput: {
    authorizationMode: "PRE_AUTHORIZATION",
    token: token,
    unscheduledCardOnFileRequestor: "cardholderInitiated"
  }
});

// Cancel booking pre-auth (we have new one)
await client.payments.cancelPayment(merchantId, reservation.payment.id);

// 3. Check-out - Capture actual charges
await client.payments.capturePayment(merchantId, stayAuth.payment.id, {
  amount: 48500, // €485 actual charges
  isFinal: true
});

// 4. Post-checkout - Damage discovered
await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 15000, currencyCode: "EUR" },
    references: { merchantReference: `damage-${confirmationNumber}` }
  },
  cardPaymentMethodSpecificInput: {
    token: token,
    unscheduledCardOnFileRequestor: "merchantInitiated"
  }
});
```

## Cancellation Policies

### Free Cancellation
Simply cancel the pre-authorization.

```javascript
await client.payments.cancelPayment(merchantId, paymentId);
```

### Partial Refund for Late Cancellation
If already captured, issue partial refund.

```javascript
await client.payments.refundPayment(merchantId, paymentId, {
  amountOfMoney: { amount: 15000, currencyCode: "EUR" } // Refund all but 1 night
});
```

## Best Practices

1. **Tokenize at booking** - Store card for all future charges
2. **Use meaningful references** - Include confirmation number
3. **Pre-auth at check-in** - New auth for actual stay
4. **Track extras in real-time** - PMS integration
5. **Clear folio at checkout** - Single capture preferred
6. **Document all MIT charges** - Keep dispute evidence

## Payment Methods by Market

| Region | Popular Methods |
|--------|-----------------|
| Netherlands | iDEAL, Cards |
| Germany | SEPA, Cards, Klarna |
| France | Cartes Bancaires, Cards |
| UK | Cards, Apple Pay |
| Switzerland | TWINT, Cards |

## Common Issues

### Guest Wants to Change Card at Checkout
Create new authorization with new card, then capture. Cancel old auth.

### Multiple Rooms Under One Booking
Either: Single auth for total, or separate auth per room with shared token.

### Extended Stay
For stays over 30 days, capture periodically (weekly) and re-authorize.
