# Card-on-File (Tokenization)

Store cards securely for future charges. Worldline returns a token that represents the card without exposing sensitive data.

## Token Types

| Type | Description | Use Case |
|------|-------------|----------|
| **CIT** | Customer Initiated Transaction | One-click checkout, customer present |
| **MIT** | Merchant Initiated Transaction | Subscriptions, no-shows, delayed charges |

## Creating a Token

### During Payment

```javascript
const payment = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 4999, currencyCode: "EUR" },
    customer: { merchantCustomerId: customerId }
  },
  cardPaymentMethodSpecificInput: {
    authorizationMode: "SALE",
    card: cardDetails,
    tokenize: true // Request token
  }
});

// Extract token from response
const token = payment.payment.paymentOutput
  .cardPaymentMethodSpecificOutput.token;

// Store token with customer profile
await database.saveCustomerToken(customerId, token);
```

### Zero-Amount Authorization (Card Verification)

```javascript
// Verify card without charging
const verification = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 0, currencyCode: "EUR" },
    customer: { merchantCustomerId: customerId }
  },
  cardPaymentMethodSpecificInput: {
    card: cardDetails,
    tokenize: true
  }
});

const token = verification.payment.paymentOutput
  .cardPaymentMethodSpecificOutput.token;
```

### Via Hosted Checkout

```javascript
const checkout = await client.hostedCheckout.createHostedCheckout(merchantId, {
  order: { amountOfMoney: { amount: 4999, currencyCode: "EUR" } },
  hostedCheckoutSpecificInput: {
    returnUrl: "https://...",
    cardPaymentMethodSpecificInput: {
      tokenize: true
    }
  }
});

// After completion, get token from status
const status = await client.hostedCheckout.getHostedCheckoutStatus(
  merchantId,
  hostedCheckoutId
);
const token = status.createdPaymentOutput.payment.paymentOutput
  .cardPaymentMethodSpecificOutput.token;
```

## Using a Token

### Customer Initiated (CIT)

Customer is present and initiates the transaction.

```javascript
// One-click checkout
const payment = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 2999, currencyCode: "EUR" },
    references: { merchantReference: orderId }
  },
  cardPaymentMethodSpecificInput: {
    token: storedToken,
    authorizationMode: "SALE",
    unscheduledCardOnFileRequestor: "cardholderInitiated",
    unscheduledCardOnFileSequenceIndicator: "subsequent",
    threeDSecure: {
      // 3DS may be required even with token
      skipAuthentication: false,
      redirectionData: {
        returnUrl: `https://yoursite.com/3ds/complete?orderId=${orderId}`
      }
    }
  }
});
```

### Merchant Initiated (MIT)

No customer present. You charge the stored card.

```javascript
// Delayed charge (e.g., damage fee, no-show)
const payment = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 5000, currencyCode: "EUR" },
    references: { merchantReference: `noshow-${bookingId}` }
  },
  cardPaymentMethodSpecificInput: {
    token: storedToken,
    authorizationMode: "SALE",
    unscheduledCardOnFileRequestor: "merchantInitiated",
    unscheduledCardOnFileSequenceIndicator: "subsequent"
  }
});
```

## Recurring Payments

### First Payment (Initial)

```javascript
const initial = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 999, currencyCode: "EUR" },
    customer: { merchantCustomerId: userId }
  },
  cardPaymentMethodSpecificInput: {
    authorizationMode: "SALE",
    card: cardDetails,
    tokenize: true,
    threeDSecure: {
      challengeIndicator: "challenge-requested" // Force 3DS on first
    }
  }
});

const token = initial.payment.paymentOutput
  .cardPaymentMethodSpecificOutput.token;
```

### Subsequent Payments

```javascript
// Fixed recurring (same amount, same interval)
const recurring = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 999, currencyCode: "EUR" },
    references: { merchantReference: `sub-${subscriptionId}-${period}` }
  },
  cardPaymentMethodSpecificInput: {
    token: token,
    authorizationMode: "SALE",
    unscheduledCardOnFileRequestor: "merchantInitiated",
    unscheduledCardOnFileSequenceIndicator: "subsequent",
    recurringPaymentSequenceIndicator: "recurring"
  }
});
```

### Variable Recurring

```javascript
// Usage-based billing (amount varies)
const usage = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: usageAmount, currencyCode: "EUR" },
    references: { merchantReference: `usage-${userId}-${period}` }
  },
  cardPaymentMethodSpecificInput: {
    token: token,
    authorizationMode: "SALE",
    unscheduledCardOnFileRequestor: "merchantInitiated",
    unscheduledCardOnFileSequenceIndicator: "subsequent"
    // No recurringPaymentSequenceIndicator for variable amounts
  }
});
```

## Token Management

### Get Token Details

```javascript
const tokenInfo = await client.tokens.getToken(merchantId, tokenId);

console.log({
  card: tokenInfo.card,
  paymentProductId: tokenInfo.paymentProductId,
  isTemporary: tokenInfo.isTemporary
});
```

### Delete Token

```javascript
await client.tokens.deleteToken(merchantId, tokenId);
```

### Update Token (New Card)

```javascript
// Customer provides new card
const update = await client.payments.createPayment(merchantId, {
  order: { amountOfMoney: { amount: 0, currencyCode: "EUR" } },
  cardPaymentMethodSpecificInput: {
    card: newCardDetails,
    tokenize: true
  }
});

const newToken = update.payment.paymentOutput
  .cardPaymentMethodSpecificOutput.token;

// Replace in database
await database.updateCustomerToken(customerId, oldToken, newToken);
```

## Network Tokenization

Enhanced security using card network tokens (Visa Token Service, Mastercard MDES).

```javascript
const payment = await client.payments.createPayment(merchantId, {
  order: { amountOfMoney: { amount: 4999, currencyCode: "EUR" } },
  cardPaymentMethodSpecificInput: {
    token: storedToken,
    // Network tokenization happens automatically if enabled
    // in your merchant configuration
  }
});
```

Benefits:
- Higher approval rates
- Automatic card updates (when reissued)
- Enhanced security

## Use Cases Summary

| Scenario | Requestor | Sequence | Example |
|----------|-----------|----------|---------|
| First purchase | cardholderInitiated | first | Initial signup |
| One-click reorder | cardholderInitiated | subsequent | Customer clicks "buy again" |
| Subscription | merchantInitiated | subsequent + recurring | Monthly charge |
| Usage billing | merchantInitiated | subsequent | Metered billing |
| No-show fee | merchantInitiated | subsequent | Hotel no-show |
| Damage charge | merchantInitiated | subsequent | Car rental damage |

## 3DS with Tokens

### When 3DS is Required
- First CIT transaction (initial)
- High-risk CIT transactions
- Issuer requests step-up

### When 3DS Can Be Skipped
- MIT transactions (no customer present)
- Low-risk transactions (TRA exemption)

```javascript
// MIT - No 3DS needed
cardPaymentMethodSpecificInput: {
  token: token,
  unscheduledCardOnFileRequestor: "merchantInitiated",
  // 3DS not applied for MIT
}

// CIT - 3DS may be required
cardPaymentMethodSpecificInput: {
  token: token,
  unscheduledCardOnFileRequestor: "cardholderInitiated",
  threeDSecure: {
    redirectionData: {
      returnUrl: "https://..."
    }
  }
}
```

## Best Practices

1. **Always get consent** - Document customer agreement to store card
2. **First payment with 3DS** - Ensures liability shift for recurring
3. **Unique references** - Include period/timestamp in MIT references
4. **Handle failures** - Cards expire, get cancelled
5. **Provide management UI** - Let customers view/delete cards
6. **Secure storage** - Encrypt token in database
7. **Regular cleanup** - Remove unused tokens

## Error Handling

```javascript
try {
  const payment = await chargeWithToken(token, amount);
} catch (error) {
  if (error.statusCode === 402) {
    // Payment declined
    await handleDecline(customerId, error);
  } else if (error.body?.errorId === "INVALID_TOKEN") {
    // Token expired or deleted
    await requestNewPaymentMethod(customerId);
  }
}
```

## Compliance Notes

- **PCI DSS**: Tokens are not card data, lower scope
- **PSD2/SCA**: First CIT requires 3DS, MIT is exempt
- **GDPR**: Include in data deletion requests
