# Test Cards

Test card numbers for the sandbox environment.

## Visa Test Cards

| Card Number | Behavior |
|-------------|----------|
| 4111111111111111 | Success |
| 4012001038443335 | Success (different BIN) |
| 4000000000000002 | Declined - Insufficient funds |
| 4000000000000069 | Declined - Card expired |
| 4000000000000119 | Declined - Generic |
| 4000000000003238 | 3DS Challenge required |

## Mastercard Test Cards

| Card Number | Behavior |
|-------------|----------|
| 5399999999999999 | Success |
| 5137009801943438 | Success (alternate) |
| 5424000000000015 | Success |
| 5200000000000007 | Declined |
| 5200000000003238 | 3DS Challenge required |

## American Express

| Card Number | Behavior |
|-------------|----------|
| 374111111111111 | Success |
| 340000000000009 | Success |
| 340000000003238 | 3DS Challenge required |

## Other Cards

| Network | Card Number | Behavior |
|---------|-------------|----------|
| Maestro | 6759000000000000 | Success |
| JCB | 3530111333300000 | Success |
| Diners | 36006666333344 | Success |
| Discover | 6011000000000004 | Success |

## Common Test Values

```javascript
const testCard = {
  cardNumber: "4111111111111111",
  expiryDate: "1225", // Any future date works (MMYY)
  cvv: "123", // Any 3 digits (4 for Amex)
  cardholderName: "Test Cardholder" // Any name
};
```

## 3D Secure Test Scenarios

### Frictionless (No Challenge)

```javascript
// Most test cards process without challenge in sandbox
const card = {
  cardNumber: "4111111111111111",
  expiryDate: "1225",
  cvv: "123"
};
```

### Challenge Required

```javascript
// Use 3DS challenge card numbers
const card = {
  cardNumber: "4000000000003238", // Forces 3DS challenge
  expiryDate: "1225",
  cvv: "123"
};

// In the 3DS challenge page, use:
// Password: 1234 (or any value in sandbox)
```

### 3DS Authentication Failed

```javascript
// Some issuers in sandbox reject 3DS
// Use specific test cards if available
```

## Testing Different Amounts

Some behaviors are triggered by specific amounts:

| Amount (cents) | Behavior |
|----------------|----------|
| Any | Standard success |
| 1000 | May trigger different flows |

## Testing Capture Scenarios

```javascript
// Pre-authorize €100
const auth = await client.payments.createPayment(merchantId, {
  order: { amountOfMoney: { amount: 10000, currencyCode: "EUR" } },
  cardPaymentMethodSpecificInput: {
    authorizationMode: "PRE_AUTHORIZATION",
    card: testCard
  }
});

// Capture €75 (partial)
await client.payments.capturePayment(merchantId, paymentId, {
  amount: 7500,
  isFinal: false
});

// Capture remaining €25
await client.payments.capturePayment(merchantId, paymentId, {
  amount: 2500,
  isFinal: true
});
```

## Testing Refunds

```javascript
// Create and capture payment
const payment = await createDirectSale(4999);

// Full refund
await client.payments.refundPayment(merchantId, paymentId, {
  amountOfMoney: { amount: 4999, currencyCode: "EUR" }
});

// Or partial refund
await client.payments.refundPayment(merchantId, paymentId, {
  amountOfMoney: { amount: 2000, currencyCode: "EUR" }
});
```

## Testing Cancellations

```javascript
// Create authorization
const auth = await createPreAuth(10000);

// Cancel before capture
await client.payments.cancelPayment(merchantId, paymentId);
```

## Testing Webhooks

1. Create a payment in sandbox
2. Wait for webhook notification
3. Verify signature
4. Process the event

```javascript
// ngrok for local testing
// ngrok http 3000

// Set webhook URL in Merchant Portal
// https://your-ngrok-url.ngrok.io/webhooks/worldline
```

## Testing iDEAL

```javascript
const payment = await client.payments.createPayment(merchantId, {
  order: { amountOfMoney: { amount: 4999, currencyCode: "EUR" } },
  redirectPaymentMethodSpecificInput: {
    paymentProductId: 809,
    returnUrl: "https://yoursite.com/return"
  }
});

// Redirect to the test bank page
// In sandbox, you can choose success/failure
```

## Testing PayPal

```javascript
// PayPal sandbox requires:
// 1. PayPal Developer account
// 2. Sandbox buyer account
// 3. Link sandbox in Merchant Portal
```

## Sandbox Environment

| Resource | URL |
|----------|-----|
| API Host | `payment.preprod.direct.worldline-solutions.com` |
| Merchant Portal | `merchant-portal.preprod.direct.worldline-solutions.com` |

## Best Practices

1. **Test all scenarios** - Success, decline, 3DS, errors
2. **Test edge cases** - Partial captures, multiple refunds
3. **Test webhooks** - Don't rely only on redirects
4. **Document test cases** - Keep a checklist
5. **Test on production** - Small amounts after go-live

## Switching to Production

```javascript
// Change host to production
const client = OnlinePayments.init({
  host: "payment.direct.worldline-solutions.com", // Production
  apiKeyId: process.env.WORLDLINE_API_KEY_PROD,
  secretApiKey: process.env.WORLDLINE_SECRET_KEY_PROD
});
```

## Troubleshooting

### Payment Always Declined
- Check you're using sandbox credentials
- Verify API key is for preprod environment
- Use known working test card

### 3DS Not Working
- Ensure returnUrl is set
- Check redirect handling
- Use 3DS-specific test cards

### Webhook Not Received
- Verify URL is publicly accessible
- Check webhook configuration in portal
- Look at webhook logs in Merchant Portal
