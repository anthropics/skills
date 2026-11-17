# Server-to-Server Integration

Full control over the payment flow with direct API calls. Requires highest PCI compliance (SAQ-D).

## When to Use

- You're already PCI DSS certified
- You need maximum control over the flow
- You're processing Card-on-File with stored tokens
- You're doing MIT (Merchant Initiated Transactions)

## Basic Payment

```javascript
const { default: OnlinePayments } = require("onlinepayments-sdk-nodejs");

const client = OnlinePayments.init({
  host: "payment.preprod.direct.worldline-solutions.com",
  apiKeyId: process.env.WORLDLINE_API_KEY,
  secretApiKey: process.env.WORLDLINE_SECRET_KEY
});

const merchantId = process.env.WORLDLINE_MERCHANT_ID;

async function createPayment(order, cardData) {
  const response = await client.payments.createPayment(merchantId, {
    order: {
      amountOfMoney: {
        amount: order.totalCents,
        currencyCode: "EUR"
      },
      customer: {
        merchantCustomerId: order.customerId,
        billingAddress: {
          street: order.address.street,
          city: order.address.city,
          countryCode: order.address.country,
          zip: order.address.postalCode
        }
      },
      references: {
        merchantReference: order.id
      }
    },
    cardPaymentMethodSpecificInput: {
      authorizationMode: "SALE",
      card: {
        cardNumber: cardData.number,
        expiryDate: cardData.expiry, // MMYY format
        cvv: cardData.cvv,
        cardholderName: cardData.name
      },
      threeDSecure: {
        redirectionData: {
          returnUrl: `https://yoursite.com/3ds/complete?orderId=${order.id}`
        },
        challengeIndicator: "no-preference"
      }
    }
  });

  return response;
}
```

## Handle 3DS Redirect

```javascript
const payment = await createPayment(order, cardData);

if (payment.merchantAction?.actionType === "REDIRECT") {
  // Redirect customer for 3DS authentication
  const redirectUrl = payment.merchantAction.redirectData.redirectURL;
  res.redirect(redirectUrl);
} else if (payment.payment.status === "CAPTURED") {
  // Payment complete (no 3DS required)
  res.redirect(`/order/${order.id}/success`);
} else if (payment.payment.status === "PENDING_CAPTURE") {
  // Authorized, capture later
  res.redirect(`/order/${order.id}/success`);
}
```

## 3DS Return Handler

```javascript
app.get("/3ds/complete", async (req, res) => {
  const { orderId, paymentId, RETURNMAC } = req.query;

  // Get payment status
  const status = await client.payments.getPaymentStatus(merchantId, paymentId);

  if (status.status === "CAPTURED" || status.status === "PENDING_CAPTURE") {
    await markOrderPaid(orderId, paymentId);
    res.redirect(`/order/${orderId}/success`);
  } else {
    res.redirect(`/order/${orderId}/failed`);
  }
});
```

## Authorization Modes

### Direct Sale (Immediate Capture)

```javascript
cardPaymentMethodSpecificInput: {
  authorizationMode: "SALE",
  card: { ... }
}
```

### Pre-Authorization (30-day hold)

```javascript
cardPaymentMethodSpecificInput: {
  authorizationMode: "PRE_AUTHORIZATION",
  card: { ... }
}

// Capture later
await client.payments.capturePayment(merchantId, paymentId, {
  amount: 5000,
  isFinal: true
});
```

### Final Authorization (7-day hold)

```javascript
cardPaymentMethodSpecificInput: {
  authorizationMode: "FINAL_AUTHORIZATION",
  card: { ... }
}
```

## Token-Based Payment

Using a previously stored token.

```javascript
async function chargeWithToken(token, amount, merchantRef) {
  return await client.payments.createPayment(merchantId, {
    order: {
      amountOfMoney: { amount, currencyCode: "EUR" },
      references: { merchantReference: merchantRef }
    },
    cardPaymentMethodSpecificInput: {
      token: token,
      authorizationMode: "SALE",
      unscheduledCardOnFileRequestor: "cardholderInitiated",
      unscheduledCardOnFileSequenceIndicator: "subsequent"
    }
  });
}
```

## Merchant Initiated Transaction (MIT)

```javascript
async function chargeMIT(token, amount, merchantRef) {
  return await client.payments.createPayment(merchantId, {
    order: {
      amountOfMoney: { amount, currencyCode: "EUR" },
      references: { merchantReference: merchantRef }
    },
    cardPaymentMethodSpecificInput: {
      token: token,
      authorizationMode: "SALE",
      unscheduledCardOnFileRequestor: "merchantInitiated",
      unscheduledCardOnFileSequenceIndicator: "subsequent"
    }
  });
}
```

## Recurring Payment

```javascript
async function chargeRecurring(token, amount, merchantRef) {
  return await client.payments.createPayment(merchantId, {
    order: {
      amountOfMoney: { amount, currencyCode: "EUR" },
      references: { merchantReference: merchantRef }
    },
    cardPaymentMethodSpecificInput: {
      token: token,
      authorizationMode: "SALE",
      unscheduledCardOnFileRequestor: "merchantInitiated",
      unscheduledCardOnFileSequenceIndicator: "subsequent",
      recurringPaymentSequenceIndicator: "recurring"
    }
  });
}
```

## Error Handling

```javascript
try {
  const payment = await client.payments.createPayment(merchantId, body);
  return payment;
} catch (error) {
  if (error.statusCode === 400) {
    // Validation error
    const errors = error.body?.errors || [];
    console.error("Validation errors:", errors);
    throw new Error("Invalid payment request");
  }

  if (error.statusCode === 402) {
    // Payment declined
    const errorId = error.body?.errorId;
    console.error("Payment declined:", errorId);
    throw new Error("Payment was declined");
  }

  if (error.statusCode === 409) {
    // Duplicate request (idempotency)
    console.error("Duplicate payment request");
    throw new Error("Payment already processed");
  }

  throw error;
}
```

## Idempotency

Prevent duplicate charges with unique references.

```javascript
const merchantReference = `order-${orderId}-${Date.now()}`;

// If same reference is used twice, second request returns existing payment
```

## Apple Pay via S2S

```javascript
const payment = await client.payments.createPayment(merchantId, {
  order: { amountOfMoney: { amount: 4999, currencyCode: "EUR" } },
  mobilePaymentMethodSpecificInput: {
    paymentProductId: 302, // Apple Pay
    authorizationMode: "SALE",
    encryptedPaymentData: applePayToken, // From Apple Pay JS
    publicKeyHash: "...",
    ephemeralKey: "..."
  }
});
```

## Google Pay via S2S

```javascript
const payment = await client.payments.createPayment(merchantId, {
  order: { amountOfMoney: { amount: 4999, currencyCode: "EUR" } },
  mobilePaymentMethodSpecificInput: {
    paymentProductId: 320, // Google Pay
    authorizationMode: "SALE",
    encryptedPaymentData: googlePayToken
  }
});
```

## Get Payment Details

```javascript
const payment = await client.payments.getPaymentDetails(merchantId, paymentId);

console.log({
  status: payment.status,
  statusOutput: payment.statusOutput,
  amount: payment.paymentOutput.amountOfMoney,
  card: payment.paymentOutput.cardPaymentMethodSpecificOutput
});
```

## Capture Payment

```javascript
// Full capture
await client.payments.capturePayment(merchantId, paymentId, {
  isFinal: true
});

// Partial capture
await client.payments.capturePayment(merchantId, paymentId, {
  amount: 5000, // Less than authorized
  isFinal: false // More captures possible
});
```

## Cancel Payment

```javascript
await client.payments.cancelPayment(merchantId, paymentId);
```

## Refund Payment

```javascript
// Full refund
await client.payments.refundPayment(merchantId, paymentId, {
  amountOfMoney: { amount: 4999, currencyCode: "EUR" }
});

// Partial refund
await client.payments.refundPayment(merchantId, paymentId, {
  amountOfMoney: { amount: 1000, currencyCode: "EUR" }
});
```

## PCI Compliance Notes

Server-to-Server requires:
- PCI DSS Level 1-4 certification (SAQ-D)
- Secure storage of card data
- Network segmentation
- Regular security audits
- Encryption at rest and in transit

**If you're not PCI certified**, use:
- Hosted Checkout (SAQ-A)
- Hosted Tokenization (SAQ-A-EP)
- Mobile SDKs (SAQ-A)
