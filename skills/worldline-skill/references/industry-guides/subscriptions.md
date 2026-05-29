# Subscription & Recurring Payment Integration

SaaS, memberships, streaming services, and any business with scheduled billing.

## Recommended Payment Flow

```
1. Initial signup: Customer-initiated payment with tokenization
2. Store token: Save for future automated charges
3. Recurring: Merchant-initiated fixed recurring payments
4. Failures: Retry logic with customer notification
```

## Key Concepts

### CIT vs MIT
- **CIT (Customer Initiated)**: Customer is present (signup, upgrade)
- **MIT (Merchant Initiated)**: Scheduled charges, no customer present

### Fixed vs Variable Recurring
- **Fixed**: Same amount, same interval (e.g., €9.99/month)
- **Variable**: Amount varies (usage-based billing)

## Initial Signup (CIT)

First payment with the customer present.

```javascript
const signup = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 999, currencyCode: "EUR" }, // €9.99/month
    customer: { merchantCustomerId: `user-${userId}` },
    references: { merchantReference: `sub-${subscriptionId}-initial` }
  },
  cardPaymentMethodSpecificInput: {
    authorizationMode: "SALE",
    card: cardDetails,
    tokenize: true, // Store for recurring
    threeDSecure: {
      challengeIndicator: "challenge-requested", // Ensure 3DS for first payment
      redirectionData: { returnUrl: "https://app.example.com/subscribe/complete" }
    }
  }
});

// Store token for future billing
const token = signup.payment.paymentOutput.cardPaymentMethodSpecificOutput.token;
await database.saveSubscription(userId, subscriptionId, token);
```

## Fixed Recurring (MIT)

Scheduled billing - same amount each period.

```javascript
async function chargeSubscription(subscription) {
  const payment = await client.payments.createPayment(merchantId, {
    order: {
      amountOfMoney: { amount: 999, currencyCode: "EUR" },
      customer: { merchantCustomerId: subscription.userId },
      references: {
        merchantReference: `sub-${subscription.id}-${Date.now()}`
      }
    },
    cardPaymentMethodSpecificInput: {
      token: subscription.token,
      unscheduledCardOnFileRequestor: "merchantInitiated",
      unscheduledCardOnFileSequenceIndicator: "subsequent",
      recurringPaymentSequenceIndicator: "recurring" // Fixed recurring
    }
  });

  return payment;
}
```

## Variable Recurring (Usage-based)

Amount varies based on usage.

```javascript
async function chargeUsage(subscription, usageAmount) {
  const payment = await client.payments.createPayment(merchantId, {
    order: {
      amountOfMoney: { amount: usageAmount, currencyCode: "EUR" },
      references: { merchantReference: `usage-${subscription.id}-${period}` }
    },
    cardPaymentMethodSpecificInput: {
      token: subscription.token,
      unscheduledCardOnFileRequestor: "merchantInitiated",
      unscheduledCardOnFileSequenceIndicator: "subsequent"
      // Note: No recurringPaymentSequenceIndicator for variable amounts
    }
  });

  return payment;
}
```

## Plan Changes

### Upgrade (Proration)
```javascript
// Customer upgrades mid-cycle - charge difference
const prorationAmount = calculateProration(oldPlan, newPlan, daysRemaining);

const upgrade = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: prorationAmount, currencyCode: "EUR" },
    references: { merchantReference: `upgrade-${subscriptionId}` }
  },
  cardPaymentMethodSpecificInput: {
    token: subscription.token,
    unscheduledCardOnFileRequestor: "cardholderInitiated", // Customer initiated upgrade
    unscheduledCardOnFileSequenceIndicator: "subsequent"
  }
});
```

### Downgrade
No charge - just update the subscription in your system.

### Update Payment Method
```javascript
// New card from customer
const update = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 0, currencyCode: "EUR" }, // Zero-amount for validation
    references: { merchantReference: `update-card-${subscriptionId}` }
  },
  cardPaymentMethodSpecificInput: {
    card: newCardDetails,
    tokenize: true
  }
});

// Replace stored token
const newToken = update.payment.paymentOutput.cardPaymentMethodSpecificOutput.token;
await database.updateSubscriptionToken(subscriptionId, newToken);
```

## Retry Logic for Failed Payments

```javascript
const RETRY_SCHEDULE = [
  { delay: 0, hours: 0 },      // Immediate
  { delay: 3, hours: 72 },     // 3 days later
  { delay: 7, hours: 168 },    // 7 days later
  { delay: 14, hours: 336 }    // 14 days later
];

async function processRecurringWithRetry(subscription, attempt = 0) {
  try {
    const payment = await chargeSubscription(subscription);

    if (payment.payment.status === "CAPTURED") {
      await updateSubscriptionStatus(subscription.id, "active");
      return { success: true };
    }

    if (payment.payment.status === "REJECTED") {
      return handleFailure(subscription, attempt);
    }
  } catch (error) {
    return handleFailure(subscription, attempt);
  }
}

async function handleFailure(subscription, attempt) {
  if (attempt < RETRY_SCHEDULE.length - 1) {
    // Schedule retry
    await scheduleRetry(subscription, RETRY_SCHEDULE[attempt + 1].delay);
    await notifyCustomer(subscription, "payment_failed", RETRY_SCHEDULE[attempt + 1]);
    return { success: false, willRetry: true };
  } else {
    // Final failure - cancel subscription
    await cancelSubscription(subscription.id);
    await notifyCustomer(subscription, "subscription_cancelled");
    return { success: false, willRetry: false };
  }
}
```

## Cancellation Flow

```javascript
async function cancelSubscription(subscriptionId) {
  const subscription = await database.getSubscription(subscriptionId);

  // If there's an active authorization, cancel it
  if (subscription.pendingPaymentId) {
    await client.payments.cancelPayment(merchantId, subscription.pendingPaymentId);
  }

  // Mark subscription as cancelled (access until period end)
  await database.updateSubscription(subscriptionId, {
    status: "cancelled",
    cancelsAt: subscription.currentPeriodEnd
  });
}
```

## Webhooks for Subscription Events

Listen for payment status changes.

```javascript
app.post("/webhooks/worldline", async (req, res) => {
  const event = req.body;

  if (event.payment) {
    const { id, status } = event.payment;
    const merchantRef = event.payment.paymentOutput.references.merchantReference;

    if (merchantRef.startsWith("sub-")) {
      const subscriptionId = extractSubscriptionId(merchantRef);

      switch (status) {
        case "CAPTURED":
          await activateSubscription(subscriptionId);
          break;
        case "REJECTED":
        case "CANCELLED":
          await handlePaymentFailure(subscriptionId);
          break;
      }
    }
  }

  res.status(200).send("OK");
});
```

## Best Practices

1. **Always use 3DS on first payment** - Required for EU SCA
2. **Store tokens securely** - Encrypted in database
3. **Implement retry logic** - Cards fail for many reasons
4. **Notify customers** - Before charges and on failures
5. **Grace periods** - Don't immediately cancel on first failure
6. **Unique merchant references** - Include timestamp for each charge
7. **Track subscription state** - Active, past_due, cancelled

## Dunning Strategy

| Day | Action |
|-----|--------|
| 0 | Initial charge attempt |
| 1 | Email: "Payment failed, retrying in 3 days" |
| 3 | Retry #1 |
| 4 | Email: "Still failing, please update card" |
| 7 | Retry #2, downgrade to limited access |
| 14 | Final retry |
| 15 | Cancel subscription, final email |

## SEPA Direct Debit for Subscriptions

Popular in Germany, Austria, Netherlands.

```javascript
// Setup mandate
const mandate = await client.payments.createPayment(merchantId, {
  order: { amountOfMoney: { amount: 0, currencyCode: "EUR" } },
  sepaDirectDebitPaymentMethodSpecificInput: {
    paymentProduct771SpecificInput: {
      mandate: {
        customerContractIdentifier: subscriptionId,
        recurrenceType: "RECURRING",
        signatureType: "SMS"
      }
    }
  }
});

// Recurring charges use the mandate
```
