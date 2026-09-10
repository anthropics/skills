# Recurring Payments

Automated billing for subscriptions, memberships, and installments.

## Types of Recurring

| Type | Amount | Interval | Example |
|------|--------|----------|---------|
| **Fixed** | Same | Same | €9.99/month subscription |
| **Variable** | Varies | Same | Usage-based monthly billing |
| **Installments** | Fixed | Fixed | 4 payments of €25 |

## Initial Setup (First Payment)

The first payment establishes the recurring relationship.

```javascript
async function setupRecurring(customer, plan) {
  const payment = await client.payments.createPayment(merchantId, {
    order: {
      amountOfMoney: {
        amount: plan.amountCents,
        currencyCode: plan.currency
      },
      customer: {
        merchantCustomerId: customer.id,
        contactDetails: { emailAddress: customer.email }
      },
      references: {
        merchantReference: `sub-${subscription.id}-initial`
      }
    },
    cardPaymentMethodSpecificInput: {
      authorizationMode: "SALE",
      card: {
        cardNumber: customer.cardNumber,
        expiryDate: customer.expiryDate,
        cvv: customer.cvv,
        cardholderName: customer.name
      },
      tokenize: true, // Essential for recurring
      threeDSecure: {
        challengeIndicator: "challenge-requested", // Force 3DS
        redirectionData: {
          returnUrl: `https://app.example.com/subscribe/complete?subId=${subscription.id}`
        }
      }
    }
  });

  // Handle 3DS redirect if needed
  if (payment.merchantAction?.actionType === "REDIRECT") {
    return {
      requires3DS: true,
      redirectUrl: payment.merchantAction.redirectData.redirectURL
    };
  }

  // Store token for future charges
  const token = payment.payment.paymentOutput
    .cardPaymentMethodSpecificOutput.token;

  await database.saveSubscription({
    id: subscription.id,
    customerId: customer.id,
    token: token,
    planId: plan.id,
    status: "active",
    currentPeriodEnd: calculatePeriodEnd(plan.interval)
  });

  return { success: true };
}
```

## Fixed Recurring Charges

Same amount on a regular schedule.

```javascript
async function chargeSubscription(subscription) {
  const plan = await database.getPlan(subscription.planId);

  const payment = await client.payments.createPayment(merchantId, {
    order: {
      amountOfMoney: {
        amount: plan.amountCents,
        currencyCode: plan.currency
      },
      customer: { merchantCustomerId: subscription.customerId },
      references: {
        merchantReference: `sub-${subscription.id}-${Date.now()}`
      }
    },
    cardPaymentMethodSpecificInput: {
      token: subscription.token,
      authorizationMode: "SALE",
      unscheduledCardOnFileRequestor: "merchantInitiated",
      unscheduledCardOnFileSequenceIndicator: "subsequent",
      recurringPaymentSequenceIndicator: "recurring"
    }
  });

  if (payment.payment.status === "CAPTURED") {
    await database.recordPayment(subscription.id, payment.payment.id);
    await database.extendSubscription(subscription.id);
    return { success: true };
  }

  return { success: false, status: payment.payment.status };
}
```

## Variable Recurring (Usage-Based)

Amount changes each billing period.

```javascript
async function chargeUsage(subscription, usageAmountCents) {
  const payment = await client.payments.createPayment(merchantId, {
    order: {
      amountOfMoney: {
        amount: usageAmountCents,
        currencyCode: "EUR"
      },
      references: {
        merchantReference: `usage-${subscription.id}-${billingPeriod}`
      }
    },
    cardPaymentMethodSpecificInput: {
      token: subscription.token,
      authorizationMode: "SALE",
      unscheduledCardOnFileRequestor: "merchantInitiated",
      unscheduledCardOnFileSequenceIndicator: "subsequent"
      // Note: No recurringPaymentSequenceIndicator for variable
    }
  });

  return payment;
}
```

## Installment Payments

Fixed number of payments over time.

```javascript
async function setupInstallments(order, installmentCount) {
  const installmentAmount = Math.ceil(order.total / installmentCount);

  // First payment
  const firstPayment = await client.payments.createPayment(merchantId, {
    order: {
      amountOfMoney: { amount: installmentAmount, currencyCode: "EUR" },
      references: { merchantReference: `order-${order.id}-inst-1of${installmentCount}` }
    },
    cardPaymentMethodSpecificInput: {
      authorizationMode: "SALE",
      card: cardDetails,
      tokenize: true,
      threeDSecure: { /* ... */ }
    }
  });

  // Store for future installments
  const token = firstPayment.payment.paymentOutput
    .cardPaymentMethodSpecificOutput.token;

  await database.createInstallmentPlan({
    orderId: order.id,
    token: token,
    totalInstallments: installmentCount,
    completedInstallments: 1,
    installmentAmount: installmentAmount,
    nextChargeDate: addMonths(new Date(), 1)
  });

  return firstPayment;
}

// Scheduled job for subsequent installments
async function processInstallment(plan) {
  if (plan.completedInstallments >= plan.totalInstallments) {
    return; // All installments complete
  }

  const payment = await client.payments.createPayment(merchantId, {
    order: {
      amountOfMoney: { amount: plan.installmentAmount, currencyCode: "EUR" },
      references: {
        merchantReference: `order-${plan.orderId}-inst-${plan.completedInstallments + 1}of${plan.totalInstallments}`
      }
    },
    cardPaymentMethodSpecificInput: {
      token: plan.token,
      authorizationMode: "SALE",
      unscheduledCardOnFileRequestor: "merchantInitiated",
      unscheduledCardOnFileSequenceIndicator: "subsequent",
      recurringPaymentSequenceIndicator: "recurring"
    }
  });

  if (payment.payment.status === "CAPTURED") {
    await database.updateInstallmentPlan(plan.id, {
      completedInstallments: plan.completedInstallments + 1,
      nextChargeDate: addMonths(new Date(), 1)
    });
  }
}
```

## Retry Logic

Handle failed payments gracefully.

```javascript
const RETRY_DELAYS = [0, 3, 7, 14]; // Days

async function processWithRetry(subscription, attempt = 0) {
  try {
    const result = await chargeSubscription(subscription);

    if (result.success) {
      await resetRetryCount(subscription.id);
      return { success: true };
    }

    // Payment failed
    return await handleFailure(subscription, attempt);
  } catch (error) {
    return await handleFailure(subscription, attempt);
  }
}

async function handleFailure(subscription, attempt) {
  if (attempt >= RETRY_DELAYS.length - 1) {
    // All retries exhausted
    await cancelSubscription(subscription.id, "payment_failed");
    await sendEmail(subscription.customerId, "subscription_cancelled");
    return { success: false, cancelled: true };
  }

  // Schedule retry
  const nextRetryDays = RETRY_DELAYS[attempt + 1];
  await scheduleRetry(subscription.id, nextRetryDays);
  await sendEmail(subscription.customerId, "payment_failed_will_retry", {
    retryDate: addDays(new Date(), nextRetryDays)
  });

  return { success: false, willRetry: true, retryIn: nextRetryDays };
}
```

## Plan Changes

### Upgrade (Immediate)

```javascript
async function upgradeSubscription(subscriptionId, newPlanId) {
  const subscription = await database.getSubscription(subscriptionId);
  const oldPlan = await database.getPlan(subscription.planId);
  const newPlan = await database.getPlan(newPlanId);

  // Calculate proration
  const daysRemaining = daysBetween(new Date(), subscription.currentPeriodEnd);
  const daysInPeriod = daysBetween(subscription.currentPeriodStart, subscription.currentPeriodEnd);
  const unusedCredit = (oldPlan.amountCents / daysInPeriod) * daysRemaining;
  const newCharge = (newPlan.amountCents / daysInPeriod) * daysRemaining;
  const prorationAmount = Math.max(0, newCharge - unusedCredit);

  if (prorationAmount > 0) {
    // Charge difference
    await client.payments.createPayment(merchantId, {
      order: {
        amountOfMoney: { amount: prorationAmount, currencyCode: "EUR" },
        references: { merchantReference: `upgrade-${subscriptionId}` }
      },
      cardPaymentMethodSpecificInput: {
        token: subscription.token,
        unscheduledCardOnFileRequestor: "cardholderInitiated", // Customer-initiated upgrade
        unscheduledCardOnFileSequenceIndicator: "subsequent"
      }
    });
  }

  await database.updateSubscription(subscriptionId, { planId: newPlanId });
}
```

### Downgrade (End of Period)

```javascript
async function downgradeSubscription(subscriptionId, newPlanId) {
  await database.updateSubscription(subscriptionId, {
    scheduledPlanChange: {
      newPlanId: newPlanId,
      effectiveDate: subscription.currentPeriodEnd
    }
  });
}
```

## Update Payment Method

```javascript
async function updatePaymentMethod(subscriptionId, newCardDetails) {
  const subscription = await database.getSubscription(subscriptionId);

  // Create new token
  const verification = await client.payments.createPayment(merchantId, {
    order: { amountOfMoney: { amount: 0, currencyCode: "EUR" } },
    cardPaymentMethodSpecificInput: {
      card: newCardDetails,
      tokenize: true,
      threeDSecure: {
        redirectionData: {
          returnUrl: `https://app.example.com/account/payment-updated`
        }
      }
    }
  });

  if (verification.merchantAction?.actionType === "REDIRECT") {
    return {
      requires3DS: true,
      redirectUrl: verification.merchantAction.redirectData.redirectURL
    };
  }

  const newToken = verification.payment.paymentOutput
    .cardPaymentMethodSpecificOutput.token;

  await database.updateSubscription(subscriptionId, { token: newToken });
  return { success: true };
}
```

## Cancellation

```javascript
async function cancelSubscription(subscriptionId, reason) {
  const subscription = await database.getSubscription(subscriptionId);

  await database.updateSubscription(subscriptionId, {
    status: "cancelled",
    cancelledAt: new Date(),
    cancelReason: reason,
    endsAt: subscription.currentPeriodEnd // Access until end of period
  });

  await sendEmail(subscription.customerId, "subscription_cancelled", {
    endsAt: subscription.currentPeriodEnd
  });
}
```

## Webhooks for Recurring

```javascript
app.post("/webhooks/worldline", async (req, res) => {
  const event = req.body;

  if (event.payment) {
    const ref = event.payment.paymentOutput.references.merchantReference;

    if (ref.startsWith("sub-")) {
      const subscriptionId = ref.split("-")[1];

      switch (event.payment.status) {
        case "CAPTURED":
          await handleSuccessfulCharge(subscriptionId, event.payment.id);
          break;
        case "REJECTED":
          await handleFailedCharge(subscriptionId);
          break;
      }
    }
  }

  res.status(200).send("OK");
});
```

## Best Practices

1. **3DS on first payment** - Required for PSD2 compliance
2. **Notify before charging** - Send reminders
3. **Grace periods** - Don't cancel immediately on failure
4. **Clear merchant references** - Include subscription ID and period
5. **Handle card updates** - Network tokenization helps
6. **Retry logic** - Multiple attempts before cancellation
7. **Audit trail** - Log all charges and failures
