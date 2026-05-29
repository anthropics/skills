/**
 * Worldline Direct - Recurring Payment Example
 *
 * This example shows how to implement subscription billing
 * with retry logic for failed payments.
 */

const { default: OnlinePayments } = require("onlinepayments-sdk-nodejs");

// Initialize the client
const client = OnlinePayments.init({
  host: "payment.preprod.direct.worldline-solutions.com",
  apiKeyId: process.env.WORLDLINE_API_KEY,
  secretApiKey: process.env.WORLDLINE_SECRET_KEY
});

const merchantId = process.env.WORLDLINE_MERCHANT_ID;

// Retry configuration
const RETRY_DELAYS_DAYS = [0, 3, 7, 14]; // Retry on day 0, 3, 7, 14

/**
 * Create initial subscription with 3DS
 */
async function createSubscription(options) {
  const { planAmount, customerId, card, returnUrl } = options;

  const subscriptionId = `sub-${Date.now()}`;

  const payment = await client.payments.createPayment(merchantId, {
    order: {
      amountOfMoney: {
        amount: planAmount,
        currencyCode: "EUR"
      },
      customer: {
        merchantCustomerId: customerId
      },
      references: {
        merchantReference: `${subscriptionId}-initial`
      }
    },
    cardPaymentMethodSpecificInput: {
      authorizationMode: "SALE",
      card: {
        cardNumber: card.number,
        expiryDate: card.expiry,
        cvv: card.cvv,
        cardholderName: card.name
      },
      tokenize: true,
      threeDSecure: {
        challengeIndicator: "challenge-requested",
        redirectionData: {
          returnUrl: returnUrl || "https://yoursite.com/subscribe/complete"
        }
      }
    }
  });

  const token = payment.payment.paymentOutput?.cardPaymentMethodSpecificOutput?.token;

  return {
    subscriptionId,
    paymentId: payment.payment.id,
    status: payment.payment.status,
    token,
    requires3DS: payment.merchantAction?.actionType === "REDIRECT",
    redirectUrl: payment.merchantAction?.redirectData?.redirectURL
  };
}

/**
 * Charge recurring payment
 */
async function chargeRecurring(subscription) {
  const { token, planAmount, customerId, subscriptionId } = subscription;

  const payment = await client.payments.createPayment(merchantId, {
    order: {
      amountOfMoney: {
        amount: planAmount,
        currencyCode: "EUR"
      },
      customer: {
        merchantCustomerId: customerId
      },
      references: {
        merchantReference: `${subscriptionId}-${Date.now()}`
      }
    },
    cardPaymentMethodSpecificInput: {
      token,
      authorizationMode: "SALE",
      unscheduledCardOnFileRequestor: "merchantInitiated",
      unscheduledCardOnFileSequenceIndicator: "subsequent",
      recurringPaymentSequenceIndicator: "recurring"
    }
  });

  return {
    paymentId: payment.payment.id,
    status: payment.payment.status,
    success: payment.payment.status === "CAPTURED"
  };
}

/**
 * Process recurring payment with retry logic
 */
async function processRecurringWithRetry(subscription, attempt = 0) {
  console.log(`   Attempt ${attempt + 1} of ${RETRY_DELAYS_DAYS.length}...`);

  try {
    const result = await chargeRecurring(subscription);

    if (result.success) {
      console.log(`   Success! Payment ID: ${result.paymentId}`);
      return {
        success: true,
        paymentId: result.paymentId,
        attempt
      };
    }

    // Payment failed
    return await handleFailure(subscription, attempt, result.status);

  } catch (error) {
    console.log(`   Error: ${error.message}`);
    return await handleFailure(subscription, attempt, "ERROR");
  }
}

/**
 * Handle failed payment
 */
async function handleFailure(subscription, attempt, reason) {
  if (attempt >= RETRY_DELAYS_DAYS.length - 1) {
    // All retries exhausted
    console.log("   All retries exhausted - cancelling subscription");
    return {
      success: false,
      cancelled: true,
      reason
    };
  }

  const nextRetryDays = RETRY_DELAYS_DAYS[attempt + 1];
  console.log(`   Failed (${reason}) - will retry in ${nextRetryDays} days`);

  return {
    success: false,
    willRetry: true,
    nextRetryDays,
    reason
  };
}

/**
 * Update payment method for subscription
 */
async function updatePaymentMethod(subscription, newCard, returnUrl) {
  // Create zero-amount payment to validate and tokenize new card
  const payment = await client.payments.createPayment(merchantId, {
    order: {
      amountOfMoney: {
        amount: 0,
        currencyCode: "EUR"
      },
      customer: {
        merchantCustomerId: subscription.customerId
      },
      references: {
        merchantReference: `${subscription.subscriptionId}-update-${Date.now()}`
      }
    },
    cardPaymentMethodSpecificInput: {
      card: {
        cardNumber: newCard.number,
        expiryDate: newCard.expiry,
        cvv: newCard.cvv,
        cardholderName: newCard.name
      },
      tokenize: true,
      threeDSecure: {
        redirectionData: {
          returnUrl: returnUrl || "https://yoursite.com/account/update-card"
        }
      }
    }
  });

  const newToken = payment.payment.paymentOutput?.cardPaymentMethodSpecificOutput?.token;

  return {
    newToken,
    requires3DS: payment.merchantAction?.actionType === "REDIRECT",
    redirectUrl: payment.merchantAction?.redirectData?.redirectURL
  };
}

// ============================================
// Example: Full Subscription Lifecycle
// ============================================

async function subscriptionLifecycleExample() {
  console.log("=== Subscription Lifecycle ===\n");

  const customerId = `customer-${Date.now()}`;
  const planAmount = 999; // €9.99/month

  // 1. Create subscription
  console.log("1. Creating subscription...");
  const subscription = await createSubscription({
    planAmount,
    customerId,
    card: {
      number: "4111111111111111",
      expiry: "1225",
      cvv: "123",
      name: "John Doe"
    }
  });

  console.log(`   Subscription ID: ${subscription.subscriptionId}`);
  console.log(`   Initial payment: ${subscription.status}`);
  console.log(`   Token: ${subscription.token}`);

  if (subscription.requires3DS) {
    console.log("   3DS required - redirect customer");
    console.log(`   URL: ${subscription.redirectUrl}`);
    // In real app, wait for 3DS completion
  }
  console.log();

  // 2. First renewal (simulate)
  console.log("2. First renewal (1 month later)...");
  const renewalData = {
    ...subscription,
    customerId,
    planAmount
  };

  const renewal1 = await processRecurringWithRetry(renewalData, 0);
  console.log();

  // 3. Second renewal (simulate failure then success)
  console.log("3. Second renewal with retry scenario...");

  // Simulate: First attempt fails, second succeeds
  const renewal2_1 = await handleFailure(renewalData, 0, "INSUFFICIENT_FUNDS");
  console.log(`   Scheduled retry in ${renewal2_1.nextRetryDays} days`);

  // Retry after 3 days
  console.log("   [3 days later]");
  const renewal2_2 = await processRecurringWithRetry(renewalData, 1);
  console.log();

  // 4. Update payment method
  console.log("4. Customer updates payment method...");
  const updateResult = await updatePaymentMethod(
    { ...subscription, customerId },
    {
      number: "5399999999999999", // New card
      expiry: "1226",
      cvv: "456",
      name: "John Doe"
    }
  );

  console.log(`   New token: ${updateResult.newToken}`);
  if (updateResult.requires3DS) {
    console.log("   3DS required for new card");
  }
  console.log();

  // 5. Renewal with new card
  console.log("5. Renewal with new card...");
  const renewal3 = await processRecurringWithRetry({
    ...renewalData,
    token: updateResult.newToken
  }, 0);
  console.log();

  return subscription;
}

// ============================================
// Example: Dunning (Failed Payment Handling)
// ============================================

async function dunningExample() {
  console.log("=== Dunning Flow (Failed Payment Recovery) ===\n");

  // Simulate a subscription that keeps failing
  const subscription = {
    subscriptionId: "sub-test",
    customerId: "customer-123",
    planAmount: 999,
    token: "test-token"
  };

  console.log("Day 0: Initial charge attempt");
  let result = await handleFailure(subscription, 0, "CARD_DECLINED");
  console.log();

  if (result.willRetry) {
    console.log("Day 3: Retry #1");
    console.log("   Sending reminder email to customer");
    result = await handleFailure(subscription, 1, "CARD_DECLINED");
    console.log();
  }

  if (result.willRetry) {
    console.log("Day 7: Retry #2");
    console.log("   Sending urgent email: 'Update your payment method'");
    console.log("   Downgrading to limited access");
    result = await handleFailure(subscription, 2, "CARD_DECLINED");
    console.log();
  }

  if (result.willRetry) {
    console.log("Day 14: Final retry");
    result = await handleFailure(subscription, 3, "CARD_DECLINED");
    console.log();
  }

  if (result.cancelled) {
    console.log("Subscription cancelled after failed retries");
    console.log("Sending cancellation email to customer");
    console.log("Revoking access");
  }
}

// Run examples
async function main() {
  try {
    await subscriptionLifecycleExample();
    console.log("---\n");
    await dunningExample();
  } catch (error) {
    console.error("Error:", error.message);
    if (error.body?.errors) {
      console.error("Details:", error.body.errors);
    }
  }
}

main();
