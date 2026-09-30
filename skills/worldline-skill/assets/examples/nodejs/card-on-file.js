/**
 * Worldline Direct - Card-on-File (Tokenization) Example
 *
 * This example shows how to:
 * - Store cards securely as tokens
 * - Charge tokens for one-click checkout (CIT)
 * - Charge tokens for subscriptions (MIT)
 */

const { default: OnlinePayments } = require("onlinepayments-sdk-nodejs");

// Initialize the client
const client = OnlinePayments.init({
  host: "payment.preprod.direct.worldline-solutions.com",
  apiKeyId: process.env.WORLDLINE_API_KEY,
  secretApiKey: process.env.WORLDLINE_SECRET_KEY
});

const merchantId = process.env.WORLDLINE_MERCHANT_ID;

/**
 * Create a payment and store the card as a token
 */
async function createPaymentWithTokenization(options) {
  const { amount, currency, orderId, card, customerId, returnUrl } = options;

  const response = await client.payments.createPayment(merchantId, {
    order: {
      amountOfMoney: {
        amount,
        currencyCode: currency || "EUR"
      },
      customer: {
        merchantCustomerId: customerId
      },
      references: {
        merchantReference: orderId
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
      tokenize: true, // Request token
      threeDSecure: {
        challengeIndicator: "challenge-requested", // Force 3DS for first transaction
        redirectionData: {
          returnUrl: returnUrl || "https://yoursite.com/3ds/complete"
        }
      }
    }
  });

  return response;
}

/**
 * Create a zero-amount authorization to validate and store a card
 */
async function validateAndStoreCard(options) {
  const { card, customerId, returnUrl } = options;

  const response = await client.payments.createPayment(merchantId, {
    order: {
      amountOfMoney: {
        amount: 0, // Zero amount for validation only
        currencyCode: "EUR"
      },
      customer: {
        merchantCustomerId: customerId
      }
    },
    cardPaymentMethodSpecificInput: {
      card: {
        cardNumber: card.number,
        expiryDate: card.expiry,
        cvv: card.cvv,
        cardholderName: card.name
      },
      tokenize: true,
      threeDSecure: {
        redirectionData: {
          returnUrl: returnUrl || "https://yoursite.com/3ds/complete"
        }
      }
    }
  });

  return response;
}

/**
 * Charge a stored token - Customer Initiated (one-click checkout)
 */
async function chargeTokenCIT(options) {
  const { token, amount, orderId, customerId, returnUrl } = options;

  const response = await client.payments.createPayment(merchantId, {
    order: {
      amountOfMoney: {
        amount,
        currencyCode: "EUR"
      },
      customer: {
        merchantCustomerId: customerId
      },
      references: {
        merchantReference: orderId
      }
    },
    cardPaymentMethodSpecificInput: {
      token,
      authorizationMode: "SALE",
      unscheduledCardOnFileRequestor: "cardholderInitiated",
      unscheduledCardOnFileSequenceIndicator: "subsequent",
      threeDSecure: {
        skipAuthentication: false, // 3DS may still be required
        redirectionData: {
          returnUrl: returnUrl || "https://yoursite.com/3ds/complete"
        }
      }
    }
  });

  return response;
}

/**
 * Charge a stored token - Merchant Initiated (subscriptions, no-shows)
 */
async function chargeTokenMIT(options) {
  const { token, amount, orderId, customerId } = options;

  const response = await client.payments.createPayment(merchantId, {
    order: {
      amountOfMoney: {
        amount,
        currencyCode: "EUR"
      },
      customer: {
        merchantCustomerId: customerId
      },
      references: {
        merchantReference: orderId
      }
    },
    cardPaymentMethodSpecificInput: {
      token,
      authorizationMode: "SALE",
      unscheduledCardOnFileRequestor: "merchantInitiated",
      unscheduledCardOnFileSequenceIndicator: "subsequent"
      // No 3DS for MIT - customer not present
    }
  });

  return response;
}

/**
 * Charge a stored token - Fixed Recurring (subscriptions)
 */
async function chargeRecurring(options) {
  const { token, amount, subscriptionId, customerId } = options;

  const response = await client.payments.createPayment(merchantId, {
    order: {
      amountOfMoney: {
        amount,
        currencyCode: "EUR"
      },
      customer: {
        merchantCustomerId: customerId
      },
      references: {
        merchantReference: `sub-${subscriptionId}-${Date.now()}`
      }
    },
    cardPaymentMethodSpecificInput: {
      token,
      authorizationMode: "SALE",
      unscheduledCardOnFileRequestor: "merchantInitiated",
      unscheduledCardOnFileSequenceIndicator: "subsequent",
      recurringPaymentSequenceIndicator: "recurring" // Fixed recurring
    }
  });

  return response;
}

/**
 * Get token details
 */
async function getTokenDetails(token) {
  const response = await client.tokens.getToken(merchantId, token);
  return {
    id: response.id,
    cardNumber: response.card?.cardNumber, // Masked
    expiryDate: response.card?.expiryDate,
    paymentProductId: response.paymentProductId
  };
}

/**
 * Delete a stored token
 */
async function deleteToken(token) {
  await client.tokens.deleteToken(merchantId, token);
  console.log(`Token ${token} deleted`);
}

// ============================================
// Example: Customer Signup with Card Storage
// ============================================

async function signupExample() {
  console.log("=== Customer Signup with Card Storage ===\n");

  const customerId = `customer-${Date.now()}`;

  // First purchase with card storage
  console.log("1. First purchase - storing card...");
  const payment = await createPaymentWithTokenization({
    amount: 999,
    orderId: `order-${Date.now()}`,
    customerId,
    card: {
      number: "4111111111111111",
      expiry: "1225",
      cvv: "123",
      name: "John Doe"
    }
  });

  const token = payment.payment.paymentOutput?.cardPaymentMethodSpecificOutput?.token;
  console.log(`   Payment status: ${payment.payment.status}`);
  console.log(`   Token stored: ${token}\n`);

  // Handle 3DS if needed
  if (payment.merchantAction?.actionType === "REDIRECT") {
    console.log("   3DS required - redirect to:");
    console.log(`   ${payment.merchantAction.redirectData.redirectURL}\n`);
  }

  return { customerId, token };
}

// ============================================
// Example: One-Click Reorder
// ============================================

async function oneClickExample(customerId, token) {
  console.log("=== One-Click Reorder ===\n");

  console.log("Customer clicks 'Buy Again' with stored card...");
  const payment = await chargeTokenCIT({
    token,
    amount: 1499,
    orderId: `reorder-${Date.now()}`,
    customerId
  });

  console.log(`Payment status: ${payment.payment.status}`);

  if (payment.merchantAction?.actionType === "REDIRECT") {
    console.log("3DS step-up required");
  }

  return payment;
}

// ============================================
// Example: Subscription Billing
// ============================================

async function subscriptionExample(customerId, token) {
  console.log("=== Subscription Billing (MIT) ===\n");

  const subscriptionId = `sub-${Date.now()}`;

  // Monthly charge (no customer present)
  console.log("Monthly subscription charge...");
  const payment = await chargeRecurring({
    token,
    amount: 999,
    subscriptionId,
    customerId
  });

  console.log(`Payment status: ${payment.payment.status}`);
  // No 3DS redirect for MIT transactions

  return payment;
}

// ============================================
// Example: No-Show Fee
// ============================================

async function noShowExample(customerId, token) {
  console.log("=== No-Show Fee (MIT) ===\n");

  console.log("Customer didn't show up - charging no-show fee...");
  const payment = await chargeTokenMIT({
    token,
    amount: 5000,
    orderId: `noshow-${Date.now()}`,
    customerId
  });

  console.log(`Payment status: ${payment.payment.status}`);

  return payment;
}

// Run examples
async function main() {
  try {
    // Signup and store card
    const { customerId, token } = await signupExample();

    if (token) {
      console.log("---\n");

      // One-click reorder
      await oneClickExample(customerId, token);
      console.log("---\n");

      // Subscription billing
      await subscriptionExample(customerId, token);
      console.log("---\n");

      // No-show fee
      await noShowExample(customerId, token);
      console.log("---\n");

      // Get token details
      console.log("=== Token Details ===\n");
      const details = await getTokenDetails(token);
      console.log(`Card: ${details.cardNumber}`);
      console.log(`Expiry: ${details.expiryDate}`);
    }

  } catch (error) {
    console.error("Error:", error.message);
    if (error.body?.errors) {
      console.error("Details:", error.body.errors);
    }
  }
}

main();
