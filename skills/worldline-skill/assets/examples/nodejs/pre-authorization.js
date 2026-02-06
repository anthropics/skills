/**
 * Worldline Direct - Pre-Authorization Example
 *
 * This example shows how to create a pre-authorization,
 * perform partial captures, and handle the full lifecycle.
 *
 * Perfect for: Car rental, hotels, variable-amount transactions
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
 * Create a pre-authorization
 * Blocks funds for up to 30 days without capturing
 */
async function createPreAuthorization(options) {
  const { amount, currency, orderId, card, returnUrl } = options;

  const response = await client.payments.createPayment(merchantId, {
    order: {
      amountOfMoney: {
        amount, // Amount in cents
        currencyCode: currency || "EUR"
      },
      references: {
        merchantReference: orderId
      }
    },
    cardPaymentMethodSpecificInput: {
      authorizationMode: "PRE_AUTHORIZATION", // Key setting!
      card: {
        cardNumber: card.number,
        expiryDate: card.expiry, // MMYY format
        cvv: card.cvv,
        cardholderName: card.name
      },
      tokenize: true, // Store for future charges
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
 * Capture funds from a pre-authorization
 * Can be partial or full
 */
async function capturePayment(paymentId, amount, isFinal = true) {
  const response = await client.payments.capturePayment(merchantId, paymentId, {
    amount, // Amount to capture in cents
    isFinal // If false, more captures are possible
  });

  return response;
}

/**
 * Cancel a pre-authorization (release funds)
 */
async function cancelAuthorization(paymentId) {
  const response = await client.payments.cancelPayment(merchantId, paymentId);
  return response;
}

/**
 * Get payment status
 */
async function getPaymentStatus(paymentId) {
  const response = await client.payments.getPaymentDetails(merchantId, paymentId);
  return {
    status: response.status,
    authorizedAmount: response.paymentOutput?.amountOfMoney?.amount,
    capturedAmount: response.paymentOutput?.acquiredAmount?.amount || 0,
    token: response.paymentOutput?.cardPaymentMethodSpecificOutput?.token
  };
}

// ============================================
// Example Usage: Car Rental Flow
// ============================================

async function carRentalExample() {
  console.log("=== Car Rental Payment Flow ===\n");

  // 1. Customer books a car - Pre-authorize deposit
  console.log("1. Creating pre-authorization for €500 deposit...");
  const preAuth = await createPreAuthorization({
    amount: 50000, // €500
    currency: "EUR",
    orderId: `rental-${Date.now()}`,
    card: {
      number: "4111111111111111",
      expiry: "1225",
      cvv: "123",
      name: "John Doe"
    },
    returnUrl: "https://example.com/3ds"
  });

  const paymentId = preAuth.payment.id;
  const token = preAuth.payment.paymentOutput?.cardPaymentMethodSpecificOutput?.token;

  console.log(`   Pre-auth created: ${paymentId}`);
  console.log(`   Status: ${preAuth.payment.status}`);
  console.log(`   Token: ${token}\n`);

  // Handle 3DS redirect if needed
  if (preAuth.merchantAction?.actionType === "REDIRECT") {
    console.log("   3DS required - redirect customer to:");
    console.log(`   ${preAuth.merchantAction.redirectData.redirectURL}\n`);
    // In real app, redirect and wait for return
  }

  // 2. Customer returns car - Capture actual rental cost
  console.log("2. Car returned - Capturing €350 (actual rental cost)...");
  const capture1 = await capturePayment(paymentId, 35000, false); // Not final yet
  console.log(`   Captured €350. Status: ${capture1.status}\n`);

  // 3. Extra charges - Fuel
  console.log("3. Adding fuel charge - Capturing €45...");
  const capture2 = await capturePayment(paymentId, 4500, true); // Final capture
  console.log(`   Captured €45. Status: ${capture2.status}\n`);

  // Check final status
  console.log("4. Checking final status...");
  const status = await getPaymentStatus(paymentId);
  console.log(`   Status: ${status.status}`);
  console.log(`   Authorized: €${status.authorizedAmount / 100}`);
  console.log(`   Captured: €${status.capturedAmount / 100}`);
  console.log(`   Remaining €${(status.authorizedAmount - status.capturedAmount) / 100} was released\n`);

  return { paymentId, token };
}

// ============================================
// Example Usage: Hotel Flow
// ============================================

async function hotelExample() {
  console.log("=== Hotel Booking Flow ===\n");

  // 1. Guest books room - Pre-authorize for stay + incidentals
  console.log("1. Creating pre-authorization for €1000 (room + incidentals)...");
  const preAuth = await createPreAuthorization({
    amount: 100000, // €1000
    currency: "EUR",
    orderId: `hotel-${Date.now()}`,
    card: {
      number: "5399999999999999",
      expiry: "1225",
      cvv: "123",
      name: "Jane Smith"
    }
  });

  const paymentId = preAuth.payment.id;
  console.log(`   Pre-auth created: ${paymentId}\n`);

  // 2. Guest checks out - Capture room + minibar
  console.log("2. Checkout - Capturing €750 (room €700 + minibar €50)...");
  const capture = await capturePayment(paymentId, 75000, true);
  console.log(`   Captured: ${capture.status}`);
  console.log(`   Remaining €250 released automatically\n`);

  return { paymentId };
}

// ============================================
// Example Usage: Cancellation
// ============================================

async function cancellationExample() {
  console.log("=== Cancellation Flow ===\n");

  // Create a pre-auth
  console.log("1. Creating pre-authorization...");
  const preAuth = await createPreAuthorization({
    amount: 20000,
    orderId: `cancel-test-${Date.now()}`,
    card: {
      number: "4111111111111111",
      expiry: "1225",
      cvv: "123",
      name: "Test User"
    }
  });

  const paymentId = preAuth.payment.id;
  console.log(`   Pre-auth created: ${paymentId}\n`);

  // Customer cancels
  console.log("2. Customer cancels - Releasing funds...");
  const cancel = await cancelAuthorization(paymentId);
  console.log(`   Cancelled: ${cancel.payment.status}`);
  console.log("   Funds released to cardholder\n");

  return { paymentId };
}

// Run examples
async function main() {
  try {
    await carRentalExample();
    console.log("---\n");
    await hotelExample();
    console.log("---\n");
    await cancellationExample();
  } catch (error) {
    console.error("Error:", error.message);
    if (error.body?.errors) {
      console.error("Details:", error.body.errors);
    }
  }
}

main();
