/**
 * Worldline Direct - Capture Payment Example
 *
 * This example shows how to capture authorized payments,
 * including full, partial, and multiple captures.
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
 * Capture full authorized amount
 */
async function captureFullAmount(paymentId) {
  const response = await client.payments.capturePayment(merchantId, paymentId, {
    isFinal: true
    // Amount not specified = capture full authorization
  });

  console.log(`Full capture: ${response.status}`);
  return response;
}

/**
 * Capture partial amount
 */
async function capturePartialAmount(paymentId, amount, isFinal = false) {
  const response = await client.payments.capturePayment(merchantId, paymentId, {
    amount, // Amount in cents
    isFinal // Set to true for final capture
  });

  console.log(`Partial capture of €${amount / 100}: ${response.status}`);
  return response;
}

/**
 * Get remaining capturable amount
 */
async function getRemainingAmount(paymentId) {
  const payment = await client.payments.getPaymentDetails(merchantId, paymentId);

  const authorized = payment.paymentOutput.amountOfMoney.amount;
  const captured = payment.paymentOutput.acquiredAmount?.amount || 0;
  const remaining = authorized - captured;

  return {
    authorized,
    captured,
    remaining,
    isCapturable: payment.statusOutput.isAuthorized && remaining > 0
  };
}

/**
 * Check if payment can be captured
 */
async function canCapture(paymentId) {
  const payment = await client.payments.getPaymentDetails(merchantId, paymentId);

  const capturableStatuses = [
    "PENDING_CAPTURE",
    "AUTHORIZATION_REQUESTED",
    "PENDING_MERCHANT",
    "AUTHORIZED"
  ];

  return capturableStatuses.includes(payment.status);
}

// ============================================
// Example: E-commerce Order Fulfillment
// ============================================

async function ecommerceExample() {
  console.log("=== E-commerce Capture Example ===\n");

  // Assume we have an authorized payment from checkout
  const paymentId = process.env.TEST_PAYMENT_ID; // Replace with actual ID

  if (!paymentId) {
    console.log("Set TEST_PAYMENT_ID environment variable to test");
    return;
  }

  // Check status before capture
  console.log("1. Checking if payment can be captured...");
  const isCapturable = await canCapture(paymentId);

  if (!isCapturable) {
    console.log("   Payment cannot be captured (wrong status)");
    return;
  }

  const amounts = await getRemainingAmount(paymentId);
  console.log(`   Authorized: €${amounts.authorized / 100}`);
  console.log(`   Already captured: €${amounts.captured / 100}`);
  console.log(`   Remaining: €${amounts.remaining / 100}\n`);

  // Capture at shipping
  console.log("2. Order shipped - Capturing full amount...");
  const capture = await captureFullAmount(paymentId);
  console.log(`   Capture status: ${capture.status}\n`);

  // Verify final status
  console.log("3. Verifying final status...");
  const finalAmounts = await getRemainingAmount(paymentId);
  console.log(`   Captured: €${finalAmounts.captured / 100}`);
  console.log(`   Remaining: €${finalAmounts.remaining / 100}\n`);
}

// ============================================
// Example: Partial Shipment
// ============================================

async function partialShipmentExample() {
  console.log("=== Partial Shipment Example ===\n");

  const paymentId = process.env.TEST_PAYMENT_ID;

  if (!paymentId) {
    console.log("Set TEST_PAYMENT_ID environment variable to test");
    return;
  }

  console.log("Order has 3 items, shipping in separate packages...\n");

  // First shipment
  console.log("1. First package shipped - Capturing €30...");
  await capturePartialAmount(paymentId, 3000, false);

  let status = await getRemainingAmount(paymentId);
  console.log(`   Remaining: €${status.remaining / 100}\n`);

  // Second shipment
  console.log("2. Second package shipped - Capturing €45...");
  await capturePartialAmount(paymentId, 4500, false);

  status = await getRemainingAmount(paymentId);
  console.log(`   Remaining: €${status.remaining / 100}\n`);

  // Final shipment
  console.log("3. Final package shipped - Capturing €25 (final)...");
  await capturePartialAmount(paymentId, 2500, true);

  status = await getRemainingAmount(paymentId);
  console.log(`   Total captured: €${status.captured / 100}`);
  console.log(`   Remaining: €${status.remaining / 100}\n`);
}

// ============================================
// Example: Order with Discount Applied Later
// ============================================

async function discountExample() {
  console.log("=== Capture Less Than Authorized ===\n");

  const paymentId = process.env.TEST_PAYMENT_ID;

  if (!paymentId) {
    console.log("Set TEST_PAYMENT_ID environment variable to test");
    return;
  }

  const amounts = await getRemainingAmount(paymentId);
  console.log(`Original authorization: €${amounts.authorized / 100}`);

  // Customer got a 20% discount after authorization
  const discountedAmount = Math.floor(amounts.authorized * 0.8);
  console.log(`After 20% discount: €${discountedAmount / 100}\n`);

  console.log("Capturing discounted amount...");
  await capturePartialAmount(paymentId, discountedAmount, true);

  const savedAmount = amounts.authorized - discountedAmount;
  console.log(`\nCustomer saved: €${savedAmount / 100}`);
  console.log("Remaining authorization automatically released");
}

// ============================================
// Error Handling Example
// ============================================

async function captureWithErrorHandling(paymentId, amount) {
  try {
    const response = await client.payments.capturePayment(merchantId, paymentId, {
      amount,
      isFinal: true
    });

    return { success: true, response };

  } catch (error) {
    if (error.statusCode === 400) {
      const errorCode = error.body?.errors?.[0]?.code;

      switch (errorCode) {
        case "AMOUNT_EXCEEDS_AUTHORIZATION":
          console.error("Cannot capture more than authorized amount");
          break;
        case "PAYMENT_NOT_FOUND":
          console.error("Payment ID not found");
          break;
        case "INVALID_PAYMENT_STATE":
          console.error("Payment cannot be captured (wrong state)");
          break;
        default:
          console.error(`Capture error: ${errorCode}`);
      }

      return { success: false, error: errorCode };
    }

    if (error.statusCode === 409) {
      console.error("Payment already captured or cancelled");
      return { success: false, error: "ALREADY_PROCESSED" };
    }

    throw error;
  }
}

// Run examples
async function main() {
  try {
    await ecommerceExample();
    // await partialShipmentExample();
    // await discountExample();
  } catch (error) {
    console.error("Error:", error.message);
  }
}

main();
