/**
 * Worldline Direct - Hosted Checkout Example
 *
 * This example shows how to create a hosted checkout session
 * and handle the return from payment.
 */

const express = require("express");
const { default: OnlinePayments } = require("onlinepayments-sdk-nodejs");

// Initialize the client
const client = OnlinePayments.init({
  host: "payment.preprod.direct.worldline-solutions.com",
  apiKeyId: process.env.WORLDLINE_API_KEY,
  secretApiKey: process.env.WORLDLINE_SECRET_KEY,
  integrator: "YourCompany"
});

const merchantId = process.env.WORLDLINE_MERCHANT_ID;

const app = express();
app.use(express.json());

// Store checkout sessions (use a real database in production)
const checkoutSessions = new Map();

/**
 * Create a hosted checkout session
 */
app.post("/api/checkout", async (req, res) => {
  try {
    const { orderId, amount, currency, customer } = req.body;

    const response = await client.hostedCheckout.createHostedCheckout(merchantId, {
      order: {
        amountOfMoney: {
          amount: amount, // Amount in cents (e.g., 4999 = €49.99)
          currencyCode: currency || "EUR"
        },
        customer: {
          merchantCustomerId: customer.id,
          billingAddress: {
            street: customer.address?.street,
            city: customer.address?.city,
            countryCode: customer.address?.country,
            zip: customer.address?.postalCode
          },
          contactDetails: {
            emailAddress: customer.email
          }
        },
        references: {
          merchantReference: orderId
        }
      },
      hostedCheckoutSpecificInput: {
        returnUrl: `${process.env.BASE_URL}/checkout/complete?orderId=${orderId}`,
        showResultPage: false,
        locale: "en_GB",
        // Optional: Restrict payment methods
        paymentProductFilters: {
          restrictTo: {
            products: [1, 3, 809, 840, 3012] // Visa, MC, iDEAL, PayPal, Klarna
          }
        },
        // Optional: Enable card tokenization
        cardPaymentMethodSpecificInput: {
          tokenize: true
        }
      }
    });

    // Store session for verification on return
    checkoutSessions.set(orderId, {
      hostedCheckoutId: response.hostedCheckoutId,
      returnMac: response.RETURNMAC,
      createdAt: new Date()
    });

    // Return redirect URL to frontend
    const redirectUrl = `https://payment.preprod.direct.worldline-solutions.com/hostedcheckout/${response.hostedCheckoutId}`;

    res.json({
      success: true,
      redirectUrl,
      hostedCheckoutId: response.hostedCheckoutId
    });

  } catch (error) {
    console.error("Checkout creation failed:", error);
    res.status(500).json({
      success: false,
      error: error.message
    });
  }
});

/**
 * Handle return from hosted checkout
 */
app.get("/checkout/complete", async (req, res) => {
  try {
    const { orderId, RETURNMAC, hostedCheckoutId } = req.query;

    // Verify session exists
    const session = checkoutSessions.get(orderId);
    if (!session) {
      return res.redirect(`/order/${orderId}/error?reason=session_not_found`);
    }

    // Verify RETURNMAC to prevent tampering
    if (RETURNMAC !== session.returnMac) {
      return res.redirect(`/order/${orderId}/error?reason=invalid_return`);
    }

    // Get checkout status from Worldline
    const status = await client.hostedCheckout.getHostedCheckoutStatus(
      merchantId,
      hostedCheckoutId
    );

    if (status.status === "PAYMENT_CREATED") {
      const payment = status.createdPaymentOutput.payment;
      const paymentStatus = payment.status;

      if (paymentStatus === "CAPTURED" || paymentStatus === "PENDING_CAPTURE") {
        // Payment successful
        const paymentId = payment.id;
        const token = payment.paymentOutput?.cardPaymentMethodSpecificOutput?.token;

        // Store payment info (use your database)
        console.log(`Order ${orderId} paid. Payment ID: ${paymentId}`);
        if (token) {
          console.log(`Card token stored: ${token}`);
        }

        // Cleanup session
        checkoutSessions.delete(orderId);

        return res.redirect(`/order/${orderId}/success`);
      }
    }

    // Payment not successful
    console.log(`Order ${orderId} failed. Status: ${status.status}`);
    checkoutSessions.delete(orderId);

    return res.redirect(`/order/${orderId}/failed`);

  } catch (error) {
    console.error("Checkout completion error:", error);
    return res.redirect(`/order/${req.query.orderId}/error`);
  }
});

/**
 * Check payment status (for polling if needed)
 */
app.get("/api/checkout/:hostedCheckoutId/status", async (req, res) => {
  try {
    const { hostedCheckoutId } = req.params;

    const status = await client.hostedCheckout.getHostedCheckoutStatus(
      merchantId,
      hostedCheckoutId
    );

    res.json({
      status: status.status,
      paymentStatus: status.createdPaymentOutput?.payment?.status,
      paymentId: status.createdPaymentOutput?.payment?.id
    });

  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

// Start server
const PORT = process.env.PORT || 3000;
app.listen(PORT, () => {
  console.log(`Server running on port ${PORT}`);
});
