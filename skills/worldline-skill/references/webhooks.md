# Webhooks

Receive real-time notifications when payment status changes.

## Why Use Webhooks?

- **Reliability** - Redirect may fail (browser closes, network issues)
- **Real-time** - Get notified immediately
- **Async payments** - Required for bank transfers, SEPA DD
- **Automation** - Trigger fulfillment, emails, etc.

## Setup

### 1. Create Webhook Endpoint

```javascript
const express = require("express");
const crypto = require("crypto");

const app = express();

// Important: Get raw body for signature verification
app.use("/webhooks/worldline", express.raw({ type: "application/json" }));

app.post("/webhooks/worldline", async (req, res) => {
  // Verify signature
  const signature = req.headers["x-gcs-signature"];
  const keyId = req.headers["x-gcs-keyid"];

  if (!verifySignature(req.body, signature)) {
    console.error("Invalid webhook signature");
    return res.status(401).send("Invalid signature");
  }

  // Parse the event
  const event = JSON.parse(req.body.toString());

  // Process the event
  await processWebhookEvent(event);

  // Always respond 200 quickly
  res.status(200).send("OK");
});

function verifySignature(payload, signature) {
  const webhookSecret = process.env.WORLDLINE_WEBHOOK_SECRET;

  const expectedSignature = crypto
    .createHmac("sha256", webhookSecret)
    .update(payload)
    .digest("base64");

  // Use timing-safe comparison
  try {
    return crypto.timingSafeEqual(
      Buffer.from(signature),
      Buffer.from(expectedSignature)
    );
  } catch {
    return false;
  }
}
```

### 2. Configure in Merchant Portal

1. Go to **Configuration > Webhooks**
2. Enter your endpoint URL
3. Select events to receive
4. Save and get the webhook secret

### 3. Store the Secret

```bash
# .env
WORLDLINE_WEBHOOK_SECRET=your_webhook_secret_from_portal
```

## Event Types

### Payment Events

```javascript
async function processWebhookEvent(event) {
  if (event.payment) {
    const payment = event.payment;
    const { id, status } = payment;
    const merchantRef = payment.paymentOutput?.references?.merchantReference;

    console.log(`Payment ${id} (${merchantRef}): ${status}`);

    switch (status) {
      case "CAPTURED":
        await handlePaymentCaptured(merchantRef, payment);
        break;
      case "PENDING_CAPTURE":
        await handlePaymentAuthorized(merchantRef, payment);
        break;
      case "REJECTED":
        await handlePaymentRejected(merchantRef, payment);
        break;
      case "CANCELLED":
        await handlePaymentCancelled(merchantRef, payment);
        break;
      case "REFUNDED":
        await handlePaymentRefunded(merchantRef, payment);
        break;
    }
  }

  if (event.refund) {
    const refund = event.refund;
    console.log(`Refund ${refund.id}: ${refund.status}`);
    await handleRefundEvent(refund);
  }

  if (event.payout) {
    const payout = event.payout;
    console.log(`Payout ${payout.id}: ${payout.status}`);
    await handlePayoutEvent(payout);
  }
}
```

## Event Handlers

### Payment Captured

```javascript
async function handlePaymentCaptured(merchantRef, payment) {
  const orderId = extractOrderId(merchantRef);

  await database.updateOrder(orderId, {
    status: "paid",
    paymentId: payment.id,
    paidAt: new Date()
  });

  await sendEmail(orderId, "order_confirmed");
  await triggerFulfillment(orderId);
}
```

### Payment Rejected

```javascript
async function handlePaymentRejected(merchantRef, payment) {
  const orderId = extractOrderId(merchantRef);
  const errors = payment.statusOutput?.errors || [];

  await database.updateOrder(orderId, {
    status: "payment_failed",
    failureReason: errors[0]?.message
  });

  await sendEmail(orderId, "payment_failed");
}
```

### Payment Refunded

```javascript
async function handlePaymentRefunded(merchantRef, payment) {
  const orderId = extractOrderId(merchantRef);
  const refundedAmount = payment.paymentOutput?.amountOfMoney?.amount;

  await database.updateOrder(orderId, {
    status: "refunded",
    refundedAmount: refundedAmount,
    refundedAt: new Date()
  });

  await sendEmail(orderId, "refund_processed");
}
```

## Webhook Payload Structure

```javascript
{
  "apiVersion": "v1",
  "created": "2025-01-15T10:30:00.000+00:00",
  "merchantId": "YOUR_MERCHANT_ID",
  "type": "payment.captured",
  "payment": {
    "id": "payment_123456",
    "status": "CAPTURED",
    "statusOutput": {
      "statusCode": 9,
      "statusCategory": "COMPLETED",
      "isAuthorized": true,
      "isCancellable": false,
      "isRefundable": true
    },
    "paymentOutput": {
      "amountOfMoney": {
        "amount": 4999,
        "currencyCode": "EUR"
      },
      "references": {
        "merchantReference": "order-12345",
        "paymentReference": "..."
      },
      "cardPaymentMethodSpecificOutput": {
        "paymentProductId": 1,
        "card": {
          "cardNumber": "************1111",
          "expiryDate": "1225"
        }
      }
    }
  }
}
```

## Idempotency

Handle duplicate webhooks gracefully:

```javascript
async function processWebhookEvent(event) {
  const eventId = `${event.type}-${event.payment?.id}-${event.payment?.status}`;

  // Check if already processed
  const processed = await database.isWebhookProcessed(eventId);
  if (processed) {
    console.log(`Duplicate webhook ignored: ${eventId}`);
    return;
  }

  // Process the event
  await handleEvent(event);

  // Mark as processed
  await database.markWebhookProcessed(eventId);
}
```

## Retry Behavior

Worldline retries failed webhooks:

| Attempt | Delay |
|---------|-------|
| 1 | Immediate |
| 2 | 5 minutes |
| 3 | 15 minutes |
| 4 | 1 hour |
| 5 | 4 hours |
| 6 | 24 hours |

**Always respond 200 quickly** - Process async if needed:

```javascript
app.post("/webhooks/worldline", async (req, res) => {
  // Verify signature first
  if (!verifySignature(req.body, req.headers["x-gcs-signature"])) {
    return res.status(401).send("Invalid signature");
  }

  // Respond immediately
  res.status(200).send("OK");

  // Process asynchronously
  const event = JSON.parse(req.body.toString());
  processWebhookEvent(event).catch(err => {
    console.error("Webhook processing failed:", err);
  });
});
```

## Testing Webhooks Locally

### Using ngrok

```bash
# Install ngrok
npm install -g ngrok

# Start your server
node server.js

# Expose locally
ngrok http 3000

# Use the ngrok URL in Merchant Portal
# https://abc123.ngrok.io/webhooks/worldline
```

### Manual Testing

```javascript
// Test endpoint
app.post("/webhooks/test", (req, res) => {
  const testEvent = {
    type: "payment.captured",
    payment: {
      id: "test_123",
      status: "CAPTURED",
      paymentOutput: {
        references: { merchantReference: "order-test-123" }
      }
    }
  };

  processWebhookEvent(testEvent);
  res.send("Test processed");
});
```

## Monitoring

### Log All Webhooks

```javascript
app.post("/webhooks/worldline", async (req, res) => {
  const event = JSON.parse(req.body.toString());

  // Log for debugging
  console.log("Webhook received:", {
    type: event.type,
    paymentId: event.payment?.id,
    status: event.payment?.status,
    timestamp: new Date().toISOString()
  });

  // Store for audit
  await database.logWebhook(event);

  // Process...
});
```

### Check Webhook Logs

In Merchant Portal > Developer > Webhook Logs:
- View sent webhooks
- See response status
- Retry failed webhooks

## Best Practices

1. **Respond quickly** - Return 200 within 5 seconds
2. **Process async** - Don't block the response
3. **Verify signatures** - Always validate authenticity
4. **Handle duplicates** - Use idempotency keys
5. **Log everything** - For debugging and audit
6. **Use HTTPS** - Required for security
7. **Handle all statuses** - Not just success
