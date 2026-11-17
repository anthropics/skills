# Maintenance Operations

Post-authorization operations: Capture, Refund, and Cancel.

## Overview

| Operation | When to Use | Requirements |
|-----------|-------------|--------------|
| **Capture** | Collect authorized funds | Status: PENDING_CAPTURE |
| **Cancel** | Release held funds | Status: PENDING_CAPTURE |
| **Refund** | Return collected funds | Status: CAPTURED |

## Capture Payment

Convert an authorization into actual funds collection.

### Full Capture

```javascript
const capture = await client.payments.capturePayment(merchantId, paymentId, {
  isFinal: true
});

// Response
{
  status: "CAPTURE_REQUESTED",
  statusOutput: {
    isCancellable: false,
    statusCategory: "PENDING_MERCHANT",
    statusCode: 800
  }
}
```

### Partial Capture (Pre-Auth Only)

```javascript
// Original authorization: €100
const capture = await client.payments.capturePayment(merchantId, paymentId, {
  amount: 7500, // €75
  isFinal: false // More captures possible
});

// Later, capture remaining
const finalCapture = await client.payments.capturePayment(merchantId, paymentId, {
  amount: 1500, // €15
  isFinal: true // No more captures
});

// Total captured: €90, €10 automatically released
```

### Multiple Partial Captures

```javascript
// Car rental example
const initialAuth = 100000; // €1000 deposit

// Capture 1: Base rental
await client.payments.capturePayment(merchantId, paymentId, {
  amount: 50000, // €500
  isFinal: false
});

// Capture 2: Fuel charge
await client.payments.capturePayment(merchantId, paymentId, {
  amount: 5000, // €50
  isFinal: false
});

// Capture 3: Toll fees (final)
await client.payments.capturePayment(merchantId, paymentId, {
  amount: 2500, // €25
  isFinal: true
});

// Remaining €425 automatically released
```

### Check if Capturable

```javascript
const payment = await client.payments.getPaymentDetails(merchantId, paymentId);

if (payment.statusOutput.isAuthorized && !payment.statusOutput.isCaptured) {
  // Can capture
  const capturable = payment.paymentOutput.amountOfMoney.amount -
    (payment.paymentOutput.acquiredAmount?.amount || 0);
  console.log(`Can capture up to: ${capturable} cents`);
}
```

## Cancel Payment

Release held funds back to cardholder.

### Full Cancellation

```javascript
await client.payments.cancelPayment(merchantId, paymentId);

// Response
{
  payment: {
    status: "CANCELLED",
    statusOutput: {
      statusCategory: "UNSUCCESSFUL"
    }
  }
}
```

### Partial Cancellation (Pre-Auth Only)

```javascript
// Authorized €1000, want to reduce to €600
await client.payments.cancelPayment(merchantId, paymentId, {
  amount: 40000, // Cancel €400
  isFinal: false
});

// €600 still available to capture
```

### Check if Cancellable

```javascript
const payment = await client.payments.getPaymentDetails(merchantId, paymentId);

if (payment.statusOutput.isCancellable) {
  await client.payments.cancelPayment(merchantId, paymentId);
}
```

## Refund Payment

Return funds after capture.

### Full Refund

```javascript
const refund = await client.payments.refundPayment(merchantId, paymentId, {
  amountOfMoney: {
    amount: 4999, // Original amount
    currencyCode: "EUR"
  }
});

// Response
{
  id: "refund_123",
  status: "REFUND_REQUESTED",
  refundOutput: {
    amountOfMoney: { amount: 4999, currencyCode: "EUR" }
  }
}
```

### Partial Refund

```javascript
// Original payment: €100
const refund = await client.payments.refundPayment(merchantId, paymentId, {
  amountOfMoney: {
    amount: 2500, // Refund €25
    currencyCode: "EUR"
  }
});

// Can issue more partial refunds up to original amount
```

### Multiple Partial Refunds

```javascript
// Order: 3 items for €90

// Return item 1: €30
await client.payments.refundPayment(merchantId, paymentId, {
  amountOfMoney: { amount: 3000, currencyCode: "EUR" },
  references: { merchantReference: `refund-${orderId}-item1` }
});

// Return item 2: €40
await client.payments.refundPayment(merchantId, paymentId, {
  amountOfMoney: { amount: 4000, currencyCode: "EUR" },
  references: { merchantReference: `refund-${orderId}-item2` }
});

// Total refunded: €70, €20 retained
```

### Check Refundable Amount

```javascript
const payment = await client.payments.getPaymentDetails(merchantId, paymentId);

if (payment.status === "CAPTURED") {
  const captured = payment.paymentOutput.amountOfMoney.amount;
  const refunded = payment.paymentOutput.amountPaid?.amount || 0;
  const refundable = captured - refunded;

  console.log(`Can refund up to: ${refundable} cents`);
}
```

## Status Flow

```
Authorization:
  PENDING_CAPTURE → CAPTURE_REQUESTED → CAPTURED
                 ↓
              CANCELLED

Capture:
  PENDING_CAPTURE → CAPTURED

Refund:
  CAPTURED → REFUND_REQUESTED → REFUNDED

Cancel:
  PENDING_CAPTURE → CANCELLED
```

## Error Handling

```javascript
async function captureWithErrorHandling(paymentId, amount) {
  try {
    return await client.payments.capturePayment(merchantId, paymentId, {
      amount: amount,
      isFinal: true
    });
  } catch (error) {
    if (error.statusCode === 400) {
      const errorCode = error.body?.errors?.[0]?.code;

      switch (errorCode) {
        case "AMOUNT_EXCEEDS_AUTHORIZATION":
          throw new Error("Cannot capture more than authorized");
        case "PAYMENT_NOT_FOUND":
          throw new Error("Payment not found");
        default:
          throw new Error(`Capture failed: ${errorCode}`);
      }
    }

    if (error.statusCode === 409) {
      throw new Error("Payment already captured or cancelled");
    }

    throw error;
  }
}
```

## Idempotency

Use unique merchant references to prevent duplicates.

```javascript
// Good: Unique reference per operation
await client.payments.capturePayment(merchantId, paymentId, {
  amount: 5000,
  isFinal: true,
  references: {
    merchantReference: `capture-${orderId}-${Date.now()}`
  }
});

// Good: Unique per refund
await client.payments.refundPayment(merchantId, paymentId, {
  amountOfMoney: { amount: 1000, currencyCode: "EUR" },
  references: {
    merchantReference: `refund-${orderId}-item-${itemId}`
  }
});
```

## Merchant Portal

All operations are also available in the Merchant Portal:
1. Find payment by ID or merchant reference
2. Click Capture, Cancel, or Refund button
3. Enter amount (for partial operations)
4. Confirm

## Webhooks

Listen for operation status changes.

```javascript
app.post("/webhooks/worldline", async (req, res) => {
  const event = req.body;

  if (event.payment) {
    const { id, status } = event.payment;

    switch (status) {
      case "CAPTURED":
        await handleCapture(id);
        break;
      case "CANCELLED":
        await handleCancellation(id);
        break;
      case "REFUNDED":
        await handleRefund(id);
        break;
    }
  }

  res.status(200).send("OK");
});
```

## Best Practices

1. **Capture promptly** - Don't wait until authorization expires
2. **Track state** - Store payment status in your database
3. **Use webhooks** - Don't rely only on API responses
4. **Unique references** - Prevent duplicate operations
5. **Handle errors** - Graceful degradation
6. **Audit trail** - Log all operations
7. **Customer communication** - Notify on refunds

## Common Scenarios

### Order Shipped
```javascript
// Capture full amount
await client.payments.capturePayment(merchantId, paymentId, { isFinal: true });
await updateOrderStatus(orderId, "shipped");
```

### Order Cancelled Before Ship
```javascript
// Cancel authorization
await client.payments.cancelPayment(merchantId, paymentId);
await updateOrderStatus(orderId, "cancelled");
```

### Item Returned
```javascript
// Refund item cost
await client.payments.refundPayment(merchantId, paymentId, {
  amountOfMoney: { amount: itemPrice, currencyCode: "EUR" }
});
await updateOrderStatus(orderId, "partially_refunded");
```

### Partial Shipment
```javascript
// Ship what's available
await client.payments.capturePayment(merchantId, paymentId, {
  amount: shippedItemsTotal,
  isFinal: false
});
// Later capture remaining or cancel
```
