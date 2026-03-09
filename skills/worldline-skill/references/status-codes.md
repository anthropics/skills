# Payment Status Codes

Understanding payment statuses and status codes.

## Status Categories

| Category | Meaning |
|----------|---------|
| `CREATED` | Payment created, not yet processed |
| `PENDING_MERCHANT` | Waiting for merchant action |
| `PENDING_PAYMENT` | Waiting for customer/bank |
| `ACCOUNT_VERIFIED` | Account validated (zero-auth) |
| `PENDING_CAPTURE` | Authorized, awaiting capture |
| `CAPTURED` | Funds collected |
| `PENDING_REFUND` | Refund in progress |
| `REFUNDED` | Refund completed |
| `CANCELLED` | Payment cancelled |
| `REJECTED` | Payment rejected |

## Common Status Values

| Status | Code | Meaning | Next Action |
|--------|------|---------|-------------|
| `CREATED` | 0 | Payment created | Wait for processing |
| `PENDING_APPROVAL` | 5 | Waiting for 3DS | Customer completes 3DS |
| `AUTHORIZATION_REQUESTED` | 15 | Auth in progress | Wait |
| `PENDING_CAPTURE` | 5 | Authorized | Capture payment |
| `CAPTURE_REQUESTED` | 800 | Capture in progress | Wait |
| `CAPTURED` | 9 | Funds collected | Done (or refund) |
| `CANCELLED` | 6 | Voided | No action needed |
| `REJECTED` | 2 | Declined | Retry or new card |
| `REFUND_REQUESTED` | 81 | Refund in progress | Wait |
| `REFUNDED` | 8 | Refund complete | Done |

## Status Code Ranges

| Range | Category |
|-------|----------|
| 0-99 | Initial/Created |
| 100-199 | Pending |
| 200-299 | Pending payment method |
| 300-399 | Authorization requested |
| 400-499 | Pending capture |
| 500-599 | Captured |
| 600-699 | Reversed |
| 700-799 | Cancelled |
| 800-899 | Capture/Refund requested |
| 900+ | Completed |

## Checking Payment Status

```javascript
const payment = await client.payments.getPaymentDetails(merchantId, paymentId);

console.log({
  status: payment.status,
  statusCode: payment.statusOutput.statusCode,
  statusCategory: payment.statusOutput.statusCategory,
  isCancellable: payment.statusOutput.isCancellable,
  isAuthorized: payment.statusOutput.isAuthorized,
  isRefundable: payment.statusOutput.isRefundable
});
```

## Status Flows

### Successful Card Payment (Direct Sale)

```
CREATED → PENDING_APPROVAL → CAPTURED
       (if 3DS required)
```

### Successful Card Payment (Authorize + Capture)

```
CREATED → PENDING_CAPTURE → CAPTURE_REQUESTED → CAPTURED
```

### Declined Payment

```
CREATED → REJECTED
```

### Cancelled Authorization

```
PENDING_CAPTURE → CANCELLED
```

### Refunded Payment

```
CAPTURED → REFUND_REQUESTED → REFUNDED
```

## Final Statuses

These statuses indicate the payment is complete (no further changes):

- `CAPTURED` - Successfully collected
- `CANCELLED` - Successfully cancelled
- `REJECTED` - Declined
- `REFUNDED` - Fully refunded
- `CHARGEBACKED` - Disputed and lost

## Status Output Fields

```javascript
const status = payment.statusOutput;

{
  // Current status
  statusCode: 9,
  statusCategory: "CAPTURED",

  // What actions are available
  isCancellable: false,
  isAuthorized: true,
  isRefundable: true,

  // Error info (if rejected)
  errors: [{ code: "...", message: "..." }]
}
```

## Handling Statuses in Code

```javascript
async function handlePaymentStatus(paymentId) {
  const payment = await client.payments.getPaymentDetails(merchantId, paymentId);

  switch (payment.status) {
    case "CAPTURED":
      await markOrderPaid(paymentId);
      break;

    case "PENDING_CAPTURE":
      // Ready to capture
      await scheduleCapture(paymentId);
      break;

    case "PENDING_APPROVAL":
      // Waiting for 3DS
      // Customer should be redirected
      break;

    case "REJECTED":
      await markOrderFailed(paymentId);
      await notifyCustomer(paymentId, "payment_failed");
      break;

    case "CANCELLED":
      await markOrderCancelled(paymentId);
      break;

    case "REFUNDED":
      await markOrderRefunded(paymentId);
      break;

    default:
      console.log(`Unknown status: ${payment.status}`);
  }
}
```

## Webhook Status Updates

```javascript
app.post("/webhooks/worldline", async (req, res) => {
  const event = req.body;

  if (event.payment) {
    const { id, status, statusOutput } = event.payment;

    console.log(`Payment ${id} status: ${status}`);

    await handlePaymentStatus(id);
  }

  res.status(200).send("OK");
});
```

## Status by Payment Method

### Cards
```
CREATED → PENDING_APPROVAL → PENDING_CAPTURE → CAPTURED
```

### iDEAL
```
CREATED → REDIRECTED → PENDING_PAYMENT → CAPTURED
```

### PayPal
```
CREATED → REDIRECTED → PENDING_PAYMENT → CAPTURED
```

### SEPA Direct Debit
```
CREATED → PENDING_PAYMENT → CAPTURED (after settlement)
```

## Polling vs Webhooks

**Polling** - Check status periodically:
```javascript
async function pollStatus(paymentId, maxAttempts = 10) {
  for (let i = 0; i < maxAttempts; i++) {
    const payment = await client.payments.getPaymentDetails(merchantId, paymentId);

    if (["CAPTURED", "REJECTED", "CANCELLED"].includes(payment.status)) {
      return payment;
    }

    await sleep(2000); // Wait 2 seconds
  }

  throw new Error("Payment status not final after polling");
}
```

**Webhooks** (Recommended) - Get notified of changes:
```javascript
// See webhooks.md for setup
```

## Error Status Details

When status is `REJECTED`, check error details:

```javascript
if (payment.status === "REJECTED") {
  const errors = payment.statusOutput.errors || [];

  errors.forEach(error => {
    console.log(`Error ${error.code}: ${error.message}`);
  });

  // Common error codes:
  // - INSUFFICIENT_FUNDS
  // - CARD_EXPIRED
  // - INVALID_CARD
  // - DO_NOT_HONOR
  // - SUSPECTED_FRAUD
}
```
