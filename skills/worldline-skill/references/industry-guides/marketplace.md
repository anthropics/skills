# Marketplace Payment Integration

Platforms connecting buyers and sellers with split payments and payouts.

## Recommended Payment Flow

```
1. Buyer checkout: Collect full payment amount
2. Hold in escrow: Wait for fulfillment
3. Split payment: Distribute to seller(s) and platform
4. Payout: Transfer funds to seller bank accounts
```

## Key Concepts

### Payment Split
Divide a single payment among multiple parties:
- Seller(s): Product/service amount
- Platform: Commission/fees
- Other: Shipping partners, service providers

### Payout
Transfer funds from merchant account to seller bank accounts.

## Basic Marketplace Flow

### 1. Collect Payment from Buyer

```javascript
const payment = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 10000, currencyCode: "EUR" }, // €100 total
    customer: { merchantCustomerId: buyerId },
    references: {
      merchantReference: `order-${orderId}`,
      descriptor: "Marketplace - Order #12345"
    }
  },
  cardPaymentMethodSpecificInput: {
    authorizationMode: "FINAL_AUTHORIZATION",
    card: cardDetails
  }
});

// Store payment info
await database.saveOrder(orderId, {
  paymentId: payment.payment.id,
  buyerAmount: 10000,
  sellerAmount: 8500,  // €85 to seller
  platformFee: 1500    // €15 platform fee (15%)
});
```

### 2. Capture on Fulfillment

```javascript
// When seller ships the item
await client.payments.capturePayment(merchantId, paymentId, {
  amount: 10000,
  isFinal: true
});

// Record for payout
await database.markReadyForPayout(orderId);
```

### 3. Payout to Seller

Use Worldline's Payout API to transfer funds.

```javascript
const payout = await client.payouts.createPayout(merchantId, {
  amountOfMoney: { amount: 8500, currencyCode: "EUR" },
  payoutDetails: {
    name: "Seller Business Name"
  },
  bankAccountBban: {
    accountNumber: "NL91ABNA0417164300",
    bankCode: "ABNANL2A"
  },
  references: {
    merchantReference: `payout-${orderId}`
  }
});
```

## Multi-Seller Order

When a single order has items from multiple sellers.

```javascript
// Order: €150 total
// - Seller A: €80 product
// - Seller B: €50 product
// - Platform: €20 (13.3% fee)

const payment = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 15000, currencyCode: "EUR" },
    references: { merchantReference: `order-${orderId}` }
  },
  cardPaymentMethodSpecificInput: {
    authorizationMode: "FINAL_AUTHORIZATION",
    card: cardDetails
  }
});

// Track splits
await database.saveOrder(orderId, {
  paymentId: payment.payment.id,
  items: [
    { sellerId: "A", amount: 6800, productAmount: 8000, fee: 1200 },
    { sellerId: "B", amount: 4250, productAmount: 5000, fee: 750 }
  ],
  platformTotal: 1950
});
```

## Partial Fulfillment

Different sellers ship at different times.

```javascript
// Use pre-auth for flexibility
const payment = await client.payments.createPayment(merchantId, {
  order: { amountOfMoney: { amount: 15000, currencyCode: "EUR" } },
  cardPaymentMethodSpecificInput: {
    authorizationMode: "PRE_AUTHORIZATION", // Allows partial captures
    card: cardDetails
  }
});

// Seller A ships first
await client.payments.capturePayment(merchantId, paymentId, {
  amount: 8000,
  isFinal: false
});
await schedulePayout("A", 6800);

// Seller B ships later
await client.payments.capturePayment(merchantId, paymentId, {
  amount: 5000,
  isFinal: true
});
await schedulePayout("B", 4250);
```

## Refund Handling

### Full Order Refund
```javascript
await client.payments.refundPayment(merchantId, paymentId, {
  amountOfMoney: { amount: 15000, currencyCode: "EUR" }
});

// Claw back from sellers if already paid out
await createSellerDebit("A", 6800);
await createSellerDebit("B", 4250);
```

### Partial Refund (One Item)
```javascript
// Seller A's item returned
await client.payments.refundPayment(merchantId, paymentId, {
  amountOfMoney: { amount: 8000, currencyCode: "EUR" }
});

// Debit seller A's balance
await createSellerDebit("A", 6800);
// Platform absorbs or refunds their fee portion
```

## Escrow Pattern

Hold funds until buyer confirms satisfaction.

```javascript
// 1. Authorize (don't capture yet)
const auth = await client.payments.createPayment(merchantId, {
  order: { amountOfMoney: { amount: 10000, currencyCode: "EUR" } },
  cardPaymentMethodSpecificInput: {
    authorizationMode: "PRE_AUTHORIZATION",
    card: cardDetails
  }
});

// 2. Seller fulfills order
await updateOrderStatus(orderId, "shipped");

// 3. Buyer receives and confirms (or auto-confirm after X days)
await updateOrderStatus(orderId, "delivered");

// Wait for dispute window (e.g., 14 days)

// 4. Capture and schedule payout
await client.payments.capturePayment(merchantId, paymentId, {
  amount: 10000,
  isFinal: true
});
await schedulePayout(sellerId, 8500);
```

## Disputes & Chargebacks

```javascript
app.post("/webhooks/worldline", async (req, res) => {
  const event = req.body;

  if (event.dispute) {
    const dispute = event.dispute;
    const orderId = extractOrderId(dispute.paymentOutput.references.merchantReference);

    // Freeze seller payout
    await freezeSellerBalance(orderId);

    // Notify seller
    await notifySeller(orderId, "dispute_opened", dispute);

    // Collect evidence
    await requestDisputeEvidence(orderId);
  }

  res.status(200).send("OK");
});
```

## Payout Schedule Options

| Model | Description | Risk |
|-------|-------------|------|
| **Instant** | Payout immediately on capture | High (chargebacks) |
| **Daily** | Batch payouts once per day | Medium |
| **Weekly** | Batch payouts weekly | Low |
| **On-demand** | Seller requests payout | Lowest |
| **Threshold** | Payout when balance exceeds €X | Variable |

## Best Practices

1. **KYC for sellers** - Verify identity before enabling payouts
2. **Escrow period** - Hold funds for dispute window
3. **Reserve balance** - Keep % for potential refunds
4. **Clear fee structure** - Document commission in terms
5. **Separate payout tracking** - Don't mix with payments
6. **Dispute evidence** - Collect shipping proof, communications
7. **Tax reporting** - Track 1099/VAT for sellers

## Seller Onboarding

Before a seller can receive payouts:

1. Collect business/personal information
2. Verify identity (KYC)
3. Collect bank account details
4. Verify bank account (micro-deposits or instant)
5. Set commission rate
6. Enable payouts

## Platform Fee Models

| Model | Example | Implementation |
|-------|---------|----------------|
| **Flat fee** | €0.50 per order | Fixed deduction |
| **Percentage** | 15% of order | Calculate on capture |
| **Tiered** | 10% for €0-1000, 8% above | Volume tracking |
| **Subscription** | €29/month + 5% | Separate billing |

## Reporting

Track daily:
- Total volume processed
- Platform fees collected
- Pending payouts
- Completed payouts
- Refunds issued
- Disputes opened/closed
- Seller balances
