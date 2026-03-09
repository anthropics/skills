# Card Payments

Credit and debit card processing with 3D Secure authentication.

## Supported Card Networks

| Network | Product ID | Coverage |
|---------|-----------|----------|
| Visa | 1 | Global |
| Mastercard | 3 | Global |
| American Express | 2 | Global |
| Maestro | 117 | Europe |
| JCB | 125 | Global |
| Diners Club | 132 | Global |
| Discover | 128 | US/Global |
| Carte Bancaire | 130 | France |
| Bancontact | 3012 | Belgium |
| Dankort | 123 | Denmark |

## Basic Card Payment

```javascript
const payment = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: {
      amount: 4999, // €49.99 in cents
      currencyCode: "EUR"
    },
    customer: {
      merchantCustomerId: customerId,
      billingAddress: {
        street: "123 Main St",
        city: "Amsterdam",
        countryCode: "NL",
        zip: "1011AB"
      }
    },
    references: {
      merchantReference: orderId
    }
  },
  cardPaymentMethodSpecificInput: {
    authorizationMode: "SALE",
    card: {
      cardNumber: "4111111111111111",
      expiryDate: "1225", // MMYY format
      cvv: "123",
      cardholderName: "John Doe"
    }
  }
});
```

## 3D Secure (3DS)

Required for EU payments under PSD2/SCA.

### With 3DS

```javascript
const payment = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 4999, currencyCode: "EUR" }
  },
  cardPaymentMethodSpecificInput: {
    authorizationMode: "SALE",
    card: cardDetails,
    threeDSecure: {
      challengeIndicator: "no-preference", // or "challenge-requested"
      redirectionData: {
        returnUrl: "https://yoursite.com/3ds/complete"
      }
    }
  }
});

// Check if redirect needed
if (payment.merchantAction?.actionType === "REDIRECT") {
  // Redirect customer for 3DS authentication
  const redirectUrl = payment.merchantAction.redirectData.redirectURL;
  res.redirect(redirectUrl);
} else {
  // No 3DS required or frictionless flow
  handlePaymentResult(payment);
}
```

### 3DS Challenge Indicators

| Value | Description |
|-------|-------------|
| `no-preference` | Let issuer decide |
| `no-challenge-requested` | Request frictionless if possible |
| `challenge-requested` | Force challenge (recommended for first CoF) |
| `challenge-required-mandate` | Challenge mandated |

### Handle 3DS Return

```javascript
app.get("/3ds/complete", async (req, res) => {
  const { paymentId, RETURNMAC } = req.query;

  // Get updated payment status
  const payment = await client.payments.getPaymentDetails(merchantId, paymentId);

  if (payment.status === "CAPTURED" || payment.status === "PENDING_CAPTURE") {
    res.redirect("/order/success");
  } else {
    res.redirect("/order/failed");
  }
});
```

## Co-Badged Cards

Cards with multiple networks (e.g., Visa + Cartes Bancaires).

```javascript
// In Hosted Checkout, customer chooses network
// In S2S, specify which network to use:
cardPaymentMethodSpecificInput: {
  paymentProductId: 130, // Force Cartes Bancaires
  card: cardDetails
}
```

## Card Validation (BIN Check)

```javascript
const binInfo = await client.services.getIINDetails(merchantId, {
  bin: "411111" // First 6 digits
});

console.log({
  cardType: binInfo.paymentProductId,
  issuingCountry: binInfo.countryCode,
  coBrands: binInfo.coBrands
});
```

## AVS (Address Verification)

```javascript
const payment = await client.payments.createPayment(merchantId, {
  order: {
    customer: {
      billingAddress: {
        street: "123 Main St",
        houseNumber: "123",
        zip: "1011AB",
        city: "Amsterdam",
        countryCode: "NL"
      }
    }
  },
  cardPaymentMethodSpecificInput: {
    card: cardDetails,
    // AVS check happens automatically
  }
});

// Check AVS result
const avsResult = payment.payment.paymentOutput
  .cardPaymentMethodSpecificOutput.fraudResults.avsResult;
```

### AVS Result Codes

| Code | Meaning |
|------|---------|
| A | Address match, ZIP no match |
| W | ZIP match, address no match |
| Y | Both match |
| N | Neither match |
| U | AVS unavailable |

## CVV Verification

```javascript
// CVV is automatically verified when provided
const cvvResult = payment.payment.paymentOutput
  .cardPaymentMethodSpecificOutput.fraudResults.cvvResult;
```

### CVV Result Codes

| Code | Meaning |
|------|---------|
| M | Match |
| N | No match |
| P | Not processed |
| U | Unavailable |

## Filtering Card Types

In Hosted Checkout:

```javascript
hostedCheckoutSpecificInput: {
  paymentProductFilters: {
    restrictTo: {
      products: [1, 3] // Only Visa and Mastercard
    },
    // Or exclude:
    exclude: {
      products: [2] // No American Express
    }
  }
}
```

## Tokenization

See [Card-on-File](../payment-flows/card-on-file.md) for details.

```javascript
cardPaymentMethodSpecificInput: {
  card: cardDetails,
  tokenize: true // Request token for future use
}
```

## Surcharging

Add card-specific fees (where legally allowed).

```javascript
order: {
  amountOfMoney: { amount: 4999, currencyCode: "EUR" },
  surchargeSpecificInput: {
    mode: "on-behalf-of"
  }
}
```

## Error Handling

### Common Decline Reasons

| Status | Meaning | Action |
|--------|---------|--------|
| REJECTED | Generic decline | Ask for another card |
| AUTHORIZATION_REQUESTED | Processing | Wait |
| PENDING_FRAUD_APPROVAL | Fraud review | Wait for review |

### Error Codes

```javascript
try {
  const payment = await client.payments.createPayment(...);
} catch (error) {
  if (error.statusCode === 402) {
    const errors = error.body?.errors || [];
    errors.forEach(e => {
      console.log(`Error: ${e.code} - ${e.message}`);
    });
  }
}
```

## Best Practices

1. **Always use 3DS** - Required in EU, reduces fraud globally
2. **Validate BIN first** - Know card type before processing
3. **Collect billing address** - Improves AVS and reduces fraud
4. **Store tokens, not cards** - Never store raw card data
5. **Handle all statuses** - Success, pending, declined
6. **Unique references** - Link payments to orders
7. **Test thoroughly** - Use test cards in sandbox
