# Banking Payment Methods

Real-time banking, SEPA Direct Debit, and local payment methods.

## iDEAL (Netherlands)

### Product ID: 809

Most popular payment method in the Netherlands (~60% of online payments).

```javascript
const payment = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 4999, currencyCode: "EUR" }
  },
  redirectPaymentMethodSpecificInput: {
    paymentProductId: 809,
    returnUrl: "https://yoursite.com/payment/complete"
  }
});

if (payment.merchantAction?.actionType === "REDIRECT") {
  res.redirect(payment.merchantAction.redirectData.redirectURL);
}
```

### Get Available Banks

```javascript
const idealProduct = await client.products.getPaymentProduct(merchantId, 809, {
  currencyCode: "EUR",
  countryCode: "NL",
  amount: 4999
});

const banks = idealProduct.fields
  .find(f => f.id === "issuerId")
  .displayHints.formElement.valueMapping;

// Show bank selection to customer
```

### With Bank Pre-Selected

```javascript
redirectPaymentMethodSpecificInput: {
  paymentProductId: 809,
  returnUrl: "https://...",
  paymentProduct809SpecificInput: {
    issuerId: "ABNANL2A" // Customer's selected bank
  }
}
```

## SEPA Direct Debit

### Product ID: 771

For recurring payments and subscriptions in SEPA zone.

### First Payment (Mandate Creation)

```javascript
const payment = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 999, currencyCode: "EUR" },
    customer: {
      billingAddress: {
        street: "Hauptstraße 1",
        city: "Berlin",
        countryCode: "DE",
        zip: "10115"
      }
    }
  },
  sepaDirectDebitPaymentMethodSpecificInput: {
    paymentProductId: 771,
    paymentProduct771SpecificInput: {
      mandate: {
        customerContractIdentifier: subscriptionId,
        recurrenceType: "RECURRING",
        signatureType: "SMS", // or "UNSIGNED"
        debtorSurname: "Müller",
        debtor: {
          firstName: "Hans",
          surname: "Müller",
          surnamePrefix: ""
        }
      },
      iban: "DE89370400440532013000"
    }
  }
});
```

### Recurring Charge

```javascript
const recurring = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 999, currencyCode: "EUR" }
  },
  sepaDirectDebitPaymentMethodSpecificInput: {
    paymentProductId: 771,
    paymentProduct771SpecificInput: {
      existingUniqueMandateReference: mandateReference,
      recurrenceType: "RECURRING"
    }
  }
});
```

## Przelewy24 (Poland)

### Product ID: 3124

```javascript
const payment = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 4999, currencyCode: "PLN" },
    customer: {
      contactDetails: { emailAddress: "customer@example.pl" }
    }
  },
  redirectPaymentMethodSpecificInput: {
    paymentProductId: 3124,
    returnUrl: "https://..."
  }
});
```

## EPS (Austria)

### Product ID: 857

```javascript
const payment = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 4999, currencyCode: "EUR" }
  },
  redirectPaymentMethodSpecificInput: {
    paymentProductId: 857,
    returnUrl: "https://..."
  }
});
```

## TWINT (Switzerland)

### Product ID: 5407

```javascript
const payment = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 4999, currencyCode: "CHF" }
  },
  redirectPaymentMethodSpecificInput: {
    paymentProductId: 5407,
    returnUrl: "https://..."
  }
});
```

## BLIK (Poland)

### Product ID: 5706

```javascript
const payment = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 4999, currencyCode: "PLN" }
  },
  redirectPaymentMethodSpecificInput: {
    paymentProductId: 5706,
    returnUrl: "https://..."
  }
});
```

## Bizum (Spain)

### Product ID: 5001

```javascript
const payment = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 4999, currencyCode: "EUR" }
  },
  redirectPaymentMethodSpecificInput: {
    paymentProductId: 5001,
    returnUrl: "https://..."
  }
});
```

## Wero (European)

### New pan-European instant payment method

```javascript
const payment = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 4999, currencyCode: "EUR" }
  },
  redirectPaymentMethodSpecificInput: {
    paymentProductId: 5901, // Check current product ID
    returnUrl: "https://..."
  }
});
```

## Bank Transfer (Offline)

For customers who prefer traditional bank transfer.

```javascript
const payment = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 4999, currencyCode: "EUR" }
  },
  bankTransferPaymentMethodSpecificInput: {
    paymentProductId: 11 // Bank Transfer
  }
});

// Response includes bank details for customer
const bankDetails = payment.payment.paymentOutput
  .bankTransferPaymentMethodSpecificOutput;
console.log(`IBAN: ${bankDetails.paymentReference}`);
```

## By Country

| Country | Popular Methods |
|---------|----------------|
| Netherlands | iDEAL, Cards |
| Germany | SEPA DD, Cards, Klarna |
| Belgium | Bancontact, Cards |
| France | Cartes Bancaires, Cards |
| Poland | Przelewy24, BLIK |
| Austria | EPS, Cards |
| Switzerland | TWINT, Cards |
| Spain | Bizum, Cards |
| Portugal | MB Way, Multibanco |

## Hosted Checkout with Multiple Methods

```javascript
const checkout = await client.hostedCheckout.createHostedCheckout(merchantId, {
  order: {
    amountOfMoney: { amount: 4999, currencyCode: "EUR" }
  },
  hostedCheckoutSpecificInput: {
    returnUrl: "https://...",
    paymentProductFilters: {
      restrictTo: {
        products: [1, 3, 809, 5001] // Cards, iDEAL, SEPA DD
      }
    }
  }
});
```

## Best Practices

1. **Show local methods** - Increases conversion significantly
2. **Default by country** - Pre-select based on customer location
3. **Handle redirects** - Most banking methods redirect
4. **Implement webhooks** - Async payment confirmation
5. **Set timeouts** - Banking payments may take time
