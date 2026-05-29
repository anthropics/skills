# Buy Now Pay Later (BNPL)

Klarna, in3, and installment payment options.

## Klarna

### Product ID: 3012

### Klarna Pay Later

Customer pays within 14-30 days.

```javascript
const payment = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 9999, currencyCode: "EUR" },
    customer: {
      billingAddress: {
        street: "123 Main St",
        city: "Amsterdam",
        countryCode: "NL",
        zip: "1011AB"
      },
      contactDetails: {
        emailAddress: "customer@example.com",
        phoneNumber: "+31612345678"
      }
    },
    shoppingCart: {
      items: [
        {
          amountOfMoney: { amount: 9999, currencyCode: "EUR" },
          invoiceData: {
            description: "Product Name",
            nrOfItems: 1,
            pricePerItem: 9999
          }
        }
      ]
    }
  },
  redirectPaymentMethodSpecificInput: {
    paymentProductId: 3012,
    returnUrl: "https://yoursite.com/payment/complete",
    paymentProduct3012SpecificInput: {
      // Klarna-specific options
    }
  }
});

if (payment.merchantAction?.actionType === "REDIRECT") {
  res.redirect(payment.merchantAction.redirectData.redirectURL);
}
```

### Klarna Pay in 3

Split into 3 interest-free payments.

```javascript
redirectPaymentMethodSpecificInput: {
  paymentProductId: 3012,
  returnUrl: "https://...",
  paymentProduct3012SpecificInput: {
    paymentOption: "pay_in_3"
  }
}
```

### Klarna Financing

Longer-term financing with interest.

```javascript
redirectPaymentMethodSpecificInput: {
  paymentProductId: 3012,
  returnUrl: "https://...",
  paymentProduct3012SpecificInput: {
    paymentOption: "financing"
  }
}
```

## in3

### Product ID: 3107

Popular in Netherlands - pay in 3 installments.

```javascript
const payment = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 15000, currencyCode: "EUR" }, // Min €100
    customer: {
      billingAddress: {
        street: "Kalverstraat 1",
        city: "Amsterdam",
        countryCode: "NL",
        zip: "1012PA"
      },
      personalInformation: {
        dateOfBirth: "19900115",
        gender: "male",
        name: {
          firstName: "Jan",
          surname: "Jansen"
        }
      },
      contactDetails: {
        emailAddress: "jan@example.nl",
        phoneNumber: "+31612345678"
      }
    },
    shoppingCart: {
      items: [
        {
          amountOfMoney: { amount: 15000, currencyCode: "EUR" },
          invoiceData: {
            description: "Electronics Bundle",
            nrOfItems: 1,
            pricePerItem: 15000
          }
        }
      ]
    }
  },
  redirectPaymentMethodSpecificInput: {
    paymentProductId: 3107,
    returnUrl: "https://yoursite.com/payment/complete"
  }
});
```

## French Installment Options

### Oney 3x/4x (Product ID: 5110)

```javascript
const payment = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 29999, currencyCode: "EUR" },
    customer: {
      billingAddress: {
        street: "1 Rue de la Paix",
        city: "Paris",
        countryCode: "FR",
        zip: "75001"
      }
    }
  },
  redirectPaymentMethodSpecificInput: {
    paymentProductId: 5110,
    returnUrl: "https://..."
  }
});
```

### Sofinco 3x-24x (Product ID: 5100)

Long-term financing in France.

```javascript
redirectPaymentMethodSpecificInput: {
  paymentProductId: 5100,
  returnUrl: "https://..."
}
```

### Cofidis 3x/4x (Product ID: 5104)

```javascript
redirectPaymentMethodSpecificInput: {
  paymentProductId: 5104,
  returnUrl: "https://..."
}
```

## Hosted Checkout with BNPL

Show BNPL alongside cards:

```javascript
const checkout = await client.hostedCheckout.createHostedCheckout(merchantId, {
  order: {
    amountOfMoney: { amount: 15000, currencyCode: "EUR" },
    customer: {
      billingAddress: {
        street: "123 Main St",
        city: "Amsterdam",
        countryCode: "NL",
        zip: "1011AB"
      }
    },
    shoppingCart: {
      items: [
        {
          amountOfMoney: { amount: 15000, currencyCode: "EUR" },
          invoiceData: {
            description: "Product Bundle",
            nrOfItems: 1,
            pricePerItem: 15000
          }
        }
      ]
    }
  },
  hostedCheckoutSpecificInput: {
    returnUrl: "https://...",
    paymentProductFilters: {
      restrictTo: {
        products: [1, 3, 3012, 3107] // Cards, Klarna, in3
      }
    }
  }
});
```

## Shopping Cart (Required for BNPL)

BNPL providers require detailed cart information:

```javascript
shoppingCart: {
  items: [
    {
      amountOfMoney: { amount: 5999, currencyCode: "EUR" },
      invoiceData: {
        description: "Blue T-Shirt Size M",
        nrOfItems: 2,
        pricePerItem: 2999,
        merchantLinenumber: "1"
      }
    },
    {
      amountOfMoney: { amount: 3000, currencyCode: "EUR" },
      invoiceData: {
        description: "Jeans Size 32",
        nrOfItems: 1,
        pricePerItem: 3000,
        merchantLinenumber: "2"
      }
    },
    {
      amountOfMoney: { amount: 500, currencyCode: "EUR" },
      invoiceData: {
        description: "Shipping",
        nrOfItems: 1,
        pricePerItem: 500,
        merchantLinenumber: "3"
      }
    }
  ]
}
```

## Refunds

BNPL refunds follow the same pattern:

```javascript
await client.payments.refundPayment(merchantId, paymentId, {
  amountOfMoney: { amount: 5999, currencyCode: "EUR" },
  // BNPL provider handles installment adjustment
});
```

## Minimum/Maximum Amounts

| Provider | Min | Max | Countries |
|----------|-----|-----|-----------|
| Klarna | €1 | €10,000 | EU-wide |
| in3 | €100 | €3,000 | Netherlands |
| Oney 3x4x | €50 | €6,000 | France |
| Sofinco | €150 | €6,000 | France |

## Risk Assessment

BNPL providers do their own risk assessment:
- Customer may be declined even with valid request
- Provide accurate customer data
- Include complete cart details
- Real phone and email required

## Best Practices

1. **Show cart details** - Required for approval
2. **Accurate customer data** - Name, address, phone, email
3. **Minimum amounts** - Check provider limits
4. **Handle declines** - Offer alternative payment
5. **Order value display** - Show total and installment amounts
6. **Terms disclosure** - Link to BNPL provider terms
