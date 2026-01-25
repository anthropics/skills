# Hosted Checkout Page Integration

The simplest integration method with lowest PCI scope (SAQ-A).

## How It Works

1. Your server creates a hosted checkout session
2. Customer is redirected to Worldline's payment page
3. Customer completes payment on Worldline's secure page
4. Customer is redirected back to your site with result

## Benefits

- **Lowest PCI scope** - Card data never touches your servers
- **All payment methods** - Cards, iDEAL, PayPal, Klarna, etc.
- **Built-in 3DS** - SCA compliance handled automatically
- **Mobile optimized** - Responsive design
- **Customizable** - Match your brand with templates

## Basic Implementation

### Create Hosted Checkout Session

```javascript
const { default: OnlinePayments } = require("onlinepayments-sdk-nodejs");

const client = OnlinePayments.init({
  host: "payment.preprod.direct.worldline-solutions.com",
  apiKeyId: process.env.WORLDLINE_API_KEY,
  secretApiKey: process.env.WORLDLINE_SECRET_KEY
});

const merchantId = process.env.WORLDLINE_MERCHANT_ID;

async function createCheckout(order) {
  const response = await client.hostedCheckout.createHostedCheckout(merchantId, {
    order: {
      amountOfMoney: {
        amount: order.totalCents, // Amount in cents
        currencyCode: "EUR"
      },
      customer: {
        merchantCustomerId: order.customerId,
        billingAddress: {
          street: order.address.street,
          city: order.address.city,
          countryCode: order.address.country,
          zip: order.address.postalCode
        }
      },
      references: {
        merchantReference: order.id // Your order ID
      }
    },
    hostedCheckoutSpecificInput: {
      returnUrl: `https://yoursite.com/checkout/complete?orderId=${order.id}`,
      showResultPage: false, // Return immediately to your site
      locale: "en_GB"
    }
  });

  return {
    checkoutId: response.hostedCheckoutId,
    redirectUrl: `https://payment.preprod.direct.worldline-solutions.com/hostedcheckout/${response.hostedCheckoutId}`,
    returnMac: response.RETURNMAC
  };
}
```

### Redirect Customer

```javascript
// Express route
app.post("/checkout/start", async (req, res) => {
  const order = await createOrder(req.body);
  const checkout = await createCheckout(order);

  // Store for verification later
  await storeCheckoutSession(order.id, checkout);

  // Redirect to Worldline
  res.redirect(checkout.redirectUrl);
});
```

### Handle Return

```javascript
app.get("/checkout/complete", async (req, res) => {
  const { orderId, RETURNMAC, hostedCheckoutId } = req.query;

  // Verify RETURNMAC matches
  const stored = await getCheckoutSession(orderId);
  if (RETURNMAC !== stored.returnMac) {
    return res.status(400).send("Invalid return");
  }

  // Get payment status
  const status = await client.hostedCheckout.getHostedCheckoutStatus(
    merchantId,
    hostedCheckoutId
  );

  if (status.status === "PAYMENT_CREATED") {
    const paymentStatus = status.createdPaymentOutput.payment.status;

    if (paymentStatus === "CAPTURED" || paymentStatus === "PENDING_CAPTURE") {
      await markOrderPaid(orderId, status.createdPaymentOutput.payment.id);
      return res.redirect(`/order/${orderId}/success`);
    }
  }

  return res.redirect(`/order/${orderId}/failed`);
});
```

## Filtering Payment Methods

Show only specific payment methods.

```javascript
hostedCheckoutSpecificInput: {
  paymentProductFilters: {
    restrictTo: {
      products: [1, 3, 809, 840, 3012] // Visa, MC, iDEAL, PayPal, Klarna
    }
  }
}
```

### Common Product IDs

| ID | Payment Method |
|----|---------------|
| 1 | Visa |
| 3 | Mastercard |
| 117 | Maestro |
| 125 | JCB |
| 130 | Carte Bancaire |
| 132 | Diners |
| 302 | Apple Pay |
| 320 | Google Pay |
| 809 | iDEAL |
| 840 | PayPal |
| 3012 | Klarna |
| 5001 | SEPA Direct Debit |

## Customization

### Locale Settings

```javascript
hostedCheckoutSpecificInput: {
  locale: "nl_NL", // Dutch
  // Or let Worldline detect from browser
  // locale: undefined
}
```

### Template Customization

Configure in Merchant Portal > Configuration > Template Customization.

```javascript
hostedCheckoutSpecificInput: {
  variant: "your-template-name" // Custom template
}
```

## Card-on-File with Hosted Checkout

Store card for future use.

```javascript
hostedCheckoutSpecificInput: {
  returnUrl: "https://...",
  cardPaymentMethodSpecificInput: {
    tokenize: true,
    authorizationMode: "SALE"
  }
}
```

Access the token in the response:
```javascript
const token = status.createdPaymentOutput.payment.paymentOutput
  .cardPaymentMethodSpecificOutput.token;
```

## Pre-Authorization

For hotels, car rental, etc.

```javascript
hostedCheckoutSpecificInput: {
  cardPaymentMethodSpecificInput: {
    authorizationMode: "PRE_AUTHORIZATION"
  }
}
```

## Shipping Address Collection

```javascript
order: {
  customer: {
    billingAddress: { ... },
  },
  shipping: {
    address: {
      street: "123 Ship St",
      city: "Amsterdam",
      countryCode: "NL",
      zip: "1011AB"
    }
  }
}
```

## Status Checking

### Hosted Checkout Status

```javascript
const status = await client.hostedCheckout.getHostedCheckoutStatus(
  merchantId,
  hostedCheckoutId
);

// Possible status values:
// - PAYMENT_CREATED: Payment was completed
// - IN_PROGRESS: Customer is still on payment page
// - CANCELLED_BY_CONSUMER: Customer cancelled
// - CLIENT_NOT_ELIGIBLE_FOR_SELECTED_PAYMENT_PRODUCT: Payment method unavailable
```

### Payment Status

After `PAYMENT_CREATED`, check the payment status:

```javascript
const paymentId = status.createdPaymentOutput.payment.id;
const paymentStatus = status.createdPaymentOutput.payment.status;

// Common values:
// - CAPTURED: Funds collected
// - PENDING_CAPTURE: Authorized, needs capture
// - PENDING_APPROVAL: Waiting for 3DS
// - REJECTED: Payment failed
```

## Error Handling

```javascript
try {
  const response = await client.hostedCheckout.createHostedCheckout(...);
} catch (error) {
  if (error.statusCode === 400) {
    console.error("Invalid request:", error.body.errors);
  } else if (error.statusCode === 401) {
    console.error("Authentication failed - check API keys");
  } else {
    console.error("Unexpected error:", error);
  }
}
```

## Webhooks

Don't rely solely on the redirect. Implement webhooks for reliability.

```javascript
app.post("/webhooks/worldline", async (req, res) => {
  // Verify signature (see webhooks.md)

  const event = req.body;

  if (event.payment) {
    const merchantRef = event.payment.paymentOutput.references.merchantReference;
    const status = event.payment.status;

    if (status === "CAPTURED") {
      await markOrderPaid(merchantRef);
    } else if (status === "REJECTED" || status === "CANCELLED") {
      await markOrderFailed(merchantRef);
    }
  }

  res.status(200).send("OK");
});
```

## Testing

Use sandbox environment:
- Host: `payment.preprod.direct.worldline-solutions.com`
- Test cards: See [test-cards.md](../test-cards.md)

## Best Practices

1. **Store RETURNMAC** - Verify on return to prevent tampering
2. **Implement webhooks** - Redirect can fail
3. **Use unique merchant references** - Link to your order ID
4. **Set showResultPage: false** - Control the experience
5. **Filter payment methods** - Show relevant options only
6. **Handle all statuses** - Success, failure, pending
7. **Log everything** - For debugging and compliance
