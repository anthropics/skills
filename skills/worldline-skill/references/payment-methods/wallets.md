# Digital Wallets

Apple Pay, Google Pay, PayPal, and Click to Pay integration.

## Apple Pay

### Product ID: 302

### Hosted Checkout

```javascript
const checkout = await client.hostedCheckout.createHostedCheckout(merchantId, {
  order: {
    amountOfMoney: { amount: 4999, currencyCode: "EUR" }
  },
  hostedCheckoutSpecificInput: {
    returnUrl: "https://...",
    paymentProductFilters: {
      restrictTo: {
        products: [302] // Apple Pay only
      }
    }
  }
});
```

### Native iOS Integration

```swift
import PassKit

// 1. Check availability
if PKPaymentAuthorizationViewController.canMakePayments(usingNetworks: [.visa, .masterCard]) {
    // Apple Pay available
}

// 2. Create payment request
let request = PKPaymentRequest()
request.merchantIdentifier = "merchant.com.yourapp"
request.supportedNetworks = [.visa, .masterCard, .amex]
request.merchantCapabilities = .capability3DS
request.countryCode = "NL"
request.currencyCode = "EUR"
request.paymentSummaryItems = [
    PKPaymentSummaryItem(label: "Your Product", amount: NSDecimalNumber(string: "49.99"))
]

// 3. Present Apple Pay sheet
let controller = PKPaymentAuthorizationViewController(paymentRequest: request)
controller?.delegate = self
present(controller!, animated: true)

// 4. Handle authorization
func paymentAuthorizationViewController(_ controller: PKPaymentAuthorizationViewController,
    didAuthorizePayment payment: PKPayment,
    handler: @escaping (PKPaymentAuthorizationResult) -> Void) {

    // Send token to server
    let tokenData = payment.token.paymentData.base64EncodedString()
    sendToServer(tokenData) { success in
        handler(PKPaymentAuthorizationResult(status: success ? .success : .failure, errors: nil))
    }
}
```

### Server-Side Processing

```javascript
app.post("/api/apple-pay", async (req, res) => {
  const { paymentData, orderId } = req.body;

  const payment = await client.payments.createPayment(merchantId, {
    order: {
      amountOfMoney: { amount: 4999, currencyCode: "EUR" },
      references: { merchantReference: orderId }
    },
    mobilePaymentMethodSpecificInput: {
      paymentProductId: 302,
      authorizationMode: "SALE",
      encryptedPaymentData: paymentData
    }
  });

  res.json({ success: payment.payment.status === "CAPTURED" });
});
```

## Google Pay

### Product ID: 320

### Web Integration

```html
<script src="https://pay.google.com/gp/p/js/pay.js"></script>
```

```javascript
// 1. Initialize
const paymentsClient = new google.payments.api.PaymentsClient({
  environment: 'TEST' // or 'PRODUCTION'
});

// 2. Check availability
const isReadyToPayRequest = {
  apiVersion: 2,
  apiVersionMinor: 0,
  allowedPaymentMethods: [{
    type: 'CARD',
    parameters: {
      allowedAuthMethods: ['PAN_ONLY', 'CRYPTOGRAM_3DS'],
      allowedCardNetworks: ['VISA', 'MASTERCARD']
    }
  }]
};

const response = await paymentsClient.isReadyToPay(isReadyToPayRequest);
if (response.result) {
  // Show Google Pay button
}

// 3. Request payment
const paymentDataRequest = {
  apiVersion: 2,
  apiVersionMinor: 0,
  allowedPaymentMethods: [{
    type: 'CARD',
    parameters: {
      allowedAuthMethods: ['PAN_ONLY', 'CRYPTOGRAM_3DS'],
      allowedCardNetworks: ['VISA', 'MASTERCARD']
    },
    tokenizationSpecification: {
      type: 'PAYMENT_GATEWAY',
      parameters: {
        gateway: 'worldlinedirect',
        gatewayMerchantId: merchantId
      }
    }
  }],
  merchantInfo: {
    merchantName: 'Your Store'
  },
  transactionInfo: {
    totalPriceStatus: 'FINAL',
    totalPrice: '49.99',
    currencyCode: 'EUR',
    countryCode: 'NL'
  }
};

const paymentData = await paymentsClient.loadPaymentData(paymentDataRequest);
// Send paymentData.paymentMethodData.tokenizationData.token to server
```

### Server-Side Processing

```javascript
app.post("/api/google-pay", async (req, res) => {
  const { token, orderId } = req.body;

  const payment = await client.payments.createPayment(merchantId, {
    order: {
      amountOfMoney: { amount: 4999, currencyCode: "EUR" },
      references: { merchantReference: orderId }
    },
    mobilePaymentMethodSpecificInput: {
      paymentProductId: 320,
      authorizationMode: "SALE",
      encryptedPaymentData: token
    }
  });

  res.json({ success: payment.payment.status === "CAPTURED" });
});
```

## PayPal

### Product ID: 840

### Hosted Checkout (Recommended)

```javascript
const checkout = await client.hostedCheckout.createHostedCheckout(merchantId, {
  order: {
    amountOfMoney: { amount: 4999, currencyCode: "EUR" }
  },
  hostedCheckoutSpecificInput: {
    returnUrl: "https://yoursite.com/checkout/complete",
    paymentProductFilters: {
      restrictTo: {
        products: [840]
      }
    }
  },
  redirectPaymentMethodSpecificInput: {
    paymentProductId: 840,
    paymentProduct840SpecificInput: {
      addressSelectionAtPayPal: true // Let customer choose address in PayPal
    }
  }
});
```

### Server-to-Server

```javascript
const payment = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 4999, currencyCode: "EUR" },
    references: { merchantReference: orderId }
  },
  redirectPaymentMethodSpecificInput: {
    paymentProductId: 840,
    returnUrl: "https://yoursite.com/paypal/return",
    paymentProduct840SpecificInput: {
      addressSelectionAtPayPal: true
    }
  }
});

// Redirect to PayPal
if (payment.merchantAction?.actionType === "REDIRECT") {
  res.redirect(payment.merchantAction.redirectData.redirectURL);
}
```

## Click to Pay

### Product ID: 3203

Visa's and Mastercard's unified checkout experience.

```javascript
const checkout = await client.hostedCheckout.createHostedCheckout(merchantId, {
  order: {
    amountOfMoney: { amount: 4999, currencyCode: "EUR" }
  },
  hostedCheckoutSpecificInput: {
    paymentProductFilters: {
      restrictTo: {
        products: [3203]
      }
    }
  }
});
```

## MB Way

### Product ID: 5500

Popular in Portugal.

```javascript
const payment = await client.payments.createPayment(merchantId, {
  order: {
    amountOfMoney: { amount: 4999, currencyCode: "EUR" }
  },
  redirectPaymentMethodSpecificInput: {
    paymentProductId: 5500,
    returnUrl: "https://...",
    paymentProduct5500SpecificInput: {
      phoneNumber: "+351912345678"
    }
  }
});
```

## Comparison

| Wallet | Regions | UX | Tokenization |
|--------|---------|-----|--------------|
| Apple Pay | Global | In-app, web | Network tokens |
| Google Pay | Global | Web, Android | Network tokens |
| PayPal | Global | Redirect | PayPal account |
| Click to Pay | Global | Embedded | Card networks |
| MB Way | Portugal | Mobile push | - |

## Best Practices

1. **Show wallet buttons prominently** - Higher conversion
2. **Check availability first** - Only show if supported
3. **Use Hosted Checkout** - Easiest integration
4. **Test on real devices** - Emulators may not work
5. **Handle all responses** - Success, cancel, error
6. **Express checkout** - Skip address entry
