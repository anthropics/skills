# Hosted Tokenization Page Integration

Embed a secure payment form (iFrame) in your checkout while maintaining PCI compliance (SAQ-A-EP).

## How It Works

1. Load Worldline's JavaScript SDK on your page
2. SDK creates a secure iFrame for card input
3. Card data is sent directly to Worldline (never touches your server)
4. You receive a token to complete the payment server-side

## Benefits

- **Full UI control** - Design your own checkout page
- **Low PCI scope** - Card data stays in iFrame
- **Better UX** - No redirect, seamless flow
- **All card features** - 3DS, tokenization, etc.

## Implementation

### 1. Include JavaScript SDK

```html
<script src="https://payment.preprod.direct.worldline-solutions.com/hostedtokenization/js/client/tokenizer.min.js"></script>
```

### 2. Create Payment Form

```html
<form id="payment-form">
  <div id="card-container">
    <!-- iFrame will be inserted here -->
  </div>

  <button type="submit" id="pay-button">Pay €49.99</button>
</form>
```

### 3. Initialize Tokenizer

```javascript
// Get session from your server first
const sessionResponse = await fetch('/api/create-tokenization-session', {
  method: 'POST',
  body: JSON.stringify({ amount: 4999, currency: 'EUR' })
});
const session = await sessionResponse.json();

// Initialize tokenizer
const tokenizer = new Tokenizer({
  sessionId: session.sessionId,
  clientApiUrl: 'https://payment.preprod.direct.worldline-solutions.com/client',
  paymentProductId: 1, // Visa (or let user select)
  tokenize: true
});

// Render card input fields
tokenizer.renderPaymentProductField(
  document.getElementById('card-container'),
  'encryptedCardNumber',
  { placeholder: 'Card number' }
);
```

### 4. Create Tokenization Session (Server)

```javascript
app.post('/api/create-tokenization-session', async (req, res) => {
  const { amount, currency } = req.body;

  const session = await client.sessions.createSession(merchantId, {
    tokens: [],
    paymentProductId: 1 // Optional: restrict to specific product
  });

  res.json({
    sessionId: session.clientSessionId,
    customerId: session.customerId,
    assetUrl: session.assetUrl
  });
});
```

### 5. Handle Form Submission

```javascript
document.getElementById('payment-form').addEventListener('submit', async (e) => {
  e.preventDefault();

  const button = document.getElementById('pay-button');
  button.disabled = true;
  button.textContent = 'Processing...';

  try {
    // Tokenize card data
    const result = await tokenizer.submitTokenization();

    if (result.success) {
      // Send token to your server
      const payment = await fetch('/api/process-payment', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          token: result.hostedTokenizationId,
          amount: 4999,
          currency: 'EUR'
        })
      });

      const paymentResult = await payment.json();

      if (paymentResult.requires3DS) {
        // Redirect for 3DS
        window.location.href = paymentResult.redirectUrl;
      } else if (paymentResult.success) {
        window.location.href = '/order/success';
      } else {
        showError('Payment failed');
      }
    } else {
      showError(result.error.message);
    }
  } catch (error) {
    showError('An error occurred');
  } finally {
    button.disabled = false;
    button.textContent = 'Pay €49.99';
  }
});
```

### 6. Process Payment (Server)

```javascript
app.post('/api/process-payment', async (req, res) => {
  const { token, amount, currency, orderId } = req.body;

  // Get tokenization result
  const tokenResult = await client.hostedTokenization.getHostedTokenization(
    merchantId,
    token
  );

  if (tokenResult.token) {
    // Create payment with token
    const payment = await client.payments.createPayment(merchantId, {
      order: {
        amountOfMoney: { amount, currencyCode: currency },
        references: { merchantReference: orderId }
      },
      cardPaymentMethodSpecificInput: {
        token: tokenResult.token.id,
        authorizationMode: 'SALE',
        threeDSecure: {
          redirectionData: {
            returnUrl: `https://yoursite.com/3ds/complete?orderId=${orderId}`
          }
        }
      }
    });

    if (payment.merchantAction?.actionType === 'REDIRECT') {
      return res.json({
        requires3DS: true,
        redirectUrl: payment.merchantAction.redirectData.redirectURL
      });
    }

    if (payment.payment.status === 'CAPTURED') {
      return res.json({ success: true, paymentId: payment.payment.id });
    }
  }

  res.json({ success: false, error: 'Payment failed' });
});
```

## Styling the iFrame

```javascript
tokenizer.renderPaymentProductField(container, 'encryptedCardNumber', {
  placeholder: 'Card number',
  style: {
    input: {
      fontSize: '16px',
      fontFamily: 'Arial, sans-serif',
      color: '#333',
      backgroundColor: '#fff'
    },
    focus: {
      borderColor: '#0066cc'
    },
    error: {
      borderColor: '#cc0000'
    }
  }
});
```

## Multiple Card Fields

```html
<div id="card-number-container"></div>
<div id="expiry-container"></div>
<div id="cvv-container"></div>
<div id="cardholder-container"></div>
```

```javascript
tokenizer.renderPaymentProductField(
  document.getElementById('card-number-container'),
  'encryptedCardNumber',
  { placeholder: 'Card number' }
);

tokenizer.renderPaymentProductField(
  document.getElementById('expiry-container'),
  'encryptedExpiryDate',
  { placeholder: 'MM/YY' }
);

tokenizer.renderPaymentProductField(
  document.getElementById('cvv-container'),
  'encryptedCvv',
  { placeholder: 'CVV' }
);

tokenizer.renderPaymentProductField(
  document.getElementById('cardholder-container'),
  'cardholderName',
  { placeholder: 'Name on card' }
);
```

## Card Type Detection

```javascript
tokenizer.on('cardTypeChanged', (event) => {
  console.log('Card type:', event.paymentProductId);
  // 1 = Visa, 3 = Mastercard, etc.

  // Update card logo
  document.getElementById('card-logo').src = event.logoUrl;
});
```

## Validation

```javascript
tokenizer.on('validationResult', (event) => {
  if (!event.valid) {
    event.errors.forEach(error => {
      console.log(`Field ${error.fieldId}: ${error.message}`);
    });
  }
});
```

## Co-Badged Cards

Handle cards with multiple networks (e.g., Cartes Bancaires + Visa).

```javascript
tokenizer.on('cobadgedCards', (event) => {
  // Let user choose network
  const networks = event.paymentProductIds;
  // Display network selection UI
});
```

## Store Token for Future Use

```javascript
const payment = await client.payments.createPayment(merchantId, {
  order: { amountOfMoney: { amount: 4999, currencyCode: 'EUR' } },
  cardPaymentMethodSpecificInput: {
    token: tokenResult.token.id,
    tokenize: true, // Create permanent token
    authorizationMode: 'SALE'
  }
});

// Store permanent token for future charges
const permanentToken = payment.payment.paymentOutput
  .cardPaymentMethodSpecificOutput.token;
```

## Best Practices

1. **Progressive enhancement** - Have fallback for old browsers
2. **Clear error messages** - Show validation inline
3. **Loading states** - Disable button during processing
4. **Responsive design** - iFrame adapts to container
5. **Test on mobile** - Keyboard behavior differs
6. **Session timeout** - Sessions expire after 25 minutes
