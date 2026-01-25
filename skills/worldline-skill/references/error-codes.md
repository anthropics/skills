# Error Codes

Common error codes and troubleshooting for Worldline Direct API.

## HTTP Status Codes

| Code | Meaning | Action |
|------|---------|--------|
| 200 | Success | Request completed |
| 201 | Created | Resource created successfully |
| 400 | Bad Request | Check request parameters |
| 401 | Unauthorized | Check API credentials |
| 403 | Forbidden | Check merchant access permissions |
| 404 | Not Found | Check payment ID or endpoint |
| 409 | Conflict | Resource state conflict (already captured, etc.) |
| 500 | Server Error | Retry with exponential backoff |
| 502 | Bad Gateway | Temporary issue, retry |
| 503 | Service Unavailable | Temporary issue, retry |

## Common API Error Codes

### Authentication Errors

| Code | ID | Meaning | Solution |
|------|-----|---------|----------|
| 9001 | INVALID_API_KEY | API key not recognized | Check apiKeyId in credentials |
| 9002 | INVALID_SIGNATURE | HMAC signature mismatch | Check secretApiKey, verify signature algorithm |
| 9007 | ACCESS_TO_MERCHANT_NOT_ALLOWED | No access to merchant | Verify merchantId and API key permissions |

### Validation Errors

| Code | ID | Meaning | Solution |
|------|-----|---------|----------|
| 1001 | INVALID_CARD_NUMBER | Card number invalid | Check card number format |
| 1002 | INVALID_EXPIRY_DATE | Expiry date invalid | Use MMYY format (e.g., "1225") |
| 1003 | INVALID_CVV | CVV invalid | Check CVV length (3-4 digits) |
| 1004 | INVALID_AMOUNT | Amount invalid | Amount must be positive integer in cents |
| 1005 | INVALID_CURRENCY | Currency not supported | Check supported currencies |

### Payment Errors

| Code | ID | Meaning | Solution |
|------|-----|---------|----------|
| 2001 | CARD_DECLINED | Card was declined | Ask customer for different card |
| 2002 | INSUFFICIENT_FUNDS | Not enough funds | Ask customer for different card |
| 2003 | CARD_EXPIRED | Card has expired | Ask customer for valid card |
| 2004 | INVALID_CARD | Card not accepted | Check card type is supported |
| 2005 | FRAUD_SUSPECTED | Fraud detection triggered | Review transaction details |
| 2006 | 3DS_FAILED | 3D Secure authentication failed | Customer must retry |
| 2007 | 3DS_REQUIRED | 3D Secure required but not provided | Enable 3DS in request |

### Capture/Refund Errors

| Code | ID | Meaning | Solution |
|------|-----|---------|----------|
| 3001 | AMOUNT_EXCEEDS_AUTHORIZATION | Capture amount > authorized | Capture less or equal to authorized |
| 3002 | PAYMENT_ALREADY_CAPTURED | Already fully captured | No action needed |
| 3003 | PAYMENT_ALREADY_CANCELLED | Payment was cancelled | Cannot capture cancelled payment |
| 3004 | AUTHORIZATION_EXPIRED | Authorization has expired | Create new payment |
| 3005 | REFUND_EXCEEDS_CAPTURED | Refund > captured amount | Refund less or equal to captured |

### Token Errors

| Code | ID | Meaning | Solution |
|------|-----|---------|----------|
| 4001 | TOKEN_NOT_FOUND | Token doesn't exist | Check token value |
| 4002 | TOKEN_EXPIRED | Token has expired | Request new card from customer |
| 4003 | TOKEN_INVALID | Token is invalid | Request new card from customer |

## Error Response Format

```json
{
  "errorId": "unique-error-id",
  "errors": [
    {
      "code": "1001",
      "id": "INVALID_CARD_NUMBER",
      "category": "DIRECT_PLATFORM_ERROR",
      "message": "Card number is invalid",
      "httpStatusCode": 400,
      "propertyName": "cardPaymentMethodSpecificInput.card.cardNumber"
    }
  ]
}
```

## Error Handling Example

```javascript
try {
  const payment = await client.payments.createPayment(merchantId, paymentRequest);
  return { success: true, payment };
} catch (error) {
  // HTTP errors
  if (error.statusCode === 400) {
    const errorCode = error.body?.errors?.[0]?.code;
    const errorId = error.body?.errors?.[0]?.id;

    switch (errorId) {
      case 'INVALID_CARD_NUMBER':
        return { success: false, message: 'Invalid card number' };
      case 'CARD_DECLINED':
        return { success: false, message: 'Card was declined' };
      case 'INSUFFICIENT_FUNDS':
        return { success: false, message: 'Insufficient funds' };
      default:
        return { success: false, message: 'Payment failed', errorCode };
    }
  }

  if (error.statusCode === 401 || error.statusCode === 403) {
    console.error('Authentication error - check API credentials');
    throw error;
  }

  if (error.statusCode >= 500) {
    // Retry with exponential backoff
    console.error('Server error - will retry');
    throw error;
  }

  throw error;
}
```

## Python Error Handling

```python
from onlinepayments.sdk.declined_payment_exception import DeclinedPaymentException
from onlinepayments.sdk.api_exception import ApiException

try:
    payment = client.merchant(merchant_id).payments().create_payment(request)
    return {"success": True, "payment": payment}

except DeclinedPaymentException as e:
    # Payment was declined
    error = e.errors[0] if e.errors else None
    return {
        "success": False,
        "declined": True,
        "error_code": error.code if error else None,
        "message": error.message if error else "Payment declined"
    }

except ApiException as e:
    # API error
    if e.status_code == 400:
        error = e.errors[0] if e.errors else None
        return {
            "success": False,
            "error_code": error.code if error else None,
            "message": error.message if error else "Invalid request"
        }
    raise
```

## Retry Strategy

For transient errors (5xx), implement exponential backoff:

```javascript
async function withRetry(fn, maxRetries = 3) {
  let lastError;

  for (let attempt = 0; attempt < maxRetries; attempt++) {
    try {
      return await fn();
    } catch (error) {
      lastError = error;

      // Only retry on server errors
      if (error.statusCode < 500) {
        throw error;
      }

      // Exponential backoff: 1s, 2s, 4s
      const delay = Math.pow(2, attempt) * 1000;
      await new Promise(resolve => setTimeout(resolve, delay));
    }
  }

  throw lastError;
}

// Usage
const payment = await withRetry(() =>
  client.payments.createPayment(merchantId, request)
);
```

## Idempotency

Use unique `merchantReference` to prevent duplicate payments:

```javascript
const payment = await client.payments.createPayment(merchantId, {
  order: {
    references: {
      merchantReference: `order-${orderId}-${timestamp}` // Unique per attempt
    }
  }
});
```

## Getting Help

- Error ID in response helps Worldline support trace issues
- Include `errorId` when contacting support
- Check logs in Merchant Portal for detailed error info
- API Reference: https://docs.direct.worldline-solutions.com/en/api-reference
