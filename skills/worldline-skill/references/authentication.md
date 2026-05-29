# Authentication

How to authenticate with the Worldline Direct API.

## Credentials

You need three pieces of information:

| Credential | Description | Where to Find |
|------------|-------------|---------------|
| **PSPID** | Your merchant identifier | Merchant Portal |
| **API Key** | Public key for identification | Developer > Payment API |
| **API Secret** | Private key for signing | Generated once, save it! |

## SDK Authentication (Recommended)

The SDK handles authentication automatically:

```javascript
const client = OnlinePayments.init({
  host: "payment.preprod.direct.worldline-solutions.com",
  apiKeyId: process.env.WORLDLINE_API_KEY,
  secretApiKey: process.env.WORLDLINE_SECRET_KEY
});
```

That's it! All requests are automatically signed.

## Manual Authentication

If you're not using an SDK, you must sign requests yourself.

### Request Signature

Each request requires an `Authorization` header:

```
Authorization: GCS v1HMAC:{apiKeyId}:{signature}
```

### Signature Calculation

1. Create the string to sign
2. Calculate HMAC-SHA256
3. Base64 encode the result

### String to Sign Format

```
{METHOD}\n
{Content-Type}\n
{Date}\n
{canonicalizedHeaders}\n
{canonicalizedResource}
```

### Example: POST Request

```javascript
const crypto = require("crypto");

function calculateSignature(method, contentType, date, path, secretKey) {
  const stringToSign = [
    method,
    contentType || "",
    date,
    path
  ].join("\n");

  const hmac = crypto.createHmac("sha256", secretKey);
  hmac.update(stringToSign);
  return hmac.digest("base64");
}

// Usage
const method = "POST";
const contentType = "application/json";
const date = new Date().toUTCString(); // RFC 1123 format
const path = `/v2/${merchantId}/payments`;
const secretKey = process.env.WORLDLINE_SECRET_KEY;

const signature = calculateSignature(method, contentType, date, path, secretKey);

const headers = {
  "Authorization": `GCS v1HMAC:${apiKeyId}:${signature}`,
  "Date": date,
  "Content-Type": contentType
};
```

### Example: GET Request

```javascript
const method = "GET";
const contentType = ""; // No content type for GET
const date = new Date().toUTCString();
const path = `/v2/${merchantId}/payments/${paymentId}`;

const stringToSign = `${method}\n\n${date}\n${path}`;
const signature = calculateSignature(stringToSign, secretKey);

const headers = {
  "Authorization": `GCS v1HMAC:${apiKeyId}:${signature}`,
  "Date": date
};
```

## Required Headers

| Header | Required | Description |
|--------|----------|-------------|
| `Authorization` | Yes | GCS signature |
| `Date` | Yes | RFC 1123 format |
| `Content-Type` | POST/PUT | `application/json` |

## API Key Management

### Create New Key

1. Merchant Portal > Developer > Payment API
2. Click "Generate new API key"
3. **Save the secret immediately** - it's only shown once!

### Key Expiration

- API keys expire **1 year** after creation
- Create a new key before expiration
- Update your application with new credentials
- Delete old key after migration

### Key Rotation

```javascript
// Recommended: Use environment variables for easy rotation
const apiKeyId = process.env.WORLDLINE_API_KEY;
const secretKey = process.env.WORLDLINE_SECRET_KEY;

// Or use a secrets manager
const secrets = await secretsManager.getSecret("worldline-credentials");
```

## IP Whitelisting (Optional)

Restrict API access to specific IPs:

1. Merchant Portal > Developer > Payment API
2. Add allowed IP addresses
3. Enable IP filtering

## Testing Authentication

```bash
# Test with curl
curl -X GET \
  -H "Authorization: GCS v1HMAC:YOUR_API_KEY:YOUR_SIGNATURE" \
  -H "Date: $(date -u +"%a, %d %b %Y %H:%M:%S GMT")" \
  "https://payment.preprod.direct.worldline-solutions.com/v2/YOUR_PSPID/services/testconnection"
```

## Common Errors

### 401 Unauthorized

```json
{
  "errorId": "...",
  "errors": [{
    "code": "UNAUTHORIZED",
    "message": "Invalid authorization"
  }]
}
```

**Causes:**
- Invalid API key
- Incorrect signature calculation
- Wrong secret key
- Clock skew (Date header too old)

### Clock Skew

The `Date` header must be within 15 minutes of server time:

```javascript
// Ensure system clock is synchronized
const date = new Date().toUTCString();
// Should be: "Wed, 15 Jan 2025 10:30:00 GMT"
```

## Webhook Authentication

Webhooks use a different authentication mechanism:

```javascript
const crypto = require("crypto");

function verifyWebhookSignature(payload, signature, keyId, secret) {
  const expectedSignature = crypto
    .createHmac("sha256", secret)
    .update(payload)
    .digest("base64");

  return crypto.timingSafeEqual(
    Buffer.from(signature),
    Buffer.from(expectedSignature)
  );
}

app.post("/webhooks/worldline", (req, res) => {
  const signature = req.headers["x-gcs-signature"];
  const keyId = req.headers["x-gcs-keyid"];

  if (!verifyWebhookSignature(req.rawBody, signature, keyId, webhookSecret)) {
    return res.status(401).send("Invalid signature");
  }

  // Process webhook
  res.status(200).send("OK");
});
```

## Security Best Practices

1. **Never commit secrets** - Use environment variables
2. **Rotate keys annually** - Before they expire
3. **Use HTTPS only** - Required for all API calls
4. **Validate webhooks** - Always verify signatures
5. **Limit access** - Use IP whitelisting if possible
6. **Audit logs** - Monitor API usage in Merchant Portal
