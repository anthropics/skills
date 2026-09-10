# SDK Setup

Official server SDKs for Worldline Direct.

## Node.js

### Installation

```bash
npm install onlinepayments-sdk-nodejs
```

### Configuration

```javascript
const { default: OnlinePayments } = require("onlinepayments-sdk-nodejs");

const client = OnlinePayments.init({
  host: "payment.preprod.direct.worldline-solutions.com", // Sandbox
  // host: "payment.direct.worldline-solutions.com", // Production
  apiKeyId: process.env.WORLDLINE_API_KEY,
  secretApiKey: process.env.WORLDLINE_SECRET_KEY,
  integrator: "YourCompany"
});

const merchantId = process.env.WORLDLINE_MERCHANT_ID;
```

### Usage Example

```javascript
async function createPayment() {
  const response = await client.payments.createPayment(merchantId, {
    order: {
      amountOfMoney: { amount: 4999, currencyCode: "EUR" }
    },
    cardPaymentMethodSpecificInput: {
      authorizationMode: "SALE",
      card: {
        cardNumber: "4111111111111111",
        expiryDate: "1225",
        cvv: "123"
      }
    }
  });

  return response;
}
```

## Python

### Installation

```bash
pip install onlinepayments-sdk-python3
```

### Configuration

```python
from onlinepayments.sdk.factory import Factory
from onlinepayments.sdk.communicator_configuration import CommunicatorConfiguration

config = CommunicatorConfiguration(
    api_endpoint="https://payment.preprod.direct.worldline-solutions.com",
    api_key_id=os.environ["WORLDLINE_API_KEY"],
    secret_api_key=os.environ["WORLDLINE_SECRET_KEY"],
    integrator="YourCompany"
)

client = Factory.create_client_from_configuration(config)
merchant_id = os.environ["WORLDLINE_MERCHANT_ID"]
```

### Usage Example

```python
from onlinepayments.sdk.domain.create_payment_request import CreatePaymentRequest
from onlinepayments.sdk.domain.amount_of_money import AmountOfMoney
from onlinepayments.sdk.domain.order import Order
from onlinepayments.sdk.domain.card import Card
from onlinepayments.sdk.domain.card_payment_method_specific_input import CardPaymentMethodSpecificInput

def create_payment():
    body = CreatePaymentRequest()
    body.order = Order()
    body.order.amount_of_money = AmountOfMoney()
    body.order.amount_of_money.amount = 4999
    body.order.amount_of_money.currency_code = "EUR"

    body.card_payment_method_specific_input = CardPaymentMethodSpecificInput()
    body.card_payment_method_specific_input.authorization_mode = "SALE"
    body.card_payment_method_specific_input.card = Card()
    body.card_payment_method_specific_input.card.card_number = "4111111111111111"
    body.card_payment_method_specific_input.card.expiry_date = "1225"
    body.card_payment_method_specific_input.card.cvv = "123"

    response = client.merchant(merchant_id).payments().create_payment(body)
    return response

# Don't forget to close the client
client.close()
```

## Java

### Installation (Maven)

```xml
<dependency>
    <groupId>com.worldline-solutions.direct</groupId>
    <artifactId>direct-sdk-java</artifactId>
    <version>1.0.0</version>
</dependency>
```

### Configuration

```java
import com.worldline.direct.sdk.java.Client;
import com.worldline.direct.sdk.java.Factory;

CommunicatorConfiguration config = new CommunicatorConfiguration()
    .withApiEndpoint(URI.create("https://payment.preprod.direct.worldline-solutions.com"))
    .withApiKeyId(System.getenv("WORLDLINE_API_KEY"))
    .withSecretApiKey(System.getenv("WORLDLINE_SECRET_KEY"));

try (Client client = Factory.createClient(config)) {
    String merchantId = System.getenv("WORLDLINE_MERCHANT_ID");
    // Use client
}
```

## PHP

### Installation

```bash
composer require worldline/connect-sdk-php
```

### Configuration

```php
<?php
require 'vendor/autoload.php';

use Worldline\Connect\Sdk\Factory;

$communicatorConfiguration = new CommunicatorConfiguration(
    'YOUR_API_KEY_ID',
    'YOUR_SECRET_API_KEY',
    'https://payment.preprod.direct.worldline-solutions.com',
    'YourCompany'
);

$client = Factory::createClient($communicatorConfiguration);
$merchantId = 'YOUR_MERCHANT_ID';
```

## .NET

### Installation

```bash
dotnet add package OnlinePayments.Sdk
```

### Configuration

```csharp
using OnlinePayments.Sdk;

var config = new CommunicatorConfiguration
{
    ApiEndpoint = new Uri("https://payment.preprod.direct.worldline-solutions.com"),
    ApiKeyId = Environment.GetEnvironmentVariable("WORLDLINE_API_KEY"),
    SecretApiKey = Environment.GetEnvironmentVariable("WORLDLINE_SECRET_KEY"),
    Integrator = "YourCompany"
};

using var client = Factory.CreateClient(config);
var merchantId = Environment.GetEnvironmentVariable("WORLDLINE_MERCHANT_ID");
```

## Ruby

### Installation

```bash
gem install worldline-direct-sdk-ruby
```

### Configuration

```ruby
require 'worldline/connect/sdk'

config = Worldline::Connect::SDK::CommunicatorConfiguration.new(
  api_key_id: ENV['WORLDLINE_API_KEY'],
  secret_api_key: ENV['WORLDLINE_SECRET_KEY'],
  api_endpoint: 'https://payment.preprod.direct.worldline-solutions.com',
  integrator: 'YourCompany'
)

client = Worldline::Connect::SDK::Factory.create_client_from_configuration(config)
merchant_id = ENV['WORLDLINE_MERCHANT_ID']
```

## Environment Variables

Create a `.env` file:

```bash
# Worldline Direct API Credentials
WORLDLINE_MERCHANT_ID=your_pspid
WORLDLINE_API_KEY=your_api_key
WORLDLINE_SECRET_KEY=your_secret_key

# Optional: Webhook secret for signature verification
WORLDLINE_WEBHOOK_SECRET=your_webhook_secret
```

## Sandbox vs Production

| Environment | Host |
|-------------|------|
| Sandbox | `payment.preprod.direct.worldline-solutions.com` |
| Production | `payment.direct.worldline-solutions.com` |

## Getting Credentials

1. Log into the **Merchant Portal**
   - Sandbox: https://merchant-portal.preprod.direct.worldline-solutions.com
   - Production: https://merchant-portal.direct.worldline-solutions.com

2. Navigate to **Developer > Payment API**

3. Click **Generate API Key**

4. Save your:
   - API Key ID
   - Secret API Key (shown only once!)
   - PSPID (Merchant ID)

## SDK Version Requirements

| SDK | Minimum Version |
|-----|-----------------|
| Node.js | 18+ |
| Python | 3.7+ |
| Java | 8+ |
| PHP | 7.4+ |
| .NET | 4.6.1+ / Core 2.0+ |
| Ruby | 2.7+ |

## Error Handling

All SDKs throw exceptions for errors:

```javascript
try {
  const payment = await client.payments.createPayment(merchantId, body);
} catch (error) {
  if (error.statusCode === 400) {
    console.error("Validation error:", error.body.errors);
  } else if (error.statusCode === 401) {
    console.error("Authentication failed");
  } else if (error.statusCode === 402) {
    console.error("Payment declined");
  } else {
    console.error("Unexpected error:", error);
  }
}
```

## Logging

Enable SDK logging for debugging:

```javascript
const client = OnlinePayments.init({
  host: "payment.preprod.direct.worldline-solutions.com",
  apiKeyId: process.env.WORLDLINE_API_KEY,
  secretApiKey: process.env.WORLDLINE_SECRET_KEY,
  enableLogging: true,
  logger: console
});
```

## Next Steps

- [Authentication](authentication.md) - Understand API authentication
- [Hosted Checkout](integration-methods/hosted-checkout.md) - Start with hosted checkout
- [Test Cards](test-cards.md) - Test your integration
