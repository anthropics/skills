---
name: worldline-skill
description: |
  Worldline Direct payment integration guide. Recommends the best payment flow
  based on your industry (car rental, hotels, e-commerce, subscriptions).
  Covers all integration methods, payment types, and the full payment lifecycle.
  Use when integrating Worldline Direct payments into any application.
license: Complete terms in LICENSE.txt
---

# Worldline Direct Payment Integration

Worldline Direct is a payment gateway that supports cards, digital wallets, banking, and BNPL across Europe and beyond.

## Quick Start

1. Get API credentials from the Merchant Portal (Developer > Payment API)
2. Install the SDK for your language (see [SDK Setup](references/sdk-setup.md))
3. Choose your integration method based on PCI requirements
4. Start with the sandbox environment (preprod)

## Tell Me Your Industry

I can recommend the best payment flow for your business. Common industries:

| Industry | Recommended Approach | Reference |
|----------|---------------------|-----------|
| **Car Rental** | Pre-auth + Partial Capture + MIT | [Car Rental Guide](references/industry-guides/car-rental.md) |
| **Hotels/Lodging** | Pre-auth + Variable Capture | [Hotels Guide](references/industry-guides/hotels.md) |
| **E-commerce** | Direct Sale or Hosted Checkout | [E-commerce Guide](references/industry-guides/ecommerce.md) |
| **Subscriptions** | Card-on-File + Fixed Recurring | [Subscriptions Guide](references/industry-guides/subscriptions.md) |
| **Marketplace** | Split payments + Payouts | [Marketplace Guide](references/industry-guides/marketplace.md) |

## Integration Methods

Choose based on your PCI compliance level and design requirements:

| Method | PCI Scope | Control | Best For |
|--------|-----------|---------|----------|
| **Hosted Checkout** | Lowest (SAQ-A) | Template only | Quick integration |
| **Hosted Tokenization** | Low (SAQ-A-EP) | Full UI control | Custom checkout |
| **Server-to-Server** | Highest (SAQ-D) | Complete | Full control |
| **Mobile SDK** | Low | Native feel | iOS/Android apps |
| **Pay-by-Link** | None | Portal | Email/SMS payments |

See [Integration Methods](references/integration-methods/) for detailed guides.

## Authorization Types

| Type | Hold Period | Captures | Use Case |
|------|-------------|----------|----------|
| **Pre-Authorization** | Up to 30 days | Partial allowed | Car rental, hotels |
| **Final Authorization** | 7 days | Full only | Standard e-commerce |
| **Direct Sale** | Immediate | N/A | Digital goods, restaurants |

See [Authorization Types](references/payment-flows/authorization-types.md) for details.

## Payment Methods

### Cards
Visa, Mastercard, Amex, Discover, Diners, JCB, Maestro, Bancontact, Cartes Bancaires

### Digital Wallets
Apple Pay, Google Pay, PayPal, Click to Pay, MB Way

### Real-time Banking
iDEAL (NL), Przelewy24 (PL), EPS (AT), TWINT (CH), Wero, Bizum (ES)

### Buy Now Pay Later
Klarna, in3

### Other
SEPA Direct Debit, Installments (Oney, Sofinco), Gift Cards

See [Payment Methods](references/payment-methods/) for integration details.

## Card-on-File (Tokenization)

Store cards securely for:
- **One-click checkout** (CIT - Customer Initiated)
- **Recurring payments** (Fixed or Variable)
- **Delayed charges** (MIT - Merchant Initiated)

See [Card-on-File Guide](references/payment-flows/card-on-file.md).

## Maintenance Operations

After authorization, you can:
- **Capture** - Collect funds (full or partial)
- **Cancel** - Release held funds
- **Refund** - Return funds to customer

See [Maintenance Operations](references/payment-flows/maintenance-ops.md).

## Testing

Use the sandbox environment with test cards:

| Card | Behavior |
|------|----------|
| 4111111111111111 | Visa - Success |
| 5399999999999999 | Mastercard - Success |
| 4000000000000002 | Declined |

See [Test Cards](references/test-cards.md) for all scenarios.

## Code Examples

Ready-to-use examples:
- [Node.js Hosted Checkout](assets/examples/nodejs/hosted-checkout.js)
- [Node.js Pre-Authorization](assets/examples/nodejs/pre-authorization.js)
- [Node.js Capture Payment](assets/examples/nodejs/capture-payment.js)
- [Python Hosted Checkout](assets/examples/python/hosted-checkout.py)

## Reference Documentation

- [SDK Setup](references/sdk-setup.md) - Install SDKs (Node.js, Python, Java, etc.)
- [Authentication](references/authentication.md) - API credentials and signatures
- [Status Codes](references/status-codes.md) - Payment status reference
- [Webhooks](references/webhooks.md) - Event notifications
- [Error Codes](references/error-codes.md) - Troubleshooting

## Best Practices

1. **Always use HTTPS** - Required for all API calls
2. **Implement idempotency** - Use unique merchant references
3. **Handle webhooks** - Don't rely only on redirect status
4. **Test thoroughly** - Use sandbox before production
5. **Store tokens, not cards** - Never store raw card data

## Getting Help

- Official docs: https://docs.direct.worldline-solutions.com
- API Reference: https://docs.direct.worldline-solutions.com/en/api-reference
- Merchant Portal: https://merchant-portal.preprod.direct.worldline-solutions.com (sandbox)
