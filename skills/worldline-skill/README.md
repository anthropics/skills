# Worldline Skill

An [Agent Skill](https://agentskills.io) for integrating **Worldline Direct** payments. Helps developers choose the right payment flow based on their industry and provides working code examples.

## What This Skill Does

When you're building a payment integration, this skill helps you:

- **Choose the right payment flow** based on your industry (car rental, hotels, e-commerce, subscriptions)
- **Understand authorization types** (pre-auth, final auth, direct sale)
- **Implement Card-on-File** for recurring payments and one-click checkout
- **Handle the full payment lifecycle** (capture, refund, cancel)
- **Get working code examples** in Node.js and Python

### Example Conversations

```
You: "I'm building a car rental app, what payment flow should I use?"

Claude: For car rental, I recommend:
1. Pre-Authorization at booking (holds funds for up to 30 days)
2. Partial Capture at return (charge actual rental cost)
3. Card-on-File for post-rental charges (damages, fuel, fines)

Here's how to implement it... [provides code]
```

```
You: "Show me how to implement hosted checkout in Node.js"

Claude: [Provides complete working example from the skill]
```

## Installation

### Claude Code (CLI)

```bash
# Clone to your skills directory
git clone https://github.com/acathelin/worldline-skill ~/.claude/skills/worldline-skill
```

### Other Agents

Follow the [Agent Skills installation guide](https://agentskills.io) for your platform.

## Skill Contents

```
worldline-skill/
├── SKILL.md                          # Main skill instructions
├── README.md                         # This file
├── references/
│   ├── industry-guides/              # Industry-specific recommendations
│   │   ├── car-rental.md             # Pre-auth + partial capture + MIT
│   │   ├── hotels.md                 # Variable capture for incidentals
│   │   ├── ecommerce.md              # Hosted checkout, direct sale
│   │   ├── subscriptions.md          # Fixed/variable recurring
│   │   └── marketplace.md            # Split payments
│   ├── integration-methods/          # How to connect
│   │   ├── hosted-checkout.md        # Redirect to Worldline (lowest PCI)
│   │   ├── hosted-tokenization.md    # iFrame in your checkout
│   │   ├── server-to-server.md       # Direct API (highest PCI)
│   │   └── mobile-sdk.md             # iOS, Android, Flutter
│   ├── payment-flows/                # Payment operations
│   │   ├── authorization-types.md    # Pre-auth vs Final vs Sale
│   │   ├── card-on-file.md           # Tokenization, CIT/MIT
│   │   ├── recurring-payments.md     # Subscriptions
│   │   └── maintenance-ops.md        # Capture, Refund, Cancel
│   ├── payment-methods/              # Supported payment types
│   │   ├── cards.md                  # Visa, MC, Amex + 3DS
│   │   ├── wallets.md                # Apple Pay, Google Pay, PayPal
│   │   ├── banking.md                # iDEAL, SEPA, regional methods
│   │   └── bnpl.md                   # Klarna, in3
│   ├── sdk-setup.md                  # SDK installation
│   ├── authentication.md             # API credentials
│   ├── status-codes.md               # Payment statuses
│   ├── test-cards.md                 # Sandbox testing
│   ├── webhooks.md                   # Event notifications
│   └── error-codes.md                # Troubleshooting
└── assets/
    └── examples/
        ├── nodejs/                   # Node.js examples
        │   ├── hosted-checkout.js
        │   ├── pre-authorization.js
        │   ├── capture-payment.js
        │   ├── card-on-file.js
        │   └── recurring-payment.js
        └── python/                   # Python examples
            ├── hosted-checkout.py
            └── pre-authorization.py
```

## Industry Recommendations

| Industry | Recommended Flow | Key Features |
|----------|-----------------|--------------|
| **Car Rental** | Pre-auth + Partial Capture | 30-day hold, MIT for no-shows, CoF for damages |
| **Hotels** | Pre-auth + Variable Capture | Hold for booking, adjust for minibar/extras |
| **E-commerce** | Direct Sale or Hosted Checkout | Immediate capture, simple flow |
| **Subscriptions** | Card-on-File + Fixed Recurring | Tokenization, scheduled charges, retry logic |
| **Marketplace** | Split payments + Payouts | Multi-party settlements |

## Requirements

This skill provides **guidance and code examples** - it doesn't require any MCP server or special tools. Developers use the standard Worldline SDK:

### Node.js
```bash
npm install onlinepayments-sdk-nodejs
```

### Python
```bash
pip install onlinepayments-sdk-python
```

### Other SDKs
- Java: `onlinepayments-sdk-java`
- PHP: `onlinepayments-sdk-php`
- .NET: `OnlinePayments.Sdk`
- Ruby: `onlinepayments-sdk-ruby`

## API Credentials

Get your credentials from the [Worldline Merchant Portal](https://merchant-portal.preprod.direct.worldline-solutions.com):

1. Go to **Developer > Payment API**
2. Copy your **API Key ID** and **Secret API Key**
3. Note your **Merchant ID**

Use the **preprod** environment for testing, **prod** for live transactions.

## Testing

Use test cards in the sandbox environment:

| Card Number | Result |
|-------------|--------|
| 4111111111111111 | Visa - Success |
| 5399999999999999 | Mastercard - Success |
| 4000000000000002 | Declined |
| 4000000000000036 | 3DS Challenge |

See [test-cards.md](references/test-cards.md) for all test scenarios.

## Contributing

Contributions welcome! Please:

1. Fork the repository
2. Create a feature branch
3. Submit a pull request

## Resources

- [Worldline Direct Documentation](https://docs.direct.worldline-solutions.com)
- [API Reference](https://docs.direct.worldline-solutions.com/en/api-reference)
- [Agent Skills Specification](https://agentskills.io)

## License

MIT License - see [LICENSE](LICENSE) for details.
