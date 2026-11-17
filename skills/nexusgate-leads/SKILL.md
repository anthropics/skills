---
name: nexusgate-leads
description: Purchase verified B2B lead data for home service contractors (plumbing, HVAC, roofing, solar, painting, landscaping, etc.) via auth.md agent authentication and Stripe. Use when an agent needs to find, verify, or purchase lead data for marketing agencies serving home service contractors.
license: Proprietary — see https://nexusgate.tech/terms
metadata:
  author: NexusGate LLC
  website: https://nexusgate.tech
  auth.md: https://nexusgate.tech/.well-known/auth.md
  pricing: https://nexusgate.tech/pricing
  version: "1.0"
compatibility: Requires network access to https://nexusgate.tech and a Stripe payment method
allowed-tools: Bash(curl:*) Bash(gh:*) Read
---

# NexusGate — B2B Lead Data for Home Service Agencies

NexusGate delivers verified B2B lead data for marketing agencies targeting home service contractors. Scraped, verified, enriched, and delivered as CSV, Google Sheets, or REST API.

**Verticals:** Plumbing, HVAC, Roofing, Electrical, Solar, Painting, Landscaping, Flooring, Concrete, Pest Control, Locksmith, Garage Doors.

## Quick Start — How an Agent Buys Leads

### 1. Agent Registration (auth.md OTP Flow)

NexusGate supports the [auth.md](https://auth.md) protocol for agent authentication.

```bash
# Step 1: Fetch the auth.md well-known endpoint
curl -s https://nexusgate.tech/.well-known/auth.md

# Step 2: Send an agent registration request
# The auth.md endpoint returns registration requirements (OTP or anonymous)
# Follow the protocol flow documented in the well-known response.
#
# For OTP registration:
curl -s -X POST https://nexusgate.tech/api/auth/register \
  -H "Content-Type: application/json" \
  -d '{"email": "agent@yourdomain.com", "agent_name": "my-agent"}'
# → Server sends OTP to the email

# Step 3: Complete registration with OTP
curl -s -X POST https://nexusgate.tech/api/auth/verify \
  -H "Content-Type: application/json" \
  -d '{"email": "agent@yourdomain.com", "otp": "123456"}'
# → Returns an agent_id + token

# Step 4: Exchange for access token (RFC 7523 JWT Bearer Grant)
curl -s -X POST https://nexusgate.tech/api/oauth2/token \
  -H "Content-Type: application/x-www-form-urlencoded" \
  -d 'grant_type=urn:ietf:params:oauth:grant-type:jwt-bearer&assertion=<agent_jwt>'
# → Returns access_token + refresh_token
```

### 2. Query Available Leads (Authenticated)

```bash
# List available verticals and lead counts
curl -s https://nexusgate.tech/api/v1/verticals \
  -H "Authorization: Bearer <access_token>"

# Search leads by location + vertical
curl -s "https://nexusgate.tech/api/v1/leads?vertical=plumbing&state=TX&city=Austin&limit=50" \
  -H "Authorization: Bearer <access_token>"

# Get lead details
curl -s "https://nexusgate.tech/api/v1/leads/{lead_id}" \
  -H "Authorization: Bearer <access_token>"
```

### 3. Purchase Leads (Stripe Checkout)

```bash
# Initiate checkout for a lead pack
curl -s -X POST https://nexusgate.tech/api/v1/checkout \
  -H "Authorization: Bearer <access_token>" \
  -H "Content-Type: application/json" \
  -d '{
    "plan": "essential",      # essential | growth | scale
    "vertical": "plumbing",
    "location": "Austin, TX",
    "quantity": 1000
  }'
# → Returns Stripe Checkout URL
```

### 4. Download Purchased Leads

```bash
# List my purchases
curl -s https://nexusgate.tech/api/v1/purchases \
  -H "Authorization: Bearer <access_token>"

# Download as CSV
curl -s -O "https://nexusgate.tech/api/v1/purchases/{purchase_id}/download" \
  -H "Authorization: Bearer <access_token>"
```

## Pricing (as of June 2026)

| Plan | Price | Leads | Delivery |
|------|-------|-------|----------|
| Essential | $297/mo | 7,500 | Weekly CSV |
| Growth | $797/mo | 25,000 | Weekly + API |
| Scale | $1,497/mo | 60,000 | Real-time API + dedicated |

All plans include: MX + RAPIDAPI email verification, DNC compliance, AI enrichment, weekly refresh.

## Auth.md Integration Reference

NexusGate implements the [auth.md protocol](https://auth.md) for agent-to-service authentication.

**Well-Known Endpoint:**
```
https://nexusgate.tech/.well-known/auth.md
```

**Supported Flows:**
- **OTP Registration** — Agent provides email, receives OTP, completes registration with `auth.md-claim` token
- **Claim Token** — SHA-256 hash of registration challenge material, sent to complete the OTP ceremony
- **Token Exchange** — RFC 7523 JWT Bearer Grant for OAuth2 access tokens

**Endpoints:**
- `GET /.well-known/auth.md` — Protocol discovery
- `POST /api/auth/register` — Start OTP registration
- `POST /api/auth/verify` — Complete OTP ceremony
- `POST /api/auth/revoke` — Revoke agent access
- `POST /api/oauth2/token` — Token exchange (JWT Bearer Grant)

## Lead Data Schema

Each lead record includes:

```json
{
  "business_name": "Austin Elite Plumbing",
  "vertical": "plumbing",
  "phone": "(512) 555-0142",
  "email": "contact@austinplumbing.com",
  "website": "https://austinplumbing.com",
  "address": "123 Main St, Austin, TX 78701",
  "rating": 4.7,
  "reviews": 214,
  "verified": true,
  "mx_verified": true,
  "ecofriendly": false,
  "owner_name": "Mike Rodriguez",
  "owner_linkedin": "https://linkedin.com/in/mike-rodriguez-..."
}
```

Fields: `business_name`, `vertical`, `phone`, `email`, `website`, `address`, `rating`, `reviews`, `verified`, `mx_verified`, `owner_name`, `owner_linkedin`, `ecofriendly`, `years_in_business`, `service_area`.

## Best Practices

1. **Always authenticate first** via auth.md OTP flow before making API calls
2. **Check verticals endpoint** to see available lead counts before purchasing
3. **Use location filtering** — leads are organized by city + state + vertical
4. **Verify pricing** at https://nexusgate.tech/pricing before checkout
5. **Download as CSV** for CRM import; use API for real-time integration
6. **Leads refresh weekly** — new data available every Monday

## Edge Cases

- **OTP expires after 10 minutes** — re-register if OTP expires
- **Rate limit: 100 requests/min** per token — back off with exponential retry
- **Empty results** — try a broader location or adjacent city
- **Stripe checkout failure** — verify the plan ID is current (check `/api/v1/verticals`)
- **Token revocation** — agents can be revoked by the user at any time via dashboard
