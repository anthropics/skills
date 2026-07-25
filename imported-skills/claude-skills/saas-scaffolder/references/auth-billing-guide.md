# Authentication & Billing Implementation Guide

## Overview

Authentication and billing are foundational SaaS capabilities that affect every user interaction. This guide covers implementation patterns, security best practices, and common pitfalls for both systems.

## Authentication

### OAuth2 / OpenID Connect (OIDC) Flows

#### Authorization Code Flow (Recommended for Web Apps)
1. Redirect user to authorization server (`/authorize`)
2. User authenticates and consents
3. Authorization server redirects back with authorization code
4. Backend exchanges code for tokens (`/token`)
5. Store tokens server-side, issue session cookie

**Use when:** Server-rendered apps, traditional web applications

#### Authorization Code Flow + PKCE (Recommended for SPAs and Mobile)
1. Generate code verifier and code challenge
2. Redirect with code challenge
3. User authenticates
4. Exchange code + code verifier for tokens
5. Store tokens securely (memory for SPAs, secure storage for mobile)

**Use when:** Single-page applications, mobile apps, any public client

#### Client Credentials Flow
1. Service authenticates with client_id and client_secret
2. Receives access token for service-to-service calls

**Use when:** Backend service-to-service communication, no user context

### JWT Best Practices

**Token Structure:**
- **Access token**: Short-lived (15-60 minutes), contains user claims
- **Refresh token**: Longer-lived (7-30 days), stored securely, used to get new access tokens
- **ID token**: Contains user identity claims, used by frontend only

**Security Guidelines:**
- Sign tokens with RS256 (asymmetric) for distributed systems
- Include `iss`, `aud`, `exp`, `iat`, `sub` standard claims
- Never store sensitive data in JWT payload (it is base64-encoded, not encrypted)
- Validate all claims on every request
- Implement token rotation for refresh tokens
- Maintain a deny-list for revoked tokens (or use short-lived access tokens)
- Set `httpOnly`, `secure`, `sameSite=strict` for cookie-stored tokens

**Common Pitfalls:**
- Using HS256 in distributed systems (shared secret)
- Storing JWTs in localStorage (XSS vulnerable)
- Not validating `aud` claim (token reuse attacks)
- Excessively long access token lifetimes

### RBAC vs ABAC

#### Role-Based Access Control (RBAC)
- Assign users to roles (Admin, Editor, Viewer)
- Roles have fixed permission sets
- Simple to implement and understand
- Works well for most SaaS applications

**Implementation:**
```
User -> Role -> Permissions
john@acme.com -> Admin -> [create, read, update, delete, manage_users]
jane@acme.com -> Editor -> [create, read, update]
bob@acme.com -> Viewer -> [read]
```

#### Attribute-Based Access Control (ABAC)
- Decisions based on user attributes, resource attributes, environment
- More flexible but more complex
- Required for fine-grained access control

**Use ABAC when:**
- Access depends on resource ownership (users can edit their own posts)
- Multi-tenant isolation requires tenant-context checks
- Time-based or location-based access rules needed
- Regulatory compliance requires granular audit trails

### Social Login Implementation
- Support Google, GitHub, Microsoft at minimum for B2B
- Map social identity to internal user record (by email)
- Handle account linking (same email, different providers)
- Always allow email/password as fallback
- Implement account deduplication strategy

## Billing & Subscriptions

### Stripe Integration Patterns

#### Setup Flow
1. Create Stripe Customer on user registration
2. Store `stripe_customer_id` in your database
3. Use Stripe Checkout for initial payment (PCI-compliant)
4. Store `subscription_id` for ongoing management
5. Sync plan status via webhooks (source of truth)

#### Key Stripe Objects
- **Customer**: Maps to your user/organization
- **Product**: Maps to your plan tier (Basic, Pro, Enterprise)
- **Price**: Specific pricing for a product (monthly, annual)
- **Subscription**: Active billing relationship
- **Invoice**: Generated per billing cycle
- **PaymentIntent**: Represents a payment attempt

### Subscription Lifecycle

#### Trial Period
- Offer 7-14 day free trial (no credit card for PLG, card required for sales-led)
- Send reminder emails at 3 days and 1 day before trial ends
- Provide clear upgrade path within the product
- Track trial engagement to predict conversion

#### Active Subscription
- Sync plan features with entitlement system
- Handle plan upgrades (immediate proration) and downgrades (end of period)
- Support annual billing with discount (typically 15-20%)
- Send receipts and invoice notifications

#### Payment Failure / Dunning
1. First failure: Retry automatically, notify user
2. Second failure (3 days later): Retry, send warning email
3. Third failure (7 days later): Retry, restrict features
4. Final attempt (14 days): Cancel subscription, move to free tier
5. Win-back: Send recovery emails at 30, 60, 90 days

#### Churned
- Downgrade to free tier (maintain data for re-activation)
- Track churn reason (survey on cancellation)
- Implement cancellation flow with save offers
- Define data retention policy (90 days typical)

#### Reactivated
- Allow easy re-subscription from settings
- Restore previous plan and data
- Consider win-back offers (discount for first month back)

### Webhook Handling

**Critical Webhooks to Handle:**
- `customer.subscription.created` - Activate plan
- `customer.subscription.updated` - Sync plan changes
- `customer.subscription.deleted` - Handle cancellation
- `invoice.paid` - Confirm payment, update status
- `invoice.payment_failed` - Trigger dunning flow
- `checkout.session.completed` - Complete signup flow

**Webhook Best Practices:**
- Verify webhook signature on every request
- Respond with 200 immediately, process asynchronously
- Implement idempotency (handle duplicate events)
- Log all webhook events for debugging
- Set up webhook failure alerts
- Use Stripe CLI for local development testing

### PCI Compliance Basics

#### SAQ-A (Recommended for SaaS)
- Use Stripe.js / Stripe Elements for card collection
- Never touch raw card numbers on your servers
- Card data goes directly from browser to Stripe
- Your servers only handle tokens and customer IDs

#### Requirements
- [ ] Use HTTPS everywhere
- [ ] Never log card numbers or CVV
- [ ] Use Stripe-hosted payment forms or Elements
- [ ] Restrict access to Stripe dashboard (2FA required)
- [ ] Regularly rotate API keys
- [ ] Document your payment processing flow

## Entitlement System Design

### Feature Gating Pattern
```
Check flow:
1. User action requested
2. Look up user's subscription plan
3. Check plan's feature flags / limits
4. Allow or deny with appropriate message
```

### Entitlement Types
- **Boolean**: Feature on/off (e.g., "SSO enabled")
- **Numeric limit**: Usage cap (e.g., "10 projects max")
- **Tiered**: Different capability levels (e.g., "basic/advanced analytics")

### Implementation Tips
- Cache entitlements locally (refresh on plan change webhook)
- Show upgrade prompts at limit boundaries (not hard blocks)
- Provide grace periods for brief overages
- Track usage for plan recommendation engine
