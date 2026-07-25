# SaaS Architecture Patterns

This reference outlines common architecture choices for SaaS products.

## Multi-Tenant Architecture

### Shared Database, Shared Schema
- Tenant isolation via `tenant_id` columns.
- Lowest operational overhead.
- Requires strict row-level authorization.

### Shared Database, Separate Schema
- Per-tenant schema boundaries.
- Better logical isolation.
- Higher migration and operations complexity.

### Separate Database Per Tenant
- Strongest isolation and compliance posture.
- Best for enterprise/high-regulatory environments.
- Highest cost and operational burden.

### Tenant Isolation Checklist

- Enforce tenant filters in all read/write queries.
- Validate authorization at API and data layers.
- Audit logs include tenant context.
- Backups and restores preserve tenant boundaries.

## Authentication Patterns

### JWT-Based Session Pattern
- Stateless access tokens.
- Use short-lived access tokens + refresh tokens.
- Rotate signing keys with versioning (`kid` usage).

### OAuth 2.0 / OIDC Pattern
- Preferred for SSO and enterprise identity.
- Support common providers (Google, Microsoft, Okta).
- Map identity claims to internal roles and tenants.

### Hybrid Auth Pattern
- Email/password for SMB self-serve.
- SSO/OAuth for enterprise accounts.

## Billing Integration Patterns

### Subscription Lifecycle
1. Trial start
2. Conversion to paid plan
3. Renewal and invoice events
4. Grace period / dunning
5. Downgrade, cancellation, reactivation

### Billing Event Handling
- Process webhook events idempotently.
- Verify provider signatures.
- Persist raw event payload for audit/debugging.
- Reconcile billing state asynchronously.

### Entitlement Model
- Separate billing plans from feature entitlements.
- Resolve effective entitlements per tenant/user at request time.

## API Versioning Patterns

### URI Versioning
- `/api/v1/...`, `/api/v2/...`
- Explicit and easy to route.

### Header Versioning
- Version via request header.
- Cleaner URLs, more client coordination required.

### Versioning Rules
- Avoid breaking changes inside a version.
- Provide deprecation windows and migration docs.
- Track version adoption per client.

## Database Schema Patterns for SaaS

### Core Entities
- `tenants`
- `users`
- `memberships` (user-tenant-role mapping)
- `plans`
- `subscriptions`
- `invoices`
- `events_audit`

### Recommended Relationship Pattern
- `tenants` 1:N `memberships`
- `users` 1:N `memberships`
- `tenants` 1:1 active `subscriptions`
- `subscriptions` 1:N `invoices`

### Data Model Guardrails
- Unique constraints on tenant-scoped natural keys.
- Soft-delete where recoverability matters.
- Created/updated timestamps on all mutable entities.
- Migration strategy supports zero-downtime changes.
