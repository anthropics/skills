---
name: clerk-convex-expo-auth
description: Complete authentication blueprint for React Native / Expo apps using Clerk + Convex. Covers backend auth config, user schema, webhook pipeline, JWT validation, frontend providers, route protection, sign-in/sign-up flows, email verification, Apple Sign-In, onboarding, and account deletion. Use when building auth for Clerk + Convex + Expo projects, setting up webhooks, or implementing sign-in/sign-up flows.
---

# Clerk + Convex + Expo Authentication

Complete authentication system for React Native / Expo apps using Clerk (identity provider) and Convex (backend). This skill provides a production-ready blueprint covering every layer from JWT validation to account deletion cascades.

## When to Use

- Setting up auth in a new Clerk + Convex + Expo project
- Adding sign-in/sign-up flows (email/password, Apple Sign-In)
- Configuring Clerk-to-Convex webhooks for user sync
- Implementing route protection and onboarding flows
- Adding account deletion with cascading cleanup

## Tech Stack

| Package | Purpose |
|---------|---------|
| `@clerk/clerk-expo` | Clerk SDK for React Native/Expo (client-side auth) |
| `@clerk/backend` | Clerk backend utilities (webhook type definitions) |
| `convex` | Backend framework (`ConvexProviderWithClerk`, `ctx.auth`) |
| `svix` | Webhook signature verification |
| `expo-secure-store` | Encrypted token storage on device |
| `expo-apple-authentication` | Native Apple Sign-In (iOS) |
| `expo-auth-session` | OAuth session handling |
| `expo-web-browser` | Opens browser for OAuth flows |

**Install:**
```bash
npx expo install @clerk/clerk-expo expo-secure-store expo-apple-authentication expo-auth-session expo-web-browser
npm install @clerk/backend svix
```

## Environment Variables

```env
CLERK_JWT_ISSUER_DOMAIN=https://<your-clerk-instance>.clerk.accounts.dev
CLERK_WEBHOOK_SECRET=whsec_<your-webhook-secret>
EXPO_PUBLIC_CLERK_PUBLISHABLE_KEY=pk_test_<your-publishable-key>
EXPO_PUBLIC_CONVEX_URL=https://<your-convex-deployment>.convex.cloud
```

## Instructions

### Architecture Overview

```
Client (Expo)                    Backend (Convex)
─────────────                    ────────────────
ClerkProvider                    auth.config.ts (JWT validation)
  └─ ConvexProviderWithClerk     getUser() helper (auth enforcement)
       └─ JWT auto-attached      Webhook handler (user sync)
            to every request     Internal mutations (upsert/delete)
```

**Data flows:**
1. **Auth**: Client -> Clerk JWT -> Convex validates against `CLERK_JWT_ISSUER_DOMAIN`
2. **User sync**: Clerk event -> Webhook POST -> Convex HTTP endpoint -> Svix verifies -> Internal mutation
3. **Per-request**: `ctx.auth.getUserIdentity()` -> lookup by `externalId` index -> return user ID

### Backend Setup

#### 1. Auth Config (`convex/auth.config.ts`)

```typescript
import { AuthConfig } from "convex/server";

export default {
  providers: [
    {
      domain: process.env.CLERK_JWT_ISSUER_DOMAIN!,
      applicationID: "convex",
    },
  ],
} satisfies AuthConfig;
```

#### 2. User Schema

```typescript
// convex/schema.ts
users: defineTable({
  externalId: v.string(),            // Clerk user ID (identity.subject)
  name: v.optional(v.string()),
  nickname: v.optional(v.string()),
  email: v.optional(v.string()),
  image_url: v.optional(v.string()),
  has_image: v.optional(v.boolean()),
  status: v.union(v.literal("online"), v.literal("offline")),
})
  .index("by_externalId", ["externalId"])
```

The `by_externalId` index is **critical** -- used by both the webhook handler and `getUser()`.

#### 3. Auth Helper (`getUser`)

Central auth enforcement function. Three usage modes:

| Call | Behavior |
|------|----------|
| `getUser(ctx)` | Returns user ID or `null` |
| `getUser(ctx, { required: true })` | Returns user ID or throws |
| `getUser(ctx, { required: true, createIfMissing: true })` | Returns user ID, creating record on first access |

See `references/backend.md` for full implementation.

#### 4. Webhook Handler (`convex/http.ts`)

Receives `user.created`, `user.updated`, `user.deleted` events from Clerk, verifies signatures with Svix, and routes to internal mutations.

See `references/webhook-setup.md` for step-by-step setup and `references/backend.md` for implementation.

#### 5. Auth Enforcement Patterns

Every protected endpoint calls `getUser()` at the top:

```typescript
// Hard requirement (most mutations)
const userId = await getUser(ctx, { required: true });

// Auto-create (onboarding, first-time actions)
const userId = await getUser(ctx, { required: true, createIfMissing: true });

// Soft check (public queries)
const userId = await getUser(ctx);
if (!userId) return null;
```

### Frontend Setup

#### 1. Auth Provider (`components/auth/index.tsx`)

Wraps the app with `ClerkProvider` + `ConvexProviderWithClerk`. Uses `expo-secure-store` for token persistence.

See `references/frontend.md` for full implementation.

#### 2. Route Protection

Two-layer protection:
1. **Clerk layer**: `isSignedIn` from `useAuth()` or `<Authenticated>` / `<Unauthenticated>` from `convex/react`
2. **App layer**: `hasCompletedOnboarding` Convex query for nickname check

#### 3. Sign-In / Sign-Up

Uses `useSignIn()` and `useSignUp()` from `@clerk/clerk-expo`:
- `signIn.create({ identifier, password })` for sign-in
- `signUp.create({ emailAddress, password })` + `prepareEmailAddressVerification()` for sign-up

#### 4. Email Verification

`signUp.attemptEmailAddressVerification({ code })` with 6-digit code.

#### 5. Apple Sign-In (iOS)

Uses `useSignInWithApple()` from `@clerk/clerk-expo` + native `expo-apple-authentication` button.

#### 6. Account Deletion Cascade

`clerkUser.delete()` -> Clerk fires `user.deleted` webhook -> Convex cleans up all related data.

### Clerk Hook Reference

| Hook | Package | Returns |
|------|---------|---------|
| `useAuth()` | `@clerk/clerk-expo` | `{ isLoaded, isSignedIn, signOut }` |
| `useUser()` | `@clerk/clerk-expo` | `{ user }` |
| `useSignIn()` | `@clerk/clerk-expo` | `{ signIn, setActive, isLoaded }` |
| `useSignUp()` | `@clerk/clerk-expo` | `{ signUp, setActive, isLoaded }` |
| `useSignInWithApple()` | `@clerk/clerk-expo` | `{ startAppleAuthenticationFlow }` |
| `useConvexAuth()` | `convex/react` | `{ isAuthenticated }` |

### Common Clerk Error Codes

| Code | Meaning |
|------|---------|
| `form_password_incorrect` | Wrong password |
| `form_identifier_not_found` | No account with this email |
| `form_param_format_invalid` | Invalid email format |
| `form_identifier_exists` | Email already registered |
| `form_password_pwned` | Password in breached database |
| `form_password_length_too_short` | Password too short |

### Security Summary

| Layer | Mechanism |
|-------|-----------|
| Client token storage | `expo-secure-store` (encrypted) |
| Client-to-backend auth | JWT auto-attached by `ConvexProviderWithClerk` |
| Backend JWT validation | Convex validates against `CLERK_JWT_ISSUER_DOMAIN` |
| Webhook security | `svix` verifies signatures with `CLERK_WEBHOOK_SECRET` |
| Per-endpoint authorization | `getUser()` at the top of every mutation/query |
| Internal mutations | `internalMutation` prevents client access |
| Account deletion | Cascading cleanup via webhook |
| Token refresh | Handled automatically by Clerk SDK |

### Gotchas

- Webhook URL uses `.convex.site` (NOT `.convex.cloud`)
- There's a ~1s delay between Clerk action and webhook arrival -- `createIfMissing` in `getUser()` acts as fallback
- Clerk retries failed webhooks with exponential backoff automatically
- `v.any() as Validator<UserJSON>` skips runtime validation but gives correct TypeScript types
- On `user.updated`, only patch Clerk-managed fields -- never overwrite app-specific fields like `nickname`

## Reference Files

- `references/backend.md` - Full backend implementation (getUser, user mutations, onboarding)
- `references/frontend.md` - Full frontend implementation (providers, forms, Apple Sign-In, modals)
- `references/webhook-setup.md` - Step-by-step webhook configuration guide
