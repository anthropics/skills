# Webhook Setup Guide (Step-by-Step)

## Why Webhooks Are Needed

Convex validates JWTs from Clerk via `ctx.auth.getUserIdentity()`, but that only gives you JWT claims (subject, email, name). It does **not** create a database record. You need a `users` table to:

- Store app-specific fields (nickname, status, preferences)
- Create relationships between users and other data
- Query users by ID in mutations and queries

**Data flow:**
```
User signs up -> Clerk creates user -> Clerk fires POST to webhook
-> Convex HTTP endpoint receives it -> Svix verifies signature
-> Internal mutation inserts/updates user in Convex DB
```

## Step 1: Install Dependencies

```bash
npm install @clerk/backend svix
```

| Package | Purpose |
|---------|---------|
| `@clerk/backend` | `WebhookEvent` and `UserJSON` TypeScript types |
| `svix` | Webhook signature verification |

## Step 2: Define User Schema

```typescript
// convex/schema.ts
users: defineTable({
  externalId: v.string(),            // Clerk user ID
  name: v.optional(v.string()),
  email: v.optional(v.string()),
  image_url: v.optional(v.string()),
  has_image: v.optional(v.boolean()),
  nickname: v.optional(v.string()),
  status: v.union(v.literal("online"), v.literal("offline")),
})
  .index("by_externalId", ["externalId"])
```

The `by_externalId` index is **critical**.

## Step 3: Create Internal Mutations

See `backend.md` for full `upsertFromClerk` and `deleteFromClerk` implementations.

Key design decisions:
- `upsertFromClerk` handles both `user.created` and `user.updated` (idempotent)
- On insert, set app-specific defaults (`status: "online"`)
- On patch, only update Clerk-managed fields -- never overwrite `nickname`, `status`
- `deleteFromClerk` cleans up all related data before deleting user record
- `v.any() as Validator<UserJSON>` skips runtime validation but gives TypeScript types

## Step 4: Create HTTP Endpoint

See `backend.md` for full `convex/http.ts` implementation.

Signature verification:
1. Clerk signs every payload using your `CLERK_WEBHOOK_SECRET` (via Svix)
2. Three headers sent: `svix-id`, `svix-timestamp`, `svix-signature`
3. `Webhook.verify()` re-computes signature and compares to header
4. Mismatch (tampered payload, wrong secret, replay attack) -> throws -> return 400

## Step 5: Deploy Convex

```bash
npx convex deploy
```

Note your HTTP Actions URL:
```
https://<your-deployment-name>.convex.site
```

**IMPORTANT:** Domain ends in `.convex.site`, NOT `.convex.cloud`. The `.cloud` domain is for queries/mutations. The `.site` domain is for HTTP actions.

Full webhook endpoint:
```
https://<your-deployment-name>.convex.site/clerk-users-webhook
```

## Step 6: Configure Clerk Dashboard

1. Go to **Clerk Dashboard** (https://dashboard.clerk.com)
2. Navigate to **Webhooks** in the left sidebar
3. Click **Add Endpoint**
4. Fill in:
   - **Endpoint URL:** `https://<your-deployment-name>.convex.site/clerk-users-webhook`
   - **Message Filtering:** Click **"user"** to subscribe to:
     - `user.created` -- new user signs up
     - `user.updated` -- profile changes (name, email, avatar)
     - `user.deleted` -- account deleted
5. Click **Create**
6. Copy the **Signing Secret** (starts with `whsec_`)

## Step 7: Set Environment Variable

In **Convex Dashboard** (https://dashboard.convex.dev):
1. Select your project
2. Go to **Settings** -> **Environment Variables**
3. Add: `CLERK_WEBHOOK_SECRET` = `whsec_<your-value>`

For local development, also add to `.env.local`:
```env
CLERK_WEBHOOK_SECRET=whsec_<your-signing-secret>
```

## Step 8: Verify It Works

1. In Clerk Dashboard Webhooks, click your endpoint
2. Go to **Testing** tab
3. Select `user.created`, click **Send Test Webhook**
4. Check **Logs** tab for `200` response
5. In Convex Dashboard, check `users` table for test record

End-to-end verification:
1. Sign up a real user -> check Convex `users` table (1-2s)
2. Update profile in Clerk Dashboard -> Convex record should update
3. Delete user in Clerk Dashboard -> Convex record + related data removed

## Troubleshooting

| Issue | Cause | Fix |
|-------|-------|-----|
| Webhook returns 400 | Wrong `CLERK_WEBHOOK_SECRET` | Re-copy from Clerk Dashboard |
| Webhook returns 400 | Secret only in `.env.local` | Set in Convex Dashboard too |
| Endpoint unreachable | Wrong URL domain | Use `.convex.site`, not `.convex.cloud` |
| User not synced | Webhook not deployed | Run `npx convex deploy` first |
| `user.deleted` user not found | User created pre-webhooks | Handle with `console.warn` |
| Duplicate records | Missing `.unique()` | Always use `.unique()` with `by_externalId` |

**Timing note:** ~1s delay between Clerk action and webhook arrival. Use `createIfMissing` in `getUser()` as fallback.

**Retry behavior:** Clerk/Svix retries failed webhooks with exponential backoff automatically.
