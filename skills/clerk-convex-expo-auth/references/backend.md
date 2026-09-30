# Backend Implementation Reference

## Auth Helper (`convex/helpers/auth.ts`)

```typescript
import { Id } from "../_generated/dataModel";
import { MutationCtx, QueryCtx } from "../_generated/server";

// Overload 1: Soft lookup (returns null if not authenticated)
export async function getUser(
  ctx: QueryCtx | MutationCtx,
): Promise<Id<"users"> | null>;

// Overload 2: Required auth (throws if not authenticated)
export async function getUser(
  ctx: QueryCtx | MutationCtx,
  options: { required: true; createIfMissing?: boolean },
): Promise<Id<"users">>;

// Implementation
export async function getUser(
  ctx: QueryCtx | MutationCtx,
  options?: { required?: true; createIfMissing?: boolean },
): Promise<Id<"users"> | null> {
  const identity = await ctx.auth.getUserIdentity();

  if (!identity) {
    if (options?.required) {
      throw new Error("Not authenticated");
    }
    return null;
  }

  const user = await ctx.db
    .query("users")
    .withIndex("by_externalId", (q) => q.eq("externalId", identity.subject))
    .unique();

  if (user) {
    return user._id;
  }

  if (options?.createIfMissing) {
    const userId = await ctx.db.insert("users", {
      externalId: identity.subject,
      name: identity.name ?? undefined,
      email: identity.email ?? undefined,
      status: "online",
    });
    return userId;
  }

  if (options?.required) {
    throw new Error("Not authenticated");
  }
  return null;
}
```

## User Mutations - Internal (Webhook-Triggered)

**File: `convex/users.ts`**

These are `internalMutation` -- only callable from the server, never from the client.

```typescript
import { UserJSON } from "@clerk/backend";
import { v, Validator } from "convex/values";
import {
  internalMutation,
  MutationCtx,
  QueryCtx,
} from "./_generated/server";

async function userByExternalId(ctx: QueryCtx, externalId: string) {
  return await ctx.db
    .query("users")
    .withIndex("by_externalId", (q) => q.eq("externalId", externalId))
    .unique();
}

export const upsertFromClerk = internalMutation({
  args: { data: v.any() as Validator<UserJSON> },
  async handler(ctx, { data }) {
    const userAttributes = {
      name: `${data.first_name} ${data.last_name}`,
      email: data.email_addresses[0]?.email_address || "",
      externalId: data.id,
      image_url: data.image_url,
      has_image: data.has_image,
    };

    const existingUser = await userByExternalId(ctx, data.id);

    if (existingUser === null) {
      await ctx.db.insert("users", {
        ...userAttributes,
        status: "online",
        nickname: undefined,
      });
    } else {
      // Only update Clerk-managed fields -- never overwrite nickname, status
      await ctx.db.patch(existingUser._id, userAttributes);
    }
  },
});

export const deleteFromClerk = internalMutation({
  args: { clerkUserId: v.string() },
  async handler(ctx, { clerkUserId }) {
    const user = await userByExternalId(ctx, clerkUserId);

    if (user !== null) {
      await performUserDataCleanup(ctx, user._id);
      await ctx.db.delete(user._id);
    } else {
      console.warn(
        `Can't delete user, there is none for Clerk user ID: ${clerkUserId}`,
      );
    }
  },
});

async function performUserDataCleanup(ctx: MutationCtx, userId: Id<"users">) {
  // Customize: delete games, invites, queue entries, etc.
}
```

## User Mutations - Public

```typescript
export const getCurrentUser = query({
  args: {},
  handler: async (ctx) => {
    const userId = await getUser(ctx);
    if (!userId) return null;
    const user = await ctx.db.get(userId);
    return {
      id: user._id,
      nickname: user.nickname,
      displayTag: user.displayTag,
      status: user.status,
    };
  },
});

export const setUserStatus = mutation({
  args: { status: userStatusValidator },
  handler: async (ctx, args) => {
    const userId = await getUser(ctx);
    if (!userId) throw new Error("Not authenticated");
    await ctx.db.patch(userId, { status: args.status });
  },
});
```

## Onboarding Mutations (`convex/onboarding.ts`)

```typescript
export const hasCompletedOnboarding = query({
  args: {},
  handler: async (ctx) => {
    const userId = await getUser(ctx, { required: true, createIfMissing: true });
    const user = await ctx.db.get(userId);
    return !!user?.nickname;
  },
});

export const setNickname = mutation({
  args: { nickname: v.string() },
  handler: async (ctx, args) => {
    const userId = await getUser(ctx, { required: true, createIfMissing: true });
    // Validate: 3-20 chars, alphanumeric + underscore
    // Generate unique displayTag (nickname#XXXX)
    await ctx.db.patch(userId, { nickname, displayTag });
  },
});

export const skipNickname = mutation({
  args: {},
  handler: async (ctx) => {
    const userId = await getUser(ctx, { required: true, createIfMissing: true });
    // Assign random default nickname
  },
});
```

## HTTP Webhook Handler (`convex/http.ts`)

```typescript
import type { WebhookEvent } from "@clerk/backend";
import { httpRouter } from "convex/server";
import { Webhook } from "svix";
import { internal } from "./_generated/api";
import { httpAction } from "./_generated/server";

const http = httpRouter();

http.route({
  path: "/clerk-users-webhook",
  method: "POST",
  handler: httpAction(async (ctx, request) => {
    const event = await validateRequest(request);
    if (!event) {
      return new Response("Invalid webhook signature", { status: 400 });
    }

    switch (event.type) {
      case "user.created":
      case "user.updated":
        await ctx.runMutation(internal.users.upsertFromClerk, {
          data: event.data,
        });
        break;

      case "user.deleted": {
        const clerkUserId = event.data.id!;
        await ctx.runMutation(internal.users.deleteFromClerk, {
          clerkUserId,
        });
        break;
      }

      default:
        console.log("Ignored Clerk webhook event", event.type);
    }

    return new Response(null, { status: 200 });
  }),
});

async function validateRequest(
  req: Request,
): Promise<WebhookEvent | null> {
  const payloadString = await req.text();

  const svixHeaders = {
    "svix-id": req.headers.get("svix-id")!,
    "svix-timestamp": req.headers.get("svix-timestamp")!,
    "svix-signature": req.headers.get("svix-signature")!,
  };

  const wh = new Webhook(process.env.CLERK_WEBHOOK_SECRET!);
  try {
    return wh.verify(payloadString, svixHeaders) as unknown as WebhookEvent;
  } catch (error) {
    console.error("Error verifying webhook event", error);
    return null;
  }
}

export default http;
```
