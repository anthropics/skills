---
name: "saas-scaffolder"
description: "Generates complete, production-ready SaaS project boilerplate including authentication, database schemas, billing integration, API routes, and a working dashboard using Next.js 14+ App Router, TypeScript, Tailwind CSS, shadcn/ui, Drizzle ORM, and Stripe. Use when the user wants to create a new SaaS app, start a subscription-based web project, scaffold a Next.js application, or mentions terms like starter template, boilerplate, new project, or wiring up auth and payments."
---

# SaaS Scaffolder

**Tier:** POWERFUL  
**Category:** Product Team  
**Domain:** Full-Stack Development / Project Bootstrapping

---

## Input Format

```
Product: [name]
Description: [1-3 sentences]
Auth: nextauth | clerk | supabase
Database: neondb | supabase | planetscale
Payments: stripe | lemonsqueezy | none
Features: [comma-separated list]
```

---

## File Tree Output

```
my-saas/
├── app/
│   ├── (auth)/
│   │   ├── login/page.tsx
│   │   ├── register/page.tsx
│   │   └── layout.tsx
│   ├── (dashboard)/
│   │   ├── dashboard/page.tsx
│   │   ├── settings/page.tsx
│   │   ├── billing/page.tsx
│   │   └── layout.tsx
│   ├── (marketing)/
│   │   ├── page.tsx
│   │   ├── pricing/page.tsx
│   │   └── layout.tsx
│   ├── api/
│   │   ├── auth/[...nextauth]/route.ts
│   │   ├── webhooks/stripe/route.ts
│   │   ├── billing/checkout/route.ts
│   │   └── billing/portal/route.ts
│   └── layout.tsx
├── components/
│   ├── ui/
│   ├── auth/
│   │   ├── login-form.tsx
│   │   └── register-form.tsx
│   ├── dashboard/
│   │   ├── sidebar.tsx
│   │   ├── header.tsx
│   │   └── stats-card.tsx
│   ├── marketing/
│   │   ├── hero.tsx
│   │   ├── features.tsx
│   │   ├── pricing.tsx
│   │   └── footer.tsx
│   └── billing/
│       ├── plan-card.tsx
│       └── usage-meter.tsx
├── lib/
│   ├── auth.ts
│   ├── db.ts
│   ├── stripe.ts
│   ├── validations.ts
│   └── utils.ts
├── db/
│   ├── schema.ts
│   └── migrations/
├── hooks/
│   ├── use-subscription.ts
│   └── use-user.ts
├── types/index.ts
├── middleware.ts
├── .env.example
├── drizzle.config.ts
└── next.config.ts
```

---

## Key Component Patterns

### Auth Config (NextAuth)

```typescript
// lib/auth.ts
import { NextAuthOptions } from "next-auth"
import GoogleProvider from "next-auth/providers/google"
import { DrizzleAdapter } from "@auth/drizzle-adapter"
import { db } from "./db"

export const authOptions: NextAuthOptions = {
  adapter: DrizzleAdapter(db),
  providers: [
    GoogleProvider({
      clientId: process.env.GOOGLE_CLIENT_ID!,
      clientSecret: process.env.GOOGLE_CLIENT_SECRET!,
    }),
  ],
  callbacks: {
    session: async ({ session, user }) => ({
      ...session,
      user: {
        ...session.user,
        id: user.id,
        subscriptionStatus: user.subscriptionStatus,
      },
    }),
  },
  pages: { signIn: "/login" },
}
```

### Database Schema (Drizzle + NeonDB)

```typescript
// db/schema.ts
import { pgTable, text, timestamp, integer } from "drizzle-orm/pg-core"

export const users = pgTable("users", {
  id: text("id").primaryKey().$defaultFn(() => crypto.randomUUID()),
  name: text("name"),
  email: text("email").notNull().unique(),
  emailVerified: timestamp("emailVerified"),
  image: text("image"),
  stripeCustomerId: text("stripe_customer_id").unique(),
  stripeSubscriptionId: text("stripe_subscription_id"),
  stripePriceId: text("stripe_price_id"),
  stripeCurrentPeriodEnd: timestamp("stripe_current_period_end"),
  createdAt: timestamp("created_at").defaultNow().notNull(),
})

export const accounts = pgTable("accounts", {
  userId: text("user_id").notNull().references(() => users.id, { onDelete: "cascade" }),
  type: text("type").notNull(),
  provider: text("provider").notNull(),
  providerAccountId: text("provider_account_id").notNull(),
  refresh_token: text("refresh_token"),
  access_token: text("access_token"),
  expires_at: integer("expires_at"),
})
```

### Stripe Checkout Route

```typescript
// app/api/billing/checkout/route.ts
import { NextResponse } from "next/server"
import { getServerSession } from "next-auth"
import { authOptions } from "@/lib/auth"
import { stripe } from "@/lib/stripe"
import { db } from "@/lib/db"
import { users } from "@/db/schema"
import { eq } from "drizzle-orm"

export async function POST(req: Request) {
  const session = await getServerSession(authOptions)
  if (!session?.user) return NextResponse.json({ error: "Unauthorized" }, { status: 401 })

  const { priceId } = await req.json()
  const [user] = await db.select().from(users).where(eq(users.id, session.user.id))

  let customerId = user.stripeCustomerId
  if (!customerId) {
    const customer = await stripe.customers.create({ email: session.user.email! })
    customerId = customer.id
    await db.update(users).set({ stripeCustomerId: customerId }).where(eq(users.id, user.id))
  }

  const checkoutSession = await stripe.checkout.sessions.create({
    customer: customerId,
    mode: "subscription",
    payment_method_types: ["card"],
    line_items: [{ price: priceId, quantity: 1 }],
    success_url: `${process.env.NEXT_PUBLIC_APP_URL}/dashboard?upgraded=true`,
    cancel_url: `${process.env.NEXT_PUBLIC_APP_URL}/pricing`,
    subscription_data: { trial_period_days: 14 },
  })

  return NextResponse.json({ url: checkoutSession.url })
}
```

### Middleware

```typescript
// middleware.ts
import { withAuth } from "next-auth/middleware"
import { NextResponse } from "next/server"

export default withAuth(
  function middleware(req) {
    const token = req.nextauth.token
    if (req.nextUrl.pathname.startsWith("/dashboard") && !token) {
      return NextResponse.redirect(new URL("/login", req.url))
    }
  },
  { callbacks: { authorized: ({ token }) => !!token } }
)

export const config = {
  matcher: ["/dashboard/:path*", "/settings/:path*", "/billing/:path*"],
}
```

### Environment Variables Template

```bash
# .env.example
NEXT_PUBLIC_APP_URL=http://localhost:3000
DATABASE_URL=postgresql://user:pass@ep-xxx.us-east-1.aws.neon.tech/neondb?sslmode=require
NEXTAUTH_SECRET=generate-with-openssl-rand-base64-32
NEXTAUTH_URL=http://localhost:3000
GOOGLE_CLIENT_ID=
GOOGLE_CLIENT_SECRET=
STRIPE_SECRET_KEY=sk_test_...
STRIPE_WEBHOOK_SECRET=whsec_...
NEXT_PUBLIC_STRIPE_PUBLISHABLE_KEY=pk_test_...
STRIPE_PRO_PRICE_ID=price_...
```

---

## Scaffold Checklist

The following phases must be completed in order. **Validate at the end of each phase before proceeding.**

### Phase 1 — Foundation
- [ ] 1. Next.js initialized with TypeScript and App Router
- [ ] 2. Tailwind CSS configured with custom theme tokens
- [ ] 3. shadcn/ui installed and configured
- [ ] 4. ESLint + Prettier configured
- [ ] 5. `.env.example` created with all required variables

✅ **Validate:** Run `npm run build` — no TypeScript or lint errors should appear.  
🔧 **If build fails:** Check `tsconfig.json` paths and that all shadcn/ui peer dependencies are installed.

### Phase 2 — Database
- [ ] 6. Drizzle ORM installed and configured
- [ ] 7. Schema written (users, accounts, sessions, verification_tokens)
- [ ] 8. Initial migration generated and applied
- [ ] 9. DB client singleton exported from `lib/db.ts`
- [ ] 10. DB connection tested in local environment

✅ **Validate:** Run a simple `db.select().from(users)` in a test script — it should return an empty array without throwing.  
🔧 **If DB connection fails:** Verify `DATABASE_URL` format includes `?sslmode=require` for NeonDB/Supabase. Check that the migration has been applied with `drizzle-kit push` (dev) or `drizzle-kit migrate` (prod).

### Phase 3 — Authentication
- [ ] 11. Auth provider installed (NextAuth / Clerk / Supabase)
- [ ] 12. OAuth provider configured (Google / GitHub)
- [ ] 13. Auth API route created
- [ ] 14. Session callback adds user ID and subscription status
- [ ] 15. Middleware protects dashboard routes
- [ ] 16. Login and register pages built with error states

✅ **Validate:** Sign in via OAuth, confirm session user has `id` and `subscriptionStatus`. Attempt to access `/dashboard` without a session — you should be redirected to `/login`.  
🔧 **If sign-out loops occur in production:** Ensure `NEXTAUTH_SECRET` is set and consistent across deployments. Add `declare module "next-auth"` to extend session types if TypeScript errors appear.

### Phase 4 — Payments
- [ ] 17. Stripe client initialized with TypeScript types
- [ ] 18. Checkout session route created
- [ ] 19. Customer portal route created
- [ ] 20. Stripe webhook handler with signature verification
- [ ] 21. Webhook updates user subscription status in DB idempotently

✅ **Validate:** Complete a Stripe test checkout using a `4242 4242 4242 4242` card. Confirm `stripeSubscriptionId` is written to the DB. Replay the `checkout.session.completed` webhook event and confirm idempotency (no duplicate DB writes).  
🔧 **If webhook signature fails:** Use `stripe listen --forward-to localhost:3000/api/webhooks/stripe` locally — never hardcode the raw webhook secret. Verify `STRIPE_WEBHOOK_SECRET` matches the listener output.

### Phase 5 — UI
- [ ] 22. Landing page with hero, features, pricing sections
- [ ] 23. Dashboard layout with sidebar and responsive header
- [ ] 24. Billing page showing current plan and upgrade options
- [ ] 25. Settings page with profile update form and success states

✅ **Validate:** Run `npm run build` for a final production build check. Navigate all routes manually and confirm no broken layouts, missing session data, or hydration errors.

---

## Reference Files

For additional guidance, generate the following companion reference files alongside the scaffold:

- **`CUSTOMIZATION.md`** — Auth providers, database options, ORM alternatives, payment providers, UI themes, and billing models (per-seat, flat-rate, usage-based).
- **`PITFALLS.md`** — Common failure modes: missing `NEXTAUTH_SECRET`, webhook secret mismatches, Edge runtime conflicts with Drizzle, unextended session types, and migration strategy differences between dev and prod.
- **`BEST_PRACTICES.md`** — Stripe singleton pattern, server actions for form mutations, idempotent webhook handlers, `Suspense` boundaries for async dashboard data, server-side feature gating via `stripeCurrentPeriodEnd`, and rate limiting on auth routes with Upstash Redis + `@upstash/ratelimit`.
