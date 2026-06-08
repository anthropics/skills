# Authentication, Authorization & Security (2025-2026)

## The 2025 Auth Landscape Shift

The landscape shifted dramatically in late 2024-2025:
- **Lucia Auth** deprecated in March 2025 — do not use for new projects
- **Auth.js v5 (NextAuth)**: Better Auth team took over maintenance; Auth.js team's own guidance for new projects now points to Better Auth
- **Better Auth v1** shipped stable in early 2025 — now the recommended open-source choice
- **Clerk**: still the best for rapid development and pre-built UI
- **CVE-2025-29927**: Critical Next.js vulnerability (CVSS 9.1, March 2025) — middleware bypass via `x-middleware-subrequest` header. Patch immediately if on affected versions.

---

## Better Auth — Recommended Open-Source Choice

Better Auth is framework-agnostic, fully self-hosted, plugin-driven TypeScript auth library. Full data ownership, no vendor lock-in.

### Setup
```bash
npm install better-auth
npx better-auth generate  # generates DB schema
```

```ts
// auth.ts:
import { betterAuth } from 'better-auth';
import { drizzleAdapter } from 'better-auth/adapters/drizzle';
import { twoFactor, organization, passkey } from 'better-auth/plugins';

export const auth = betterAuth({
  database: drizzleAdapter(db, { provider: 'pg' }),
  emailAndPassword: { enabled: true },
  socialProviders: {
    github: { clientId: process.env.GITHUB_CLIENT_ID!, clientSecret: process.env.GITHUB_CLIENT_SECRET! },
    google: { clientId: process.env.GOOGLE_CLIENT_ID!, clientSecret: process.env.GOOGLE_CLIENT_SECRET! },
  },
  plugins: [
    twoFactor(),
    organization(), // multi-tenant orgs
    passkey(),
  ],
});
```

```ts
// Next.js App Router — Route Handler:
// app/api/auth/[...all]/route.ts
import { auth } from '@/lib/auth';
import { toNextJsHandler } from 'better-auth/next-js';
export const { GET, POST } = toNextJsHandler(auth);

// Server Component — get session:
import { auth } from '@/lib/auth';
import { headers } from 'next/headers';
const session = await auth.api.getSession({ headers: await headers() });

// Client Component:
import { authClient } from '@/lib/auth-client';
const { data: session } = authClient.useSession();
await authClient.signIn.email({ email, password });
await authClient.signOut();
```

Better Auth advantages: 2FA, passkeys, RBAC, impersonation, organization/multi-tenant support all built-in via plugins. Sessions stored in your DB. Immediate revocation. Full code ownership.

---

## Clerk — Best for Speed to Market

Clerk: ~30-minute setup, pre-built UI components, manages the entire auth stack for you.

```tsx
// app/layout.tsx:
import { ClerkProvider } from '@clerk/nextjs';
export default function Layout({ children }) {
  return <ClerkProvider>{children}</ClerkProvider>;
}

// Protected route (middleware):
// middleware.ts:
import { clerkMiddleware, createRouteMatcher } from '@clerk/nextjs/server';
const isProtected = createRouteMatcher(['/dashboard(.*)']);
export default clerkMiddleware(async (auth, req) => {
  if (isProtected(req)) await auth.protect();
});

// Server Component:
import { currentUser } from '@clerk/nextjs/server';
const user = await currentUser();

// Pre-built UI:
import { SignIn, UserButton, OrganizationSwitcher } from '@clerk/nextjs';
```

Clerk pricing: 10,000 MAU free, then $0.02/MAU. Session tokens have 60-second TTL with automatic 50-second refresh. Clerk Organizations are GA for multi-tenant SaaS.

### Clerk vs Better Auth Decision
| Factor | Better Auth | Clerk |
|--------|-------------|-------|
| Setup time | 2-4 hours | 30 minutes |
| Vendor lock-in | None | High |
| Data ownership | Your DB | Clerk's servers |
| UI components | Build your own | Pre-built |
| Cost at scale | Fixed (your infra) | Per-MAU pricing |
| GDPR/compliance | Full control | Clerk handles |
| Best for | Funded teams, compliance-sensitive | Prototypes, fast launch |

---

## Auth.js v5 (NextAuth) — When to Use

Only for migrating existing Auth.js v4 codebases. New projects should use Better Auth.

```ts
// auth.ts (v5 pattern):
import NextAuth from 'next-auth';
import GitHub from 'next-auth/providers/github';
import { DrizzleAdapter } from '@auth/drizzle-adapter';

export const { handlers, signIn, signOut, auth } = NextAuth({
  adapter: DrizzleAdapter(db),
  providers: [GitHub],
});

// Server Component:
const session = await auth();
```

---

## JWT vs Sessions — Decision

**Sessions** (server-side): store minimal data in cookie (session ID), look up server-side. Immediate revocation, no stale data. Better Auth uses this model.

**JWTs**: stateless, include claims, no DB lookup per request. Harder to revoke (need blocklist). Use for: inter-service auth, short-lived API tokens, mobile apps without session infrastructure.

**Hybrid** (Clerk's model): short-lived JWT (60s TTL) + server-side session. Best of both.

---

## RBAC — Role-Based Access Control

### Simple Role Pattern (DB column)
```ts
// In DB schema:
export const users = pgTable('users', {
  id: serial('id').primaryKey(),
  role: text('role', { enum: ['user', 'admin', 'moderator'] }).notNull().default('user'),
});

// In Server Action/Route Handler:
const session = await getSession();
if (session.user.role !== 'admin') throw new Error('Unauthorized');
```

### Permission-Based (More Granular)
```ts
// Permission table:
export const userPermissions = pgTable('user_permissions', {
  userId: integer('user_id').references(() => users.id),
  permission: text('permission').notNull(), // 'posts:write', 'users:delete'
});

// Check permission:
async function can(userId: number, permission: string): Promise<boolean> {
  const result = await db.select().from(userPermissions)
    .where(and(eq(userPermissions.userId, userId), eq(userPermissions.permission, permission)));
  return result.length > 0;
}
```

### PostgreSQL Row-Level Security (Most Secure)
```sql
-- Enforced at DB level — even if app code is buggy:
CREATE POLICY "org_isolation" ON posts
  FOR ALL USING (org_id = current_setting('app.org_id')::int);

-- Set in DB connection before queries:
await db.execute(sql`SET LOCAL app.org_id = ${session.orgId}`);
```

---

## Security — OWASP Top 10 for Full-Stack Apps

### XSS Prevention
React escapes JSX content by default — safe from reflected XSS. Dangerous patterns to avoid:
```tsx
// DANGEROUS — never do this:
<div dangerouslySetInnerHTML={{ __html: userContent }} />

// SAFE alternative — use a sanitizer:
import DOMPurify from 'dompurify';
<div dangerouslySetInnerHTML={{ __html: DOMPurify.sanitize(userContent) }} />
```

### CSRF Protection
Next.js App Router Server Actions have built-in CSRF protection (Origin header check). For API routes:
```ts
// Verify Origin header matches your domain:
if (req.headers.get('origin') !== process.env.NEXT_PUBLIC_URL) {
  return new Response('Forbidden', { status: 403 });
}
```

### Content Security Policy (CSP)
```ts
// next.config.ts:
const cspHeader = `
  default-src 'self';
  script-src 'self' 'nonce-${nonce}';
  style-src 'self' 'unsafe-inline';
  img-src 'self' blob: data: https:;
  connect-src 'self' https://api.example.com;
  frame-ancestors 'none';
`;
```
Use `nonce`-based CSP in Next.js (set in middleware, passed to `<Script nonce={nonce}>` and `next.config.ts`).

### Rate Limiting
```ts
// Upstash Ratelimit (works on edge):
import { Ratelimit } from '@upstash/ratelimit';
import { Redis } from '@upstash/redis';

const ratelimit = new Ratelimit({
  redis: Redis.fromEnv(),
  limiter: Ratelimit.slidingWindow(10, '10 s'), // 10 req/10 seconds
});

// In middleware or route handler:
const identifier = req.ip ?? 'anonymous';
const { success, remaining } = await ratelimit.limit(identifier);
if (!success) return new Response('Too Many Requests', { status: 429 });
```

### SQL Injection
Parameterized queries prevent SQL injection. All ORMs (Drizzle, Prisma) use parameterized queries by default. Never interpolate user input into raw SQL strings.

```ts
// SAFE with Drizzle:
await db.select().from(posts).where(eq(posts.id, userId));

// DANGEROUS — never do:
await db.execute(sql.raw(`SELECT * FROM posts WHERE id = ${userId}`));
// SAFE raw SQL:
await db.execute(sql`SELECT * FROM posts WHERE id = ${userId}`);
```

### Dependency Vulnerability Scanning
- Enable **Dependabot** in GitHub: automatically opens PRs for vulnerable dependencies
- **Snyk**: `snyk test` in CI pipeline
- `npm audit` / `pnpm audit` as part of CI
- Set `overrides` in package.json to force patched versions of transitive dependencies

### Environment Variables
- Never commit `.env` files
- Use `.env.example` with all variable names (no values) as documentation
- Runtime validation with Zod:
```ts
import { z } from 'zod';
const envSchema = z.object({
  DATABASE_URL: z.string().url(),
  NEXTAUTH_SECRET: z.string().min(32),
  GITHUB_CLIENT_SECRET: z.string(),
});
export const env = envSchema.parse(process.env);
```
Use `@t3-oss/env-nextjs` for Next.js-specific env validation.
