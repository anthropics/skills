# Deployment & Infrastructure (2025-2026)

## Platform Decision Guide

### Vercel — Default for Next.js
Zero-config deployment for Next.js, Nuxt, SvelteKit, Astro, Remix. Optimized for serverless functions and edge middleware.

Key features:
- Automatic CI/CD from GitHub (preview deployments for every PR)
- Edge Middleware (Cloudflare Workers-based, zero cold starts)
- Vercel Blob (file storage), KV (Redis-compatible), Postgres (Neon-backed)
- Automatic image optimization, ISR (Incremental Static Regeneration)
- Analytics and Core Web Vitals monitoring

```json
// vercel.json (minimal config):
{
  "regions": ["iad1", "cdg1"],
  "functions": {
    "app/api/**": { "maxDuration": 60 }
  }
}
```

Free tier: generous for hobby/side projects. Pro plan: $20/user/mo. Expensive at scale — consider Railway/Render + Cloudflare CDN for cost-sensitive apps.

### Railway — Best Developer Experience for Backend Services
"Railway is the fastest path from code to URL." Auto-detects runtime with Railpack — no Dockerfile required for most projects. Includes PostgreSQL, Redis, and custom services.

```yaml
# railway.toml (optional override):
[build]
builder = "nixpacks"

[deploy]
startCommand = "node dist/server.js"
healthcheckPath = "/health"
restartPolicyType = "on-failure"
```

Railway excels for: Node.js APIs, FastAPI backends, background workers with BullMQ+Redis, monorepos with multiple services. Connect GitHub → Railway detects and deploys. $5/mo hobby, usage-based after.

### Fly.io — Global Distribution, Docker-Native
Requires Dockerfile and `flyctl` CLI. Most flexible — full VM-like environment.
```bash
fly launch        # generates fly.toml
fly deploy        # build + deploy
fly scale count 2 # run 2 instances
```

Best for: apps needing multiple regions, WebSocket-heavy apps, Docker-dependent apps, apps that need persistent volumes. No sleep-to-zero by default (machines stay warm). Use Fly Machines API for on-demand scaling.

```toml
# fly.toml:
[http_service]
  internal_port = 3000
  force_https = true
  auto_stop_machines = true
  auto_start_machines = true
  min_machines_running = 0

[[regions]]
  code = "iad"
```

### Render — Managed Services with Predictable Pricing
Auto-deploy from GitHub, managed PostgreSQL, Redis, background workers. No Docker expertise needed. Better than Railway for regulated environments (SOC 2).

### Cloudflare Workers / Pages — Edge-First
Workers for API/backend logic, Pages for static + SSR frontend. Zero cold starts. Most cost-effective at scale ($5/mo for 10M requests).

```bash
npm create cloudflare@latest my-app
wrangler deploy
wrangler dev  # local dev with Cloudflare runtime
```

---

## Turborepo Monorepo — Production Configuration

### Structure
```
apps/
  web/           # Next.js frontend
  api/           # Hono/Fastify API (or same Next.js app)
  mobile/        # Expo app
packages/
  ui/            # Shared shadcn/ui components
  db/            # Drizzle schema + migrations
  types/         # Shared TypeScript types
  utils/         # Shared utilities
  config/        # Shared ESLint, TypeScript, Tailwind configs
turbo.json
pnpm-workspace.yaml
package.json
```

### pnpm-workspace.yaml
```yaml
packages:
  - 'apps/*'
  - 'packages/*'
```

### turbo.json
```json
{
  "$schema": "https://turbo.build/schema.json",
  "tasks": {
    "build": {
      "dependsOn": ["^build"],
      "outputs": [".next/**", "!.next/cache/**", "dist/**"]
    },
    "dev": {
      "cache": false,
      "persistent": true
    },
    "test": {
      "dependsOn": ["^build"],
      "outputs": ["coverage/**"]
    },
    "lint": {
      "outputs": []
    },
    "type-check": {
      "dependsOn": ["^build"]
    }
  }
}
```

### GitHub Actions CI (Turborepo-aware)
```yaml
# .github/workflows/ci.yml:
name: CI
on: [push, pull_request]

jobs:
  ci:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
        with:
          fetch-depth: 0  # Required for Turborepo to compare with main
      - uses: pnpm/action-setup@v4
        with:
          version: 9
      - uses: actions/setup-node@v4
        with:
          node-version: 22
          cache: 'pnpm'
      - run: pnpm install --frozen-lockfile
      - run: pnpm turbo build lint test --filter='...[origin/main...HEAD]'
        env:
          TURBO_TOKEN: ${{ secrets.TURBO_TOKEN }}  # Remote cache
          TURBO_TEAM: ${{ secrets.TURBO_TEAM }}
```

Remote caching: free on Vercel. Cuts CI time by 10-12x through affected-only execution.

### Shared Package Pattern
```ts
// packages/ui/src/button.tsx:
export { Button } from './components/button';

// packages/ui/package.json:
{
  "name": "@acme/ui",
  "exports": {
    ".": { "types": "./dist/index.d.ts", "default": "./src/index.ts" }
  }
}

// apps/web/package.json:
{ "dependencies": { "@acme/ui": "workspace:*" } }
```

---

## Docker & Containerization

### Next.js Production Dockerfile
```dockerfile
FROM node:22-alpine AS base
RUN corepack enable pnpm

FROM base AS deps
WORKDIR /app
COPY package.json pnpm-lock.yaml ./
RUN pnpm install --frozen-lockfile

FROM base AS builder
WORKDIR /app
COPY --from=deps /app/node_modules ./node_modules
COPY . .
RUN pnpm build

FROM base AS runner
WORKDIR /app
ENV NODE_ENV=production
RUN addgroup --system --gid 1001 nodejs && adduser --system --uid 1001 nextjs
COPY --from=builder /app/public ./public
COPY --from=builder --chown=nextjs:nodejs /app/.next/standalone ./
COPY --from=builder --chown=nextjs:nodejs /app/.next/static ./.next/static
USER nextjs
EXPOSE 3000
CMD ["node", "server.js"]
```

Enable standalone output in next.config.ts:
```ts
const nextConfig = { output: 'standalone' };
```

---

## SST v3 — Infrastructure as Code for TypeScript

SST v3 (Ion) uses Pulumi + Terraform providers under the hood. TypeScript-first, multi-cloud (AWS + 150+ providers including Cloudflare, Vercel).

```ts
// sst.config.ts:
/// <reference path="./.sst/platform/config.d.ts" />

export default $config({
  app(input) {
    return {
      name: 'my-app',
      removal: input?.stage === 'production' ? 'retain' : 'remove',
      home: 'aws',
    };
  },
  async run() {
    const bucket = new sst.aws.Bucket('MyBucket', { public: true });

    const api = new sst.aws.Function('Api', {
      handler: 'packages/functions/src/api.handler',
      url: true,
      environment: { BUCKET_NAME: bucket.name },
    });

    const web = new sst.aws.Nextjs('Web', {
      link: [api, bucket],
      domain: {
        name: 'myapp.com',
        redirects: ['www.myapp.com'],
      },
    });

    return { web: web.url, api: api.url };
  },
});
```

```bash
sst dev    # local development with live Lambda
sst deploy --stage production
```

SST advantages vs Terraform/CDK: TypeScript native, no YAML, resource linking (auto environment variable injection), local Lambda dev with actual cloud resources.

---

## GitHub Actions — Key Patterns

### Preview Deployments
```yaml
- name: Deploy Preview
  if: github.event_name == 'pull_request'
  run: vercel deploy --token=${{ secrets.VERCEL_TOKEN }}
  # Or for Railway:
  run: railway up --service web --environment pr-${{ github.event.pull_request.number }}
```

### Database Migrations in CI
```yaml
- name: Run Migrations
  run: pnpm drizzle-kit migrate
  env:
    DATABASE_URL: ${{ secrets.DATABASE_URL }}
```

### Environment-Specific Secrets
Use GitHub Environments (Settings > Environments) with required reviewers for production. Store `DATABASE_URL`, API keys per environment.
