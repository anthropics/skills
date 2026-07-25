# Fullstack Development Workflows

Complete development lifecycle workflows from local setup to production deployment.

---

## Table of Contents

- [Local Development Setup](#local-development-setup)
- [Git Workflows](#git-workflows)
- [CI/CD Pipelines](#cicd-pipelines)
- [Testing Strategies](#testing-strategies)
- [Code Review Process](#code-review-process)
- [Deployment Strategies](#deployment-strategies)
- [Monitoring and Observability](#monitoring-and-observability)

---

## Local Development Setup

### Docker Compose Development Environment

```yaml
# docker-compose.yml
version: "3.8"

services:
  app:
    build:
      context: .
      target: development
    volumes:
      - .:/app
      - /app/node_modules
    ports:
      - "3000:3000"
    environment:
      - DATABASE_URL=postgresql://user:pass@db:5432/app
      - REDIS_URL=redis://redis:6379
    depends_on:
      - db
      - redis

  db:
    image: postgres:16-alpine
    environment:
      POSTGRES_USER: user
      POSTGRES_PASSWORD: pass
      POSTGRES_DB: app
    volumes:
      - postgres_data:/var/lib/postgresql/data
    ports:
      - "5432:5432"

  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"

volumes:
  postgres_data:
```

**Multistage Dockerfile:**

```dockerfile
# Base stage
FROM node:20-alpine AS base
WORKDIR /app
RUN apk add --no-cache libc6-compat

# Development stage
FROM base AS development
COPY package*.json ./
RUN npm ci
COPY . .
CMD ["npm", "run", "dev"]

# Builder stage
FROM base AS builder
COPY package*.json ./
RUN npm ci
COPY . .
RUN npm run build

# Production stage
FROM base AS production
ENV NODE_ENV=production
COPY --from=builder /app/package*.json ./
RUN npm ci --only=production
COPY --from=builder /app/dist ./dist
USER node
CMD ["node", "dist/index.js"]
```

### Environment Configuration

```bash
# .env.local (development)
DATABASE_URL="postgresql://user:pass@localhost:5432/app_dev"
REDIS_URL="redis://localhost:6379"
JWT_SECRET="development-secret-change-in-prod"
LOG_LEVEL="debug"

# .env.test
DATABASE_URL="postgresql://user:pass@localhost:5432/app_test"
LOG_LEVEL="error"

# .env.production (via secrets management)
DATABASE_URL="${DATABASE_URL}"
REDIS_URL="${REDIS_URL}"
JWT_SECRET="${JWT_SECRET}"
```

**Environment validation:**

```typescript
import { z } from "zod";

const envSchema = z.object({
  NODE_ENV: z.enum(["development", "test", "production"]),
  DATABASE_URL: z.string().url(),
  REDIS_URL: z.string().url().optional(),
  JWT_SECRET: z.string().min(32),
  PORT: z.coerce.number().default(3000),
});

export const env = envSchema.parse(process.env);
```

---

## Git Workflows

### Trunk-Based Development

```
main (protected)
  │
  ├── feature/user-auth (short-lived, 1-2 days max)
  │   └── squash merge → main
  │
  ├── feature/payment-flow
  │   └── squash merge → main
  │
  └── release/v1.2.0 (cut from main for hotfixes)
```

**Branch naming:**
- `feature/description` - New features
- `fix/description` - Bug fixes
- `chore/description` - Maintenance tasks
- `release/vX.Y.Z` - Release branches

### Commit Standards

**Conventional Commits:**

```
<type>(<scope>): <description>

[optional body]

[optional footer(s)]
```

**Types:**
- `feat`: New feature
- `fix`: Bug fix
- `docs`: Documentation
- `style`: Formatting
- `refactor`: Code restructuring
- `test`: Adding tests
- `chore`: Maintenance

**Examples:**

```bash
feat(auth): add password reset flow

Implement password reset with email verification.
Tokens expire after 1 hour.

Closes #123

---

fix(api): handle null response in user endpoint

The API was returning 500 when user profile was incomplete.
Now returns partial data with null fields.

---

chore(deps): update Next.js to 14.1.0

Breaking changes addressed:
- Updated Image component usage
- Migrated to new metadata API
```

### Pre-commit Hooks

```json
// package.json
{
  "scripts": {
    "prepare": "husky install"
  },
  "lint-staged": {
    "*.{ts,tsx}": ["eslint --fix", "prettier --write"],
    "*.{json,md}": ["prettier --write"]
  }
}
```

```bash
# .husky/pre-commit
#!/bin/sh
. "$(dirname "$0")/_/husky.sh"

npx lint-staged

# .husky/commit-msg
#!/bin/sh
. "$(dirname "$0")/_/husky.sh"

npx commitlint --edit $1
```

---

## CI/CD Pipelines

### GitHub Actions

```yaml
# .github/workflows/ci.yml
name: CI

on:
  push:
    branches: [main]
  pull_request:
    branches: [main]

jobs:
  lint:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with:
          node-version: 20
          cache: npm
      - run: npm ci
      - run: npm run lint
      - run: npm run type-check

  test:
    runs-on: ubuntu-latest
    services:
      postgres:
        image: postgres:16
        env:
          POSTGRES_USER: test
          POSTGRES_PASSWORD: test
          POSTGRES_DB: test
        ports:
          - 5432:5432
        options: >-
          --health-cmd pg_isready
          --health-interval 10s
          --health-timeout 5s
          --health-retries 5
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with:
          node-version: 20
          cache: npm
      - run: npm ci
      - run: npm run test:unit
      - run: npm run test:integration
        env:
          DATABASE_URL: postgresql://test:test@localhost:5432/test
      - uses: codecov/codecov-action@v3

  build:
    runs-on: ubuntu-latest
    needs: [lint, test]
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with:
          node-version: 20
          cache: npm
      - run: npm ci
      - run: npm run build
      - uses: actions/upload-artifact@v4
        with:
          name: build
          path: dist/

  deploy-preview:
    if: github.event_name == 'pull_request'
    runs-on: ubuntu-latest
    needs: build
    steps:
      - uses: actions/checkout@v4
      - uses: actions/download-artifact@v4
        with:
          name: build
          path: dist/
      # Deploy to preview environment
      - name: Deploy Preview
        run: |
          # Deploy logic here
          echo "Deployed to preview-${{ github.event.pull_request.number }}"

  deploy-production:
    if: github.ref == 'refs/heads/main'
    runs-on: ubuntu-latest
    needs: build
    environment: production
    steps:
      - uses: actions/checkout@v4
      - uses: actions/download-artifact@v4
        with:
          name: build
          path: dist/
      - name: Deploy Production
        run: |
          # Production deployment
          echo "Deployed to production"
```

### Database Migrations in CI

```yaml
# Part of deploy job
- name: Run Migrations
  run: |
    npx prisma migrate deploy
  env:
    DATABASE_URL: ${{ secrets.DATABASE_URL }}

- name: Verify Migration
  run: |
    npx prisma migrate status
```

---

## Testing Strategies

### Testing Pyramid

```
         /\
        /  \        E2E Tests (10%)
       /    \       - Critical user journeys
      /──────\
     /        \     Integration Tests (20%)
    /          \    - API endpoints
   /────────────\   - Database operations
  /              \
 /                \ Unit Tests (70%)
/──────────────────\ - Components, hooks, utilities
```

### Unit Testing

```typescript
// Component test with React Testing Library
import { render, screen, fireEvent } from "@testing-library/react";
import { UserForm } from "./UserForm";

describe("UserForm", () => {
  it("submits form with valid data", async () => {
    const onSubmit = vi.fn();
    render(<UserForm onSubmit={onSubmit} />);

    fireEvent.change(screen.getByLabelText(/email/i), {
      target: { value: "test@example.com" },
    });
    fireEvent.change(screen.getByLabelText(/name/i), {
      target: { value: "John Doe" },
    });
    fireEvent.click(screen.getByRole("button", { name: /submit/i }));

    await waitFor(() => {
      expect(onSubmit).toHaveBeenCalledWith({
        email: "test@example.com",
        name: "John Doe",
      });
    });
  });

  it("shows validation error for invalid email", async () => {
    render(<UserForm onSubmit={vi.fn()} />);

    fireEvent.change(screen.getByLabelText(/email/i), {
      target: { value: "invalid" },
    });
    fireEvent.click(screen.getByRole("button", { name: /submit/i }));

    expect(await screen.findByText(/invalid email/i)).toBeInTheDocument();
  });
});
```

### Integration Testing

```typescript
// API integration test
import { createTestClient } from "./test-utils";
import { db } from "@/lib/db";

describe("POST /api/users", () => {
  beforeEach(async () => {
    await db.user.deleteMany();
  });

  it("creates user with valid data", async () => {
    const client = createTestClient();

    const response = await client.post("/api/users", {
      email: "new@example.com",
      name: "New User",
    });

    expect(response.status).toBe(201);
    expect(response.data.user.email).toBe("new@example.com");

    // Verify in database
    const user = await db.user.findUnique({
      where: { email: "new@example.com" },
    });
    expect(user).toBeTruthy();
  });

  it("returns 409 for duplicate email", async () => {
    await db.user.create({
      data: { email: "existing@example.com", name: "Existing" },
    });

    const client = createTestClient();

    const response = await client.post("/api/users", {
      email: "existing@example.com",
      name: "Duplicate",
    });

    expect(response.status).toBe(409);
    expect(response.data.error.code).toBe("EMAIL_EXISTS");
  });
});
```

### E2E Testing with Playwright

```typescript
// e2e/auth.spec.ts
import { test, expect } from "@playwright/test";

test.describe("Authentication", () => {
  test("user can log in and access dashboard", async ({ page }) => {
    await page.goto("/login");

    await page.fill('[name="email"]', "user@example.com");
    await page.fill('[name="password"]', "password123");
    await page.click('button[type="submit"]');

    await expect(page).toHaveURL("/dashboard");
    await expect(page.locator("h1")).toHaveText("Welcome back");
  });

  test("shows error for invalid credentials", async ({ page }) => {
    await page.goto("/login");

    await page.fill('[name="email"]', "wrong@example.com");
    await page.fill('[name="password"]', "wrongpassword");
    await page.click('button[type="submit"]');

    await expect(page.locator('[role="alert"]')).toHaveText(
      "Invalid email or password"
    );
  });
});
```

---

## Code Review Process

### PR Template

```markdown
## Summary
<!-- Brief description of changes -->

## Type of Change
- [ ] Bug fix
- [ ] New feature
- [ ] Breaking change
- [ ] Documentation update

## Changes Made
<!-- List specific changes -->

## Testing
- [ ] Unit tests added/updated
- [ ] Integration tests added/updated
- [ ] Manual testing completed

## Screenshots
<!-- If applicable -->

## Checklist
- [ ] Code follows style guidelines
- [ ] Self-review completed
- [ ] Documentation updated
- [ ] No new warnings
```

### Review Checklist

**Functionality:**
- Does the code do what it's supposed to?
- Are edge cases handled?
- Is error handling appropriate?

**Code Quality:**
- Is the code readable and maintainable?
- Are there any code smells?
- Is there unnecessary duplication?

**Performance:**
- Are there N+1 queries?
- Is caching used appropriately?
- Are there memory leaks?

**Security:**
- Is user input validated?
- Are there injection vulnerabilities?
- Is sensitive data protected?

---

## Deployment Strategies

### Blue-Green Deployment

```
                 Load Balancer
                      │
         ┌────────────┴────────────┐
         │                         │
    ┌────┴────┐              ┌─────┴────┐
    │  Blue   │              │  Green   │
    │ (Live)  │              │  (Idle)  │
    └─────────┘              └──────────┘

1. Deploy new version to Green
2. Run smoke tests on Green
3. Switch traffic to Green
4. Blue becomes idle (rollback target)
```

### Canary Deployment

```
                 Load Balancer
                      │
         ┌────────────┴────────────┐
         │                         │
         │ 95%                5%   │
         ▼                         ▼
    ┌─────────┐              ┌──────────┐
    │ Stable  │              │  Canary  │
    │ v1.0.0  │              │  v1.1.0  │
    └─────────┘              └──────────┘

1. Deploy canary with small traffic %
2. Monitor error rates, latency
3. Gradually increase traffic
4. Full rollout or rollback
```

### Feature Flags

```typescript
// Feature flag service
const flags = {
  newCheckoutFlow: {
    enabled: true,
    rolloutPercentage: 25,
    allowedUsers: ["beta-testers"],
  },
};

function isFeatureEnabled(flag: string, userId: string): boolean {
  const config = flags[flag];
  if (!config?.enabled) return false;

  // Check allowed users
  if (config.allowedUsers?.includes(userId)) return true;

  // Check rollout percentage
  const hash = hashUserId(userId);
  return hash < config.rolloutPercentage;
}

// Usage
if (isFeatureEnabled("newCheckoutFlow", user.id)) {
  return <NewCheckout />;
}
return <LegacyCheckout />;
```

---

## Monitoring and Observability

### Structured Logging

```typescript
import pino from "pino";

const logger = pino({
  level: process.env.LOG_LEVEL || "info",
  formatters: {
    level: (label) => ({ level: label }),
  },
});

// Request logging middleware
app.use((req, res, next) => {
  const start = Date.now();
  const requestId = req.headers["x-request-id"] || crypto.randomUUID();

  res.on("finish", () => {
    logger.info({
      type: "request",
      requestId,
      method: req.method,
      path: req.path,
      statusCode: res.statusCode,
      duration: Date.now() - start,
      userAgent: req.headers["user-agent"],
    });
  });

  next();
});

// Application logging
logger.info({ userId: user.id, action: "login" }, "User logged in");
logger.error({ err, orderId }, "Failed to process order");
```

### Metrics Collection

```typescript
import { Counter, Histogram } from "prom-client";

const httpRequestsTotal = new Counter({
  name: "http_requests_total",
  help: "Total HTTP requests",
  labelNames: ["method", "path", "status"],
});

const httpRequestDuration = new Histogram({
  name: "http_request_duration_seconds",
  help: "HTTP request duration",
  labelNames: ["method", "path"],
  buckets: [0.1, 0.3, 0.5, 1, 3, 5, 10],
});

// Middleware
app.use((req, res, next) => {
  const end = httpRequestDuration.startTimer({
    method: req.method,
    path: req.route?.path || req.path,
  });

  res.on("finish", () => {
    httpRequestsTotal.inc({
      method: req.method,
      path: req.route?.path || req.path,
      status: res.statusCode,
    });
    end();
  });

  next();
});
```

### Health Checks

```typescript
app.get("/health", async (req, res) => {
  const checks = {
    database: await checkDatabase(),
    redis: await checkRedis(),
    memory: checkMemory(),
  };

  const healthy = Object.values(checks).every((c) => c.status === "healthy");

  res.status(healthy ? 200 : 503).json({
    status: healthy ? "healthy" : "unhealthy",
    checks,
    timestamp: new Date().toISOString(),
  });
});

async function checkDatabase() {
  try {
    await db.$queryRaw`SELECT 1`;
    return { status: "healthy" };
  } catch (error) {
    return { status: "unhealthy", error: error.message };
  }
}

function checkMemory() {
  const used = process.memoryUsage();
  const heapUsedMB = Math.round(used.heapUsed / 1024 / 1024);
  const heapTotalMB = Math.round(used.heapTotal / 1024 / 1024);

  return {
    status: heapUsedMB < heapTotalMB * 0.9 ? "healthy" : "warning",
    heapUsedMB,
    heapTotalMB,
  };
}
```

---

## Quick Reference

### Daily Workflow

```bash
# 1. Start work
git checkout main && git pull
git checkout -b feature/my-feature

# 2. Develop with hot reload
docker-compose up -d
npm run dev

# 3. Test changes
npm run test
npm run lint

# 4. Commit
git add -A
git commit -m "feat(scope): description"

# 5. Push and create PR
git push -u origin feature/my-feature
gh pr create
```

### Release Workflow

```bash
# 1. Ensure main is stable
git checkout main
npm run test:all

# 2. Create release
npm version minor  # or major/patch
git push --follow-tags

# 3. Verify deployment
# CI/CD deploys automatically
# Monitor dashboards
```
