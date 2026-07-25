# Flaky Test Taxonomy

## Decision Tree

```
Test is flaky
│
├── Fails locally with --repeat-each=20?
│   ├── YES → TIMING / ASYNC
│   │   ├── Missing await? → Add await
│   │   ├── waitForTimeout? → Replace with assertion
│   │   ├── Race condition? → Wait for specific event
│   │   └── Animation? → Wait for animation end or disable
│   │
│   └── NO → Continue...
│
├── Passes alone, fails in suite?
│   ├── YES → TEST ISOLATION
│   │   ├── Shared variable? → Make per-test
│   │   ├── Database state? → Reset per-test
│   │   ├── localStorage? → Clear in beforeEach
│   │   └── Cookie leak? → Use isolated contexts
│   │
│   └── NO → Continue...
│
├── Fails in CI, passes locally?
│   ├── YES → ENVIRONMENT
│   │   ├── Viewport? → Set explicit size
│   │   ├── Fonts? → Use Docker locally
│   │   ├── Timezone? → Use UTC everywhere
│   │   └── Network? → Mock external services
│   │
│   └── NO → INFRASTRUCTURE
│       ├── Browser crash? → Reduce workers
│       ├── OOM? → Limit parallel tests
│       ├── DNS? → Add retry config
│       └── File system? → Use unique temp dirs
```

## Common Fixes by Category

### Timing / Async

**Missing await:**
```typescript
// BAD — race condition
page.goto('/dashboard');
expect(page.getByText('Welcome')).toBeVisible();

// GOOD
await page.goto('/dashboard');
await expect(page.getByText('Welcome')).toBeVisible();
```

**Clicking before visible:**
```typescript
// BAD — element may not be ready
await page.getByRole('button', { name: 'Submit' }).click();

// GOOD — ensure visible first
const submitBtn = page.getByRole('button', { name: 'Submit' });
await expect(submitBtn).toBeVisible();
await submitBtn.click();
```

**Race with network:**
```typescript
// BAD — data might not be loaded
await page.goto('/users');
await expect(page.getByRole('table')).toBeVisible();

// GOOD — wait for API response
const responsePromise = page.waitForResponse('**/api/users');
await page.goto('/users');
await responsePromise;
await expect(page.getByRole('table')).toBeVisible();
```

### Test Isolation

**Shared state fix:**
```typescript
// BAD — tests share userId
let userId: string;
test('create', async () => { userId = '123'; });
test('read', async () => { /* uses userId */ });

// GOOD — each test is independent
test('read user', async ({ request }) => {
  const response = await request.post('/api/users', { data: { name: 'Test' } });
  const { id } = await response.json();
  // Use id within this test
});
```

**localStorage cleanup:**
```typescript
test.beforeEach(async ({ page }) => {
  await page.goto('/');
  await page.evaluate(() => localStorage.clear());
});
```

### Environment

**Explicit viewport:**
```typescript
test.use({ viewport: { width: 1280, height: 720 } });
```

**Timezone-safe dates:**
```typescript
// BAD
expect(dateText).toBe('March 5, 2026');

// GOOD — timezone independent
expect(dateText).toMatch(/\d{1,2}\/\d{1,2}\/\d{4}/);
```

### Infrastructure

**Retry config:**
```typescript
// playwright.config.ts
export default defineConfig({
  retries: process.env.CI ? 2 : 0,
  workers: process.env.CI ? 2 : undefined,
});
```

**Increase timeout for CI:**
```typescript
test.setTimeout(60_000); // 60s for slow CI
```
