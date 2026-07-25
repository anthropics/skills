# Flaky Test Quick Reference

## Diagnosis Commands

```bash
# Burn-in: expose timing issues
npx playwright test tests/checkout.spec.ts --repeat-each=10

# Isolation: expose state leaks
npx playwright test tests/checkout.spec.ts --grep "adds item" --workers=1

# Full trace: capture everything
npx playwright test tests/checkout.spec.ts --trace=on --retries=0

# Parallel stress: expose race conditions
npx playwright test --fully-parallel --workers=4 --repeat-each=5
```

## Four Categories

| Category | Symptom | Fix |
|---|---|---|
| **Timing** | Fails intermittently | Replace waits with assertions |
| **Isolation** | Fails in suite, passes alone | Remove shared state |
| **Environment** | Fails in CI only | Match viewport, fonts, timezone |
| **Infrastructure** | Random crashes | Reduce workers, increase memory |

## Quick Fixes

**Timing → Add proper waits:**
```typescript
// Wait for specific response
const response = page.waitForResponse('**/api/data');
await page.getByRole('button', { name: 'Load' }).click();
await response;
await expect(page.getByTestId('results')).toBeVisible();
```

**Isolation → Unique test data:**
```typescript
const uniqueEmail = `test-${Date.now()}@example.com`;
```

**Environment → Explicit viewport:**
```typescript
test.use({ viewport: { width: 1280, height: 720 } });
```

**Infrastructure → CI-safe config:**
```typescript
export default defineConfig({
  retries: process.env.CI ? 2 : 0,
  workers: process.env.CI ? 2 : undefined,
  timeout: process.env.CI ? 60_000 : 30_000,
});
```
