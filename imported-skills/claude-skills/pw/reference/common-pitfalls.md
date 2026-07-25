# Common Pitfalls (Top 10)

## 1. waitForTimeout

**Symptom:** Slow, flaky tests.

```typescript
// BAD
await page.waitForTimeout(3000);

// GOOD
await expect(page.getByTestId('result')).toBeVisible();
```

## 2. Non-Web-First Assertions

**Symptom:** Assertions fail on dynamic content.

```typescript
// BAD — checks once, no retry
const text = await page.textContent('.msg');
expect(text).toBe('Done');

// GOOD — retries until timeout
await expect(page.getByText('Done')).toBeVisible();
```

## 3. Missing await

**Symptom:** Random passes/failures, tests seem to skip steps.

```typescript
// BAD
page.goto('/dashboard');
expect(page.getByText('Welcome')).toBeVisible();

// GOOD
await page.goto('/dashboard');
await expect(page.getByText('Welcome')).toBeVisible();
```

## 4. Hardcoded URLs

**Symptom:** Tests break in different environments.

```typescript
// BAD
await page.goto('http://localhost:3000/login');

// GOOD — uses baseURL from config
await page.goto('/login');
```

## 5. CSS Selectors Instead of Roles

**Symptom:** Tests break after CSS refactors.

```typescript
// BAD
await page.click('#submit-btn');

// GOOD
await page.getByRole('button', { name: 'Submit' }).click();
```

## 6. Shared State Between Tests

**Symptom:** Tests pass alone, fail in suite.

```typescript
// BAD — test B depends on test A
let userId: string;
test('create user', async () => { userId = '123'; });
test('edit user', async () => { /* uses userId */ });

// GOOD — each test is independent
test('edit user', async ({ request }) => {
  const res = await request.post('/api/users', { data: { name: 'Test' } });
  const { id } = await res.json();
  // ...
});
```

## 7. Using networkidle

**Symptom:** Tests hang or timeout unpredictably.

```typescript
// BAD — waits for all network activity to stop
await page.goto('/dashboard', { waitUntil: 'networkidle' });

// GOOD — wait for specific content
await page.goto('/dashboard');
await expect(page.getByRole('heading', { name: 'Dashboard' })).toBeVisible();
```

## 8. Not Waiting for Navigation

**Symptom:** Assertions run on wrong page.

```typescript
// BAD — click navigates but we don't wait
await page.getByRole('link', { name: 'Settings' }).click();
await expect(page.getByRole('heading')).toHaveText('Settings');

// GOOD — wait for URL change
await page.getByRole('link', { name: 'Settings' }).click();
await expect(page).toHaveURL('/settings');
await expect(page.getByRole('heading')).toHaveText('Settings');
```

## 9. Testing Implementation, Not Behavior

**Symptom:** Tests break on every refactor.

```typescript
// BAD — tests CSS class (implementation detail)
await expect(page.locator('.btn')).toHaveClass('btn-primary active');

// GOOD — tests what the user sees
await expect(page.getByRole('button', { name: 'Save' })).toBeEnabled();
```

## 10. No Error Case Tests

**Symptom:** App breaks on errors but all tests pass.

```typescript
// Missing: what happens when the API fails?
test('should handle API error', async ({ page }) => {
  await page.route('**/api/data', (route) =>
    route.fulfill({ status: 500 })
  );
  await page.goto('/dashboard');
  await expect(page.getByText(/error|try again/i)).toBeVisible();
});
```
