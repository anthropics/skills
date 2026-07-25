# Playwright Anti-Patterns Reference

## 1. Using `waitForTimeout()`

**Bad:**
```typescript
await page.click('.submit');
await page.waitForTimeout(3000);
await expect(page.locator('.result')).toBeVisible();
```

**Good:**
```typescript
await page.getByRole('button', { name: 'Submit' }).click();
await expect(page.getByTestId('result')).toBeVisible();
```

**Why:** Arbitrary waits slow tests and cause flakiness. Web-first assertions auto-retry.

## 2. Non-Web-First Assertions

**Bad:**
```typescript
const text = await page.textContent('.message');
expect(text).toBe('Success');
```

**Good:**
```typescript
await expect(page.getByText('Success')).toBeVisible();
```

**Why:** `expect(locator)` auto-retries until timeout. `expect(value)` checks once and fails.

## 3. Hardcoded URLs

**Bad:**
```typescript
await page.goto('http://localhost:3000/login');
```

**Good:**
```typescript
await page.goto('/login');
```

**Why:** `baseURL` in config handles the host. Tests break across environments with hardcoded URLs.

## 4. CSS/XPath When Role-Based Exists

**Bad:**
```typescript
await page.click('#submit-btn');
await page.locator('.nav-link.active').click();
```

**Good:**
```typescript
await page.getByRole('button', { name: 'Submit' }).click();
await page.getByRole('link', { name: 'Dashboard' }).click();
```

**Why:** Role-based locators survive CSS renames, class refactors, and component library changes.

## 5. Missing `await`

**Bad:**
```typescript
page.goto('/dashboard');
expect(page.getByText('Welcome')).toBeVisible();
```

**Good:**
```typescript
await page.goto('/dashboard');
await expect(page.getByText('Welcome')).toBeVisible();
```

**Why:** Missing `await` causes race conditions. Tests pass sometimes, fail others.

## 6. Shared Mutable State

**Bad:**
```typescript
let userId: string;

test('create user', async ({ page }) => {
  // ... creates user, sets userId
  userId = '123';
});

test('edit user', async ({ page }) => {
  await page.goto(`/users/${userId}`); // depends on previous test
});
```

**Good:**
```typescript
test('edit user', async ({ page }) => {
  // Create user via API in this test's setup
  const userId = await createUserViaAPI();
  await page.goto(`/users/${userId}`);
});
```

**Why:** Tests must be independent. Shared state causes order-dependent failures.

## 7. Execution Order Dependencies

**Bad:**
```typescript
test('step 1: fill form', async ({ page }) => { ... });
test('step 2: submit form', async ({ page }) => { ... });
test('step 3: verify result', async ({ page }) => { ... });
```

**Good:**
```typescript
test('should fill and submit form successfully', async ({ page }) => {
  // All steps in one test
});
```

**Why:** Playwright runs tests in parallel by default. Order-dependent tests fail randomly.

## 8. Tests Over 50 Lines

Split into focused tests. Each test should verify one behavior.

## 9. Magic Strings

**Bad:**
```typescript
await page.getByLabel('Email').fill('admin@test.com');
```

**Good:**
```typescript
const TEST_USER = { email: 'admin@test.com', password: 'Test123!' };
await page.getByLabel('Email').fill(TEST_USER.email);
```

## 10. Missing Error Cases

If you test the happy path, also test:
- Invalid input
- Empty state
- Network error
- Permission denied
- Timeout/loading state

## 11. Using `page.evaluate()` Unnecessarily

**Bad:**
```typescript
const text = await page.evaluate(() => document.querySelector('.title')?.textContent);
```

**Good:**
```typescript
await expect(page.getByRole('heading')).toHaveText('Expected Title');
```

## 12. Deep Nesting

Keep `test.describe()` to max 2 levels. More makes tests hard to find and maintain.

## 13. Generic Test Names

**Bad:** `test('test 1')`, `test('should work')`, `test('login test')`

**Good:** `test('should show error when email is invalid')`, `test('should redirect to dashboard after successful login')`

## 14-20. Style Issues

- No page objects for complex pages → create them
- Inline data → use factories or fixtures
- Missing a11y assertions → add `toHaveAttribute('role', ...)`
- No visual regression → add `toHaveScreenshot()` for key pages
- Not checking console errors → add `page.on('console', ...)`
- Using `networkidle` → use specific assertions instead
- No `test.describe()` → group related tests
