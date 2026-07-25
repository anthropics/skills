# Dashboard Data Loading Template

Tests loading state, skeleton screens, and data display after fetch.

## Prerequisites
- Authenticated session via `{{authStorageStatePath}}`
- Dashboard at `{{baseUrl}}/dashboard`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Dashboard Data Loading', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  // Happy path: skeleton shown then replaced by data
  test('shows skeleton during load, then displays data', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    // Skeleton should resolve; real data appears
    await expect(page.getByTestId('skeleton')).toBeHidden();
    await expect(page.getByRole('heading', { name: /dashboard/i })).toBeVisible();
    await expect(page.getByRole('region', { name: /{{widgetName}}/i })).toBeVisible();
  });

  // Happy path: all metric cards populated
  test('renders metric cards with values', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    const cards = page.getByRole('article', { name: /metric/i });
    await expect(cards).toHaveCount({{expectedMetricCount}});
    await expect(cards.first().getByText(/\d/)).toBeVisible();
  });

  // Happy path: data updates on refresh
  test('refreshes data when refresh button clicked', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await expect(page.getByTestId('skeleton')).toBeHidden();
    const before = await page.getByTestId('{{metricId}}').textContent();
    await page.getByRole('button', { name: /refresh/i }).click();
    await expect(page.getByTestId('skeleton')).toBeHidden();
    // Value may or may not change — just confirm data loads again
    await expect(page.getByTestId('{{metricId}}')).toBeVisible();
  });

  // Error case: shows error state when API fails
  test('shows error state when data fetch fails', async ({ page }) => {
    await page.route('{{baseUrl}}/api/dashboard*', route =>
      route.fulfill({ status: 500, body: JSON.stringify({ error: 'Internal Server Error' }) })
    );
    await page.goto('{{baseUrl}}/dashboard');
    await expect(page.getByRole('alert')).toContainText(/failed to load|error loading/i);
    await expect(page.getByRole('button', { name: /retry/i })).toBeVisible();
  });

  // Error case: retry after failure loads data
  test('retries and loads data after error', async ({ page }) => {
    let callCount = 0;
    await page.route('{{baseUrl}}/api/dashboard*', route => {
      callCount++;
      if (callCount === 1) return route.fulfill({ status: 500, body: '{}' });
      return route.continue();
    });
    await page.goto('{{baseUrl}}/dashboard');
    await page.getByRole('button', { name: /retry/i }).click();
    await expect(page.getByTestId('skeleton')).toBeHidden();
    await expect(page.getByRole('region', { name: /{{widgetName}}/i })).toBeVisible();
  });

  // Edge case: slow network shows skeleton for duration
  test('skeleton persists during slow API response', async ({ page }) => {
    await page.route('{{baseUrl}}/api/dashboard*', async route => {
      await new Promise(r => setTimeout(r, 2000));
      await route.continue();
    });
    await page.goto('{{baseUrl}}/dashboard');
    await expect(page.getByTestId('skeleton')).toBeVisible();
    await expect(page.getByTestId('skeleton')).toBeHidden(); // eventually resolves
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Dashboard Data Loading', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test('renders metric cards after loading', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await expect(page.getByTestId('skeleton')).toBeHidden();
    await expect(page.getByRole('article', { name: /metric/i }).first()).toBeVisible();
  });

  test('shows error state on API failure', async ({ page }) => {
    await page.route('{{baseUrl}}/api/dashboard*', route =>
      route.fulfill({ status: 500, body: '{}' })
    );
    await page.goto('{{baseUrl}}/dashboard');
    await expect(page.getByRole('alert')).toContainText(/failed to load|error/i);
    await expect(page.getByRole('button', { name: /retry/i })).toBeVisible();
  });

  test('skeleton visible during slow response', async ({ page }) => {
    await page.route('{{baseUrl}}/api/dashboard*', async route => {
      await new Promise(r => setTimeout(r, 1500));
      await route.continue();
    });
    await page.goto('{{baseUrl}}/dashboard');
    await expect(page.getByTestId('skeleton')).toBeVisible();
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Skeleton → data | Loading state resolves to populated widgets |
| Metric cards | N cards each showing a numeric value |
| Refresh | Data reloaded on button click |
| API error | Error alert + retry button shown |
| Retry success | Second request succeeds after failure |
| Slow network | Skeleton persists during delay |
