# Date Range Filter Template

Tests date picker interaction, preset ranges, and data refresh on selection.

## Prerequisites
- Authenticated session via `{{authStorageStatePath}}`
- Dashboard at `{{baseUrl}}/dashboard`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Date Range Filter', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
  });

  // Happy path: preset range — last 7 days
  test('applies "last 7 days" preset', async ({ page }) => {
    await page.getByRole('button', { name: /date range/i }).click();
    await page.getByRole('option', { name: /last 7 days/i }).click();
    await expect(page).toHaveURL(/from=|start_date=/);
    await expect(page.getByRole('button', { name: /date range/i })).toContainText(/last 7 days/i);
  });

  // Happy path: preset range — last 30 days
  test('applies "last 30 days" preset', async ({ page }) => {
    await page.getByRole('button', { name: /date range/i }).click();
    await page.getByRole('option', { name: /last 30 days/i }).click();
    await expect(page.getByRole('button', { name: /date range/i })).toContainText(/last 30 days/i);
    await expect(page.getByTestId('skeleton')).toBeHidden();
  });

  // Happy path: custom date range via date picker
  test('applies custom date range from picker', async ({ page }) => {
    await page.getByRole('button', { name: /date range/i }).click();
    await page.getByRole('option', { name: /custom/i }).click();
    const picker = page.getByRole('dialog', { name: /date range/i });
    await expect(picker).toBeVisible();
    // Select start date
    await picker.getByRole('button', { name: '{{startDay}}' }).click();
    // Select end date
    await picker.getByRole('button', { name: '{{endDay}}' }).click();
    await picker.getByRole('button', { name: /apply/i }).click();
    await expect(picker).toBeHidden();
    await expect(page.getByRole('button', { name: /date range/i })).toContainText('{{startDateFormatted}}');
  });

  // Happy path: data reloads on range change
  test('reloads dashboard data on date range change', async ({ page }) => {
    let requestCount = 0;
    await page.route('{{baseUrl}}/api/dashboard*', route => {
      requestCount++;
      return route.continue();
    });
    await page.getByRole('button', { name: /date range/i }).click();
    await page.getByRole('option', { name: /last 7 days/i }).click();
    expect(requestCount).toBeGreaterThan(0);
    await expect(page.getByTestId('skeleton')).toBeHidden();
  });

  // Error case: invalid custom range (end before start)
  test('shows error when end date is before start date', async ({ page }) => {
    await page.getByRole('button', { name: /date range/i }).click();
    await page.getByRole('option', { name: /custom/i }).click();
    const picker = page.getByRole('dialog', { name: /date range/i });
    await picker.getByRole('button', { name: '{{endDay}}' }).click();   // pick later date first
    await picker.getByRole('button', { name: '{{startDay}}' }).click(); // then earlier
    await expect(picker.getByText(/end.*after.*start|invalid.*range/i)).toBeVisible();
    await expect(picker.getByRole('button', { name: /apply/i })).toBeDisabled();
  });

  // Edge case: range persists after page reload
  test('date range persists in URL after reload', async ({ page }) => {
    await page.getByRole('button', { name: /date range/i }).click();
    await page.getByRole('option', { name: /last 7 days/i }).click();
    const url = page.url();
    await page.reload();
    await expect(page).toHaveURL(url);
    await expect(page.getByRole('button', { name: /date range/i })).toContainText(/last 7 days/i);
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Date Range Filter', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test('applies last-7-days preset', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.getByRole('button', { name: /date range/i }).click();
    await page.getByRole('option', { name: /last 7 days/i }).click();
    await expect(page.getByRole('button', { name: /date range/i })).toContainText(/last 7 days/i);
  });

  test('shows error for invalid range', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.getByRole('button', { name: /date range/i }).click();
    await page.getByRole('option', { name: /custom/i }).click();
    const picker = page.getByRole('dialog', { name: /date range/i });
    await picker.getByRole('button', { name: '{{endDay}}' }).click();
    await picker.getByRole('button', { name: '{{startDay}}' }).click();
    await expect(picker.getByRole('button', { name: /apply/i })).toBeDisabled();
  });

  test('range persists after page reload', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.getByRole('button', { name: /date range/i }).click();
    await page.getByRole('option', { name: /last 7 days/i }).click();
    const url = page.url();
    await page.reload();
    await expect(page).toHaveURL(url);
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Last 7 days | Preset applied, URL updated |
| Last 30 days | Preset applied, data refreshed |
| Custom range | Date picker → start + end → apply |
| Data reload | API called again on range change |
| Invalid range | End before start → apply disabled |
| URL persistence | Range in URL survives reload |
