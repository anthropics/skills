# Chart Rendering Template

Tests chart visibility, interactive tooltips, and legend behaviour.

## Prerequisites
- Authenticated session via `{{authStorageStatePath}}`
- Dashboard with charts at `{{baseUrl}}/dashboard`
- Chart library: `{{chartLibrary}}` (e.g. Chart.js, Recharts, D3)

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Chart Rendering', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    // Wait for chart container to be visible
    await expect(page.getByRole('img', { name: /{{chartName}} chart/i })
      .or(page.getByTestId('{{chartTestId}}'))).toBeVisible();
  });

  // Happy path: chart rendered and visible
  test('renders {{chartName}} chart', async ({ page }) => {
    const chart = page.getByTestId('{{chartTestId}}');
    await expect(chart).toBeVisible();
    // Chart has non-zero dimensions
    const box = await chart.boundingBox();
    expect(box?.width).toBeGreaterThan(0);
    expect(box?.height).toBeGreaterThan(0);
  });

  // Happy path: tooltip shown on hover
  test('shows tooltip on data point hover', async ({ page }) => {
    const chart = page.getByTestId('{{chartTestId}}');
    const box = await chart.boundingBox();
    // Hover over the centre of the chart
    await page.mouse.move(box!.x + box!.width / 2, box!.y + box!.height / 2);
    await expect(page.getByRole('tooltip')).toBeVisible();
    await expect(page.getByRole('tooltip')).toContainText(/\d/);
  });

  // Happy path: legend visible with correct labels
  test('displays chart legend with correct series labels', async ({ page }) => {
    const legend = page.getByRole('list', { name: /legend/i });
    await expect(legend).toBeVisible();
    await expect(legend.getByRole('listitem', { name: '{{seriesName1}}' })).toBeVisible();
    await expect(legend.getByRole('listitem', { name: '{{seriesName2}}' })).toBeVisible();
  });

  // Happy path: clicking legend toggles series visibility
  test('toggles series visibility via legend click', async ({ page }) => {
    await page.getByRole('button', { name: '{{seriesName1}}' }).click();
    // Series hidden — legend item shows struck-through or disabled state
    await expect(page.getByRole('button', { name: '{{seriesName1}}' })).toHaveAttribute('aria-pressed', 'false');
  });

  // Happy path: chart updates when date range changed
  test('updates chart when date range filter applied', async ({ page }) => {
    const before = await page.getByTestId('{{chartTestId}}').screenshot();
    await page.getByRole('combobox', { name: /date range/i }).selectOption('last_7_days');
    const after = await page.getByTestId('{{chartTestId}}').screenshot();
    expect(Buffer.compare(before, after)).not.toBe(0);
  });

  // Error case: empty data shows no-data state
  test('shows no-data message when chart has no data', async ({ page }) => {
    await page.route('{{baseUrl}}/api/chart-data*', route =>
      route.fulfill({ status: 200, body: JSON.stringify({ data: [] }) })
    );
    await page.reload();
    const chart = page.getByTestId('{{chartTestId}}');
    await expect(chart.getByText(/no data|no results/i)).toBeVisible();
  });

  // Edge case: chart accessible via aria
  test('chart has accessible title and description', async ({ page }) => {
    const chart = page.getByTestId('{{chartTestId}}');
    await expect(chart.getByRole('img')).toHaveAttribute('aria-label', /{{chartName}}/i);
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Chart Rendering', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test('renders chart with non-zero dimensions', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    const chart = page.getByTestId('{{chartTestId}}');
    await expect(chart).toBeVisible();
    const box = await chart.boundingBox();
    expect(box?.width).toBeGreaterThan(0);
    expect(box?.height).toBeGreaterThan(0);
  });

  test('shows tooltip on hover', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    const chart = page.getByTestId('{{chartTestId}}');
    const box = await chart.boundingBox();
    await page.mouse.move(box.x + box.width / 2, box.y + box.height / 2);
    await expect(page.getByRole('tooltip')).toBeVisible();
  });

  test('displays legend labels', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await expect(page.getByRole('list', { name: /legend/i })).toBeVisible();
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Chart visible | Non-zero bounding box confirmed |
| Tooltip on hover | Tooltip appears with numeric value |
| Legend labels | Series names present in legend |
| Legend toggle | Click hides/shows series |
| Date range update | Chart changes when filter applied |
| No-data state | Empty dataset → no-data message |
| Accessible label | aria-label present on chart element |
