# Export Template

Tests CSV and PDF export, download triggering, and file verification.

## Prerequisites
- Authenticated session via `{{authStorageStatePath}}`
- Dashboard or report page at `{{baseUrl}}/{{reportPath}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';
import path from 'path';
import fs from 'fs';

test.describe('Export', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/{{reportPath}}');
  });

  // Happy path: CSV download
  test('downloads CSV export', async ({ page }) => {
    const downloadPromise = page.waitForEvent('download');
    await page.getByRole('button', { name: /export.*csv|download.*csv/i }).click();
    const download = await downloadPromise;
    expect(download.suggestedFilename()).toMatch(/\.csv$/);
    const filePath = path.join('/tmp', download.suggestedFilename());
    await download.saveAs(filePath);
    const content = fs.readFileSync(filePath, 'utf-8');
    expect(content).toContain('{{expectedCsvHeader}}');
    expect(content.split('\n').length).toBeGreaterThan(1);
  });

  // Happy path: PDF download
  test('downloads PDF export', async ({ page }) => {
    const downloadPromise = page.waitForEvent('download');
    await page.getByRole('button', { name: /export.*pdf|download.*pdf/i }).click();
    const download = await downloadPromise;
    expect(download.suggestedFilename()).toMatch(/\.pdf$/);
    const filePath = path.join('/tmp', download.suggestedFilename());
    await download.saveAs(filePath);
    const buffer = fs.readFileSync(filePath);
    // PDF magic bytes
    expect(buffer.slice(0, 4).toString()).toBe('%PDF');
  });

  // Happy path: export with current filters applied
  test('export respects active date range filter', async ({ page }) => {
    await page.getByRole('button', { name: /date range/i }).click();
    await page.getByRole('option', { name: /last 7 days/i }).click();
    const downloadPromise = page.waitForEvent('download');
    await page.getByRole('button', { name: /export.*csv/i }).click();
    const download = await downloadPromise;
    const filePath = path.join('/tmp', download.suggestedFilename());
    await download.saveAs(filePath);
    const content = fs.readFileSync(filePath, 'utf-8');
    expect(content.split('\n').length).toBeGreaterThan(1);
  });

  // Happy path: export loading indicator
  test('shows loading state during export generation', async ({ page }) => {
    const downloadPromise = page.waitForEvent('download');
    await page.getByRole('button', { name: /export.*csv/i }).click();
    await expect(page.getByRole('button', { name: /export.*csv/i })).toBeDisabled();
    await downloadPromise;
    await expect(page.getByRole('button', { name: /export.*csv/i })).toBeEnabled();
  });

  // Error case: export fails with server error
  test('shows error when export generation fails', async ({ page }) => {
    await page.route('{{baseUrl}}/api/export*', route =>
      route.fulfill({ status: 500, body: JSON.stringify({ error: 'Export failed' }) })
    );
    await page.getByRole('button', { name: /export.*csv/i }).click();
    await expect(page.getByRole('alert')).toContainText(/export failed|could not generate/i);
  });

  // Edge case: export with no data shows warning
  test('shows warning when exporting empty dataset', async ({ page }) => {
    await page.route('{{baseUrl}}/api/{{reportEndpoint}}*', route =>
      route.fulfill({ status: 200, body: JSON.stringify({ data: [] }) })
    );
    await page.reload();
    await page.getByRole('button', { name: /export.*csv/i }).click();
    await expect(page.getByRole('alert')).toContainText(/no data to export|empty/i);
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');
const path = require('path');
const fs = require('fs');

test.describe('Export', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test('downloads CSV export with correct header', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{reportPath}}');
    const downloadPromise = page.waitForEvent('download');
    await page.getByRole('button', { name: /export.*csv/i }).click();
    const download = await downloadPromise;
    expect(download.suggestedFilename()).toMatch(/\.csv$/);
    const filePath = path.join('/tmp', download.suggestedFilename());
    await download.saveAs(filePath);
    expect(fs.readFileSync(filePath, 'utf-8')).toContain('{{expectedCsvHeader}}');
  });

  test('downloads PDF with correct magic bytes', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{reportPath}}');
    const downloadPromise = page.waitForEvent('download');
    await page.getByRole('button', { name: /export.*pdf/i }).click();
    const download = await downloadPromise;
    const filePath = path.join('/tmp', download.suggestedFilename());
    await download.saveAs(filePath);
    expect(fs.readFileSync(filePath).slice(0, 4).toString()).toBe('%PDF');
  });

  test('shows error when export fails', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{reportPath}}');
    await page.route('{{baseUrl}}/api/export*', route =>
      route.fulfill({ status: 500, body: '{}' })
    );
    await page.getByRole('button', { name: /export.*csv/i }).click();
    await expect(page.getByRole('alert')).toContainText(/export failed/i);
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| CSV download | File downloaded, header row verified |
| PDF download | File downloaded, %PDF magic bytes checked |
| Filtered export | Active filters applied to exported data |
| Loading state | Button disabled during generation |
| Server error | Export failure → error alert |
| Empty dataset | No-data warning shown |
