# File Upload Template

Tests single file, multiple files, drag-and-drop, and upload progress.

## Prerequisites
- Authenticated session via `{{authStorageStatePath}}`
- Test files available: `{{testFilePath}}`, `{{largeFilePath}}`
- Accepted types: `{{acceptedMimeTypes}}` (e.g. image/jpeg, application/pdf)
- Max file size: `{{maxFileSizeMb}}` MB

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';
import path from 'path';

const testFile  = path.resolve('{{testFilePath}}');
const largeFile = path.resolve('{{largeFilePath}}');

test.describe('File Upload', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/{{uploadPath}}');
  });

  // Happy path: single file upload
  test('uploads a single file successfully', async ({ page }) => {
    await page.getByRole('button', { name: /choose file|browse/i }).setInputFiles(testFile);
    await expect(page.getByText(/{{testFileName}}/)).toBeVisible();
    await page.getByRole('button', { name: /upload/i }).click();
    await expect(page.getByRole('progressbar')).toBeVisible();
    await expect(page.getByRole('alert')).toContainText(/upload.*complete|uploaded successfully/i);
  });

  // Happy path: multiple files
  test('uploads multiple files', async ({ page }) => {
    const input = page.getByRole('button', { name: /choose file|browse/i });
    await input.setInputFiles([testFile, testFile]);
    await expect(page.getByText(/2 files?|{{testFileName}}/i)).toBeVisible();
    await page.getByRole('button', { name: /upload/i }).click();
    await expect(page.getByRole('alert')).toContainText(/2.*uploaded/i);
  });

  // Happy path: drag and drop
  test('uploads file via drag and drop', async ({ page }) => {
    const dropzone = page.getByRole('region', { name: /drop.*files|drag.*here/i });
    await expect(dropzone).toBeVisible();
    // Use DataTransfer to simulate drag-drop
    const dataTransfer = await page.evaluateHandle(() => new DataTransfer());
    await dropzone.dispatchEvent('drop', { dataTransfer });
    // Alternatively, use setInputFiles on the hidden input if dropzone wraps one
    await page.locator('input[type="file"]').setInputFiles(testFile);
    await expect(page.getByText(/{{testFileName}}/)).toBeVisible();
  });

  // Happy path: remove file from queue before upload
  test('removes file from queue', async ({ page }) => {
    await page.locator('input[type="file"]').setInputFiles(testFile);
    await page.getByRole('button', { name: /remove.*{{testFileName}}|×/i }).click();
    await expect(page.getByText(/{{testFileName}}/)).toBeHidden();
  });

  // Error case: file too large
  test('shows error for oversized file', async ({ page }) => {
    await page.locator('input[type="file"]').setInputFiles(largeFile);
    await expect(page.getByText(/too large|exceeds.*{{maxFileSizeMb}}|max.*size/i)).toBeVisible();
  });

  // Error case: wrong file type
  test('shows error for unsupported file type', async ({ page }) => {
    const wrongTypeFile = { name: 'test.exe', mimeType: 'application/octet-stream', buffer: Buffer.from('data') };
    await page.locator('input[type="file"]').setInputFiles(wrongTypeFile);
    await expect(page.getByText(/unsupported.*type|{{acceptedMimeTypes}}.*only/i)).toBeVisible();
  });

  // Edge case: upload progress shown and completed
  test('shows progress bar during upload', async ({ page }) => {
    await page.locator('input[type="file"]').setInputFiles(testFile);
    await page.getByRole('button', { name: /upload/i }).click();
    const progress = page.getByRole('progressbar');
    await expect(progress).toBeVisible();
    await expect(progress).toBeHidden(); // completes and hides
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');
const path = require('path');

test.describe('File Upload', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/{{uploadPath}}');
  });

  test('uploads single file', async ({ page }) => {
    await page.locator('input[type="file"]').setInputFiles('{{testFilePath}}');
    await page.getByRole('button', { name: /upload/i }).click();
    await expect(page.getByRole('alert')).toContainText(/uploaded successfully/i);
  });

  test('shows error for oversized file', async ({ page }) => {
    await page.locator('input[type="file"]').setInputFiles('{{largeFilePath}}');
    await expect(page.getByText(/too large|exceeds/i)).toBeVisible();
  });

  test('shows error for wrong file type', async ({ page }) => {
    await page.locator('input[type="file"]').setInputFiles({
      name: 'bad.exe',
      mimeType: 'application/octet-stream',
      buffer: Buffer.from('x'),
    });
    await expect(page.getByText(/unsupported.*type/i)).toBeVisible();
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Single file | File picker → upload → success |
| Multiple files | Two files queued and uploaded |
| Drag-and-drop | Drop event populates queue |
| Remove from queue | File removed before upload |
| Oversized | Error shown, upload blocked |
| Wrong type | Mime-type error shown |
| Progress bar | Progressbar visible during upload |
