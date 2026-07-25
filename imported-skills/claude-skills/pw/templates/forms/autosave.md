# Autosave Template

Tests auto-save draft functionality and draft restoration on revisit.

## Prerequisites
- Authenticated session via `{{authStorageStatePath}}`
- Form with autosave at `{{baseUrl}}/{{formPath}}`
- Autosave interval: `{{autosaveIntervalMs}}` ms

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Autosave', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/{{formPath}}');
  });

  // Happy path: autosave indicator appears after typing
  test('shows autosave indicator after typing', async ({ page }) => {
    await page.getByRole('textbox', { name: /{{fieldLabel}}/i }).fill('{{draftContent}}');
    await page.clock.install();
    await page.clock.fastForward({{autosaveIntervalMs}});
    await expect(page.getByText(/saved|draft saved/i)).toBeVisible();
  });

  // Happy path: draft restored on revisit
  test('restores draft on page revisit', async ({ page }) => {
    await page.getByRole('textbox', { name: /{{fieldLabel}}/i }).fill('{{draftContent}}');
    await page.clock.install();
    await page.clock.fastForward({{autosaveIntervalMs}});
    await expect(page.getByText(/draft saved/i)).toBeVisible();
    // Simulate revisit
    await page.reload();
    await expect(page.getByRole('textbox', { name: /{{fieldLabel}}/i })).toHaveValue('{{draftContent}}');
    await expect(page.getByText(/draft restored|you have a saved draft/i)).toBeVisible();
  });

  // Happy path: restore draft via banner
  test('restores draft when user clicks restore', async ({ page }) => {
    await page.reload();
    const banner = page.getByRole('alert', { name: /saved draft/i });
    if (await banner.isVisible()) {
      await banner.getByRole('button', { name: /restore/i }).click();
      await expect(page.getByRole('textbox', { name: /{{fieldLabel}}/i })).toHaveValue('{{draftContent}}');
    }
  });

  // Happy path: dismiss draft banner discards old draft
  test('discards draft when user clicks dismiss', async ({ page }) => {
    await page.reload();
    const banner = page.getByRole('alert', { name: /saved draft/i });
    if (await banner.isVisible()) {
      await banner.getByRole('button', { name: /dismiss|discard/i }).click();
      await expect(banner).toBeHidden();
      await expect(page.getByRole('textbox', { name: /{{fieldLabel}}/i })).toHaveValue('');
    }
  });

  // Happy path: draft cleared after successful submit
  test('clears autosaved draft after form submission', async ({ page }) => {
    await page.getByRole('textbox', { name: /{{fieldLabel}}/i }).fill('{{draftContent}}');
    await page.clock.install();
    await page.clock.fastForward({{autosaveIntervalMs}});
    await page.getByRole('button', { name: /submit|save/i }).click();
    await expect(page.getByRole('alert')).toContainText(/submitted|saved/i);
    // Revisit — no draft banner
    await page.goto('{{baseUrl}}/{{formPath}}');
    await expect(page.getByRole('alert', { name: /saved draft/i })).toBeHidden();
  });

  // Error case: autosave fails silently and retries
  test('shows autosave error when network fails', async ({ page }) => {
    await page.route('{{baseUrl}}/api/drafts*', route => route.abort('failed'));
    await page.getByRole('textbox', { name: /{{fieldLabel}}/i }).fill('{{draftContent}}');
    await page.clock.install();
    await page.clock.fastForward({{autosaveIntervalMs}});
    await expect(page.getByText(/save failed|could not save/i)).toBeVisible();
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Autosave', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test('shows autosave indicator after interval', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{formPath}}');
    await page.getByRole('textbox', { name: /{{fieldLabel}}/i }).fill('{{draftContent}}');
    await page.clock.install();
    await page.clock.fastForward({{autosaveIntervalMs}});
    await expect(page.getByText(/draft saved/i)).toBeVisible();
  });

  test('restores draft on page revisit', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{formPath}}');
    await page.getByRole('textbox', { name: /{{fieldLabel}}/i }).fill('{{draftContent}}');
    await page.clock.install();
    await page.clock.fastForward({{autosaveIntervalMs}});
    await page.reload();
    await expect(page.getByRole('textbox', { name: /{{fieldLabel}}/i })).toHaveValue('{{draftContent}}');
  });

  test('clears draft after successful submit', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{formPath}}');
    await page.getByRole('textbox', { name: /{{fieldLabel}}/i }).fill('{{draftContent}}');
    await page.clock.install();
    await page.clock.fastForward({{autosaveIntervalMs}});
    await page.getByRole('button', { name: /submit/i }).click();
    await page.goto('{{baseUrl}}/{{formPath}}');
    await expect(page.getByRole('alert', { name: /saved draft/i })).toBeHidden();
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Autosave indicator | "Draft saved" shown after interval |
| Draft restored | Revisit → field pre-filled |
| Restore via banner | Banner restore button populates field |
| Dismiss draft | Discard clears saved value |
| Cleared on submit | No draft banner after successful submit |
| Network failure | Save-failed message shown |
