# Toast Messages Template

Tests success, error, and warning toasts with auto-dismiss and manual close.

## Prerequisites
- Authenticated session via `{{authStorageStatePath}}`
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Toast Messages', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  // Happy path: success toast on action
  test('shows success toast after save action', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{formPath}}');
    await page.getByRole('textbox', { name: /{{fieldLabel}}/i }).fill('{{validValue}}');
    await page.getByRole('button', { name: /save/i }).click();
    const toast = page.getByRole('alert').filter({ hasText: /saved|success/i });
    await expect(toast).toBeVisible();
  });

  // Happy path: error toast on failure
  test('shows error toast when action fails', async ({ page }) => {
    await page.route('{{baseUrl}}/api/{{endpoint}}*', route =>
      route.fulfill({ status: 500, body: '{}' })
    );
    await page.goto('{{baseUrl}}/{{formPath}}');
    await page.getByRole('button', { name: /save/i }).click();
    const toast = page.getByRole('alert').filter({ hasText: /error|failed/i });
    await expect(toast).toBeVisible();
  });

  // Happy path: warning toast shown
  test('shows warning toast', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{warningTriggerPath}}');
    await page.getByRole('button', { name: /{{warningAction}}/i }).click();
    const toast = page.getByRole('alert').filter({ hasText: /warning|attention/i });
    await expect(toast).toBeVisible();
  });

  // Happy path: toast auto-dismisses
  test('toast auto-dismisses after timeout', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{formPath}}');
    await page.clock.install();
    await page.getByRole('textbox', { name: /{{fieldLabel}}/i }).fill('{{validValue}}');
    await page.getByRole('button', { name: /save/i }).click();
    const toast = page.getByRole('alert').filter({ hasText: /saved/i });
    await expect(toast).toBeVisible();
    await page.clock.fastForward({{toastDurationMs}});
    await expect(toast).toBeHidden();
  });

  // Happy path: toast manually dismissed
  test('dismisses toast via close button', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{formPath}}');
    await page.getByRole('button', { name: /save/i }).click();
    const toast = page.getByRole('alert').filter({ hasText: /saved/i });
    await expect(toast).toBeVisible();
    await toast.getByRole('button', { name: /close|dismiss|×/i }).click();
    await expect(toast).toBeHidden();
  });

  // Happy path: multiple toasts stack
  test('stacks multiple toasts', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{formPath}}');
    // Trigger two saves quickly
    await page.getByRole('button', { name: /save/i }).click();
    await page.getByRole('button', { name: /save/i }).click();
    const toasts = page.getByRole('alert');
    const count = await toasts.count();
    expect(count).toBeGreaterThanOrEqual(2);
  });

  // Edge case: toast announces to screen readers
  test('toast has live region role for accessibility', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{formPath}}');
    await page.getByRole('button', { name: /save/i }).click();
    const toast = page.getByRole('alert').first();
    await expect(toast).toBeVisible();
    // role="alert" implies aria-live="assertive"
    const role = await toast.getAttribute('role');
    expect(role).toMatch(/alert|status/);
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Toast Messages', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test('shows success toast after save', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{formPath}}');
    await page.getByRole('textbox', { name: /{{fieldLabel}}/i }).fill('{{validValue}}');
    await page.getByRole('button', { name: /save/i }).click();
    await expect(page.getByRole('alert').filter({ hasText: /saved|success/i })).toBeVisible();
  });

  test('toast auto-dismisses after timeout', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{formPath}}');
    await page.clock.install();
    await page.getByRole('button', { name: /save/i }).click();
    const toast = page.getByRole('alert').filter({ hasText: /saved/i });
    await expect(toast).toBeVisible();
    await page.clock.fastForward({{toastDurationMs}});
    await expect(toast).toBeHidden();
  });

  test('dismisses toast via close button', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{formPath}}');
    await page.getByRole('button', { name: /save/i }).click();
    const toast = page.getByRole('alert').filter({ hasText: /saved/i });
    await toast.getByRole('button', { name: /close|×/i }).click();
    await expect(toast).toBeHidden();
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Success toast | Save → green/success alert visible |
| Error toast | 500 → red/error alert visible |
| Warning toast | Trigger action → warning alert |
| Auto-dismiss | Toast hidden after N ms (clock-controlled) |
| Manual dismiss | Close button hides toast |
| Stacked toasts | Multiple alerts visible simultaneously |
| Accessible | role=alert or role=status present |
