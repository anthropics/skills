# Notification Preferences Template

Tests toggling notification channels and saving preferences.

## Prerequisites
- Authenticated session via `{{authStorageStatePath}}`
- Settings page at `{{baseUrl}}/settings/notifications`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Notification Preferences', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/settings/notifications');
  });

  // Happy path: enable email notifications
  test('enables email notifications', async ({ page }) => {
    const emailToggle = page.getByRole('switch', { name: /email notifications/i });
    if (!(await emailToggle.isChecked())) {
      await emailToggle.click();
    }
    await expect(emailToggle).toBeChecked();
    await page.getByRole('button', { name: /save|update/i }).click();
    await expect(page.getByRole('alert')).toContainText(/preferences.*saved|updated/i);
  });

  // Happy path: disable push notifications
  test('disables push notifications', async ({ page }) => {
    const pushToggle = page.getByRole('switch', { name: /push notifications/i });
    if (await pushToggle.isChecked()) {
      await pushToggle.click();
    }
    await expect(pushToggle).not.toBeChecked();
    await page.getByRole('button', { name: /save/i }).click();
    await expect(page.getByRole('alert')).toContainText(/saved/i);
  });

  // Happy path: preferences persist after reload
  test('saved preferences persist after page reload', async ({ page }) => {
    const emailToggle = page.getByRole('switch', { name: /email notifications/i });
    const wasChecked = await emailToggle.isChecked();
    await emailToggle.click();
    await page.getByRole('button', { name: /save/i }).click();
    await expect(page.getByRole('alert')).toContainText(/saved/i);
    await page.reload();
    if (wasChecked) {
      await expect(emailToggle).not.toBeChecked();
    } else {
      await expect(emailToggle).toBeChecked();
    }
  });

  // Happy path: notification frequency selector
  test('changes notification frequency', async ({ page }) => {
    await page.getByRole('combobox', { name: /frequency|digest/i }).selectOption('{{frequency}}');
    await page.getByRole('button', { name: /save/i }).click();
    await expect(page.getByRole('alert')).toContainText(/saved/i);
    await page.reload();
    await expect(page.getByRole('combobox', { name: /frequency|digest/i })).toHaveValue('{{frequency}}');
  });

  // Error case: save fails — preferences not changed
  test('shows error when save fails', async ({ page }) => {
    await page.route('{{baseUrl}}/api/settings/notifications*', route =>
      route.fulfill({ status: 500, body: JSON.stringify({ error: 'Server error' }) })
    );
    await page.getByRole('switch', { name: /email notifications/i }).click();
    await page.getByRole('button', { name: /save/i }).click();
    await expect(page.getByRole('alert')).toContainText(/error|failed to save/i);
  });

  // Edge case: unsubscribe all shows confirmation
  test('shows confirmation before unsubscribing all', async ({ page }) => {
    await page.getByRole('button', { name: /unsubscribe all/i }).click();
    await expect(page.getByRole('dialog', { name: /unsubscribe/i })).toBeVisible();
    await page.getByRole('button', { name: /cancel/i }).click();
    // Still subscribed
    await expect(page.getByRole('switch', { name: /email notifications/i })).toBeChecked();
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Notification Preferences', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test('saves notification preferences', async ({ page }) => {
    await page.goto('{{baseUrl}}/settings/notifications');
    const toggle = page.getByRole('switch', { name: /email notifications/i });
    await toggle.click();
    await page.getByRole('button', { name: /save/i }).click();
    await expect(page.getByRole('alert')).toContainText(/saved/i);
  });

  test('preferences persist after reload', async ({ page }) => {
    await page.goto('{{baseUrl}}/settings/notifications');
    const toggle = page.getByRole('switch', { name: /email notifications/i });
    const was = await toggle.isChecked();
    await toggle.click();
    await page.getByRole('button', { name: /save/i }).click();
    await page.reload();
    was
      ? await expect(toggle).not.toBeChecked()
      : await expect(toggle).toBeChecked();
  });

  test('shows error when save fails', async ({ page }) => {
    await page.goto('{{baseUrl}}/settings/notifications');
    await page.route('{{baseUrl}}/api/settings/notifications*', r =>
      r.fulfill({ status: 500, body: '{}' })
    );
    await page.getByRole('button', { name: /save/i }).click();
    await expect(page.getByRole('alert')).toContainText(/error|failed/i);
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Enable email | Toggle on → saved → success |
| Disable push | Toggle off → saved |
| Persists reload | Saved state survives page reload |
| Frequency selector | Dropdown value saved and restored |
| Save error | Server error → error alert |
| Unsubscribe all | Confirmation dialog before all disabled |
