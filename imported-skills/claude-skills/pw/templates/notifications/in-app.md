# In-App Notifications Template

Tests notification badge count, dropdown, and mark-as-read behaviour.

## Prerequisites
- Authenticated session via `{{authStorageStatePath}}`
- At least `{{unreadCount}}` unread notifications seeded
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('In-App Notifications', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  // Happy path: badge shows unread count
  test('shows unread notification count badge', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await expect(page.getByRole('status', { name: /notification.*count/i }))
      .toContainText('{{unreadCount}}');
  });

  // Happy path: dropdown opens on bell click
  test('opens notification dropdown on bell click', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.getByRole('button', { name: /notifications/i }).click();
    await expect(page.getByRole('menu', { name: /notifications/i })).toBeVisible();
    const items = page.getByRole('menuitem');
    await expect(items.first()).toBeVisible();
  });

  // Happy path: mark single notification as read
  test('marks notification as read', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.getByRole('button', { name: /notifications/i }).click();
    const firstNotif = page.getByRole('menuitem').first();
    await firstNotif.getByRole('button', { name: /mark as read/i }).click();
    await expect(firstNotif).toHaveAttribute('aria-label', /read/i);
    // Badge count decremented
    await expect(page.getByRole('status', { name: /notification.*count/i }))
      .toContainText(`${{{unreadCount}} - 1}`);
  });

  // Happy path: mark all as read
  test('marks all notifications as read', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.getByRole('button', { name: /notifications/i }).click();
    await page.getByRole('button', { name: /mark all.*read/i }).click();
    await expect(page.getByRole('status', { name: /notification.*count/i })).toBeHidden();
  });

  // Happy path: clicking notification navigates to context
  test('clicking notification navigates to relevant page', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.getByRole('button', { name: /notifications/i }).click();
    await page.getByRole('menuitem').first().click();
    await expect(page).toHaveURL(/\/{{notificationTargetPath}}/);
  });

  // Error case: notification dropdown empty state
  test('shows empty state when no notifications', async ({ page }) => {
    await page.route('{{baseUrl}}/api/notifications*', route =>
      route.fulfill({ status: 200, body: JSON.stringify({ items: [], unread: 0 }) })
    );
    await page.goto('{{baseUrl}}/dashboard');
    await page.getByRole('button', { name: /notifications/i }).click();
    await expect(page.getByText(/no notifications|all caught up/i)).toBeVisible();
  });

  // Edge case: dropdown closes on outside click
  test('closes notification dropdown on outside click', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.getByRole('button', { name: /notifications/i }).click();
    await expect(page.getByRole('menu', { name: /notifications/i })).toBeVisible();
    await page.getByRole('heading', { name: /dashboard/i }).click();
    await expect(page.getByRole('menu', { name: /notifications/i })).toBeHidden();
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('In-App Notifications', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test('badge shows unread count', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await expect(page.getByRole('status', { name: /notification.*count/i }))
      .toContainText('{{unreadCount}}');
  });

  test('opens dropdown on bell click', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.getByRole('button', { name: /notifications/i }).click();
    await expect(page.getByRole('menu', { name: /notifications/i })).toBeVisible();
  });

  test('marks all as read clears badge', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.getByRole('button', { name: /notifications/i }).click();
    await page.getByRole('button', { name: /mark all.*read/i }).click();
    await expect(page.getByRole('status', { name: /notification.*count/i })).toBeHidden();
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Badge count | Unread count shown in badge |
| Dropdown open | Bell click → notification list |
| Mark single read | Item marked, badge decremented |
| Mark all read | Badge hidden |
| Notification click | Navigates to context page |
| Empty state | No-notifications message |
| Outside click | Dropdown closes |
