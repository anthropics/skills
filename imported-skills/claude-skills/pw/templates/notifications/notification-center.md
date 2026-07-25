# Notification Center Template

Tests full notification list, filtering, and bulk clear.

## Prerequisites
- Authenticated session via `{{authStorageStatePath}}`
- Mix of read/unread notifications seeded
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Notification Center', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/notifications');
  });

  // Happy path: notification list visible
  test('displays notification list', async ({ page }) => {
    await expect(page.getByRole('heading', { name: /notifications/i })).toBeVisible();
    await expect(page.getByRole('list', { name: /notifications/i })).toBeVisible();
    const items = page.getByRole('listitem');
    await expect(items.first()).toBeVisible();
  });

  // Happy path: filter by unread
  test('filters to show only unread notifications', async ({ page }) => {
    await page.getByRole('button', { name: /unread/i }).click();
    const items = page.getByRole('listitem');
    const count = await items.count();
    for (let i = 0; i < count; i++) {
      await expect(items.nth(i)).toHaveAttribute('aria-label', /unread/i);
    }
  });

  // Happy path: filter by type
  test('filters notifications by type', async ({ page }) => {
    await page.getByRole('combobox', { name: /type|category/i }).selectOption('{{notificationType}}');
    const items = page.getByRole('listitem');
    await expect(items.first()).toContainText(/{{notificationTypeLabel}}/i);
  });

  // Happy path: mark single as read
  test('marks individual notification as read', async ({ page }) => {
    const first = page.getByRole('listitem').first();
    await first.getByRole('button', { name: /mark.*read/i }).click();
    await expect(first).not.toHaveAttribute('data-unread', 'true');
  });

  // Happy path: clear all notifications
  test('clears all notifications', async ({ page }) => {
    await page.getByRole('button', { name: /clear all/i }).click();
    await page.getByRole('dialog').getByRole('button', { name: /confirm/i }).click();
    await expect(page.getByText(/no notifications|all cleared/i)).toBeVisible();
    await expect(page.getByRole('listitem')).toHaveCount(0);
  });

  // Happy path: pagination / load more
  test('loads more notifications on scroll or button click', async ({ page }) => {
    const initialCount = await page.getByRole('listitem').count();
    await page.getByRole('button', { name: /load more/i }).click();
    const newCount = await page.getByRole('listitem').count();
    expect(newCount).toBeGreaterThan(initialCount);
  });

  // Error case: empty state after clearing
  test('shows empty state after clearing all', async ({ page }) => {
    await page.getByRole('button', { name: /clear all/i }).click();
    await page.getByRole('dialog').getByRole('button', { name: /confirm/i }).click();
    await expect(page.getByText(/no notifications/i)).toBeVisible();
  });

  // Edge case: notification links to source
  test('clicking notification navigates to source', async ({ page }) => {
    await page.getByRole('listitem').first().getByRole('link').click();
    await expect(page).not.toHaveURL('{{baseUrl}}/notifications');
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Notification Center', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test('displays notification list', async ({ page }) => {
    await page.goto('{{baseUrl}}/notifications');
    await expect(page.getByRole('list', { name: /notifications/i })).toBeVisible();
    await expect(page.getByRole('listitem').first()).toBeVisible();
  });

  test('filters to unread only', async ({ page }) => {
    await page.goto('{{baseUrl}}/notifications');
    await page.getByRole('button', { name: /unread/i }).click();
    await expect(page.getByRole('listitem').first()).toHaveAttribute('aria-label', /unread/i);
  });

  test('clears all notifications', async ({ page }) => {
    await page.goto('{{baseUrl}}/notifications');
    await page.getByRole('button', { name: /clear all/i }).click();
    await page.getByRole('dialog').getByRole('button', { name: /confirm/i }).click();
    await expect(page.getByText(/no notifications/i)).toBeVisible();
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| List display | Notification items visible |
| Unread filter | Only unread items shown |
| Type filter | Category filter scopes list |
| Mark single read | Item marked, styling changes |
| Clear all | Confirmation → empty state |
| Load more | Additional items appended |
| Empty state | No-notifications message post-clear |
| Source link | Click navigates away from center |
