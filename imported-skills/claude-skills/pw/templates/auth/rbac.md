# RBAC Template

Tests role-based access control: admin vs user permissions and forbidden pages.

## Prerequisites
- Admin account: `{{adminUsername}}` / `{{adminPassword}}`
- Regular user: `{{userUsername}}` / `{{userPassword}}`
- App running at `{{baseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

const adminState = '{{adminStorageStatePath}}';
const userState  = '{{userStorageStatePath}}';

test.describe('RBAC — Admin', () => {
  test.use({ storageState: adminState });

  // Happy path: admin accesses admin panel
  test('admin can access admin panel', async ({ page }) => {
    await page.goto('{{baseUrl}}/admin');
    await expect(page.getByRole('heading', { name: /admin/i })).toBeVisible();
  });

  test('admin can see user management menu item', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await expect(page.getByRole('link', { name: /user management/i })).toBeVisible();
  });

  test('admin can delete any resource', async ({ page }) => {
    await page.goto('{{baseUrl}}/admin/{{entityName}}s');
    await page.getByRole('row').nth(1).getByRole('button', { name: /delete/i }).click();
    await page.getByRole('button', { name: /confirm/i }).click();
    await expect(page.getByRole('alert')).toContainText(/deleted/i);
  });
});

test.describe('RBAC — Regular User', () => {
  test.use({ storageState: userState });

  // Error case: user cannot access admin panel
  test('regular user sees 403 on admin panel', async ({ page }) => {
    await page.goto('{{baseUrl}}/admin');
    await expect(page).toHaveURL(/\/403|\/forbidden|\/dashboard/);
    const forbidden = page.getByRole('heading', { name: /403|forbidden|not authorized/i });
    await expect(forbidden).toBeVisible();
  });

  test('regular user does not see admin menu items', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await expect(page.getByRole('link', { name: /user management/i })).toBeHidden();
  });

  // Error case: user cannot delete others' resources
  test('regular user cannot delete another user\'s resource', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{entityName}}s/{{otherUsersEntityId}}');
    await expect(page.getByRole('button', { name: /delete/i })).toBeHidden();
  });

  // Edge case: direct navigation to admin API returns 403
  test('API returns 403 for unauthorized role', async ({ page }) => {
    const response = await page.request.get('{{baseUrl}}/api/admin/users');
    expect(response.status()).toBe(403);
  });
});

test.describe('RBAC — Role Elevation', () => {
  // Edge case: user promoted to admin gains access
  test('newly promoted admin can access admin panel', async ({ browser }) => {
    // Step 1: use admin context to promote user
    const adminCtx = await browser.newContext({ storageState: adminState });
    const adminPage = await adminCtx.newPage();
    await adminPage.goto('{{baseUrl}}/admin/users/{{promotedUserId}}/role');
    await adminPage.getByRole('combobox', { name: /role/i }).selectOption('admin');
    await adminPage.getByRole('button', { name: /save/i }).click();
    await adminCtx.close();

    // Step 2: promoted user can now access admin panel
    const userCtx = await browser.newContext({ storageState: userState });
    const userPage = await userCtx.newPage();
    await userPage.goto('{{baseUrl}}/admin');
    await expect(userPage.getByRole('heading', { name: /admin/i })).toBeVisible();
    await userCtx.close();
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('RBAC — Admin', () => {
  test.use({ storageState: '{{adminStorageStatePath}}' });

  test('admin can access admin panel', async ({ page }) => {
    await page.goto('{{baseUrl}}/admin');
    await expect(page.getByRole('heading', { name: /admin/i })).toBeVisible();
  });
});

test.describe('RBAC — Regular User', () => {
  test.use({ storageState: '{{userStorageStatePath}}' });

  test('regular user sees 403 on admin panel', async ({ page }) => {
    await page.goto('{{baseUrl}}/admin');
    await expect(page.getByRole('heading', { name: /403|forbidden/i })).toBeVisible();
  });

  test('API returns 403 for unauthorized role', async ({ page }) => {
    const res = await page.request.get('{{baseUrl}}/api/admin/users');
    expect(res.status()).toBe(403);
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Admin access | Admin reaches /admin panel |
| Admin menu | Admin-only nav items visible |
| Admin delete | Admin can delete any resource |
| User forbidden | Regular user → 403/redirect on /admin |
| User hidden menu | Admin nav items not rendered for user |
| API 403 | Backend enforces role on API routes |
| Role elevation | Promoted user gains new access immediately |
