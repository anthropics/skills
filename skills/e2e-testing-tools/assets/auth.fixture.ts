import { test as base, Page } from '@playwright/test';
import { LoginPage } from '../pages/LoginPage';

/**
 * Authenticated user fixture
 * Automatically logs in before each test
 */
export const test = base.extend<{
  authenticatedPage: Page;
  loginPage: LoginPage;
}>({
  authenticatedPage: async ({ page }, use) => {
    const loginPage = new LoginPage(page);

    // Login before test
    await loginPage.goto();
    await loginPage.login(
      process.env.TEST_USER_EMAIL || 'testuser@example.com',
      process.env.TEST_USER_PASSWORD || 'password123'
    );

    // Wait for dashboard to load
    await page.waitForURL('/dashboard');

    // Use authenticated page in test
    await use(page);

    // Logout after test (cleanup)
    await page.goto('/logout');
    await page.waitForURL('/login');
  },

  loginPage: async ({ page }, use) => {
    const loginPage = new LoginPage(page);
    await use(loginPage);
  },
});

export { expect } from '@playwright/test';
