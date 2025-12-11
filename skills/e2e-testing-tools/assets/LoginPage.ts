import { Page, expect } from '@playwright/test';

/**
 * LoginPage - Page Object for authentication flows
 * Encapsulates all login selectors and interactions
 */
export class LoginPage {
  constructor(private page: Page) {}

  /**
   * Navigate to login page
   */
  async goto() {
    await this.page.goto('/login');
    await this.page.waitForLoadState('networkidle');
  }

  /**
   * Fill email field
   */
  async fillEmail(email: string) {
    await this.page.fill('input[type="email"]', email);
  }

  /**
   * Fill password field
   */
  async fillPassword(password: string) {
    await this.page.fill('input[type="password"]', password);
  }

  /**
   * Click submit button and wait for navigation
   */
  async submitForm() {
    await Promise.all([
      this.page.waitForNavigation(),
      this.page.click('button[type="submit"]:has-text("Sign In")')
    ]);
  }

  /**
   * Complete login with email and password
   */
  async login(email: string, password: string) {
    await this.fillEmail(email);
    await this.fillPassword(password);
    await this.submitForm();
  }

  /**
   * Check if error message is displayed
   */
  async expectError(message: string) {
    const alert = this.page.locator('[role="alert"]');
    await expect(alert).toContainText(message);
  }

  /**
   * Check if email error is shown
   */
  async expectEmailError(message: string) {
    const error = this.page.locator('[data-testid="email-error"]');
    await expect(error).toContainText(message);
  }

  /**
   * Check if password error is shown
   */
  async expectPasswordError(message: string) {
    const error = this.page.locator('[data-testid="password-error"]');
    await expect(error).toContainText(message);
  }

  /**
   * Check if "Remember me" checkbox is present
   */
  async isRememberMeAvailable(): Promise<boolean> {
    return this.page.locator('input[type="checkbox"]').isVisible();
  }

  /**
   * Check if "Forgot password" link is present
   */
  async isForgotPasswordAvailable(): Promise<boolean> {
    return this.page.locator('a:has-text("Forgot password")').isVisible();
  }

  /**
   * Get submit button
   */
  getSubmitButton() {
    return this.page.locator('button[type="submit"]');
  }

  /**
   * Check if submit button is disabled
   */
  async isSubmitDisabled(): Promise<boolean> {
    return this.getSubmitButton().isDisabled();
  }
}
