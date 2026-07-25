# Assertions Reference

## Web-First Assertions (Always Use These)

Auto-retry until timeout. Safe for dynamic content.

```typescript
// Visibility
await expect(locator).toBeVisible();
await expect(locator).not.toBeVisible();
await expect(locator).toBeHidden();

// Text
await expect(locator).toHaveText('exact text');
await expect(locator).toHaveText(/partial/i);
await expect(locator).toContainText('partial');

// Value (inputs)
await expect(locator).toHaveValue('entered text');
await expect(locator).toHaveValues(['option1', 'option2']);

// Attributes
await expect(locator).toHaveAttribute('href', '/dashboard');
await expect(locator).toHaveClass(/active/);
await expect(locator).toHaveId('main-nav');

// State
await expect(locator).toBeEnabled();
await expect(locator).toBeDisabled();
await expect(locator).toBeChecked();
await expect(locator).toBeEditable();
await expect(locator).toBeFocused();
await expect(locator).toBeAttached();

// Count
await expect(locator).toHaveCount(5);
await expect(locator).toHaveCount(0); // element doesn't exist

// CSS
await expect(locator).toHaveCSS('color', 'rgb(255, 0, 0)');

// Screenshots
await expect(locator).toHaveScreenshot('button.png');
await expect(page).toHaveScreenshot('full-page.png');
```

## Page Assertions

```typescript
await expect(page).toHaveURL('/dashboard');
await expect(page).toHaveURL(/\/dashboard/);
await expect(page).toHaveTitle('Dashboard - App');
await expect(page).toHaveTitle(/Dashboard/);
```

## Anti-Patterns (Never Do This)

```typescript
// BAD — no auto-retry
const text = await locator.textContent();
expect(text).toBe('Hello');

// BAD — snapshot in time, not reactive
const isVisible = await locator.isVisible();
expect(isVisible).toBe(true);

// BAD — evaluating in page context
const value = await page.evaluate(() =>
  document.querySelector('input')?.value
);
expect(value).toBe('test');
```

## Custom Timeout

```typescript
// Override timeout for slow operations
await expect(locator).toBeVisible({ timeout: 30_000 });
```

## Soft Assertions

Continue test even if assertion fails (report all failures at end):

```typescript
await expect.soft(locator).toHaveText('Expected');
await expect.soft(page).toHaveURL('/next');
// Test continues even if above fail
```
