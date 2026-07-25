# Keyboard Navigation Template

Tests tab order, focus visibility, and keyboard shortcuts.

## Prerequisites
- App running at `{{baseUrl}}`
- Page under test: `{{baseUrl}}/{{pagePath}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Keyboard Navigation', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/{{pagePath}}');
  });

  // Happy path: Tab moves through interactive elements in logical order
  test('Tab key cycles through focusable elements in correct order', async ({ page }) => {
    await page.keyboard.press('Tab');
    await expect(page.getByRole('link', { name: /skip.*main|skip navigation/i }))
      .toBeFocused();
    await page.keyboard.press('Tab');
    // First nav link focused
    const navLinks = page.getByRole('navigation').getByRole('link');
    await expect(navLinks.first()).toBeFocused();
  });

  // Happy path: skip link skips to main content
  test('skip-to-content link moves focus to main', async ({ page }) => {
    await page.keyboard.press('Tab');
    await page.keyboard.press('Enter');
    await expect(page.getByRole('main')).toBeFocused();
  });

  // Happy path: focus visible on all interactive elements
  test('focus ring visible on interactive elements', async ({ page }) => {
    const interactive = page.getByRole('button').first();
    await interactive.focus();
    const box = await interactive.boundingBox();
    // Take screenshot with focus and assert element has outline (visual only — use CSS check)
    const outline = await interactive.evaluate(el =>
      getComputedStyle(el).outlineWidth
    );
    expect(parseFloat(outline)).toBeGreaterThan(0);
  });

  // Happy path: modal traps focus
  test('focus is trapped within modal when open', async ({ page }) => {
    await page.getByRole('button', { name: /open modal/i }).click();
    const modal = page.getByRole('dialog');
    await expect(modal).toBeVisible();
    // Repeatedly Tab and verify focus stays within dialog
    for (let i = 0; i < 10; i++) {
      await page.keyboard.press('Tab');
      const focused = page.locator(':focus');
      await expect(modal).toContainElement(focused);
    }
  });

  // Happy path: Escape closes modal
  test('Escape key closes modal', async ({ page }) => {
    await page.getByRole('button', { name: /open modal/i }).click();
    await expect(page.getByRole('dialog')).toBeVisible();
    await page.keyboard.press('Escape');
    await expect(page.getByRole('dialog')).toBeHidden();
    // Focus returns to trigger button
    await expect(page.getByRole('button', { name: /open modal/i })).toBeFocused();
  });

  // Happy path: keyboard shortcut
  test('keyboard shortcut {{shortcutKey}} triggers action', async ({ page }) => {
    await page.keyboard.press('{{shortcutKey}}');
    await expect(page.getByRole('{{shortcutTargetRole}}', { name: /{{shortcutTargetName}}/i })).toBeVisible();
  });

  // Error case: focus not lost on dynamic content update
  test('focus stays on element after async update', async ({ page }) => {
    const btn = page.getByRole('button', { name: /{{asyncButton}}/i });
    await btn.focus();
    await btn.press('Enter');
    await expect(btn).toBeFocused();
  });

  // Edge case: arrow keys navigate within component (listbox, tabs)
  test('arrow keys navigate within tab list', async ({ page }) => {
    const firstTab = page.getByRole('tab').first();
    await firstTab.focus();
    await page.keyboard.press('ArrowRight');
    await expect(page.getByRole('tab').nth(1)).toBeFocused();
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Keyboard Navigation', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/{{pagePath}}');
  });

  test('skip link moves focus to main content', async ({ page }) => {
    await page.keyboard.press('Tab');
    await page.keyboard.press('Enter');
    await expect(page.getByRole('main')).toBeFocused();
  });

  test('Escape closes modal and returns focus', async ({ page }) => {
    await page.getByRole('button', { name: /open modal/i }).click();
    await page.keyboard.press('Escape');
    await expect(page.getByRole('dialog')).toBeHidden();
    await expect(page.getByRole('button', { name: /open modal/i })).toBeFocused();
  });

  test('focus ring visible on buttons', async ({ page }) => {
    await page.getByRole('button').first().focus();
    const outline = await page.getByRole('button').first().evaluate(
      el => getComputedStyle(el).outlineWidth
    );
    expect(parseFloat(outline)).toBeGreaterThan(0);
  });

  test('arrow keys navigate tab list', async ({ page }) => {
    await page.getByRole('tab').first().focus();
    await page.keyboard.press('ArrowRight');
    await expect(page.getByRole('tab').nth(1)).toBeFocused();
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Tab order | Skip link first, nav links after |
| Skip link | Moves focus to `<main>` |
| Focus ring | CSS outline-width > 0 on focus |
| Focus trap | Tab stays within open modal |
| Escape closes | Modal closed, trigger re-focused |
| Keyboard shortcut | Custom key triggers action |
| Focus after update | Focus not lost on async update |
| Arrow keys | Tab/listbox/menu arrow navigation |
