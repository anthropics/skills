# Screen Reader Template

Tests ARIA labels, live regions, and announcements for assistive technology.

## Prerequisites
- App running at `{{baseUrl}}`
- Page under test: `{{baseUrl}}/{{pagePath}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Screen Reader Accessibility', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/{{pagePath}}');
  });

  // Happy path: page has descriptive title
  test('page has meaningful title', async ({ page }) => {
    await expect(page).toHaveTitle(/{{expectedPageTitle}}/i);
  });

  // Happy path: main landmark exists
  test('page has main landmark', async ({ page }) => {
    await expect(page.getByRole('main')).toBeVisible();
  });

  // Happy path: images have alt text
  test('informational images have non-empty alt text', async ({ page }) => {
    const images = page.getByRole('img');
    const count = await images.count();
    for (let i = 0; i < count; i++) {
      const alt = await images.nth(i).getAttribute('alt');
      const isDecorative = await images.nth(i).getAttribute('role') === 'presentation'
        || alt === '';
      if (!isDecorative) {
        expect(alt).toBeTruthy();
      }
    }
  });

  // Happy path: form fields have accessible labels
  test('all form inputs have associated labels', async ({ page }) => {
    const inputs = page.getByRole('textbox');
    const count = await inputs.count();
    for (let i = 0; i < count; i++) {
      const input = inputs.nth(i);
      const labelledBy = await input.getAttribute('aria-labelledby');
      const ariaLabel = await input.getAttribute('aria-label');
      const id = await input.getAttribute('id');
      const hasLabel = labelledBy || ariaLabel || (id && await page.locator(`label[for="${id}"]`).count() > 0);
      expect(hasLabel).toBeTruthy();
    }
  });

  // Happy path: live region announces updates
  test('live region announces async updates', async ({ page }) => {
    const liveRegion = page.getByRole('status').or(page.locator('[aria-live]'));
    await page.getByRole('button', { name: /{{asyncTrigger}}/i }).click();
    await expect(liveRegion).not.toBeEmpty();
  });

  // Happy path: alert role used for errors
  test('validation errors use role="alert"', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{formPath}}');
    await page.getByRole('button', { name: /submit/i }).click();
    await expect(page.getByRole('alert')).toBeVisible();
    const liveValue = await page.getByRole('alert').first().getAttribute('aria-live');
    expect(liveValue ?? 'assertive').toBe('assertive');
  });

  // Happy path: buttons have accessible names
  test('icon-only buttons have aria-label', async ({ page }) => {
    const buttons = page.getByRole('button');
    const count = await buttons.count();
    for (let i = 0; i < count; i++) {
      const btn = buttons.nth(i);
      const text = (await btn.textContent())?.trim();
      const ariaLabel = await btn.getAttribute('aria-label');
      const ariaLabelledBy = await btn.getAttribute('aria-labelledby');
      // Must have visible text or aria-label or aria-labelledby
      expect(text || ariaLabel || ariaLabelledBy).toBeTruthy();
    }
  });

  // Happy path: navigation landmark labelled
  test('multiple nav elements have distinct aria-labels', async ({ page }) => {
    const navs = page.getByRole('navigation');
    const count = await navs.count();
    if (count > 1) {
      const labels = new Set<string>();
      for (let i = 0; i < count; i++) {
        const label = await navs.nth(i).getAttribute('aria-label') ?? '';
        labels.add(label);
      }
      expect(labels.size).toBe(count); // all unique
    }
  });

  // Edge case: expanded/collapsed state communicated
  test('accordion aria-expanded reflects open/closed state', async ({ page }) => {
    const trigger = page.getByRole('button', { name: /{{accordionItem}}/i });
    await expect(trigger).toHaveAttribute('aria-expanded', 'false');
    await trigger.click();
    await expect(trigger).toHaveAttribute('aria-expanded', 'true');
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Screen Reader Accessibility', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/{{pagePath}}');
  });

  test('page has meaningful title', async ({ page }) => {
    await expect(page).toHaveTitle(/{{expectedPageTitle}}/i);
  });

  test('main landmark exists', async ({ page }) => {
    await expect(page.getByRole('main')).toBeVisible();
  });

  test('validation errors use role=alert', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{formPath}}');
    await page.getByRole('button', { name: /submit/i }).click();
    await expect(page.getByRole('alert')).toBeVisible();
  });

  test('accordion aria-expanded toggles', async ({ page }) => {
    const trigger = page.getByRole('button', { name: /{{accordionItem}}/i });
    await expect(trigger).toHaveAttribute('aria-expanded', 'false');
    await trigger.click();
    await expect(trigger).toHaveAttribute('aria-expanded', 'true');
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Page title | `<title>` matches expected pattern |
| Main landmark | `<main>` present and visible |
| Image alt text | Informational images have non-empty alt |
| Form labels | All inputs have accessible label |
| Live region | Status region updated on async action |
| Alert role | Errors use role=alert (assertive) |
| Button names | Icon buttons have aria-label |
| Unique nav labels | Multiple navs have distinct labels |
| aria-expanded | Accordion state communicated |
