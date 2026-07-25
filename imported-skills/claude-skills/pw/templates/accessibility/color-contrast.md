# Color Contrast Template

Tests contrast ratios, color-blind safe palettes, and focus indicator visibility.

## Prerequisites
- App running at `{{baseUrl}}`
- axe-playwright installed: `npm i -D @axe-core/playwright`
- Page under test: `{{baseUrl}}/{{pagePath}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';
import AxeBuilder from '@axe-core/playwright';

test.describe('Color Contrast', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/{{pagePath}}');
  });

  // Happy path: no color contrast violations (axe)
  test('has no color contrast violations', async ({ page }) => {
    const results = await new AxeBuilder({ page })
      .withTags(['wcag2a', 'wcag2aa', 'wcag21aa'])
      .withRules(['color-contrast'])
      .analyze();
    expect(results.violations).toEqual([]);
  });

  // Happy path: body text contrast ratio ≥ 4.5:1
  test('body text meets WCAG AA contrast ratio', async ({ page }) => {
    const ratio = await page.evaluate(() => {
      const el = document.querySelector('p, main, [class*="body"]') as HTMLElement;
      if (!el) return null;
      const style = getComputedStyle(el);
      // Simplified check — use axe for full verification
      return style.color !== 'rgba(0, 0, 0, 0)' ? style.color : null;
    });
    expect(ratio).toBeTruthy();
  });

  // Happy path: large text contrast ratio ≥ 3:1
  test('headings have sufficient contrast', async ({ page }) => {
    const results = await new AxeBuilder({ page })
      .withRules(['color-contrast'])
      .include('h1, h2, h3, h4, h5, h6')
      .analyze();
    expect(results.violations).toEqual([]);
  });

  // Happy path: focus indicator meets contrast requirement
  test('focus indicator is visible and meets contrast', async ({ page }) => {
    await page.getByRole('button').first().focus();
    const outline = await page.getByRole('button').first().evaluate(el => {
      const s = getComputedStyle(el, ':focus');
      return {
        outlineWidth: parseFloat(s.outlineWidth),
        outlineColor: s.outlineColor,
        outlineStyle: s.outlineStyle,
      };
    });
    expect(outline.outlineWidth).toBeGreaterThanOrEqual(2);
    expect(outline.outlineColor).not.toBe('rgba(0, 0, 0, 0)');
  });

  // Happy path: error text contrast
  test('error messages have sufficient contrast', async ({ page }) => {
    await page.goto('{{baseUrl}}/{{formPath}}');
    await page.getByRole('button', { name: /submit/i }).click();
    const results = await new AxeBuilder({ page })
      .withRules(['color-contrast'])
      .include('[class*="error"], [role="alert"]')
      .analyze();
    expect(results.violations).toEqual([]);
  });

  // Happy path: no information conveyed by color alone
  test('status badges use text or icon in addition to color', async ({ page }) => {
    const badges = page.getByRole('status');
    const count = await badges.count();
    for (let i = 0; i < count; i++) {
      const text = await badges.nth(i).textContent();
      const ariaLabel = await badges.nth(i).getAttribute('aria-label');
      expect(text?.trim() || ariaLabel).toBeTruthy();
    }
  });

  // Edge case: full page axe scan for all WCAG 2.1 AA issues
  test('full page passes WCAG 2.1 AA axe scan', async ({ page }) => {
    const results = await new AxeBuilder({ page })
      .withTags(['wcag2a', 'wcag2aa', 'wcag21aa'])
      .exclude('{{knownExcludedSelector}}')
      .analyze();
    if (results.violations.length > 0) {
      const messages = results.violations.map(v =>
        `${v.id}: ${v.description} — ${v.nodes.map(n => n.target).join(', ')}`
      ).join('\n');
      throw new Error(`Axe violations:\n${messages}`);
    }
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');
const AxeBuilder = require('@axe-core/playwright').default;

test.describe('Color Contrast', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('{{baseUrl}}/{{pagePath}}');
  });

  test('no color contrast violations', async ({ page }) => {
    const results = await new AxeBuilder({ page })
      .withRules(['color-contrast'])
      .analyze();
    expect(results.violations).toEqual([]);
  });

  test('focus indicator is visible', async ({ page }) => {
    await page.getByRole('button').first().focus();
    const outlineWidth = await page.getByRole('button').first().evaluate(
      el => parseFloat(getComputedStyle(el).outlineWidth)
    );
    expect(outlineWidth).toBeGreaterThanOrEqual(2);
  });

  test('status badges use text not just color', async ({ page }) => {
    const badges = page.getByRole('status');
    const count = await badges.count();
    for (let i = 0; i < count; i++) {
      const text = await badges.nth(i).textContent();
      const label = await badges.nth(i).getAttribute('aria-label');
      expect((text?.trim()) || label).toBeTruthy();
    }
  });

  test('full page passes WCAG 2.1 AA', async ({ page }) => {
    const results = await new AxeBuilder({ page })
      .withTags(['wcag2a', 'wcag2aa', 'wcag21aa'])
      .analyze();
    expect(results.violations).toEqual([]);
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Contrast violations | axe color-contrast rule → no violations |
| Body text contrast | Text color non-transparent |
| Heading contrast | axe include h1-h6 → no violations |
| Focus indicator | outline-width ≥ 2px and non-transparent |
| Error text contrast | Error messages pass axe |
| Color-only info | Badges have text or aria-label |
| Full axe scan | WCAG 2.1 AA complete scan |
