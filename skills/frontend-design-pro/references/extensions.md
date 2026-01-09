# Frontend Design Pro Extensions

Detailed guidance for advanced frontend design patterns.

## Table of Contents

1. [Anti-Convergence Deep Dive](#anti-convergence-deep-dive)
2. [Visual Iteration Workflow](#visual-iteration-workflow)
3. [Test-Driven UI Patterns](#test-driven-ui-patterns)
4. [Progressive Disclosure](#progressive-disclosure-patterns)
5. [Skill Stacking](#skill-stacking-patterns)

---

## Anti-Convergence Deep Dive

### The Problem

Even with instructions to avoid generic aesthetics, Claude can converge on "alternative defaults":
- Space Grotesk instead of Inter
- Teal gradients instead of purple gradients
- Same asymmetric pattern repeatedly

### The Solution: Forced Variation

Maintain a mental checklist for each generation:

**Typography Rotation**:
\`\`\`
Generation 1: Playfair Display + IBM Plex Mono
Generation 2: Bricolage Grotesque + JetBrains Mono
Generation 3: Crimson Pro + Fira Code
Generation 4: Newsreader + Berkeley Mono
[cycle continues...]
\`\`\`

**Theme Rotation**:
\`\`\`
Generation 1: Dark theme, cool colors (blues, teals)
Generation 2: Light theme, warm colors (oranges, corals)
Generation 3: Dark theme, earth tones (greens, browns)
Generation 4: Light theme, vibrant (magentas, cyans)
\`\`\`

**Layout Rotation**:
\`\`\`
Generation 1: Asymmetric with left-heavy content
Generation 2: Centered with grid structure
Generation 3: Diagonal flow with overlapping elements
Generation 4: Minimal with maximum whitespace
\`\`\`

### Implementation

Add to your prompt:
\`\`\`
Before generating this UI, I'll check: which fonts/colors/layouts did I use in my last generation? I'll explicitly choose DIFFERENT ones for variation.
\`\`\`

---

## Visual Iteration Workflow

### Setup: Puppeteer MCP

Add to your claude_desktop_config.json:
\`\`\`json
{
  "mcpServers": {
    "puppeteer": {
      "command": "npx",
      "args": ["-y", "@modelcontextprotocol/server-puppeteer"]
    }
  }
}
\`\`\`

### Workflow Steps

1. **Initial Generation**: Create first implementation
2. **Screenshot Capture**:
   \`\`\`
   "Navigate to http://localhost:3000 and take a screenshot"
   \`\`\`
3. **Visual Comparison**:
   \`\`\`
   "Compare this screenshot to the design mockup. List all differences in:
    - Spacing (padding, margins)
    - Colors (exact hex values)
    - Typography (font size, weight, line-height)
    - Layout (alignment, positioning)"
   \`\`\`
4. **Targeted Fixes**: Address each discrepancy
5. **Iterate**: Repeat until match achieved

### Style Extraction

To replicate a reference design:
\`\`\`
"Analyze https://stripe.com/design and extract a style.md file with:
1. Typography system (families, scales, weights)
2. Color palette (primary, secondary, accents)
3. Spacing system (padding/margin patterns)
4. Component patterns (buttons, cards, forms)
5. Animation philosophy"
\`\`\`

---

## Test-Driven UI Patterns

### Playwright Visual Tests

\`\`\`typescript
// tests/ui.spec.ts
import { test, expect } from '@playwright/test';

test.describe('Landing Page UI', () => {
  test('typography uses non-generic fonts', async ({ page }) => {
    await page.goto('/');
    const h1Font = await page.evaluate(() => {
      const h1 = document.querySelector('h1');
      return window.getComputedStyle(h1).fontFamily;
    });
    expect(h1Font).not.toContain('Inter');
    expect(h1Font).not.toContain('Roboto');
    expect(h1Font).not.toContain('Arial');
  });

  test('no purple gradients on white', async ({ page }) => {
    await page.goto('/');
    const backgrounds = await page.evaluate(() => {
      const elements = document.querySelectorAll('*');
      return Array.from(elements).map(el =>
        window.getComputedStyle(el).background
      );
    });
    const hasPurpleGradient = backgrounds.some(bg =>
      bg.includes('gradient') && bg.includes('purple')
    );
    expect(hasPurpleGradient).toBe(false);
  });

  test('responsive breakpoints', async ({ page }) => {
    const viewports = [
      { width: 375, height: 667 },  // Mobile
      { width: 768, height: 1024 }, // Tablet
      { width: 1440, height: 900 }, // Desktop
    ];

    for (const viewport of viewports) {
      await page.setViewportSize(viewport);
      await page.goto('/');
      // Add specific assertions for each breakpoint
      await expect(page.locator('nav')).toBeVisible();
    }
  });

  test('color contrast meets WCAG AA', async ({ page }) => {
    await page.goto('/');
    // Use axe-playwright for accessibility testing
    const accessibilityScanResults = await new AxeBuilder({ page })
      .withTags(['wcag2aa'])
      .analyze();
    expect(accessibilityScanResults.violations).toEqual([]);
  });
});
\`\`\`

---

## Progressive Disclosure Patterns

### For Skills
- Keep SKILL.md under 500 lines
- Split detailed guidance into references/
- Reference files with clear "when to read" instructions

### For UIs
- Design information hierarchy first
- Critical content above fold
- Progressive loading for secondary content
- Skeleton states during load

---

## Skill Stacking Patterns

### With Brand Guidelines
\`\`\`
"Use two skills:
1. sg-brand-guidelines - Apply company colors and typography
2. frontend-design-pro - Ensure distinctive, non-generic aesthetics

Create a dashboard for our internal analytics."
\`\`\`

### With Web Artifacts Builder
\`\`\`
"Use two skills:
1. web-artifacts-builder - Build with React + Tailwind + shadcn/ui
2. frontend-design-pro - Apply distinctive aesthetics

Create an interactive data visualization dashboard."
\`\`\`

### Priority Order
When skills conflict, follow this priority:
1. Brand guidelines (company requirements)
2. Accessibility requirements
3. frontend-design-pro aesthetics
4. Technical constraints
