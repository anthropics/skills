# Quick Start: Playwright Testing

## Setup (First Time Only)

```bash
# 1. Install dependencies
npm install

# 2. Install Playwright browsers
npx playwright install
```

## Running Tests

```bash
# All tests
npm test

# Interactive UI (recommended for development)
npm run test:ui

# Watch for changes and re-run
npm test -- --watch

# See results in HTML report
npx playwright show-report
```

## Creating Your First Test

1. Create `tests/my-feature.spec.ts`:

```typescript
import { test, expect } from '@playwright/test';

test('my first test', async ({ page }) => {
  await page.goto('http://localhost:3000');
  await page.wait_for_load_state('networkidle');
  
  // Add your test logic
  const heading = page.locator('h1');
  await expect(heading).toBeVisible();
});
```

1. Run it:

```bash
npm test
```

## Key Patterns

### Testing Local Server

```typescript
// Start your server first, then:
await page.goto('http://localhost:3000');
await page.wait_for_load_state('networkidle');
```

### Finding Elements

```typescript
// By text
page.locator('text=Click me')

// By role (accessible)
page.locator('role=button')

// By selector
page.locator('.my-button')
```

### Interactions

```typescript
// Click
await page.click('button');

// Fill input
await page.fill('input[type="email"]', 'test@example.com');

// Wait for element
await page.waitForSelector('.success-message');
```

## Common Commands

| Command | Purpose |
|---------|---------|
| `npm test` | Run all tests |
| `npm run test:ui` | Interactive UI mode |
| `npm run test:debug` | Step through tests |
| `npm run test:headed` | See browser while testing |
| `npx playwright test --grep "pattern"` | Run matching tests |
| `npx playwright show-report` | View HTML report |

## Debugging

### UI Mode (Best for Development)

```bash
npm run test:ui
```

- Click through test steps
- Jump to specific test
- View page snapshots

### Debug Mode

```bash
npm run test:debug
```

- Step through with DevTools
- Inspect page state
- Modify and re-run

### Screenshot on Failure

```typescript
await page.screenshot({ path: 'debug.png' });
```

## Next Steps

- Read [PLAYWRIGHT_GUIDE.md](./PLAYWRIGHT_GUIDE.md) for detailed documentation
- Check [tests/example.spec.ts](./tests/example.spec.ts) for examples
- Review [tests/advanced-examples.spec.ts](./tests/advanced-examples.spec.ts) for patterns
- Visit [playwright.dev](https://playwright.dev) for full API reference

## Troubleshooting

**Tests fail to run?**

```bash
npm install
npx playwright install
```

**Can't find elements?**

```bash
npm run test:debug  # Use DevTools to inspect
```

**Port already in use?**
Change the port in your server config, then update tests accordingly.

**On macOS with M1/M2 chip?**
Playwright should work fine, but rebuild if needed:

```bash
npm rebuild @playwright/test
```
