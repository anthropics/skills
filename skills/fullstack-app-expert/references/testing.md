# Testing (2025-2026)

## Testing Strategy for Full-Stack Apps

The modern stack is: **Vitest** for unit/integration, **Playwright** for E2E, **React Testing Library** for components, **MSW** for API mocking, **Storybook** for visual/component catalog.

Layer your tests:
1. **Unit** (Vitest): pure functions, utilities, Zod schemas, Server Actions, business logic
2. **Integration** (Vitest + RTL): React components with mocked APIs (MSW), Server Component rendering
3. **E2E** (Playwright): auth flows, checkout, critical user journeys — run against real app

Rule: most tests at integration level, fewer E2E (slower, flakier), minimal pure unit tests.

---

## Vitest — Configuration

Vitest is 5-10x faster than Jest and is Vite-native. 1.2s boot vs 8s for Jest.

```ts
// vitest.config.ts:
import { defineConfig } from 'vitest/config';
import react from '@vitejs/plugin-react';
import path from 'path';

export default defineConfig({
  plugins: [react()],
  test: {
    environment: 'jsdom',         // for React components
    globals: true,                // no import { describe, it, expect } needed
    setupFiles: ['./src/test/setup.ts'],
    coverage: {
      provider: 'v8',
      reporter: ['text', 'html'],
      exclude: ['node_modules/', 'src/test/'],
    },
  },
  resolve: {
    alias: { '@': path.resolve(__dirname, './src') },
  },
});
```

```ts
// src/test/setup.ts:
import '@testing-library/jest-dom';
import { server } from './mocks/server';

beforeAll(() => server.listen());
afterEach(() => server.resetHandlers());
afterAll(() => server.close());
```

### Testing Server Actions
```ts
// actions.test.ts:
import { createPost } from '@/app/actions';
import { db } from '@/lib/db';
import { posts } from '@/lib/schema';
import { vi } from 'vitest';

vi.mock('@/lib/db');

it('creates a post and returns it', async () => {
  vi.mocked(db.insert).mockResolvedValueOnce([{ id: 1, title: 'Test' }]);
  const formData = new FormData();
  formData.set('title', 'Test Post');
  const result = await createPost({}, formData);
  expect(db.insert).toHaveBeenCalledWith(posts);
  expect(result.success).toBe(true);
});
```

### Vitest Browser Mode (Component Testing in Real Browser)
Vitest 3.0 Browser Mode shares Chromium contexts — 30% faster than Playwright E2E for component-level tests:
```ts
// vitest.config.ts (browser mode):
test: {
  browser: {
    enabled: true,
    provider: 'playwright',
    name: 'chromium',
  },
}
```

---

## React Testing Library

```tsx
// UserProfile.test.tsx:
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import { UserProfile } from './UserProfile';

it('displays user name and allows editing', async () => {
  const user = userEvent.setup();
  render(<UserProfile userId="123" />);

  // Wait for async data:
  await screen.findByText('John Doe');

  // Simulate interaction:
  await user.click(screen.getByRole('button', { name: /edit/i }));
  await user.clear(screen.getByLabelText(/name/i));
  await user.type(screen.getByLabelText(/name/i), 'Jane Doe');
  await user.click(screen.getByRole('button', { name: /save/i }));

  await waitFor(() => {
    expect(screen.getByText('Jane Doe')).toBeInTheDocument();
  });
});
```

Key RTL principles:
- Query by role, label, or text (not CSS selectors or test IDs — tests should reflect user experience)
- `findBy*` for async, `getBy*` for sync
- `userEvent.setup()` over `fireEvent` — simulates real user interactions including pointer events

---

## Mock Service Worker (MSW) v2

MSW intercepts network requests at the service worker level — no monkey-patching, works identically in browser and Node.js.

```ts
// src/test/mocks/handlers.ts:
import { http, HttpResponse } from 'msw';

export const handlers = [
  http.get('/api/posts', () => {
    return HttpResponse.json([
      { id: 1, title: 'Test Post', content: 'Content' },
    ]);
  }),

  http.post('/api/posts', async ({ request }) => {
    const body = await request.json();
    return HttpResponse.json({ id: 2, ...body }, { status: 201 });
  }),

  // Error state:
  http.get('/api/user/me', () => {
    return HttpResponse.json({ error: 'Unauthorized' }, { status: 401 });
  }),
];

// src/test/mocks/server.ts (Node/Vitest):
import { setupServer } from 'msw/node';
import { handlers } from './handlers';
export const server = setupServer(...handlers);

// Override per-test:
it('handles error state', async () => {
  server.use(
    http.get('/api/posts', () => HttpResponse.json({ error: 'Server error' }, { status: 500 }))
  );
  render(<PostList />);
  await screen.findByText(/something went wrong/i);
});
```

MSW v2 changes from v1: `rest.*` → `http.*`, `req.json()` → `request.json()`, `ctx.json()` → `HttpResponse.json()`.

---

## Playwright — E2E Testing

```ts
// playwright.config.ts:
import { defineConfig, devices } from '@playwright/test';

export default defineConfig({
  testDir: './e2e',
  fullyParallel: true,
  retries: process.env.CI ? 2 : 0,
  workers: process.env.CI ? 1 : undefined,
  reporter: [['html'], ['github']],
  use: {
    baseURL: 'http://localhost:3000',
    trace: 'on-first-retry',
    screenshot: 'only-on-failure',
  },
  projects: [
    { name: 'chromium', use: { ...devices['Desktop Chrome'] } },
    { name: 'Mobile Safari', use: { ...devices['iPhone 14'] } },
  ],
  webServer: {
    command: 'pnpm dev',
    port: 3000,
    reuseExistingServer: !process.env.CI,
  },
});
```

```ts
// e2e/auth.spec.ts:
import { test, expect } from '@playwright/test';

test.describe('Authentication flow', () => {
  test('user can sign up and access dashboard', async ({ page }) => {
    await page.goto('/signup');
    await page.getByLabel('Email').fill('test@example.com');
    await page.getByLabel('Password').fill('SecurePass123!');
    await page.getByRole('button', { name: 'Create account' }).click();
    await expect(page).toHaveURL('/dashboard');
    await expect(page.getByRole('heading', { name: 'Welcome' })).toBeVisible();
  });

  test('protected routes redirect unauthenticated users', async ({ page }) => {
    await page.goto('/dashboard');
    await expect(page).toHaveURL('/login');
  });
});
```

### Playwright Auth State Reuse
```ts
// e2e/auth.setup.ts — run once, save state:
import { test as setup } from '@playwright/test';
setup('authenticate', async ({ page }) => {
  await page.goto('/login');
  await page.getByLabel('Email').fill('test@example.com');
  await page.getByLabel('Password').fill('password');
  await page.getByRole('button', { name: 'Sign in' }).click();
  await page.waitForURL('/dashboard');
  await page.context().storageState({ path: 'e2e/.auth/user.json' });
});

// playwright.config.ts:
projects: [
  { name: 'setup', testMatch: /auth\.setup\.ts/ },
  {
    name: 'authenticated',
    use: { storageState: 'e2e/.auth/user.json' },
    dependencies: ['setup'],
  },
]
```

---

## Storybook 8 — Component Documentation

Storybook 8 adds React Server Components support and improved MSW integration.

```tsx
// Button.stories.tsx:
import type { Meta, StoryObj } from '@storybook/react';
import { Button } from './Button';

const meta: Meta<typeof Button> = {
  component: Button,
  parameters: {
    msw: {
      handlers: [
        http.post('/api/action', () => HttpResponse.json({ success: true }))
      ]
    }
  }
};
export default meta;
type Story = StoryObj<typeof Button>;

export const Primary: Story = {
  args: { variant: 'default', children: 'Click me' },
};

export const Loading: Story = {
  args: { disabled: true, children: 'Loading...' },
};
```

Use Storybook for: component library documentation, visual regression testing (Chromatic), designer handoff, testing edge cases in isolation (error states, loading, empty, overflow).

---

## Testing Strategy by Layer

| What to test | Tool | Priority |
|---|---|---|
| Server Actions | Vitest + mocked DB | High |
| API route handlers | Vitest + supertest | High |
| Zod schemas | Vitest | High |
| React components (logic) | Vitest + RTL + MSW | High |
| Component library | Storybook | Medium |
| Auth flows | Playwright | High |
| Checkout/payment | Playwright | High |
| API contracts | MSW + Vitest | High |
| Cross-browser | Playwright projects | Medium |

Colocate unit/integration tests with source files (`Button.test.tsx` next to `Button.tsx`). Put E2E tests in top-level `e2e/` directory.
