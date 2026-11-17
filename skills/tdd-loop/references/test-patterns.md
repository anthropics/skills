# Test Patterns Reference

Per-framework boilerplate for the TDD loop.

---

## React + TypeScript (Vitest + React Testing Library)

### Component test

```typescript
import { render, screen, fireEvent } from '@testing-library/react'
import { describe, it, expect, vi } from 'vitest'
import { MyComponent } from './MyComponent'

describe('MyComponent', () => {
  it('should display error message when submission fails', async () => {
    const onSubmit = vi.fn().mockRejectedValueOnce(new Error('Network error'))
    render(<MyComponent onSubmit={onSubmit} />)

    fireEvent.click(screen.getByRole('button', { name: /submit/i }))

    expect(await screen.findByText(/something went wrong/i)).toBeInTheDocument()
  })
})
```

### Hook test

```typescript
import { renderHook, act } from '@testing-library/react'
import { useMyHook } from './useMyHook'

it('should toggle state on call', () => {
  const { result } = renderHook(() => useMyHook())
  expect(result.current.active).toBe(false)
  act(() => result.current.toggle())
  expect(result.current.active).toBe(true)
})
```

### Mocking modules

```typescript
vi.mock('../api/client', () => ({
  fetchUser: vi.fn().mockResolvedValue({ id: '1', name: 'Test User' })
}))
```

---

## Java / Spring Boot (JUnit 5 + Mockito + AssertJ)

### Service unit test

```java
@ExtendWith(MockitoExtension.class)
class UserServiceTest {

    @Mock
    private UserRepository userRepository;

    @InjectMocks
    private UserService userService;

    @Test
    void shouldThrowNotFoundWhenUserDoesNotExist() {
        when(userRepository.findById("missing-id")).thenReturn(Optional.empty());

        assertThatThrownBy(() -> userService.getUser("missing-id"))
            .isInstanceOf(UserNotFoundException.class)
            .hasMessageContaining("missing-id");
    }
}
```

### Controller slice test

```java
@WebMvcTest(UserController.class)
class UserControllerTest {

    @Autowired
    private MockMvc mockMvc;

    @MockBean
    private UserService userService;

    @Test
    void shouldReturn401WhenTokenIsExpired() throws Exception {
        mockMvc.perform(get("/api/users/me")
                .header("Authorization", "Bearer expired-token"))
            .andExpect(status().isUnauthorized());
    }
}
```

### Repository slice test

```java
@DataJpaTest
class UserRepositoryTest {

    @Autowired
    private UserRepository userRepository;

    @Test
    void shouldFindUserByEmail() {
        userRepository.save(new User("test@example.com", "Test User"));
        Optional<User> found = userRepository.findByEmail("test@example.com");
        assertThat(found).isPresent();
        assertThat(found.get().getName()).isEqualTo("Test User");
    }
}
```

---

## Node.js / Express (Jest + Supertest)

### Route integration test

```typescript
import request from 'supertest'
import { app } from '../app'
import { db } from '../db'

jest.mock('../db')

describe('POST /api/cards', () => {
  it('should return 201 with created card', async () => {
    (db.create as jest.Mock).mockResolvedValueOnce({ id: 'card-1', name: 'Visa' })

    const res = await request(app)
      .post('/api/cards')
      .set('Authorization', 'Bearer valid-token')
      .send({ name: 'Visa', last4: '1234' })

    expect(res.status).toBe(201)
    expect(res.body.id).toBe('card-1')
  })

  it('should return 400 when name is missing', async () => {
    const res = await request(app)
      .post('/api/cards')
      .set('Authorization', 'Bearer valid-token')
      .send({ last4: '1234' })

    expect(res.status).toBe(400)
  })
})
```

### Service unit test

```typescript
import { CardService } from './CardService'

const mockRepo = { save: jest.fn(), findById: jest.fn() }
const service = new CardService(mockRepo as any)

it('should throw when card limit exceeded', async () => {
  mockRepo.findById.mockResolvedValue(null)
  jest.spyOn(service, 'countByUser').mockResolvedValue(10)

  await expect(service.createCard('user-1', { name: 'Amex' }))
    .rejects.toThrow('Card limit exceeded')
})
```

---

## Playwright (TypeScript)

### Page interaction test

```typescript
import { test, expect } from '@playwright/test'

test('user can add a card and see it in the list', async ({ page }) => {
  await page.goto('/cards')
  await page.getByRole('button', { name: 'Add Card' }).click()
  await page.getByLabel('Card name').fill('Visa Platinum')
  await page.getByRole('button', { name: 'Save' }).click()

  await expect(page.getByText('Visa Platinum')).toBeVisible()
})
```

### Auth setup (reusable storage state)

```typescript
// auth.setup.ts
import { test as setup } from '@playwright/test'

setup('authenticate', async ({ page }) => {
  await page.goto('/login')
  await page.getByLabel('Email').fill(process.env.TEST_EMAIL!)
  await page.getByLabel('Password').fill(process.env.TEST_PASSWORD!)
  await page.getByRole('button', { name: 'Sign in' }).click()
  await page.waitForURL('/dashboard')
  await page.context().storageState({ path: 'playwright/.auth/user.json' })
})
```

### API mock within Playwright

```typescript
test('shows error banner when API fails', async ({ page }) => {
  await page.route('**/api/cards', route =>
    route.fulfill({ status: 500, body: 'Internal Server Error' })
  )
  await page.goto('/cards')
  await expect(page.getByRole('alert')).toContainText('Unable to load cards')
})
```

---

## Config snippets

### vitest.config.ts

```typescript
import { defineConfig } from 'vitest/config'
export default defineConfig({
  test: {
    environment: 'jsdom',
    setupFiles: ['./src/test/setup.ts'],
    coverage: { reporter: ['text', 'lcov'], threshold: { lines: 80 } }
  }
})
```

### playwright.config.ts (projects pattern — driven by TDD_CONFIG.browsers)

```typescript
import { defineConfig, devices } from '@playwright/test'

// Projects to include depend on TDD_CONFIG.browsers set during skill configuration:
// chromium               → projects: [chromium]
// chromium+firefox       → projects: [chromium, firefox]
// chromium+firefox+webkit → projects: [chromium, firefox, webkit]

export default defineConfig({
  testDir: './e2e',
  // headed=true during development (RED/GREEN phases), false for CI
  use: {
    baseURL: 'http://localhost:3000',
    trace: 'on-first-retry',
    // Override per run: npx playwright test --headed
  },
  projects: [
    { name: 'setup', testMatch: /auth\.setup\.ts/ },
    {
      name: 'chromium',
      use: { ...devices['Desktop Chrome'], storageState: 'playwright/.auth/user.json' },
      dependencies: ['setup'],
    },
    // Uncomment based on TDD_CONFIG.browsers:
    // {
    //   name: 'firefox',
    //   use: { ...devices['Desktop Firefox'], storageState: 'playwright/.auth/user.json' },
    //   dependencies: ['setup'],
    // },
    // {
    //   name: 'webkit',
    //   use: { ...devices['Desktop Safari'], storageState: 'playwright/.auth/user.json' },
    //   dependencies: ['setup'],
    // },
  ],
  // Development: run headed to visually verify behavior
  // CI: omit --headed flag; headless is the default
})
```

### Playwright headed run commands (for RED/GREEN development phases)

```bash
# Run specific test file headed in chromium
npx playwright test e2e/cards.spec.ts --headed --project=chromium

# Run all UI tests headed across configured browsers
npx playwright test --headed

# Run with UI mode (interactive, best for debugging failures)
npx playwright test --ui

# Show test report after run
npx playwright show-report
```
