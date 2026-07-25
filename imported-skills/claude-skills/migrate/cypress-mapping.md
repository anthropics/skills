# Cypress → Playwright Mapping

## Commands

| Cypress | Playwright | Notes |
|---|---|---|
| `cy.visit('/page')` | `await page.goto('/page')` | Use `baseURL` in config |
| `cy.get('.selector')` | `page.locator('.selector')` | Prefer `getByRole()` |
| `cy.get('[data-cy=x]')` | `page.getByTestId('x')` | |
| `cy.contains('text')` | `page.getByText('text')` | |
| `cy.find('.child')` | `parent.locator('.child')` | Chain from parent locator |
| `cy.first()` | `locator.first()` | |
| `cy.last()` | `locator.last()` | |
| `cy.eq(n)` | `locator.nth(n)` | |
| `cy.parent()` | `locator.locator('..')` | Or restructure with better locators |
| `cy.children()` | `locator.locator('> *')` | |
| `cy.siblings()` | Not direct — restructure test | Use parent + filter |

## Actions

| Cypress | Playwright | Notes |
|---|---|---|
| `.click()` | `await locator.click()` | Always `await` |
| `.dblclick()` | `await locator.dblclick()` | |
| `.rightclick()` | `await locator.click({ button: 'right' })` | |
| `.type('text')` | `await locator.fill('text')` | `fill()` clears first |
| `.type('text', { delay: 50 })` | `await locator.pressSequentially('text', { delay: 50 })` | Simulates typing |
| `.clear()` | `await locator.clear()` | |
| `.check()` | `await locator.check()` | |
| `.uncheck()` | `await locator.uncheck()` | |
| `.select('value')` | `await locator.selectOption('value')` | |
| `.scrollTo()` | `await locator.scrollIntoViewIfNeeded()` | |
| `.trigger('event')` | `await locator.dispatchEvent('event')` | |
| `.focus()` | `await locator.focus()` | |
| `.blur()` | `await locator.blur()` | |

## Assertions

| Cypress | Playwright | Notes |
|---|---|---|
| `.should('be.visible')` | `await expect(locator).toBeVisible()` | Web-first, auto-retry |
| `.should('not.exist')` | `await expect(locator).not.toBeVisible()` | Or `.toHaveCount(0)` |
| `.should('have.text', 'x')` | `await expect(locator).toHaveText('x')` | |
| `.should('contain', 'x')` | `await expect(locator).toContainText('x')` | |
| `.should('have.value', 'x')` | `await expect(locator).toHaveValue('x')` | |
| `.should('have.attr', 'x', 'y')` | `await expect(locator).toHaveAttribute('x', 'y')` | |
| `.should('have.class', 'x')` | `await expect(locator).toHaveClass(/x/)` | |
| `.should('be.disabled')` | `await expect(locator).toBeDisabled()` | |
| `.should('be.checked')` | `await expect(locator).toBeChecked()` | |
| `.should('have.length', n)` | `await expect(locator).toHaveCount(n)` | |
| `cy.url().should('include', '/x')` | `await expect(page).toHaveURL(/\/x/)` | |
| `cy.title().should('eq', 'x')` | `await expect(page).toHaveTitle('x')` | |

## Network

| Cypress | Playwright |
|---|---|
| `cy.intercept('GET', '/api/*', { body: data })` | `await page.route('**/api/*', route => route.fulfill({ body: JSON.stringify(data) }))` |
| `cy.intercept('POST', '/api/*').as('save')` | `const savePromise = page.waitForResponse('**/api/*')` |
| `cy.wait('@save')` | `await savePromise` |

## Fixtures & Custom Commands

| Cypress | Playwright |
|---|---|
| `cy.fixture('data.json')` | `import data from './test-data/data.json'` |
| `Cypress.Commands.add('login', ...)` | `test.extend({ authenticatedPage: ... })` |
| `beforeEach(() => { ... })` | `test.beforeEach(async ({ page }) => { ... })` |
| `before(() => { ... })` | `test.beforeAll(async () => { ... })` |

## Config

| Cypress | Playwright |
|---|---|
| `baseUrl` in `cypress.config.ts` | `use.baseURL` in `playwright.config.ts` |
| `defaultCommandTimeout` | `expect.timeout` or `use.actionTimeout` |
| `video: true` | `use.video: 'on'` |
| `screenshotOnRunFailure` | `use.screenshot: 'only-on-failure'` |
| `retries: { runMode: 2 }` | `retries: 2` |
