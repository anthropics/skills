---
name: "migrate"
description: >-
  Migrate from Cypress or Selenium to Playwright. Use when user mentions
  "cypress", "selenium", "migrate tests", "convert tests", "switch to
  playwright", "move from cypress", or "replace selenium".
---

# Migrate to Playwright

Interactive migration from Cypress or Selenium to Playwright with file-by-file conversion.

## Input

`$ARGUMENTS` can be:
- `"from cypress"` — migrate Cypress test suite
- `"from selenium"` — migrate Selenium/WebDriver tests
- A file path: convert a specific test file
- Empty: auto-detect source framework

## Steps

### 1. Detect Source Framework

Use `Explore` subagent to scan:
- `cypress/` directory or `cypress.config.ts` → Cypress
- `selenium`, `webdriver` in `package.json` deps → Selenium
- `.py` test files with `selenium` imports → Selenium (Python)

### 2. Assess Migration Scope

Count files and categorize:

```
Migration Assessment:
- Total test files: X
- Cypress custom commands: Y
- Cypress fixtures: Z
- Estimated effort: [small|medium|large]
```

| Size | Files | Approach |
|---|---|---|
| Small (1-10) | Convert sequentially | Direct conversion |
| Medium (11-30) | Batch in groups of 5 | Use sub-agents |
| Large (31+) | Use `/batch` | Parallel conversion with `/batch` |

### 3. Set Up Playwright (If Not Present)

Run `/pw:init` first if Playwright isn't configured.

### 4. Convert Files

For each file, apply the appropriate mapping:

#### Cypress → Playwright

Load `cypress-mapping.md` for complete reference.

Key translations:
```
cy.visit(url)           → page.goto(url)
cy.get(selector)        → page.locator(selector) or page.getByRole(...)
cy.contains(text)       → page.getByText(text)
cy.find(selector)       → locator.locator(selector)
cy.click()              → locator.click()
cy.type(text)           → locator.fill(text)
cy.should('be.visible') → expect(locator).toBeVisible()
cy.should('have.text')  → expect(locator).toHaveText(text)
cy.intercept()          → page.route()
cy.wait('@alias')       → page.waitForResponse()
cy.fixture()            → JSON import or test data file
```

**Cypress custom commands** → Playwright fixtures or helper functions
**Cypress plugins** → Playwright config or fixtures
**`before`/`beforeEach`** → `test.beforeAll()` / `test.beforeEach()`

#### Selenium → Playwright

Load `selenium-mapping.md` for complete reference.

Key translations:
```
driver.get(url)                    → page.goto(url)
driver.findElement(By.id('x'))     → page.locator('#x') or page.getByTestId('x')
driver.findElement(By.css('.x'))   → page.locator('.x') or page.getByRole(...)
element.click()                    → locator.click()
element.sendKeys(text)             → locator.fill(text)
element.getText()                  → locator.textContent()
WebDriverWait + ExpectedConditions → expect(locator).toBeVisible()
driver.switchTo().frame()          → page.frameLocator()
Actions                            → locator.hover(), locator.dragTo()
```

### 5. Upgrade Locators

During conversion, upgrade selectors to Playwright best practices:
- `#id` → `getByTestId()` or `getByRole()`
- `.class` → `getByRole()` or `getByText()`
- `[data-testid]` → `getByTestId()`
- XPath → role-based locators

### 6. Convert Custom Commands / Utilities

- Cypress custom commands → Playwright custom fixtures via `test.extend()`
- Selenium page objects → Playwright page objects (keep structure, update API)
- Shared helpers → TypeScript utility functions

### 7. Verify Each Converted File

After converting each file:

```bash
npx playwright test <converted-file> --reporter=list
```

Fix any compilation or runtime errors before moving to the next file.

### 8. Clean Up

After all files are converted:
- Remove Cypress/Selenium dependencies from `package.json`
- Remove old config files (`cypress.config.ts`, etc.)
- Update CI workflow to use Playwright
- Update README with new test commands

Ask user before deleting anything.

## Output

- Conversion summary: files converted, total tests migrated
- Any tests that couldn't be auto-converted (manual intervention needed)
- Updated CI config
- Before/after comparison of test run results
