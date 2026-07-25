# Selenium → Playwright Mapping

## Driver Setup

| Selenium (JS) | Playwright |
|---|---|
| `new Builder().forBrowser('chrome').build()` | Handled by config — no driver setup |
| `driver.quit()` | Automatic — Playwright manages browser lifecycle |
| `driver.manage().setTimeouts(...)` | Config: `timeout`, `expect.timeout` |

## Navigation

| Selenium | Playwright | Notes |
|---|---|---|
| `driver.get(url)` | `await page.goto(url)` | Use `baseURL` |
| `driver.navigate().back()` | `await page.goBack()` | |
| `driver.navigate().forward()` | `await page.goForward()` | |
| `driver.navigate().refresh()` | `await page.reload()` | |
| `driver.getCurrentUrl()` | `page.url()` | |
| `driver.getTitle()` | `await page.title()` | |

## Element Location

| Selenium | Playwright | Preferred |
|---|---|---|
| `By.id('x')` | `page.locator('#x')` | `page.getByTestId('x')` |
| `By.css('.x')` | `page.locator('.x')` | `page.getByRole(...)` |
| `By.xpath('//div')` | `page.locator('xpath=//div')` | Avoid — use role-based |
| `By.name('x')` | `page.locator('[name=x]')` | `page.getByLabel(...)` |
| `By.linkText('x')` | `page.getByRole('link', { name: 'x' })` | ✅ Best practice |
| `By.partialLinkText('x')` | `page.getByRole('link', { name: /x/ })` | ✅ Best practice |
| `By.tagName('button')` | `page.getByRole('button')` | ✅ Best practice |
| `By.className('x')` | `page.locator('.x')` | `page.getByRole(...)` |
| `findElement()` | Returns first match | `locator.first()` |
| `findElements()` | `page.locator(selector)` | Use `.count()` or `.all()` |

## Actions

| Selenium | Playwright |
|---|---|
| `element.click()` | `await locator.click()` |
| `element.sendKeys('text')` | `await locator.fill('text')` |
| `element.sendKeys(Key.ENTER)` | `await locator.press('Enter')` |
| `element.clear()` | `await locator.clear()` |
| `element.submit()` | `await locator.press('Enter')` or click submit button |
| `element.getText()` | `await locator.textContent()` |
| `element.getAttribute('x')` | `await locator.getAttribute('x')` |
| `element.isDisplayed()` | `await locator.isVisible()` |
| `element.isEnabled()` | `await locator.isEnabled()` |
| `element.isSelected()` | `await locator.isChecked()` |

## Waits

| Selenium | Playwright | Notes |
|---|---|---|
| `WebDriverWait(driver, 10).until(EC.visibilityOf(el))` | `await expect(locator).toBeVisible()` | Auto-retries |
| `WebDriverWait(driver, 10).until(EC.elementToBeClickable(el))` | `await locator.click()` | Auto-waits for clickable |
| `WebDriverWait(driver, 10).until(EC.presenceOf(el))` | `await expect(locator).toBeAttached()` | |
| `WebDriverWait(driver, 10).until(EC.textToBe(el, 'x'))` | `await expect(locator).toHaveText('x')` | |
| `Thread.sleep(3000)` | ❌ Never use | Use assertions instead |
| `driver.manage().setTimeouts({ implicit: 10000 })` | Not needed | Playwright auto-waits |

## Advanced

| Selenium | Playwright |
|---|---|
| `Actions(driver).moveToElement(el).perform()` | `await locator.hover()` |
| `Actions(driver).dragAndDrop(src, tgt).perform()` | `await src.dragTo(tgt)` |
| `Actions(driver).doubleClick(el).perform()` | `await locator.dblclick()` |
| `Actions(driver).contextClick(el).perform()` | `await locator.click({ button: 'right' })` |
| `driver.switchTo().frame(el)` | `page.frameLocator('#frame')` |
| `driver.switchTo().defaultContent()` | Not needed — use `page` directly |
| `driver.switchTo().alert()` | `page.on('dialog', d => d.accept())` |
| `driver.switchTo().window(handle)` | `const popup = await page.waitForEvent('popup')` |
| `driver.executeScript(js)` | `await page.evaluate(js)` |
| `driver.takeScreenshot()` | `await page.screenshot({ path: 'x.png' })` |

## Test Structure

| Selenium (Jest/Mocha) | Playwright |
|---|---|
| `describe('Suite', () => { ... })` | `test.describe('Suite', () => { ... })` |
| `it('should...', () => { ... })` | `test('should...', async ({ page }) => { ... })` |
| `beforeAll(() => { ... })` | `test.beforeAll(async () => { ... })` |
| `beforeEach(() => { ... })` | `test.beforeEach(async ({ page }) => { ... })` |
| `afterEach(() => { ... })` | `test.afterEach(async ({ page }) => { ... })` |

## Key Differences

1. **No implicit waits** — Playwright auto-waits for actionability
2. **No driver management** — Playwright handles browser lifecycle
3. **Built-in assertions** — `expect(locator)` with auto-retry
4. **Parallel by default** — tests run in parallel, must be isolated
5. **Traces instead of screenshots** — richer debugging artifacts
