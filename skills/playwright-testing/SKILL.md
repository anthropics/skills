---
name: playwright-testing
description: Production-tested Playwright patterns for E2E, API, component, visual, accessibility, and security testing. Covers locators, fixtures, POM, network mocking, auth flows, debugging, CI/CD (GitHub Actions, GitLab, CircleCI, Azure, Jenkins), framework recipes (React, Next.js, Vue, Angular), and migration guides from Cypress/Selenium. TypeScript and JavaScript.
license: MIT
---

# Playwright Testing

> Opinionated, production-tested Playwright guidance. Every pattern includes when (and when *not*) to use it.

**70+ reference guides** covering the full Playwright surface: selectors, assertions, fixtures, page objects, network mocking, auth, visual regression, accessibility, API testing, CI/CD, debugging, and more, with TypeScript and JavaScript examples throughout.

## Golden Rules

1. **`getByRole()` over CSS/XPath** - resilient to markup changes, mirrors how users see the page
2. **Never `page.waitForTimeout()`** - use `expect(locator).toBeVisible()` or `page.waitForURL()`
3. **Web-first assertions** - `expect(locator)` auto-retries; `expect(await locator.textContent())` does not
4. **Isolate every test** - no shared state, no execution-order dependencies
5. **`baseURL` in config** - zero hardcoded URLs in tests
6. **Retries: `2` in CI, `0` locally** - surface flakiness where it matters
7. **Traces: `'on-first-retry'`** - rich debugging artifacts without CI slowdown
8. **Fixtures over globals** - share state via `test.extend()`, not module-level variables
9. **One behavior per test** - multiple related `expect()` calls are fine
10. **Mock external services only** - never mock your own app; mock third-party APIs, payment gateways, email

## Guide Index

### Writing Tests

| What you're doing | Guide | Deep dive |
|---|---|---|
| Choosing selectors | [locators.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/locators.md) | [locator-strategy.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/locator-strategy.md) |
| Assertions & waiting | [assertions-and-waiting.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/assertions-and-waiting.md) | |
| Organizing test suites | [test-organization.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/test-organization.md) | [test-architecture.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/test-architecture.md) |
| Playwright config | [configuration.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/configuration.md) | |
| Page objects | [page-object-model.md](https://github.com/testdino-hq/playwright-skill/blob/main/pom/page-object-model.md) | [pom-vs-fixtures-vs-helpers.md](https://github.com/testdino-hq/playwright-skill/blob/main/pom/pom-vs-fixtures-vs-helpers.md) |
| Fixtures & hooks | [fixtures-and-hooks.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/fixtures-and-hooks.md) | |
| Test data | [test-data-management.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/test-data-management.md) | |
| Auth & login | [authentication.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/authentication.md) | [auth-flows.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/auth-flows.md) |
| API testing (REST/GraphQL) | [api-testing.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/api-testing.md) | |
| Visual regression | [visual-regression.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/visual-regression.md) | |
| Accessibility | [accessibility.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/accessibility.md) | |
| Mobile & responsive | [mobile-and-responsive.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/mobile-and-responsive.md) | |
| Component testing | [component-testing.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/component-testing.md) | |
| Network mocking | [network-mocking.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/network-mocking.md) | [when-to-mock.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/when-to-mock.md) |
| Forms & validation | [forms-and-validation.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/forms-and-validation.md) | |
| File uploads/downloads | [file-operations.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/file-operations.md) | [file-upload-download.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/file-upload-download.md) |
| Error & edge cases | [error-and-edge-cases.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/error-and-edge-cases.md) | |
| CRUD flows | [crud-testing.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/crud-testing.md) | |
| Drag and drop | [drag-and-drop.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/drag-and-drop.md) | |
| Search & filter UI | [search-and-filter.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/search-and-filter.md) | |

### Debugging & Fixing

| Problem | Guide |
|---|---|
| General debugging workflow | [debugging.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/debugging.md) |
| Specific error message | [error-index.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/error-index.md) |
| Flaky / intermittent tests | [flaky-tests.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/flaky-tests.md) |
| Common beginner mistakes | [common-pitfalls.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/common-pitfalls.md) |

### Framework Recipes

| Framework | Guide |
|---|---|
| Next.js (App Router + Pages Router) | [nextjs.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/nextjs.md) |
| React (CRA, Vite) | [react.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/react.md) |
| Vue 3 / Nuxt | [vue.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/vue.md) |
| Angular | [angular.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/angular.md) |

### Migration Guides

| From | Guide |
|---|---|
| Cypress | [from-cypress.md](https://github.com/testdino-hq/playwright-skill/blob/main/migration/from-cypress.md) |
| Selenium / WebDriver | [from-selenium.md](https://github.com/testdino-hq/playwright-skill/blob/main/migration/from-selenium.md) |

### Architecture Decisions

| Question | Guide |
|---|---|
| Which locator strategy? | [locator-strategy.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/locator-strategy.md) |
| E2E vs component vs API? | [test-architecture.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/test-architecture.md) |
| Mock vs real services? | [when-to-mock.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/when-to-mock.md) |
| POM vs fixtures vs helpers? | [pom-vs-fixtures-vs-helpers.md](https://github.com/testdino-hq/playwright-skill/blob/main/pom/pom-vs-fixtures-vs-helpers.md) |

### CI/CD & Infrastructure

| Topic | Guide |
|---|---|
| GitHub Actions | [ci-github-actions.md](https://github.com/testdino-hq/playwright-skill/blob/main/ci/ci-github-actions.md) |
| GitLab CI | [ci-gitlab.md](https://github.com/testdino-hq/playwright-skill/blob/main/ci/ci-gitlab.md) |
| CircleCI / Azure DevOps / Jenkins | [ci-other.md](https://github.com/testdino-hq/playwright-skill/blob/main/ci/ci-other.md) |
| Parallel execution & sharding | [parallel-and-sharding.md](https://github.com/testdino-hq/playwright-skill/blob/main/ci/parallel-and-sharding.md) |
| Docker & containers | [docker-and-containers.md](https://github.com/testdino-hq/playwright-skill/blob/main/ci/docker-and-containers.md) |
| Reports & artifacts | [reporting-and-artifacts.md](https://github.com/testdino-hq/playwright-skill/blob/main/ci/reporting-and-artifacts.md) |
| Code coverage | [test-coverage.md](https://github.com/testdino-hq/playwright-skill/blob/main/ci/test-coverage.md) |
| Global setup/teardown | [global-setup-teardown.md](https://github.com/testdino-hq/playwright-skill/blob/main/ci/global-setup-teardown.md) |
| Multi-project config | [projects-and-dependencies.md](https://github.com/testdino-hq/playwright-skill/blob/main/ci/projects-and-dependencies.md) |

### Specialized Topics

| Topic | Guide |
|---|---|
| Multi-user & collaboration | [multi-user-and-collaboration.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/multi-user-and-collaboration.md) |
| WebSockets & real-time | [websockets-and-realtime.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/websockets-and-realtime.md) |
| Browser APIs (geo, clipboard, permissions) | [browser-apis.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/browser-apis.md) |
| iframes & Shadow DOM | [iframes-and-shadow-dom.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/iframes-and-shadow-dom.md) |
| Canvas & WebGL | [canvas-and-webgl.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/canvas-and-webgl.md) |
| Service workers & PWA | [service-workers-and-pwa.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/service-workers-and-pwa.md) |
| Electron apps | [electron-testing.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/electron-testing.md) |
| Browser extensions | [browser-extensions.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/browser-extensions.md) |
| Security testing | [security-testing.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/security-testing.md) |
| Performance & benchmarks | [performance-testing.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/performance-testing.md) |
| i18n & localization | [i18n-and-localization.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/i18n-and-localization.md) |
| Multi-tab & popups | [multi-context-and-popups.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/multi-context-and-popups.md) |
| Clock & time mocking | [clock-and-time-mocking.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/clock-and-time-mocking.md) |
| Third-party integrations | [third-party-integrations.md](https://github.com/testdino-hq/playwright-skill/blob/main/core/third-party-integrations.md) |

### CLI Browser Automation

| What you're doing | Guide |
|---|---|
| Core commands (open, click, fill, navigate) | [core-commands.md](https://github.com/testdino-hq/playwright-skill/blob/main/playwright-cli/core-commands.md) |
| Network mocking & interception | [request-mocking.md](https://github.com/testdino-hq/playwright-skill/blob/main/playwright-cli/request-mocking.md) |
| Running custom Playwright code | [running-custom-code.md](https://github.com/testdino-hq/playwright-skill/blob/main/playwright-cli/running-custom-code.md) |
| Multi-session browser management | [session-management.md](https://github.com/testdino-hq/playwright-skill/blob/main/playwright-cli/session-management.md) |
| Cookies, localStorage, auth state | [storage-and-auth.md](https://github.com/testdino-hq/playwright-skill/blob/main/playwright-cli/storage-and-auth.md) |
| Test code generation from CLI | [test-generation.md](https://github.com/testdino-hq/playwright-skill/blob/main/playwright-cli/test-generation.md) |
| Tracing and debugging | [tracing-and-debugging.md](https://github.com/testdino-hq/playwright-skill/blob/main/playwright-cli/tracing-and-debugging.md) |
| Screenshots, video, PDF | [screenshots-and-media.md](https://github.com/testdino-hq/playwright-skill/blob/main/playwright-cli/screenshots-and-media.md) |
| Device & environment emulation | [device-emulation.md](https://github.com/testdino-hq/playwright-skill/blob/main/playwright-cli/device-emulation.md) |
| Complex multi-step workflows | [advanced-workflows.md](https://github.com/testdino-hq/playwright-skill/blob/main/playwright-cli/advanced-workflows.md) |

## Language Note

All guides include TypeScript and JavaScript examples. When the project uses `.js` files or has no `tsconfig.json`, examples are adapted to plain JavaScript.
