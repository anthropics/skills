---
name: swift-testing
description: Generate production-grade iOS XCUITest (Swift) UI tests from plain-English scenarios using accessibility identifiers, explicit waits, screen objects, robust scrolling, and failure diagnostics.
---

# Swift Testing (XCUITest)

This skill teaches the agent how to turn plain-English iOS UI scenarios into **production-grade XCUITest** code that is **stable, readable, scalable, and CI-friendly**.

## When to use this skill
Use this skill when the user asks for any of the following:
- Write or refactor **XCUITest** UI tests in **Swift**
- Convert a **scenario / user story** into XCUITest
- Stabilize flaky UI tests (waits, scrolling, selectors, alerts)
- Create screen/page objects for XCUITest suites

Do not use this skill for:
- Unit tests, integration tests, snapshot tests
- Appium/Detox/Espresso (non-XCUITest)
- Performance tests or Xcode Instruments workflows

---

## Inputs to ask for (only if missing)
Ask ONLY for what’s needed to generate correct tests; do not over-question.

1) **Scenario**
- Steps the user wants to automate
- Expected outcomes / assertions

2) **Selector availability**
- Do accessibility identifiers exist already?
- If not, generate the list of identifiers needed

3) **App launch & environment**
- Is login required? Are there feature flags?
- Should tests start from a deep link or home screen?
- Any special environment setup (staging, mock server)?

4) **System dialogs**
- Are permission prompts expected (notifications, location, camera, etc.)?

If the user cannot provide identifiers, proceed anyway:
- Generate test code using *assumed* identifiers (clearly labeled)
- Output the “Identifiers to add” list as part of the deliverable

---

## Output contract (STRICT)
When you generate a test, you MUST always output:

A) **Test plan**
- numbered steps
- assertions after critical steps

B) **Swift XCUITest code**
- clean, compiling, copy/paste ready

C) **Screen Objects**
- created or updated (with selectors centralized)

D) **Accessibility identifiers required**
- exact strings and where they’re used

E) **Stability notes**
- waits, scroll strategy, alert handling, anchors

---

## Non-negotiable engineering rules

### Selector rules
1. Prefer `accessibilityIdentifier` selectors:
   - `app.buttons["id"]`
   - `app.textFields["id"]`
   - `app.staticTexts["id"]`
2. Avoid queries by localized labels, titles, or dynamic text.
3. Avoid XPath-like approaches (not applicable here) and brittle hierarchy traversal.
4. If identifiers are missing, output the required list and proceed with assumed IDs.

### Waiting/synchronization rules
- Never use `sleep()`.
- Use explicit waits:
  - `waitForExistence`
  - `XCTNSPredicateExpectation` for `exists` / `hittable`
- Wait on **navigation anchors** (a stable element that proves the screen is loaded).

### Assertions
- Assert after each meaningful navigation:
  - screen loaded anchor visible
  - error state visible
  - success state visible
- Prefer `XCTAssertTrue(anchor.exists)` only after `waitForVisible`.

### Scrolling
- Use bounded scrolling with max swipes.
- If not found after max swipes, fail with diagnostics.

### Failure diagnostics (always)
- Screenshot on failure (keepAlways)
- Include meaningful failure messages (“Expected Home title to appear…”)

---

## Project conventions the agent must follow

### Naming
- Test classes: `FeatureFlowTests` (e.g., `LoginFlowTests`)
- Test methods: `test_<action>_<expectedOutcome>()`
- Screen objects: `LoginScreen`, `HomeScreen`, `SettingsScreen`
- Identifier style: `screen.element` (e.g., `login.email`, `home.title`)

### Structure (recommended)
- `UITests/BaseUITestCase.swift`
- `UITests/Helpers/*.swift`
- `UITests/Screens/*.swift`
- `UITests/Tests/*.swift`

---

## Required helper set
When writing any test suite, prefer reusing the helper patterns in `templates/`:

- `templates/BaseUITestCase.swift`
- `templates/XCUIElement+Waits.swift`
- `templates/XCUIApplication+Scroll.swift`
- `templates/SystemAlerts.swift`

---

## What to generate (decision rules)

### If user gives a scenario only
Generate:
- screen objects required for that scenario
- the test case using those screen objects
- identifier list to add

### If user provides existing test code
Refactor into:
- screen objects
- helpers
- explicit waits
- stable selectors
…and return the improved code.

### If user asks to “make tests easier”
Introduce:
- screen objects
- small helper APIs (`tapWhenHittable`, `typeAndDismissKeyboard`, etc.)
but keep it simple and conventional (no heavy DSL unless asked).

---

## References in this skill folder
- `references/authoring-contract.md` — how to interpret user input and output format
- `references/locator-strategy.md` — detailed selector rules, tables, cells, dynamic content
- `references/flake-playbook.md` — flake patterns and fixes
- `references/examples.md` — complete end-to-end examples

---

## Minimal example (pattern)
User scenario:
> “Open app, login, verify home title.”

Agent output:
1) Test plan steps + assertions
2) `LoginScreen`, `HomeScreen`
3) `LoginFlowTests`
4) identifier list: `login.email`, `login.password`, `login.submit`, `home.title`

---

## Enforcement checklist (before final answer)
- [ ] No `sleep()`
- [ ] Accessibility IDs first
- [ ] Anchors used for screen load
- [ ] Assertions after critical steps
- [ ] Scrolling bounded
- [ ] Failure diagnostics included
- [ ] Output includes A–E sections (contract)
