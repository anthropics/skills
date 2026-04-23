---
name: awt
description: AI-powered E2E web app testing with self-healing DevQA loop. Use when asked to test a URL, run QA on a feature, check login/signup/checkout flows, or verify behavior after a code change. AWT scans the page, writes test scenarios, runs them in a real browser, and automatically fixes failures.
license: Apache-2.0
---

# AWT — AI Watch Tester

AWT gives Claude vision and browser control to run E2E tests automatically — no test code needed.

## When to use this skill

- User asks to "test this URL" or "run QA on my app"
- Checking if a user flow (login, signup, checkout) works
- Verifying behavior after a code change
- Running regression tests before a release

## Installation

```bash
pip install aat-devqa
playwright install chromium
```

## Workflow (always follow this order)

### Step 1 — Scan
```bash
aat scan --url <URL>
```
Read `.aat/scan_result.json`. Summarize what AWT found (pages, forms, buttons). **Show to user and wait for approval.**

### Step 2 — Generate scenario

Write a YAML test scenario. Example:

```yaml
id: SC-001
name: Login flow
steps:
  - action: navigate
    value: "{{url}}/login"
  - action: fill
    target: {text: "Email"}
    value: "test@example.com"
  - action: click
    target: {text: "Sign In"}
  - action: assert
    assert_type: url_contains
    value: "/dashboard"
```

**Show the scenario to the user. Wait for approval before running.**

### Step 3 — Run
```bash
aat run --skill-mode --fast <scenario.yaml>
```
If any step fails: stop immediately, report the failure, and wait for instructions.

### Step 4 — Report
Summarize: N/N steps passed, time taken, screenshot locations, any failures.

## Self-healing DevQA Loop

If tests fail repeatedly, use the full loop:
```bash
aat devqa "<description>" --url <URL> --max-attempts 3
```
AWT will analyze failures, patch the scenario, and retry automatically.

## Rules

- **Never run without user approval** between scan and run
- **Never use** `--auto-approve` or `-y` flags  
- **Never auto-fix source code** without explicit user instruction

## Links

- GitHub: https://github.com/ksgisang/AI-Watch-Tester
- PyPI: https://pypi.org/project/aat-devqa/
