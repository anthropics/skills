---
name: awt
description: AI-powered E2E web testing with self-healing DevQA loop. Use this skill when asked to test a web app, run QA, check if a feature works, or verify a URL. AWT scans the page, generates test scenarios, runs them in a real browser, and automatically fixes failures.
license: Apache-2.0
---

# AWT — AI Watch Tester

AWT is an open-source tool that gives Claude vision and browser control to run E2E tests automatically.

## When to use this skill

Use AWT when the user asks to:
- Test a web app or a specific URL
- Run QA on a feature or user flow
- Check if signup, login, checkout, or any form works
- Verify behavior after a code change
- Run regression tests

## How to use

### Step 1 — Scan the page
```bash
aat scan --url <URL>
```
Read `.aat/scan_result.json` and summarize findings. **Wait for user approval before continuing.**

### Step 2 — Generate scenario
Write a YAML test scenario based on scan results. Show it to the user. **Wait for approval.**

### Step 3 — Run the test
```bash
aat run --skill-mode --fast <scenario.yaml>
```
If a step fails, stop immediately and report to the user.

### Step 4 — Report
Summarize results: steps passed, steps failed, screenshots saved.

## Rules

- Never run `aat devqa` (skips user checkpoints)
- Never use `--auto-approve` or `-y`
- Always show the scenario to the user before running
- Never auto-fix code without explicit instruction

## Installation

```bash
pip install aat-devqa
playwright install chromium
```

## Links

- GitHub: https://github.com/ksgisang/AI-Watch-Tester
- PyPI: https://pypi.org/project/aat-devqa/

