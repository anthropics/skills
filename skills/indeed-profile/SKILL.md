---
name: indeed-profile
description: Automate updating Indeed profile education and work experience sections using Playwright browser automation. TRIGGER when: user wants to update Indeed profile, add or edit education on Indeed, add or edit work experience on Indeed, update resume on Indeed, or manage Indeed profile sections. DO NOT TRIGGER when: user is asking about job searching, Indeed job listings, salary information, or non-profile related Indeed tasks.
license: Complete terms in LICENSE.txt
---

# Indeed Profile Updater

This skill automates updating the **education** and **work experience** sections of an Indeed profile using Playwright browser automation.

## Prerequisites

Ensure Playwright is installed:
```bash
pip install playwright
playwright install chromium
```

## How to Use This Skill

### Step 1: Collect Required Information

Before running automation, ask the user for:

**Indeed Credentials:**
- Email address
- Password

**Education Details** (for each entry to add/update):
- School name
- Degree type (e.g., Bachelor's, Master's, Associate's, High School Diploma)
- Field of study / Major
- Start date (month and year)
- End date (month and year, or "Present" if still enrolled)
- GPA (optional)

**Work Experience Details** (for each entry to add/update):
- Job title
- Company name
- Location (city, state)
- Start date (month and year)
- End date (month and year, or "Present" if current job)
- Job description / responsibilities (bullet points recommended)

### Step 2: Run the Automation Script

Use the script at `scripts/update_indeed_profile.py`. Always run with `--help` first:

```bash
python scripts/update_indeed_profile.py --help
```

**Example usage — update education:**
```bash
python scripts/update_indeed_profile.py \
  --email "user@example.com" \
  --password "yourpassword" \
  --action education \
  --school "State University" \
  --degree "Bachelor of Science" \
  --field "Computer Science" \
  --edu-start "2018-09" \
  --edu-end "2022-05"
```

**Example usage — update work experience:**
```bash
python scripts/update_indeed_profile.py \
  --email "user@example.com" \
  --password "yourpassword" \
  --action work \
  --title "Software Engineer" \
  --company "Acme Corp" \
  --location "Austin, TX" \
  --work-start "2022-06" \
  --work-end "present" \
  --description "Developed and maintained web applications using Python and React."
```

### Step 3: Custom Playwright Script (if needed)

If the helper script does not cover a specific case, write a custom Playwright script following this pattern:

```python
from playwright.sync_api import sync_playwright
import time

INDEED_PROFILE_URL = "https://profile.indeed.com"

def login(page, email, password):
    page.goto("https://secure.indeed.com/auth")
    page.wait_for_load_state("networkidle")
    # Fill email
    page.fill('input[name="__email"]', email)
    page.click('button[type="submit"]')
    page.wait_for_load_state("networkidle")
    # Fill password
    page.fill('input[name="__password"]', password)
    page.click('button[type="submit"]')
    page.wait_for_load_state("networkidle")

def update_education(page, school, degree, field, start_date, end_date):
    page.goto(f"{INDEED_PROFILE_URL}/education")
    page.wait_for_load_state("networkidle")
    # Click "Add education" button
    page.click('text=Add education')
    page.wait_for_selector('input[name="school"]')
    page.fill('input[name="school"]', school)
    # ... fill remaining fields
    page.click('button[type="submit"]')

def update_work_experience(page, title, company, location, start_date, end_date, description):
    page.goto(f"{INDEED_PROFILE_URL}/experience")
    page.wait_for_load_state("networkidle")
    # Click "Add work experience" button
    page.click('text=Add work experience')
    page.wait_for_selector('input[name="jobTitle"]')
    page.fill('input[name="jobTitle"]', title)
    page.fill('input[name="company"]', company)
    # ... fill remaining fields
    page.click('button[type="submit"]')

with sync_playwright() as p:
    browser = p.chromium.launch(headless=False)  # Use headless=False to handle 2FA if needed
    page = browser.new_page()
    login(page, EMAIL, PASSWORD)
    update_education(page, SCHOOL, DEGREE, FIELD, START, END)
    update_work_experience(page, TITLE, COMPANY, LOCATION, START, END, DESC)
    browser.close()
```

## Reconnaissance-Then-Action Pattern

Indeed's UI can change. Always inspect the page before acting:

1. **Navigate and screenshot** to understand the current state:
   ```python
   page.goto("https://profile.indeed.com")
   page.wait_for_load_state("networkidle")
   page.screenshot(path="/tmp/indeed_profile.png", full_page=True)
   ```

2. **Inspect the DOM** to discover current selectors:
   ```python
   content = page.content()
   buttons = page.locator('button').all()
   inputs = page.locator('input').all()
   ```

3. **Use discovered selectors** to fill forms accurately.

## Important Notes

- **Two-factor authentication**: If Indeed prompts for 2FA, run with `headless=False` so the user can complete it manually, then resume automation.
- **Rate limiting**: Add `page.wait_for_timeout(1000)` between actions to avoid triggering bot detection.
- **Session cookies**: Save cookies after login to avoid re-authenticating on subsequent runs.
- **Existing entries**: To edit an existing entry instead of adding a new one, navigate to the entry and click its "Edit" button before filling fields.
- **Captcha**: If Indeed shows a CAPTCHA, the user must solve it manually. Run with `headless=False` in that case.

## Security

- Never hardcode credentials in scripts. Pass them via environment variables or command-line arguments.
- Do not log or store passwords in output files.

## Troubleshooting

| Problem | Solution |
|---|---|
| Login fails | Check credentials; run with `headless=False` to see what's happening |
| Element not found | Take a screenshot to inspect the current DOM; Indeed may have updated their UI |
| 2FA required | Switch to `headless=False` and complete 2FA manually |
| CAPTCHA appears | Run with `headless=False` and solve manually before automation continues |
| Form submission fails | Add `page.wait_for_load_state("networkidle")` after clicking submit |
