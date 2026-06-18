#!/usr/bin/env python3
"""
Indeed Profile Updater
======================
Automates updating education and work experience sections on an Indeed profile
using Playwright browser automation.

Usage:
    python update_indeed_profile.py --help
    python update_indeed_profile.py --email EMAIL --password PASSWORD --action education ...
    python update_indeed_profile.py --email EMAIL --password PASSWORD --action work ...

Environment variables (alternative to flags):
    INDEED_EMAIL     - Indeed account email
    INDEED_PASSWORD  - Indeed account password
"""

import argparse
import os
import sys
import time

try:
    from playwright.sync_api import sync_playwright, TimeoutError as PlaywrightTimeoutError
except ImportError:
    print("ERROR: Playwright is not installed.")
    print("Install it with: pip install playwright && playwright install chromium")
    sys.exit(1)

INDEED_BASE_URL = "https://www.indeed.com"
INDEED_PROFILE_URL = "https://profile.indeed.com"
INDEED_AUTH_URL = "https://secure.indeed.com/auth"

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def screenshot(page, label: str):
    path = f"/tmp/indeed_{label}.png"
    page.screenshot(path=path, full_page=True)
    print(f"[screenshot] saved to {path}")


def wait(page, ms: int = 1500):
    """Polite pause to avoid bot-detection triggers."""
    page.wait_for_timeout(ms)


# ---------------------------------------------------------------------------
# Authentication
# ---------------------------------------------------------------------------

def login(page, email: str, password: str) -> bool:
    """
    Log in to Indeed. Returns True on success, False on failure.
    If 2FA or CAPTCHA appears, the script will pause and ask the user to
    complete it manually (only works with headless=False).
    """
    print(f"[login] Navigating to {INDEED_AUTH_URL} ...")
    page.goto(INDEED_AUTH_URL)
    page.wait_for_load_state("networkidle")
    wait(page)

    # --- Email step ---
    try:
        email_input = page.locator('input[name="__email"], input[type="email"], input[id*="email"]').first
        email_input.wait_for(state="visible", timeout=10000)
        email_input.fill(email)
        print("[login] Filled email.")
    except PlaywrightTimeoutError:
        screenshot(page, "login_no_email_field")
        print("[login] ERROR: Could not find email input. See /tmp/indeed_login_no_email_field.png")
        return False

    # Click Continue / Next
    try:
        page.locator('button[type="submit"], button:has-text("Continue"), button:has-text("Next")').first.click()
        page.wait_for_load_state("networkidle")
        wait(page)
    except PlaywrightTimeoutError:
        pass

    # --- Password step ---
    try:
        pwd_input = page.locator('input[name="__password"], input[type="password"]').first
        pwd_input.wait_for(state="visible", timeout=10000)
        pwd_input.fill(password)
        print("[login] Filled password.")
    except PlaywrightTimeoutError:
        screenshot(page, "login_no_password_field")
        print("[login] ERROR: Could not find password input. See /tmp/indeed_login_no_password_field.png")
        return False

    # Click Sign In
    try:
        page.locator('button[type="submit"], button:has-text("Sign in"), button:has-text("Log in")').first.click()
        page.wait_for_load_state("networkidle")
        wait(page, 2000)
    except PlaywrightTimeoutError:
        pass

    # Check for 2FA / CAPTCHA
    current_url = page.url
    if "challenge" in current_url or "captcha" in current_url or "verify" in current_url:
        print("\n[login] 2FA or CAPTCHA detected!")
        print("        Please complete the verification in the browser window, then press ENTER here.")
        input("        Press ENTER when done: ")
        page.wait_for_load_state("networkidle")
        wait(page, 2000)

    # Verify we are logged in by checking for profile-related elements
    if "indeed.com" in page.url and "auth" not in page.url:
        print("[login] Login appears successful.")
        return True

    screenshot(page, "login_failed")
    print(f"[login] Login may have failed. Current URL: {page.url}")
    print("        See /tmp/indeed_login_failed.png for details.")
    return False


# ---------------------------------------------------------------------------
# Education
# ---------------------------------------------------------------------------

def add_education(page, school: str, degree: str, field: str,
                  start_date: str, end_date: str, gpa: str = ""):
    """
    Add a new education entry on the Indeed profile.

    date format: "YYYY-MM" (e.g. "2018-09") or "present"
    """
    print(f"\n[education] Navigating to profile education page ...")
    page.goto(f"{INDEED_PROFILE_URL}/education")
    page.wait_for_load_state("networkidle")
    wait(page)
    screenshot(page, "education_before")

    # Click "Add education"
    try:
        add_btn = page.locator(
            'button:has-text("Add education"), a:has-text("Add education"), '
            'button:has-text("Add"), [data-testid*="add-education"]'
        ).first
        add_btn.wait_for(state="visible", timeout=10000)
        add_btn.click()
        page.wait_for_load_state("networkidle")
        wait(page)
        print("[education] Clicked 'Add education'.")
    except PlaywrightTimeoutError:
        screenshot(page, "education_no_add_button")
        print("[education] ERROR: Could not find 'Add education' button.")
        print("            See /tmp/indeed_education_no_add_button.png")
        return False

    screenshot(page, "education_form")

    # School name
    _fill_field(page, 'input[name*="school"], input[placeholder*="school"], input[id*="school"]', school, "school")

    # Degree
    _fill_field_or_select(page,
        'input[name*="degree"], input[placeholder*="degree"], select[name*="degree"]',
        degree, "degree")

    # Field of study
    _fill_field(page,
        'input[name*="field"], input[placeholder*="field"], input[name*="major"], input[placeholder*="major"]',
        field, "field of study")

    # Dates
    _fill_date(page, start_date, role="start", context="education")
    _fill_date(page, end_date, role="end", context="education")

    # GPA (optional)
    if gpa:
        _fill_field(page, 'input[name*="gpa"], input[placeholder*="gpa"]', gpa, "GPA", required=False)

    # Submit
    _submit_form(page, "education")
    return True


# ---------------------------------------------------------------------------
# Work Experience
# ---------------------------------------------------------------------------

def add_work_experience(page, title: str, company: str, location: str,
                        start_date: str, end_date: str, description: str = ""):
    """
    Add a new work experience entry on the Indeed profile.

    date format: "YYYY-MM" (e.g. "2022-06") or "present"
    """
    print(f"\n[work] Navigating to profile experience page ...")
    page.goto(f"{INDEED_PROFILE_URL}/experience")
    page.wait_for_load_state("networkidle")
    wait(page)
    screenshot(page, "work_before")

    # Click "Add work experience"
    try:
        add_btn = page.locator(
            'button:has-text("Add work experience"), a:has-text("Add work experience"), '
            'button:has-text("Add experience"), [data-testid*="add-work"]'
        ).first
        add_btn.wait_for(state="visible", timeout=10000)
        add_btn.click()
        page.wait_for_load_state("networkidle")
        wait(page)
        print("[work] Clicked 'Add work experience'.")
    except PlaywrightTimeoutError:
        screenshot(page, "work_no_add_button")
        print("[work] ERROR: Could not find 'Add work experience' button.")
        print("       See /tmp/indeed_work_no_add_button.png")
        return False

    screenshot(page, "work_form")

    # Job title
    _fill_field(page,
        'input[name*="title"], input[name*="jobTitle"], input[placeholder*="title"]',
        title, "job title")

    # Company
    _fill_field(page,
        'input[name*="company"], input[name*="employer"], input[placeholder*="company"]',
        company, "company")

    # Location
    _fill_field(page,
        'input[name*="location"], input[name*="city"], input[placeholder*="location"]',
        location, "location", required=False)

    # Currently working here checkbox
    if end_date.lower() == "present":
        try:
            checkbox = page.locator(
                'input[type="checkbox"][name*="current"], '
                'input[type="checkbox"][id*="current"]'
            ).first
            if not checkbox.is_checked():
                checkbox.check()
                print("[work] Checked 'I currently work here'.")
            wait(page)
        except Exception:
            pass

    # Dates
    _fill_date(page, start_date, role="start", context="work")
    if end_date.lower() != "present":
        _fill_date(page, end_date, role="end", context="work")

    # Description
    if description:
        _fill_field(page,
            'textarea[name*="description"], textarea[name*="duties"], '
            'textarea[placeholder*="description"], textarea[placeholder*="duties"]',
            description, "description", required=False)

    # Submit
    _submit_form(page, "work")
    return True


# ---------------------------------------------------------------------------
# Internal helpers
# ---------------------------------------------------------------------------

def _fill_field(page, selector: str, value: str, label: str, required: bool = True):
    try:
        el = page.locator(selector).first
        el.wait_for(state="visible", timeout=8000)
        el.fill(value)
        wait(page, 500)
        print(f"  Filled {label}: {value!r}")
    except PlaywrightTimeoutError:
        if required:
            print(f"  WARNING: Could not find {label} field (selector: {selector})")
        else:
            print(f"  SKIPPED optional {label} field (not found).")


def _fill_field_or_select(page, selector: str, value: str, label: str):
    """Try fill; if a <select>, pick by matching option text."""
    try:
        el = page.locator(selector).first
        el.wait_for(state="visible", timeout=8000)
        tag = el.evaluate("el => el.tagName.toLowerCase()")
        if tag == "select":
            el.select_option(label=value)
        else:
            el.fill(value)
        wait(page, 500)
        print(f"  Filled/selected {label}: {value!r}")
    except PlaywrightTimeoutError:
        print(f"  WARNING: Could not find {label} field (selector: {selector})")


def _fill_date(page, date_str: str, role: str, context: str):
    """
    Fill a date field.  date_str is "YYYY-MM" or "present".
    Tries common Indeed date input patterns (month/year dropdowns or text inputs).
    """
    if date_str.lower() == "present":
        return

    parts = date_str.split("-")
    year = parts[0] if len(parts) > 0 else ""
    month = parts[1] if len(parts) > 1 else ""

    role_label = "start" if role == "start" else "end"

    # Try month dropdown / input
    month_selectors = (
        f'select[name*="{role_label}Month"], select[name*="{role}Month"], '
        f'input[name*="{role_label}Month"], input[placeholder*="Month"][name*="{role}"]'
    )
    try:
        el = page.locator(month_selectors).first
        el.wait_for(state="visible", timeout=5000)
        tag = el.evaluate("el => el.tagName.toLowerCase()")
        if tag == "select":
            el.select_option(value=month)
        else:
            el.fill(month)
        print(f"  Filled {role_label} month: {month}")
    except PlaywrightTimeoutError:
        print(f"  SKIPPED {role_label} month field (not found).")

    # Try year dropdown / input
    year_selectors = (
        f'select[name*="{role_label}Year"], select[name*="{role}Year"], '
        f'input[name*="{role_label}Year"], input[placeholder*="Year"][name*="{role}"]'
    )
    try:
        el = page.locator(year_selectors).first
        el.wait_for(state="visible", timeout=5000)
        tag = el.evaluate("el => el.tagName.toLowerCase()")
        if tag == "select":
            el.select_option(value=year)
        else:
            el.fill(year)
        print(f"  Filled {role_label} year: {year}")
    except PlaywrightTimeoutError:
        print(f"  SKIPPED {role_label} year field (not found).")


def _submit_form(page, context: str):
    wait(page)
    try:
        submit_btn = page.locator(
            'button[type="submit"], button:has-text("Save"), button:has-text("Add")'
        ).first
        submit_btn.wait_for(state="visible", timeout=8000)
        submit_btn.click()
        page.wait_for_load_state("networkidle")
        wait(page, 2000)
        screenshot(page, f"{context}_after_submit")
        print(f"[{context}] Form submitted.")
    except PlaywrightTimeoutError:
        screenshot(page, f"{context}_submit_failed")
        print(f"[{context}] WARNING: Could not click submit button.")


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Update Indeed profile education and work experience via Playwright.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Add education
  python update_indeed_profile.py \\
      --email you@example.com --password secret \\
      --action education \\
      --school "MIT" --degree "Bachelor of Science" --field "Computer Science" \\
      --edu-start 2018-09 --edu-end 2022-05

  # Add work experience
  python update_indeed_profile.py \\
      --email you@example.com --password secret \\
      --action work \\
      --title "Software Engineer" --company "Acme Corp" --location "Austin, TX" \\
      --work-start 2022-06 --work-end present \\
      --description "Developed Python microservices and React frontends."

  # Use environment variables for credentials
  export INDEED_EMAIL=you@example.com
  export INDEED_PASSWORD=secret
  python update_indeed_profile.py --action education ...
""",
    )

    # Credentials
    creds = parser.add_argument_group("credentials")
    creds.add_argument("--email", default=os.environ.get("INDEED_EMAIL"),
                       help="Indeed account email (or set INDEED_EMAIL env var)")
    creds.add_argument("--password", default=os.environ.get("INDEED_PASSWORD"),
                       help="Indeed account password (or set INDEED_PASSWORD env var)")

    # Action
    parser.add_argument("--action", choices=["education", "work"], required=True,
                        help="Which section to update: 'education' or 'work'")

    # Browser options
    parser.add_argument("--headless", action="store_true", default=False,
                        help="Run browser in headless mode (default: visible window)")
    parser.add_argument("--slow-mo", type=int, default=50,
                        help="Slow down Playwright actions by N ms (default: 50)")

    # Education fields
    edu = parser.add_argument_group("education (required when --action education)")
    edu.add_argument("--school", help="School / university name")
    edu.add_argument("--degree", help="Degree type (e.g. Bachelor of Science)")
    edu.add_argument("--field", help="Field of study / major")
    edu.add_argument("--edu-start", metavar="YYYY-MM", help="Education start date")
    edu.add_argument("--edu-end", metavar="YYYY-MM", help="Education end date (or 'present')")
    edu.add_argument("--gpa", default="", help="GPA (optional)")

    # Work experience fields
    work = parser.add_argument_group("work experience (required when --action work)")
    work.add_argument("--title", help="Job title")
    work.add_argument("--company", help="Company / employer name")
    work.add_argument("--location", default="", help="Job location (city, state)")
    work.add_argument("--work-start", metavar="YYYY-MM", help="Employment start date")
    work.add_argument("--work-end", metavar="YYYY-MM",
                      help="Employment end date (or 'present' for current job)")
    work.add_argument("--description", default="",
                      help="Job description / responsibilities")

    return parser


def validate_args(args, parser):
    if not args.email or not args.password:
        parser.error("--email and --password are required (or set INDEED_EMAIL / INDEED_PASSWORD env vars).")

    if args.action == "education":
        missing = [f for f, v in [
            ("--school", args.school),
            ("--degree", args.degree),
            ("--field", args.field),
            ("--edu-start", args.edu_start),
            ("--edu-end", args.edu_end),
        ] if not v]
        if missing:
            parser.error(f"Education action requires: {', '.join(missing)}")

    if args.action == "work":
        missing = [f for f, v in [
            ("--title", args.title),
            ("--company", args.company),
            ("--work-start", args.work_start),
            ("--work-end", args.work_end),
        ] if not v]
        if missing:
            parser.error(f"Work action requires: {', '.join(missing)}")


def main():
    parser = build_parser()
    args = parser.parse_args()
    validate_args(args, parser)

    print("=" * 60)
    print("Indeed Profile Updater")
    print("=" * 60)
    print(f"Action   : {args.action}")
    print(f"Headless : {args.headless}")
    if not args.headless:
        print("NOTE     : Browser window will be visible. Complete any 2FA/CAPTCHA manually.")
    print()

    with sync_playwright() as p:
        browser = p.chromium.launch(
            headless=args.headless,
            slow_mo=args.slow_mo,
        )
        context = browser.new_context(
            viewport={"width": 1280, "height": 900},
            user_agent=(
                "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/120.0.0.0 Safari/537.36"
            ),
        )
        page = context.new_page()

        try:
            # Login
            ok = login(page, args.email, args.password)
            if not ok:
                print("\nERROR: Login failed. Cannot continue.")
                sys.exit(1)

            # Perform requested action
            if args.action == "education":
                success = add_education(
                    page,
                    school=args.school,
                    degree=args.degree,
                    field=args.field,
                    start_date=args.edu_start,
                    end_date=args.edu_end,
                    gpa=args.gpa,
                )
            else:  # work
                success = add_work_experience(
                    page,
                    title=args.title,
                    company=args.company,
                    location=args.location,
                    start_date=args.work_start,
                    end_date=args.work_end,
                    description=args.description,
                )

            if success:
                print(f"\nDone! '{args.action}' entry added successfully.")
            else:
                print(f"\nWARNING: '{args.action}' update may not have completed. Check screenshots in /tmp/.")
                sys.exit(1)

        finally:
            browser.close()


if __name__ == "__main__":
    main()
