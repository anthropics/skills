#!/usr/bin/env python3
"""
Indeed profile updater pre-filled for Akash Poddar.
Logs in via Google OAuth (no password needed) then adds education
and work experience entries automatically.

Usage:
    python run_akash_profile_update.py

    # Update only one section
    python run_akash_profile_update.py --section education
    python run_akash_profile_update.py --section work

Prerequisites:
    pip install playwright
    playwright install chromium
"""

import argparse
import os
import sys
import time

try:
    from playwright.sync_api import sync_playwright, TimeoutError as PlaywrightTimeoutError
except ImportError:
    print("ERROR: Playwright not installed. Run: pip install playwright && playwright install chromium")
    sys.exit(1)

# ---------------------------------------------------------------------------
# Profile data
# ---------------------------------------------------------------------------

EMAIL = "akashpoddar.strategy@gmail.com"

EDUCATION = [
    {
        "school": "King's College London",
        "degree": "Master of Science",
        "field": "Strategic Entrepreneurship & Innovation",
        "start_month": "09",
        "start_year": "2019",
        "end_month": "09",
        "end_year": "2020",
        "gpa": "",
        "description": (
            "Distinction (70%). "
            "Business Plan Thesis (Distinction): Decentralized P2P Solar Microgrid for Rural Electrification. "
            "Business Strategy Case Study (Distinction): Google Stadia, Cloud Gaming Entry & Competitive Positioning."
        ),
    },
    {
        "school": "Savitribai Phule Pune University",
        "degree": "Bachelor of Business Administration",
        "field": "International Business",
        "start_month": "06",
        "start_year": "2015",
        "end_month": "05",
        "end_year": "2018",
        "gpa": "",
        "description": (
            "First Class. "
            "M&A Strategy Thesis (Distinction): Disney-Fox $52.4B Acquisition - Marvel IP Consolidation & Integration."
        ),
    },
]

WORK_EXPERIENCE = [
    {
        "title": "Strategy Manager - CEO's Office",
        "company": "Ingenious e-Brain",
        "location": "",
        "start_month": "01",
        "start_year": "2025",
        "current": True,
        "description": (
            "AI Strategy: Secured CEO approval for AI adoption across 80-member consulting firm by designing 6-function "
            "digitization roadmap. Deployed Copilot firm-wide & Claude for consulting teams by benchmarking 6 GenAI "
            "platforms across capability, cost & fit. Projected 30-40% research efficiency & 50% faster retrieval by "
            "delivering 72-page AI strategy mapping 40+ use cases firm-wide.\n"
            "Corporate Strategy: Earned board approval for 3-pillar transformation (Japan/GCC expansion, org "
            "consolidation, digitization). Determined Pharma, Semiconductor/EV & Clean Energy as FY26-27 "
            "capability-building priorities via structural IP filing surge analysis.\n"
            "Market Expansion: Delivered urgent pharma client engagement by sourcing & coordinating 70+ Market "
            "Access experts across U.S. Enabled Japan revenue diversification by selecting KK entity & hiring "
            "Country Manager (30+ screened)."
        ),
    },
    {
        "title": "Business Manager",
        "company": "Saraswati Material Science (Saraswati Group)",
        "location": "",
        "start_month": "01",
        "start_year": "2021",
        "end_month": "12",
        "end_year": "2024",
        "current": False,
        "description": (
            "Grew South India revenue to ₹24 Cr at 28% YoY by rolling out Polycarbonate & Agrochemicals business units. "
            "Captured 96% ROI & 9.7% gross margin in Year 1 by establishing 15K sq ft distribution hub enabling ~900 "
            "tons annual throughput. Raised on-time delivery to 80% & cut TAT to ~2 days from ~12.5 days by redesigning "
            "fulfillment workflows. Achieved 99% inventory accuracy across ₹17 Cr portfolio by deploying Python ETL "
            "workflows. Produced 3× ROI & drove 300+ leads (8% MQL-SQL) via ₹80K monthly campaigns across Google & Meta."
        ),
    },
    {
        "title": "IT Business Analyst",
        "company": "Accenture",
        "location": "",
        "start_month": "07",
        "start_year": "2018",
        "end_month": "07",
        "end_year": "2019",
        "current": False,
        "description": (
            "Banking Transformation: Advanced Tier-1 Nordic bank digitization across 275+ staff & dual JV partners. "
            "Eliminated 120+ manual hours/month & improved SLA precision to 95% by automating workflows via process "
            "mapping & VBA/Macros. Built dashboard tracking 10+ KPIs across time, cost & quality for 3 enterprise clients."
        ),
    },
]

# ---------------------------------------------------------------------------
# Browser helpers
# ---------------------------------------------------------------------------

def shot(page, label):
    path = f"/tmp/indeed_{label}.png"
    page.screenshot(path=path, full_page=True)
    print(f"  [screenshot] {path}")


def pause(page, ms=1200):
    page.wait_for_timeout(ms)


def try_click(page, selectors, label):
    for sel in selectors:
        try:
            el = page.locator(sel).first
            el.wait_for(state="visible", timeout=6000)
            el.click()
            print(f"  [click] {label}")
            return True
        except Exception:
            continue
    print(f"  [skip] could not click: {label}")
    return False


def try_fill(page, selectors, value, label, required=True):
    for sel in selectors:
        try:
            el = page.locator(sel).first
            el.wait_for(state="visible", timeout=6000)
            tag = el.evaluate("el => el.tagName.toLowerCase()")
            if tag == "select":
                el.select_option(label=value)
            else:
                el.fill(value)
            print(f"  [fill] {label}: {value!r}")
            return True
        except Exception:
            continue
    if required:
        print(f"  [warn] could not fill required field: {label}")
    return False


def try_select_by_value(page, selectors, value, label):
    for sel in selectors:
        try:
            el = page.locator(sel).first
            el.wait_for(state="visible", timeout=6000)
            el.select_option(value=value)
            print(f"  [select] {label}: {value!r}")
            return True
        except Exception:
            continue
    return False


# ---------------------------------------------------------------------------
# Login — Google OAuth
# ---------------------------------------------------------------------------

def login(page):
    """
    Log in to Indeed via 'Continue with Google'.
    Opens the Google OAuth popup and waits for the user to complete sign-in.
    Returns True on success.
    """
    print("\n--- LOGIN (Google OAuth) ---")
    page.goto("https://secure.indeed.com/auth")
    page.wait_for_load_state("networkidle")
    pause(page)
    shot(page, "login_page")

    # Find and click the "Continue with Google" / "Sign in with Google" button
    google_btn_selectors = [
        'a:has-text("Continue with Google")',
        'button:has-text("Continue with Google")',
        'a:has-text("Sign in with Google")',
        'button:has-text("Sign in with Google")',
        '[data-testid*="google"]',
        'a[href*="google"]',
        'button[aria-label*="Google"]',
    ]

    found = False
    for sel in google_btn_selectors:
        try:
            el = page.locator(sel).first
            el.wait_for(state="visible", timeout=5000)
            print(f"  [found] Google login button: {sel}")
            found = True

            # Google OAuth opens in a popup — capture it
            with page.context.expect_page(timeout=10000) as popup_info:
                el.click()

            popup = popup_info.value
            popup.wait_for_load_state("domcontentloaded")
            print(f"  [popup] Google auth popup opened: {popup.url[:80]}")
            print()
            print("  =============================================================")
            print("  ACTION REQUIRED: Complete Google sign-in in the popup window.")
            print(f"  Select account: {EMAIL}")
            print("  =============================================================")
            print()

            # Wait for the popup to close (user completed auth) — up to 3 minutes
            popup.wait_for_event("close", timeout=180000)
            print("  [ok] Google auth popup closed.")
            break

        except PlaywrightTimeoutError:
            continue
        except Exception as e:
            # Popup may not have fired — button might navigate in-place instead
            print(f"  [info] Popup handling note: {e}")
            found = True
            break

    if not found:
        shot(page, "login_no_google_btn")
        print("  [warn] Could not find 'Continue with Google' button.")
        print("         See /tmp/indeed_login_no_google_btn.png")
        print("         Please log in manually in the browser window, then press ENTER.")
        input("  Press ENTER once logged in: ")

    # Wait for Indeed to redirect back after OAuth
    page.wait_for_load_state("networkidle")
    pause(page, 2000)

    # If Indeed still shows auth page, wait for manual completion
    if "auth" in page.url or "login" in page.url.lower():
        shot(page, "login_waiting")
        print("  [wait] Still on auth page. Please complete login in the browser, then press ENTER.")
        input("  Press ENTER once you are logged in: ")
        page.wait_for_load_state("networkidle")
        pause(page, 2000)

    if "indeed.com" in page.url:
        print(f"  [ok] Logged in successfully. URL: {page.url}")
        return True

    shot(page, "login_failed")
    print(f"  [error] Login may have failed. URL: {page.url}")
    return False


# ---------------------------------------------------------------------------
# Education
# ---------------------------------------------------------------------------

def add_education_entry(page, edu):
    school = edu["school"]
    print(f"\n  Adding education: {school} ...")

    # Navigate and look for Add button
    page.goto("https://profile.indeed.com/education")
    page.wait_for_load_state("networkidle")
    pause(page)
    shot(page, f"edu_before_{school[:10].replace(' ', '_')}")

    clicked = try_click(page, [
        'button:has-text("Add education")',
        'a:has-text("Add education")',
        '[data-testid*="add-education"]',
        'button:has-text("Add")',
    ], "Add education")

    if not clicked:
        # Try navigating directly to add form
        page.goto("https://profile.indeed.com/education/add")
        page.wait_for_load_state("networkidle")
        pause(page)

    shot(page, f"edu_form_{school[:10].replace(' ', '_')}")

    # School
    try_fill(page, [
        'input[name*="school"]',
        'input[name*="School"]',
        'input[placeholder*="school" i]',
        'input[placeholder*="university" i]',
        'input[id*="school" i]',
    ], school, "school")
    pause(page, 500)

    # Degree
    try_fill(page, [
        'input[name*="degree"]',
        'input[name*="Degree"]',
        'input[placeholder*="degree" i]',
        'select[name*="degree" i]',
    ], edu["degree"], "degree")
    pause(page, 500)

    # Field of study
    try_fill(page, [
        'input[name*="field"]',
        'input[name*="major"]',
        'input[name*="study"]',
        'input[placeholder*="field" i]',
        'input[placeholder*="major" i]',
    ], edu["field"], "field of study")
    pause(page, 500)

    # Start month / year
    try_select_by_value(page, [
        'select[name*="startMonth"]',
        'select[name*="start_month"]',
        'select[id*="startMonth"]',
    ], edu["start_month"], "start month")
    try_select_by_value(page, [
        'select[name*="startYear"]',
        'select[name*="start_year"]',
        'select[id*="startYear"]',
    ], edu["start_year"], "start year")
    try_fill(page, ['input[name*="startDate"]', 'input[placeholder*="start" i]'],
             f"{edu['start_month']}/{edu['start_year']}", "start date", required=False)

    # End month / year
    try_select_by_value(page, [
        'select[name*="endMonth"]',
        'select[name*="end_month"]',
        'select[id*="endMonth"]',
    ], edu["end_month"], "end month")
    try_select_by_value(page, [
        'select[name*="endYear"]',
        'select[name*="end_year"]',
        'select[id*="endYear"]',
    ], edu["end_year"], "end year")
    try_fill(page, ['input[name*="endDate"]', 'input[placeholder*="end" i]'],
             f"{edu['end_month']}/{edu['end_year']}", "end date", required=False)

    # Description (if field available)
    if edu.get("description"):
        try_fill(page, [
            'textarea[name*="description"]',
            'textarea[placeholder*="description" i]',
        ], edu["description"], "description", required=False)

    pause(page)

    # Submit
    clicked = try_click(page, [
        'button[type="submit"]',
        'button:has-text("Save")',
        'button:has-text("Add")',
        'button:has-text("Done")',
    ], "Save education")
    page.wait_for_load_state("networkidle")
    pause(page, 2000)
    shot(page, f"edu_after_{school[:10].replace(' ', '_')}")
    return clicked


# ---------------------------------------------------------------------------
# Work Experience
# ---------------------------------------------------------------------------

def add_work_entry(page, job):
    title = job["title"]
    company = job["company"]
    print(f"\n  Adding work: {title} @ {company} ...")

    page.goto("https://profile.indeed.com/experience")
    page.wait_for_load_state("networkidle")
    pause(page)
    shot(page, f"work_before_{company[:10].replace(' ', '_')}")

    clicked = try_click(page, [
        'button:has-text("Add work experience")',
        'a:has-text("Add work experience")',
        'button:has-text("Add experience")',
        '[data-testid*="add-work"]',
        '[data-testid*="add-experience"]',
        'button:has-text("Add")',
    ], "Add work experience")

    if not clicked:
        page.goto("https://profile.indeed.com/experience/add")
        page.wait_for_load_state("networkidle")
        pause(page)

    shot(page, f"work_form_{company[:10].replace(' ', '_')}")

    # Job title
    try_fill(page, [
        'input[name*="jobTitle"]',
        'input[name*="title"]',
        'input[placeholder*="title" i]',
        'input[placeholder*="job title" i]',
        'input[id*="jobTitle" i]',
    ], title, "job title")
    pause(page, 500)

    # Company
    try_fill(page, [
        'input[name*="company"]',
        'input[name*="employer"]',
        'input[placeholder*="company" i]',
        'input[placeholder*="employer" i]',
        'input[id*="company" i]',
    ], company, "company")
    pause(page, 500)

    # Location (optional)
    if job.get("location"):
        try_fill(page, [
            'input[name*="location"]',
            'input[name*="city"]',
            'input[placeholder*="location" i]',
            'input[placeholder*="city" i]',
        ], job["location"], "location", required=False)
        pause(page, 500)

    # "I currently work here" checkbox
    if job.get("current"):
        try:
            cb = page.locator(
                'input[type="checkbox"][name*="current"], '
                'input[type="checkbox"][id*="current"]'
            ).first
            if not cb.is_checked():
                cb.check()
                print("  [check] I currently work here")
            pause(page, 500)
        except Exception:
            pass

    # Start month / year
    try_select_by_value(page, [
        'select[name*="startMonth"]', 'select[name*="start_month"]', 'select[id*="startMonth"]',
    ], job["start_month"], "start month")
    try_select_by_value(page, [
        'select[name*="startYear"]', 'select[name*="start_year"]', 'select[id*="startYear"]',
    ], job["start_year"], "start year")
    try_fill(page, ['input[name*="startDate"]', 'input[placeholder*="start" i]'],
             f"{job['start_month']}/{job['start_year']}", "start date", required=False)

    # End month / year (skip for current jobs)
    if not job.get("current") and job.get("end_month"):
        try_select_by_value(page, [
            'select[name*="endMonth"]', 'select[name*="end_month"]', 'select[id*="endMonth"]',
        ], job["end_month"], "end month")
        try_select_by_value(page, [
            'select[name*="endYear"]', 'select[name*="end_year"]', 'select[id*="endYear"]',
        ], job["end_year"], "end year")
        try_fill(page, ['input[name*="endDate"]', 'input[placeholder*="end" i]'],
                 f"{job['end_month']}/{job['end_year']}", "end date", required=False)

    # Description
    if job.get("description"):
        try_fill(page, [
            'textarea[name*="description"]',
            'textarea[name*="duties"]',
            'textarea[placeholder*="description" i]',
            'textarea[placeholder*="duties" i]',
            'textarea[placeholder*="responsibilities" i]',
        ], job["description"], "description", required=False)

    pause(page)

    # Submit
    clicked = try_click(page, [
        'button[type="submit"]',
        'button:has-text("Save")',
        'button:has-text("Add")',
        'button:has-text("Done")',
    ], "Save work experience")
    page.wait_for_load_state("networkidle")
    pause(page, 2000)
    shot(page, f"work_after_{company[:10].replace(' ', '_')}")
    return clicked


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Update Akash Poddar's Indeed profile via Google login (education + work experience)."
    )
    parser.add_argument("--section", choices=["education", "work", "all"], default="all",
                        help="Which section(s) to update (default: all)")
    args = parser.parse_args()

    print("=" * 60)
    print("Indeed Profile Updater — Akash Poddar")
    print("=" * 60)
    print(f"Account : {EMAIL}")
    print(f"Login   : Google OAuth (popup will appear)")
    print(f"Section : {args.section}")
    print()
    print("A browser window will open. When prompted, select:")
    print(f"  Google account: {EMAIL}")
    print()

    with sync_playwright() as p:
        # Always run with visible window — needed for Google OAuth popup
        browser = p.chromium.launch(headless=False, slow_mo=60)
        ctx = browser.new_context(
            viewport={"width": 1280, "height": 900},
            user_agent=(
                "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/120.0.0.0 Safari/537.36"
            ),
        )
        page = ctx.new_page()

        try:
            if not login(page):
                print("\nERROR: Login failed. Exiting.")
                sys.exit(1)

            if args.section in ("education", "all"):
                print("\n=== EDUCATION ===")
                for edu in EDUCATION:
                    add_education_entry(page, edu)

            if args.section in ("work", "all"):
                print("\n=== WORK EXPERIENCE ===")
                for job in WORK_EXPERIENCE:
                    add_work_entry(page, job)

            print("\nDone! Check screenshots in /tmp/ for confirmation.")

        finally:
            browser.close()


if __name__ == "__main__":
    main()
