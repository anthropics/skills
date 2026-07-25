"""
Universal Scraping Architect: Traditional / Local Scraping Example
==================================================================
Extracts a data table from a static HTML page using Requests and BeautifulSoup,
then validates, cleans, and saves to CSV.

Demonstrates:
  - Safe HTTP fetching with headers, timeouts, and retry logic
  - HTML table parsing with pandas
  - Column name normalisation to snake_case
  - Required field validation before saving
  - Structured error handling at every stage
  - Clean, logged output

Usage:
  pip install -r requirements.txt
  python scripts/local_bs4_example.py
"""

from __future__ import annotations  # defer annotation eval so --help works without deps

import argparse
import sys
import time
import urllib.robotparser
from datetime import datetime

# Third-party deps are imported lazily/guarded so `--help` and `--sample` work
# even when pandas/requests/bs4 aren't installed (repo smoke-test convention).
try:
    import pandas as pd
    import requests
    from bs4 import BeautifulSoup
    _DEPS_OK = True
except ImportError:
    pd = requests = BeautifulSoup = None
    _DEPS_OK = False

# =============================================================================
# CONFIG — Edit these for your task
# =============================================================================
TARGET_URL = "https://example.com/macroeconomic-indicators/energy-prices"
OUTPUT_FILE = "energy_price_data.csv"
LOG_FILE = "local_scrape_run.log"

# HTTP settings
USER_AGENT = "UniversalScrapingArchitect/1.0 (contact: your@email.com)"
TIMEOUT_SECONDS = 15
MAX_RETRIES = 3
RETRY_BASE_DELAY_SECONDS = 1     # exponential backoff: 1s, 2s, 4s, ...
RESPECT_ROBOTS = True            # Set False only for targets you know are safe to fetch

# Validation
REQUIRED_COLUMNS = ["date", "price_index", "yoy_change"]
TABLE_SELECTOR = {"id": "indicator-data"}     # Edit to match your target table's HTML attributes


# =============================================================================
# HELPERS
# =============================================================================

def log(message: str, level: str = "INFO"):
    """Prints a timestamped log line and appends it to the log file."""
    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    line = f"[{timestamp}] [{level}] {message}"
    print(line)
    with open(LOG_FILE, "a", encoding="utf-8") as f:
        f.write(line + "\n")


def check_robots(url: str) -> bool:
    """
    Courtesy robots.txt check using the stdlib (RFC 9309). Returns True if the
    fetch is allowed (or robots.txt is unreachable, which we treat as allowed
    but log). The skill mandates this — model the correct behaviour by default.
    """
    if not RESPECT_ROBOTS:
        log("robots.txt check skipped (RESPECT_ROBOTS=False).", level="WARNING")
        return True
    try:
        parts = url.split("/")
        robots_url = f"{parts[0]}//{parts[2]}/robots.txt"
        rp = urllib.robotparser.RobotFileParser()
        rp.set_url(robots_url)
        rp.read()
        allowed = rp.can_fetch(USER_AGENT, url)
        log("robots.txt allows this fetch." if allowed
            else f"robots.txt DISALLOWS fetching {url}. Aborting.",
            level="INFO" if allowed else "ERROR")
        return allowed
    except Exception as e:
        log(f"Could not read robots.txt ({e}); proceeding with caution.", level="WARNING")
        return True


def safe_get(url: str) -> str:
    """
    Fetches HTML from a URL with polite headers, a timeout, and retry logic
    using exponential backoff (RETRY_BASE_DELAY_SECONDS * 2**n).
    Raises on non-2xx status.
    """
    headers = {"User-Agent": USER_AGENT}

    for attempt in range(1, MAX_RETRIES + 1):
        try:
            log(f"Attempt {attempt}/{MAX_RETRIES}: GET {url}")
            response = requests.get(url, headers=headers, timeout=TIMEOUT_SECONDS)
            response.raise_for_status()
            log(f"HTTP {response.status_code} — content length: {len(response.text):,} chars.")
            return response.text
        except requests.exceptions.HTTPError as e:
            log(f"HTTP error on attempt {attempt}: {e}", level="ERROR")
        except requests.exceptions.ConnectionError as e:
            log(f"Connection error on attempt {attempt}: {e}", level="ERROR")
        except requests.exceptions.Timeout:
            log(f"Timeout on attempt {attempt} after {TIMEOUT_SECONDS}s.", level="WARNING")
        except requests.exceptions.RequestException as e:
            log(f"Request failed on attempt {attempt}: {e}", level="ERROR")

        if attempt < MAX_RETRIES:
            delay = RETRY_BASE_DELAY_SECONDS * (2 ** (attempt - 1))
            log(f"Waiting {delay}s before retry (exponential backoff)...")
            time.sleep(delay)

    raise RuntimeError(f"All {MAX_RETRIES} attempts failed for URL: {url}")


def find_table(html: str) -> BeautifulSoup:
    """
    Parses the HTML and returns the target table element.
    Adjust TABLE_SELECTOR to match the table you need.
    """
    soup = BeautifulSoup(html, "html.parser")
    table = soup.find("table", TABLE_SELECTOR)
    if not table:
        raise ValueError(
            f"Target table not found. Selector used: {TABLE_SELECTOR}. "
            "Inspect the page source and update TABLE_SELECTOR in CONFIG."
        )
    log("Target table found in HTML.")
    return table


def parse_table(table) -> pd.DataFrame:
    """Converts a BeautifulSoup table element into a pandas DataFrame."""
    df = pd.read_html(str(table))[0]
    log(f"Parsed table: {len(df)} rows, {len(df.columns)} columns.")
    return df


def clean_column_names(df: pd.DataFrame) -> pd.DataFrame:
    """Normalises all column names to snake_case."""
    df.columns = (
        df.columns
        .str.strip()
        .str.lower()
        .str.replace(r"\s+", "_", regex=True)
        .str.replace(r"[^\w]", "", regex=True)
    )
    log(f"Columns after normalisation: {list(df.columns)}")
    return df


def clean_data(df: pd.DataFrame) -> pd.DataFrame:
    """
    Applies general cleaning rules.
    Extend this function for your task-specific cleaning needs.
    """
    # Strip whitespace from string columns
    for col in df.select_dtypes(include="object").columns:
        df[col] = df[col].str.strip()

    # Drop fully empty rows
    before = len(df)
    df = df.dropna(how="all")
    dropped = before - len(df)
    if dropped:
        log(f"Dropped {dropped} fully empty rows.", level="WARNING")

    return df


def validate(df: pd.DataFrame) -> bool:
    """
    Checks that the DataFrame is non-empty and contains all required columns.
    Returns True if valid, False otherwise.
    """
    if df.empty:
        log("Validation failed: DataFrame is empty.", level="ERROR")
        return False

    missing = [col for col in REQUIRED_COLUMNS if col not in df.columns]
    if missing:
        log(
            f"Validation failed: missing required columns: {missing}. "
            f"Available columns: {list(df.columns)}",
            level="ERROR"
        )
        return False

    log(f"Validation passed. {len(df)} rows, {len(df.columns)} columns.")
    return True


def save_output(df: pd.DataFrame, path: str):
    """Saves the validated DataFrame to CSV."""
    df.to_csv(path, index=False, encoding="utf-8")
    log(f"Output saved to: {path}")


# =============================================================================
# MAIN
# =============================================================================

def main():
    log("=" * 60)
    log("Universal Scraping Architect — Traditional / Local Scraping")
    log("=" * 60)

    if not _DEPS_OK:
        log(
            "Missing dependencies (requests, beautifulsoup4, pandas). "
            "Install them from the skill's requirements.txt before running.",
            level="ERROR"
        )
        sys.exit(1)

    # Step 1: robots.txt courtesy check (the skill mandates this), then fetch
    if not check_robots(TARGET_URL):
        sys.exit(1)
    try:
        html = safe_get(TARGET_URL)
    except RuntimeError as e:
        log(str(e), level="ERROR")
        sys.exit(1)

    # Step 2: Find table
    try:
        table = find_table(html)
    except ValueError as e:
        log(str(e), level="ERROR")
        sys.exit(1)

    # Step 3: Parse
    try:
        df = parse_table(table)
    except Exception as e:
        log(f"Failed to parse table into DataFrame: {e}", level="ERROR")
        sys.exit(1)

    # Step 4: Clean
    df = clean_column_names(df)
    df = clean_data(df)

    # Step 5: Validate
    if not validate(df):
        sys.exit(1)

    # Step 6: Save
    save_output(df, OUTPUT_FILE)

    # Step 7: Final summary
    log("=" * 60)
    log("EXTRACTION COMPLETE")
    log(f"  Source URL   : {TARGET_URL}")
    log(f"  Output file  : {OUTPUT_FILE}")
    log(f"  Rows saved   : {len(df)}")
    log(f"  Columns      : {list(df.columns)}")
    log(f"  Log file     : {LOG_FILE}")
    log("=" * 60)
    log("Customisable: TARGET_URL, OUTPUT_FILE, TABLE_SELECTOR, REQUIRED_COLUMNS.")


def _print_sample():
    """Prints a non-network sample of what this template does (for smoke tests)."""
    print("Local BS4 example (template). Edit the CONFIG block, install deps, then run.")
    print(f"  TARGET_URL       = {TARGET_URL}")
    print(f"  OUTPUT_FILE      = {OUTPUT_FILE}")
    print(f"  TABLE_SELECTOR   = {TABLE_SELECTOR}")
    print(f"  REQUIRED_COLUMNS = {REQUIRED_COLUMNS}")
    print("  Pipeline: robots.txt -> fetch(retry+backoff) -> find table -> "
          "parse -> normalize -> clean -> validate -> save CSV")
    print(f"  Dependencies installed: {_DEPS_OK}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Local BeautifulSoup/pandas scraping example (editable runner template).")
    parser.add_argument("--sample", action="store_true", help="Print a sample summary and exit (no network).")
    args = parser.parse_args()
    if args.sample:
        _print_sample()
        sys.exit(0)
    main()
