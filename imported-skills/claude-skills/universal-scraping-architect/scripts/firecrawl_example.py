"""
Universal Scraping Architect: Firecrawl Example (Path C — Repeatable Deliverable)
===================================================================================
Extracts clean markdown content from a target URL using the Firecrawl SDK.

Demonstrates:
  - Safe API key loading from environment
  - robots.txt courtesy check (stdlib, no extra dependency)
  - Token budget tracking before LLM processing
  - Firecrawl quota awareness logging
  - Structured error handling
  - Clean output saving with validation

This is an editable runner template: tweak the CONFIG block, then run it.
It also supports `--help` and `--sample` so it passes the repo smoke tests
without Firecrawl installed (the SDK is imported lazily inside main()).

Usage:
  export FIRECRAWL_API_KEY="fc-YOUR_KEY_HERE"     # Linux/macOS
  $env:FIRECRAWL_API_KEY = "fc-YOUR_KEY_HERE"     # Windows PowerShell
  python scripts/firecrawl_example.py
"""

import argparse
import os
import sys
import urllib.robotparser
from datetime import datetime

# =============================================================================
# CONFIG — Edit these for your task
# =============================================================================
TARGET_URL = "https://example.com/research-data"
OUTPUT_FILE = "clean_extraction.md"
LOG_FILE = "firecrawl_run.log"

# Firecrawl / Token settings
FIRECRAWL_API_KEY_ENV = "FIRECRAWL_API_KEY"
USER_AGENT = "UniversalScrapingArchitect/1.0 (contact: your@email.com)"
TOKEN_CONTEXT_LIMIT = 100_000     # Adjust to your model's context window
RESERVED_OUTPUT_TOKENS = 4_000    # Tokens held back for the model's response
RESPECT_ROBOTS = True             # Set False only for targets you know are safe to fetch


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


def check_environment() -> str:
    """Loads the Firecrawl API key from the environment. Fails fast if missing."""
    api_key = os.getenv(FIRECRAWL_API_KEY_ENV)
    if not api_key:
        log(
            f"Missing environment variable: {FIRECRAWL_API_KEY_ENV}. "
            "Set it before running this script.",
            level="ERROR"
        )
        sys.exit(1)
    log("API key loaded successfully from environment.")
    return api_key


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
        if not allowed:
            log(f"robots.txt DISALLOWS fetching {url}. Aborting.", level="ERROR")
        else:
            log("robots.txt allows this fetch.")
        return allowed
    except Exception as e:
        log(f"Could not read robots.txt ({e}); proceeding with caution.", level="WARNING")
        return True


def estimate_tokens(text: str) -> int:
    """Rough token estimate based on character count (characters / 4)."""
    return len(text) // 4


def check_token_budget(text: str) -> bool:
    """
    Estimates token usage and warns if over budget.
    Returns True if within budget, False if over.
    """
    estimated = estimate_tokens(text)
    available = TOKEN_CONTEXT_LIMIT - RESERVED_OUTPUT_TOKENS
    log(f"Token estimate: {estimated:,} / {available:,} available tokens.")
    if estimated > available:
        log(
            f"OVER TOKEN BUDGET by {estimated - available:,} tokens. "
            "Consider chunking the output before passing to an LLM.",
            level="WARNING"
        )
        return False
    log("Within token budget.")
    return True


def validate_content(content: str) -> bool:
    """Basic validation — checks the response is non-empty."""
    if not content or not content.strip():
        log("Validation failed: empty content received from Firecrawl.", level="ERROR")
        return False
    log(f"Validation passed. Content length: {len(content):,} characters.")
    return True


def save_output(content: str, path: str):
    """Saves validated content to the output path."""
    with open(path, "w", encoding="utf-8") as f:
        f.write(content)
    log(f"Output saved to: {path}")


# =============================================================================
# MAIN
# =============================================================================

def main():
    log("=" * 60)
    log("Universal Scraping Architect — Firecrawl Path C")
    log("=" * 60)

    # Step 1: Environment check
    api_key = check_environment()

    # Step 2: robots.txt courtesy check (the skill mandates this)
    if not check_robots(TARGET_URL):
        sys.exit(1)

    # Step 3: Initialise Firecrawl client (imported lazily so --help works without the SDK)
    from firecrawl import FirecrawlApp
    app = FirecrawlApp(api_key=api_key)
    log(f"Firecrawl client initialised. Target: {TARGET_URL}")

    # Step 4: Scrape
    #   Firecrawl Python SDK v1+ passes options directly: scrape_url(url, formats=[...]).
    #   Older SDKs used the params={"formats": [...]} dict wrapper.
    try:
        log("Starting scrape...")
        result = app.scrape_url(TARGET_URL, formats=["markdown"])
        # Result may be a dict (older SDK) or an object with a .markdown attribute (v1+).
        markdown_content = (
            result.get("markdown", "") if isinstance(result, dict)
            else getattr(result, "markdown", "")
        )
    except Exception as e:
        log(f"Firecrawl scrape failed: {e}", level="ERROR")
        log(
            "Tip: if this is a quota or auth error, check your FIRECRAWL_API_KEY "
            "and run `firecrawl --status` to inspect account state.",
            level="WARNING"
        )
        sys.exit(1)

    # Step 5: Validate
    if not validate_content(markdown_content):
        sys.exit(1)

    # Step 6: Token budget check
    check_token_budget(markdown_content)

    # Step 7: Save clean output
    save_output(markdown_content, OUTPUT_FILE)

    # Step 8: Final summary
    log("=" * 60)
    log("EXTRACTION COMPLETE")
    log(f"  Source URL  : {TARGET_URL}")
    log(f"  Output file : {OUTPUT_FILE}")
    log(f"  Characters  : {len(markdown_content):,}")
    log(f"  Est. tokens : {estimate_tokens(markdown_content):,}")
    log(f"  Log file    : {LOG_FILE}")
    log("=" * 60)
    log("Customisable: TARGET_URL, OUTPUT_FILE, TOKEN_CONTEXT_LIMIT, formats.")


def _print_sample():
    """Prints a non-network sample of what this template does (for smoke tests)."""
    print("Firecrawl example (template). Edit the CONFIG block, set FIRECRAWL_API_KEY, then run.")
    print(f"  TARGET_URL          = {TARGET_URL}")
    print(f"  OUTPUT_FILE         = {OUTPUT_FILE}")
    print(f"  TOKEN_CONTEXT_LIMIT = {TOKEN_CONTEXT_LIMIT}")
    print("  Pipeline: env-check -> robots.txt -> scrape -> validate -> token-budget -> save")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Firecrawl extraction example (editable runner template).")
    parser.add_argument("--sample", action="store_true", help="Print a sample summary and exit (no network).")
    args = parser.parse_args()
    if args.sample:
        _print_sample()
        sys.exit(0)
    main()
