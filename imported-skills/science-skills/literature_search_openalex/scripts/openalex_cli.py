# Copyright 2026 Google LLC
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""CLI tool for querying the OpenAlex API.

This script provides robust access to the OpenAlex REST API with automatic
pagination handling, rate limit backoffs, and error checking.
"""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
#   "python-dotenv",
# ]
# ///

from __future__ import annotations

import argparse
import json
import logging
import os
import re
import sys
from typing import Any, Sequence
import urllib.parse

import dotenv
from polite_http import http_client

logging.basicConfig(level=logging.INFO, format="%(levelname)s: %(message)s")

BASE_URL = "https://api.openalex.org"
PDF_BASE_URL = "https://content.openalex.org"

_API_CLIENT = http_client.HttpClient(
    BASE_URL,
    qps=10.0,
    referer="https://github.com/google-deepmind/science-skills/tree/main/literature-search-openalex",
)
_PDF_CLIENT = http_client.HttpClient(
    PDF_BASE_URL,
    qps=1.0,
    referer="https://github.com/google-deepmind/science-skills/tree/main/literature-search-openalex",
)


DEFAULT_PER_PAGE = 25
MAX_PER_PAGE = 100
RESOLVE_PER_PAGE = 5
DEFAULT_TIMEOUT_SECS = 30
PDF_TIMEOUT_SECS = 60
MAX_RETRIES = 5
TRUNCATE_LINE_LIMIT = 500

ENTITY_TYPES = [
    "works",
    "authors",
    "sources",
    "institutions",
    "topics",
    "domains",
    "fields",
    "subfields",
    "sdgs",
    "countries",
    "continents",
    "languages",
    "keywords",
    "publishers",
    "funders",
    "awards",
    "work-types",
    "source-types",
    "institution-types",
    "licenses",
]


def _build_url_with_api_key(url: str, api_key: str | None) -> str:
  """Appends the ``api_key`` query parameter to *url* if a key is provided.

  Callers should keep the original *url* for logging so the key does not
  leak into log messages.

  Args:
      url: The base URL, which may already contain query parameters.
      api_key: Optional API key string.

  Returns:
      The URL with ``api_key`` appended, or the original URL unchanged
      if *api_key* is ``None``.
  """
  if not api_key:
    return url
  separator = "&" if "?" in url else "?"
  return f"{url}{separator}{urllib.parse.urlencode({'api_key': api_key})}"


def fetch_with_retry(
    url: str,
    params: dict[str, Any],
    api_key: str | None = None,
    max_retries: int = MAX_RETRIES,
    exit_on_error: bool = True,
    return_headers: bool = False,
) -> dict[str, Any] | None:
  """Fetches data from the OpenAlex API with exponential backoff.

  Args:
      url: The base URL to fetch.
      params: URL query parameters.
      api_key: Optional API key for authentication.
      max_retries: Maximum number of retry attempts.
      exit_on_error: If True, exit the process on non-retriable errors.
      return_headers: If True, include response headers under a
        "_response_headers" key in the returned dict.

  Returns:
      The JSON-parsed response as a dictionary.
  """
  # Build the URL from params, then append the API key separately via the
  # shared helper.  This keeps the key out of the params dict so it cannot
  # be accidentally logged or returned to the caller.
  query_string = urllib.parse.urlencode(params, doseq=True)
  full_url = f"{url}?{query_string}" if query_string else url
  full_url = _build_url_with_api_key(full_url, api_key)

  try:
    if url.startswith(PDF_BASE_URL):
      resp = _PDF_CLIENT.fetch(full_url, max_retries=max_retries)
    elif url.startswith(BASE_URL):
      resp = _API_CLIENT.fetch(full_url, max_retries=max_retries)
    else:
      raise ValueError(f"Unsupported URL base: {url}")
    data = resp.json()
    if return_headers:
      data["_response_headers"] = resp.headers
    return data
  except http_client.HttpError as e:
    if e.status_code == 429 and not api_key:
      logging.warning(
          "Rate limit hit (429 Too Many Requests). You are currently running "
          "without an API key, which limits API usage. Please provide an API "
          "key via --api-key to increase your limit."
      )
    if e.status_code == 404:
      logging.error(
          "HTTP Error 404: Entity not found at %s. Hint: verify the ID is"
          " correct, or use the 'resolve' command to look it up by name.",
          url,
      )
    else:
      logging.error(
          "HTTP Error %s while fetching %s: %s", e.status_code, url, e
      )
    if exit_on_error:
      sys.exit(1)
    return None


def print_json(data: Any) -> None:
  """Prints JSON data.

  Truncates output if it exceeds TRUNCATE_LINE_LIMIT lines to protect context
  when printing to a terminal. If output is redirected to a file, the full data
  is printed.

  Args:
      data: The JSON-serializable Python object to print.
  """
  output = json.dumps(data, indent=2)

  if not sys.stdout.isatty():
    print(output)
    return

  lines = output.splitlines()
  if len(lines) > TRUNCATE_LINE_LIMIT:
    remaining = len(lines) - TRUNCATE_LINE_LIMIT
    print("\n".join(lines[:TRUNCATE_LINE_LIMIT]))
    logging.warning(
        "Output truncated. %d additional lines not shown. Redirect"
        " output to a file if you need the full data.",
        remaining,
    )
  else:
    print(output)


# --- Command Handlers ---


def handle_resolve(args: argparse.Namespace) -> None:
  """Searches for an entity by name and returns candidate IDs.

  Args:
      args: Parsed command-line arguments containing `entity_type`, `query`,
        `per_page`, and optional `api_key`.
  """
  # Construct search URL (e.g., https://api.openalex.org/works)
  url = f"{BASE_URL}/{args.entity_type}"
  params = {
      "search": args.query,
      "per_page": max(1, min(args.per_page, MAX_PER_PAGE)),
  }
  data = fetch_with_retry(url, params, api_key=args.api_key)
  if data is None:
    logging.error("No response received from the API.")
    sys.exit(1)

  # Extract minimal fields to make disambiguation easier for the user/agent.
  results = []
  for item in data.get("results", []):
    entry = {
        "id": item.get("id"),
        "display_name": item.get("display_name"),
        "hint": item.get("hint") or item.get("works_count"),
    }
    results.append(entry)
  print_json(results)


# Matches standard OpenAlex short IDs like W2741809807, A5023888391, etc.
_OPENALEX_SHORT_ID_RE = re.compile(r"^[A-Za-z]\d+$")


def _is_valid_entity_id(entity_id: str) -> bool:
  """Returns True if *entity_id* looks like a valid OpenAlex entity reference.

  Accepted formats:
    - Short IDs: W2741809807, A5023888391
    - Full OpenAlex URLs: https://openalex.org/W2741809807
    - DOIs: https://doi.org/10.xxx
  """
  return bool(
      _OPENALEX_SHORT_ID_RE.match(entity_id)
      or entity_id.startswith("https://openalex.org/")
      or entity_id.startswith("https://doi.org/")
  )


def handle_get(args: argparse.Namespace) -> None:
  """Retrieves complete details for a single entity by its ID.

  Args:
      args: Parsed command-line arguments containing `entity_type`, `id`,
        optional `select` (fields to return), and optional `api_key`.
  """
  if not _is_valid_entity_id(args.id):
    logging.error(
        "Invalid entity ID %r. Expected a short ID (e.g. W2741809807),"
        " a full OpenAlex URL, or a DOI URL.",
        args.id,
    )
    sys.exit(1)

  # Construct entity-specific URL (e.g., https://api.openalex.org/works/W123)
  url = f"{BASE_URL}/{args.entity_type}/{args.id}"
  params = {}

  # Add optional 'select' parameter to return only requested fields.
  if args.select is not None:
    params["select"] = args.select

  data = fetch_with_retry(url, params, api_key=args.api_key)
  print_json(data)


def _is_valid_pdf(data: bytes) -> bool:
  """Checks whether raw bytes represent a valid PDF by inspecting the header.

  PDF files must start with the magic bytes '%PDF-'. This catches common
  failure modes where a server returns an HTML error page, paywall redirect,
  or other non-PDF content with a 200 status code.

  Args:
      data: The raw bytes to validate.

  Returns:
      True if the data starts with the PDF magic bytes, False otherwise.
  """
  return data[:5] == b"%PDF-"


def _try_download_url(url: str, output_path: str) -> bool:
  """Attempts to download a PDF from a URL.

  Downloads the content and validates that it is actually a PDF by checking
  for the %PDF- magic bytes before writing to disk.

  Args:
      url: The URL to download from.
      output_path: The local file path to save to.

  Returns:
      True if a valid PDF was downloaded, False otherwise.
  """
  try:
    # Extract the base URL (scheme + netloc) for the HttpClient.
    parsed = urllib.parse.urlparse(url)
    base = f"{parsed.scheme}://{parsed.netloc}"
    client = http_client.HttpClient(base, qps=1.0)
    data = client.fetch_bytes(url, timeout=PDF_TIMEOUT_SECS)
    if not _is_valid_pdf(data):
      logging.warning(
          "Downloaded content from %s is not a valid PDF (missing %%PDF-"
          " header). Skipping.",
          url,
      )
      return False
    with open(output_path, "wb") as f:
      f.write(data)
    return True
  except http_client.HttpError as e:
    logging.warning("Failed to download from %s: %s", url, e)
    return False


def _try_fallback_locations(
    work_id: str, output_path: str, api_key: str | None
) -> bool:
  """Tries to download a PDF from alternative locations in work metadata.

  Queries the OpenAlex API for the work's metadata and attempts each location
  that has a pdf_url. If no PDF can be downloaded, logs any available landing
  pages as manual alternatives.

  Args:
      work_id: The OpenAlex work ID.
      output_path: The local file path to save the PDF to.
      api_key: Optional API key for authentication.

  Returns:
      True if a PDF was successfully downloaded, False otherwise.
  """
  logging.info("Checking alternative locations in work metadata...")
  work_url = f"{BASE_URL}/works/{work_id}"
  work_data = fetch_with_retry(
      work_url, {}, api_key=api_key, exit_on_error=False
  )
  if work_data is None:
    logging.error("Failed to fetch work metadata for %s.", work_id)
    return False

  locations = work_data.get("locations", [])
  if not locations and "best_oa_location" in work_data:
    locations = [work_data["best_oa_location"]]

  for loc in locations:
    if loc and loc.get("pdf_url"):
      logging.info("Attempting fallback download from: %s", loc["pdf_url"])
      if _try_download_url(loc["pdf_url"], output_path):
        logging.info("Successfully downloaded PDF from fallback location.")
        return True

  logging.error("No direct PDF download link found in locations.")
  landing_pages = [
      loc.get("landing_page_url")
      for loc in locations
      if loc and loc.get("landing_page_url")
  ]
  if landing_pages:
    logging.info("Alternative Landing Pages to check manually:")
    for page_url in landing_pages:
      logging.info("  - %s", page_url)
  return False


def handle_download_pdf(args: argparse.Namespace) -> None:
  """Fetches and saves the open-access PDF for a specific work.

  Tries the OpenAlex premium content server first (requires API key), then
  falls back to PDF URLs listed in the work's metadata.

  Args:
      args: Parsed command-line arguments containing `id` (the OpenAlex work
        ID), `output` (destination file path), and optional `api_key`.
  """
  # OpenAlex serves PDFs via a separate base URL (content.openalex.org)
  url = f"{PDF_BASE_URL}/works/{args.id}.pdf"

  # Build the authenticated URL in a separate variable so the API key
  # does not leak into log messages that reference ``url``.
  fetch_url = _build_url_with_api_key(url, args.api_key)

  logging.info("Downloading PDF for %s to %s", args.id, args.output)
  try:
    data = _PDF_CLIENT.fetch_bytes(fetch_url, timeout=PDF_TIMEOUT_SECS)
    if not _is_valid_pdf(data):
      logging.warning(
          "Content server returned non-PDF content (missing %%PDF- header)."
      )
    else:
      with open(args.output, "wb") as f:
        f.write(data)
      logging.info("Successfully downloaded PDF to %s", args.output)
      return
  except http_client.HttpError as e:
    if e.status_code == 401:
      logging.warning(
          "Premium content server requires an API key (HTTP 401)."
          " Trying fallback locations from work metadata..."
      )
    elif e.status_code == 404:
      logging.warning("PDF not found on OpenAlex content server (404).")
    else:
      logging.warning("Failed to download PDF from primary server: %s", e)
  except OSError as e:
    logging.warning("Network error downloading PDF: %s", e)

  # Try fallback: download from PDF URLs in the work's metadata.
  if _try_fallback_locations(args.id, args.output, args.api_key):
    return

  logging.error(
      "Could not download PDF for %s. If the work requires premium access,"
      " provide an API key via --api-key or OPENALEX_API_KEY.",
      args.id,
  )
  sys.exit(1)


def handle_filter(args: argparse.Namespace) -> None:
  """Searches and filters entities based on various criteria.

  Args:
      args: Parsed arguments defining filters (`search`, `filter`, `sort`,
        `group_by`, pagination vars, random `sample`, `seed`, `select`), and
        `api_key`.
  """
  # Warn about incompatible flag combinations before making the request.
  if args.sample is not None and args.sort is not None:
    logging.warning(
        "--sort is ignored when --sample is used. OpenAlex returns random"
        " results regardless of sort order."
    )

  url = f"{BASE_URL}/{args.entity_type}"

  # Populate provided query parameters. Exclude --sort when sampling since
  # the API ignores it and including it would be misleading.
  optional_params = [
      "search",
      "filter",
      "group_by",
      "sample",
      "seed",
      "select",
  ]
  params = {
      k: getattr(args, k)
      for k in optional_params
      if getattr(args, k) is not None
  }
  # Only include sort when NOT sampling.
  if args.sort is not None and args.sample is None:
    params["sort"] = args.sort

  # Pagination parameters are only valid if we are NOT grouping or sampling.
  # OpenAlex does not allow paging when 'group_by' or 'sample' is requested.
  if args.group_by is None and args.sample is None:
    params["per_page"] = max(1, min(args.per_page, MAX_PER_PAGE))
    params["page"] = args.page

  data = fetch_with_retry(url, params, api_key=args.api_key)
  print_json(data)


def handle_rate_limit(args: argparse.Namespace) -> None:
  """Checks the current rate limit status.

  Args:
      args: Parsed command-line arguments containing optional `api_key`.
  """
  url = f"{BASE_URL}/works"

  # Fetch a single result just to obtain the rate limit HTTP headers.
  data = fetch_with_retry(
      url, {"per_page": 1}, api_key=args.api_key, return_headers=True
  )
  if data is None:
    logging.error("Could not fetch rate limit information from the API.")
    sys.exit(1)

  # Read rate limits from standard headers injected by OpenAlex.
  headers = {k.lower(): v for k, v in data.pop("_response_headers", {}).items()}
  limit_val = headers.get("x-ratelimit-limit")
  remaining_val = headers.get("x-ratelimit-remaining")
  reset_val = headers.get("x-ratelimit-reset")

  limits = {
      "x-ratelimit-limit": limit_val,
      "x-ratelimit-remaining": remaining_val,
      "x-ratelimit-reset": reset_val,
  }

  if limit_val is None and remaining_val is None:
    logging.warning(
        "Rate limit headers were not returned by the API. This can happen"
        " when using an unauthenticated (polite pool) request. Provide an"
        " API key via --api-key or OPENALEX_API_KEY for detailed limits."
    )

  # Output the captured limits to the user.
  print_json({"rate_limits": limits})


def main(argv: Sequence[str]) -> None:
  """Main entry point for the OpenAlex CLI.

  Args:
      argv: Command line arguments, including the executable name.
  """
  dotenv.load_dotenv(os.path.expanduser("~/.env"))
  parser = argparse.ArgumentParser(description="OpenAlex API CLI Utility")

  # Global arguments applying to all subcommands.
  parser.add_argument(
      "--api-key",
      type=str,
      default=os.environ.get("OPENALEX_API_KEY"),
      help=(
          "Optional API key for higher rate limits. Without it, usage is "
          "strictly limited. If you hit rate limits frequently, please provide "
          "an API key. Defaults to the OPENALEX_API_KEY environment variable "
          "if set. An explicit --api-key flag overrides the environment "
          "variable."
      ),
  )

  # Organize commands using subparsers for clarity and isolated configurations.
  subparsers = parser.add_subparsers(dest="command", required=True)

  # Resolve Command
  parser_resolve = subparsers.add_parser(
      "resolve", help="Resolve an entity name to its OpenAlex ID"
  )
  parser_resolve.add_argument("entity_type", choices=ENTITY_TYPES)
  parser_resolve.add_argument(
      "query", help="Name or part of the name to search for"
  )
  parser_resolve.add_argument(
      "--per-page",
      type=int,
      default=RESOLVE_PER_PAGE,
      help=f"Number of candidates to return (default: {RESOLVE_PER_PAGE})",
  )
  parser_resolve.set_defaults(func=handle_resolve)

  # Get Entity Command
  parser_get = subparsers.add_parser(
      "get", help="Get a single entity by its ID"
  )
  parser_get.add_argument("entity_type", choices=ENTITY_TYPES)
  parser_get.add_argument("id", help="The OpenAlex ID (e.g., W2741809807)")
  parser_get.add_argument(
      "--select", type=str, help="Limit returned fields (e.g., id,title)"
  )
  parser_get.set_defaults(func=handle_get)

  # Download PDF Command
  parser_pdf = subparsers.add_parser(
      "download-pdf", help="Download PDF for a work (costs $0.01 per request)"
  )
  parser_pdf.add_argument("id", help="The OpenAlex Work ID (e.g., W2741809807)")
  parser_pdf.add_argument("output", help="Output file path (e.g., paper.pdf)")
  parser_pdf.set_defaults(func=handle_download_pdf)

  # Filter Command
  parser_filter = subparsers.add_parser(
      "filter", help="Filter and search entities"
  )
  parser_filter.add_argument("entity_type", choices=ENTITY_TYPES)
  parser_filter.add_argument(
      "--search", type=str, help="Full-text search query"
  )
  parser_filter.add_argument(
      "--filter", type=str, help="Filter string (e.g. is_oa:true)"
  )
  parser_filter.add_argument(
      "--sort", type=str, help="Sort string (e.g. cited_by_count:desc)"
  )
  parser_filter.add_argument(
      "--group-by", type=str, help="Group results by a field"
  )
  parser_filter.add_argument(
      "--per-page",
      type=int,
      default=DEFAULT_PER_PAGE,
      help=(
          f"Results per page (max {MAX_PER_PAGE}, default: {DEFAULT_PER_PAGE})"
      ),
  )
  parser_filter.add_argument("--page", type=int, default=1, help="Page number")
  parser_filter.add_argument(
      "--sample", type=int, help="Number of random samples to return"
  )
  parser_filter.add_argument(
      "--seed", type=int, help="Seed for random sampling"
  )
  parser_filter.add_argument(
      "--select", type=str, help="Limit returned fields (e.g., id,title)"
  )
  parser_filter.set_defaults(func=handle_filter)

  # Rate Limit Command
  parser_rate_limit = subparsers.add_parser(
      "rate-limit",
      help="Check current rate limit status",
  )
  parser_rate_limit.set_defaults(func=handle_rate_limit)

  # Parse the arguments and dispatch execution to the appropriate handle_*
  # function set as the default via .set_defaults(func=...) above.
  args = parser.parse_args(argv[1:])
  args.func(args)


if __name__ == "__main__":
  main(sys.argv)
