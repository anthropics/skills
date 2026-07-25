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

"""Queries the openFDA API and returns results in clean JSON format.

This script provides a CLI for searching, counting, and downloading data from
all 28 openFDA API endpoints across 8 categories: drug, device, food, tobacco,
other, animalandveterinary, cosmetic, and transparency.
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
import os
import sys
from typing import Any

import dotenv
from polite_http import http_client

BASE_URL = "https://api.fda.gov"
CLIENT = http_client.HttpClient(BASE_URL, qps=4.0)

VALID_ENDPOINTS = {
    "drug": [
        "event",
        "label",
        "ndc",
        "enforcement",
        "drugsfda",
        "shortages",
    ],
    "device": [
        "510k",
        "classification",
        "enforcement",
        "event",
        "pma",
        "recall",
        "registrationlisting",
        "udi",
        "covid19serology",
    ],
    "food": ["enforcement", "event"],
    "tobacco": [
        "problem",
        "researchpreventionads",
        "researchdigitalads",
        "researchsmokefree",
    ],
    "other": ["historicaldocument", "nsde", "substance", "unii"],
    "animalandveterinary": ["event"],
    "cosmetic": ["event"],
    "transparency": ["crl"],
}

ALL_RESULTS_SAFETY_CAP = 25000


def _warn_no_api_key(api_key: str | None) -> None:
  key = api_key or os.environ.get("FDA_API_KEY")
  if not key:
    print(
        "WARNING: No API key provided. This API has much lower rate limits"
        " without a key. Get one at https://open.fda.gov/apis/authentication/"
        " and pass via --api_key or the FDA_API_KEY environment variable.",
        file=sys.stderr,
    )


def _write_output(data: dict[str, Any], output_path: str) -> None:
  out_dir = os.path.dirname(output_path)
  if out_dir:
    os.makedirs(out_dir, exist_ok=True)

  if isinstance(data, dict):
    data["_license_notice"] = (
        "Data provided by openFDA. Please review the licensing terms at"
        " https://open.fda.gov/license/"
    )

  with open(output_path, "w") as f:
    json.dump(data, f, indent=2)


def _print_json(data: dict[str, Any]) -> None:
  """Prints a dictionary as indented JSON to stdout."""
  print(json.dumps(data, indent=2))


def _validate_endpoint(category: str, endpoint: str) -> bool:
  if category not in VALID_ENDPOINTS:
    return False
  return endpoint in VALID_ENDPOINTS[category]


def _print_endpoint_error(category: str, endpoint: str) -> None:
  """Prints an error message for an invalid endpoint and exits.

  The error message includes the valid endpoints for the given category.

  Args:
    category: The API category provided.
    endpoint: The invalid API endpoint provided.
  """
  valid = ", ".join(VALID_ENDPOINTS.get(category, []))
  _print_json({
      "status": "error",
      "message": (
          f"Invalid endpoint '{endpoint}' for category "
          f"'{category}'. Valid endpoints: {valid}"
      ),
  })
  sys.exit(1)


def _build_url(
    *,
    category: str,
    endpoint: str,
    search: str | None = None,
    sort: str | None = None,
    limit: int = 10,
    skip: int = 0,
    count_field: str | None = None,
    api_key: str | None = None,
) -> str:
  """Builds the openFDA API URL with the given parameters.

  Args:
    category: The API category (e.g., "drug").
    endpoint: The API endpoint within the category (e.g., "event").
    search: Optional search query string.
    sort: Optional sort field and order string.
    limit: The maximum number of results per request.
    skip: The number of records to skip for pagination.
    count_field: Optional field to count unique values for.
    api_key: Optional API key.

  Returns:
    A string representing the constructed URL.
  """
  url = f"{BASE_URL}/{category}/{endpoint}.json?"
  params = []

  key = api_key or os.environ.get("FDA_API_KEY")
  if key:
    params.append(f"api_key={key}")
  if search:
    params.append(f"search={search}")
  if sort:
    params.append(f"sort={sort}")
  if count_field:
    params.append(f"count={count_field}")
  else:
    params.append(f"limit={limit}")
    params.append(f"skip={skip}")

  return url + "&".join(params)


def _fetch(url: str) -> dict[str, Any]:
  """Fetches JSON data from the given URL and handles errors."""

  try:
    return CLIENT.fetch_json(url)
  except http_client.HttpError as e:
    if e.status_code == 429:
      return {
          "status": "error",
          "http_code": 429,
          "message": (
              "Rate limit exceeded (HTTP 429). You have hit the openFDA request"
              " limit. Without an API key the limit is 240 requests/min and"
              " 1,000/day. With a free API key the daily limit increases to"
              " 120,000. Register at: https://open.fda.gov/apis/authentication/"
          ),
      }
    if e.status_code is not None:
      body = ""
      if e.body:
        body = e.body.decode("utf-8", errors="replace")
      try:
        error_json = json.loads(body)
        return {"status": "error", "http_code": e.status_code, **error_json}
      except (json.JSONDecodeError, ValueError):
        return {
            "status": "error",
            "http_code": e.status_code,
            "message": f"HTTP {e.status_code}: {str(e)}",
            "body": body[:500],
        }
    return {"status": "error", "message": f"Network error: {str(e)}"}


def cmd_search(args: argparse.Namespace) -> None:
  """Searches the openFDA API and writes the results to a file.

  Constructs a search URL based on the provided arguments, fetches the data,
  and writes the JSON response to the file specified by --output. Also prints
  a summary of the operation to stdout.

  Args:
    args: An argparse.Namespace object containing the command-line arguments,
      including category, endpoint, search, sort, limit, skip, api_key, and
      output.
  """
  if not _validate_endpoint(args.category, args.endpoint):
    _print_endpoint_error(args.category, args.endpoint)

  _warn_no_api_key(args.api_key)

  url = _build_url(
      category=args.category,
      endpoint=args.endpoint,
      search=args.search,
      sort=args.sort,
      limit=args.limit,
      skip=args.skip,
      api_key=args.api_key,
  )
  result = _fetch(url)
  _write_output(result, args.output)

  total = result.get("meta", {}).get("results", {}).get("total", "?")
  count = len(result.get("results", []))
  _print_json({
      "status": "success",
      "output": args.output,
      "results_in_file": count,
      "total_matching": total,
  })


def cmd_count(args: argparse.Namespace) -> None:
  """Counts unique values for a specified field using the openFDA API.

  Fetches counts of unique terms for a given field based on the provided
  search criteria. Optionally, it can return only a summary of the top N
  most frequent terms. The results are written to the file specified by
  --output.

  Args:
    args: An argparse.Namespace object containing the command-line arguments,
      including category, endpoint, search, count_field, summary, and output.
  """
  if not _validate_endpoint(args.category, args.endpoint):
    _print_endpoint_error(args.category, args.endpoint)

  _warn_no_api_key(args.api_key)

  url = _build_url(
      category=args.category,
      endpoint=args.endpoint,
      search=args.search,
      sort=args.sort,
      count_field=args.count_field,
      api_key=args.api_key,
  )
  result = _fetch(url)

  if args.summary and "results" in result:
    result["results"] = result["results"][: args.summary]

  _write_output(result, args.output)

  entries = len(result.get("results", []))
  top_terms = []
  for r in result.get("results", [])[:5]:
    top_terms.append({"term": r.get("term"), "count": r.get("count")})
  _print_json({
      "status": "success",
      "output": args.output,
      "entries": entries,
      "top_terms": top_terms,
  })


def cmd_download(args: argparse.Namespace) -> None:
  """Downloads multiple pages of openFDA results and writes them to a file.

  Fetches results from the specified openFDA endpoint, handling pagination
  based on --max_pages or --all_results. The fetched records are
  accumulated and written as a single JSON object to the file specified
  by --output.

  Args:
    args: An argparse.Namespace object containing the command-line arguments.
  """
  if not _validate_endpoint(args.category, args.endpoint):
    _print_endpoint_error(args.category, args.endpoint)

  _warn_no_api_key(args.api_key)

  all_results = []
  skip = args.skip
  limit = args.limit

  if args.all_results:
    max_records = ALL_RESULTS_SAFETY_CAP
    limit = min(limit, 1000) if limit else 1000
    max_pages = max_records // limit + 1
    print(
        f"Fetching all results (safety cap: {max_records} records)...",
        file=sys.stderr,
    )
  else:
    max_pages = args.max_pages
    max_records = max_pages * limit

  for page in range(max_pages):
    url = _build_url(
        category=args.category,
        endpoint=args.endpoint,
        search=args.search,
        sort=args.sort,
        limit=limit,
        skip=skip,
        api_key=args.api_key,
    )
    result = _fetch(url)

    if result.get("status") == "error" or "error" in result:
      print(json.dumps(result, indent=2), file=sys.stderr)
      break

    results = result.get("results", [])
    if not results:
      break

    all_results.extend(results)
    meta = result.get("meta", {}).get("results", {})
    total = meta.get("total", 0)

    print(
        f"Page {page + 1}: fetched {len(results)} records "
        f"({len(all_results)}/{total} total)",
        file=sys.stderr,
    )

    skip += limit
    if skip >= total or len(all_results) >= max_records:
      break

  output_data = {
      "status": "success",
      "results_count": len(all_results),
      "results": all_results,
  }
  _write_output(output_data, args.output)

  _print_json({
      "status": "success",
      "message": f"Downloaded {len(all_results)} records to {args.output}",
  })


def parse_args() -> argparse.Namespace:
  """Parses command-line arguments for the openFDA query script.

  Defines subparsers for 'search', 'count', and 'download' commands,
  along with common arguments like category, endpoint, search, sort,
  limit, skip, api_key, and output.

  Returns:
      argparse.Namespace: The parsed command-line arguments.
  """
  parser = argparse.ArgumentParser(
      description="Query the openFDA API (all 28 endpoints)"
  )
  subparsers = parser.add_subparsers(dest="command", required=True)

  common = argparse.ArgumentParser(add_help=False)
  common.add_argument(
      "--category",
      type=str,
      required=True,
      choices=sorted(VALID_ENDPOINTS.keys()),
      help="API category (e.g. drug, device, food)",
  )
  common.add_argument(
      "--endpoint",
      type=str,
      required=True,
      help="API endpoint within the category (e.g. event, label, 510k)",
  )
  common.add_argument(
      "--search",
      type=str,
      default=None,
      help="Search query (e.g. 'patient.drug.medicinalproduct:aspirin')",
  )
  common.add_argument(
      "--sort",
      type=str,
      default=None,
      help="Sort field:order (e.g. 'receivedate:desc')",
  )
  common.add_argument(
      "--limit",
      type=int,
      default=10,
      help="Max results per request (default 10, max 1000)",
  )
  common.add_argument(
      "--skip",
      type=int,
      default=0,
      help="Pagination offset (default 0)",
  )
  common.add_argument(
      "--api_key",
      type=str,
      default=None,
      help="API key (also reads FDA_API_KEY env var)",
  )
  common.add_argument(
      "--output",
      type=str,
      required=True,
      help="Output file path for results JSON (required)",
  )

  subparsers.add_parser(
      "search",
      parents=[common],
      help="Search an endpoint and save JSON results to --output",
  )

  count_parser = subparsers.add_parser(
      "count",
      parents=[common],
      help="Count unique field values and save to --output",
  )
  count_parser.add_argument(
      "--count_field",
      type=str,
      required=True,
      help="Field to count on (e.g. 'patient.reaction.reactionmeddrapt.exact')",
  )
  count_parser.add_argument(
      "--summary",
      type=int,
      default=None,
      metavar="N",
      help="Return only the top N most frequent terms (e.g. --summary 10)",
  )

  download_parser = subparsers.add_parser(
      "download",
      parents=[common],
      help="Download multiple pages of results to --output",
  )
  download_parser.add_argument(
      "--max_pages",
      type=int,
      default=10,
      help="Max pages to fetch (default 10)",
  )
  download_parser.add_argument(
      "--all_results",
      action="store_true",
      default=False,
      help=(
          "Fetch all matching results (auto-paginate). "
          f"Safety cap: {ALL_RESULTS_SAFETY_CAP} records."
      ),
  )

  return parser.parse_args()


def main():
  dotenv.load_dotenv(os.path.expanduser("~/.env"))
  main_args = parse_args()
  if main_args.command == "search":
    cmd_search(main_args)
  elif main_args.command == "count":
    cmd_count(main_args)
  elif main_args.command == "download":
    cmd_download(main_args)


if __name__ == "__main__":
  main()
