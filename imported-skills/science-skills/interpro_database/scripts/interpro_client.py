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

"""InterPro API client for fetching data with pagination and backoff."""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
# ]
# ///

from __future__ import annotations

import argparse
from collections.abc import Iterator
import json
import sys
import time
from typing import Any
import urllib.parse

from polite_http import http_client

BASE_URL = "https://www.ebi.ac.uk/interpro/api/"
DEFAULT_PAGE_SIZE = 200

CLIENT = http_client.HttpClient(BASE_URL, qps=2.0)


def build_interpro_url(
    endpoint: str,
    source_db: str | None = None,
    accession: str | None = None,
    linked_endpoint: str | None = None,
    linked_source_db: str | None = None,
    linked_accession: str | None = None,
) -> str:
  """Constructs a full InterPro API URL from an endpoint path.

  If endpoint starts with 'http', it assumes it's a full URL and returns it.
  Otherwise, it builds the canonical InterPro path:
  `/{endpoint}/{source_db}/{accession}/{linked_endpoint}/{linked_source_db}/{linked_accession}`

  Args:
      endpoint: The API endpoint (e.g., 'entry' or 'protein').
      source_db: The source database (e.g., 'interpro' or 'uniprot').
      accession: The specific accession (e.g., 'IPR0001').
      linked_endpoint: A secondary endpoint to link entities.
      linked_source_db: The database of the linked entity.
      linked_accession: The accession of the linked entity.

  Returns:
      The full URL to fetch.
  """
  if source_db and not endpoint:
    raise ValueError(
        "Invalid arguments: 'source_db' is set but 'endpoint' is missing. "
        "An 'endpoint' is required when specifying a 'source_db'."
    )
  if linked_source_db and not linked_endpoint:
    raise ValueError(
        "Invalid arguments: 'linked_source_db' is set but 'linked_endpoint' "
        "is missing. A 'linked_endpoint' is required when specifying a "
        "'linked_source_db'."
    )
  if accession and not source_db:
    raise ValueError(
        "Invalid arguments: 'accession' is set but 'source_db' is missing. "
        "A 'source_db' is required when specifying an 'accession'."
    )
  if linked_accession and not linked_source_db:
    raise ValueError(
        "Invalid arguments: 'linked_accession' is set but 'linked_source_db' "
        "is missing. A 'linked_source_db' is required when specifying a "
        "'linked_accession'."
    )

  if endpoint and endpoint.startswith("http"):
    return endpoint

  parts = [endpoint.strip("/")]

  for part in [
      source_db,
      accession,
      linked_endpoint,
      linked_source_db,
      linked_accession,
  ]:
    if part:
      parts.append(part.strip("/"))

  path = "/".join(parts)
  return urllib.parse.urljoin(BASE_URL, path)


def _safe_fetch(
    url: str, max_minutes_to_wait: int = 5
) -> dict[str, Any] | None:
  """Fetch JSON and handle HTTP 408 Background Task Timeout gracefully."""
  headers = {"Accept": "application/json"}
  retries_408 = 0
  while True:
    try:
      resp = CLIENT.fetch(url, headers=headers)
      if resp.status_code == 204:
        return None
      return resp.json()
    except http_client.HttpError as e:
      if e.status_code == 408 and retries_408 < max_minutes_to_wait:
        print("Query is running in the background. Waiting for 1 minute...")
        time.sleep(60)
        retries_408 += 1
        continue
      raise


def get_interpro_count(
    endpoint: str,
    source_db: str | None = None,
    accession: str | None = None,
    linked_endpoint: str | None = None,
    linked_source_db: str | None = None,
    linked_accession: str | None = None,
    query_params: dict[str, Any] | None = None,
    flags: list[str] | None = None,
    max_minutes_to_wait_for_background_task: int = 5,
) -> int:
  """Fetches the total count of items matching the query without downloading them.

  Args:
      endpoint: The API endpoint (e.g., 'entry' or 'protein').
      source_db: The source database (e.g., 'interpro' or 'uniprot').
      accession: The specific accession (e.g., 'IPR0001').
      linked_endpoint: A secondary endpoint to link entities.
      linked_source_db: The database of the linked entity.
      linked_accession: The accession of the linked entity.
      query_params: Optional dictionary of query string parameters.
      flags: Optional list of boolean flags.
      max_minutes_to_wait_for_background_task: Maximum minutes to wait for
        background queries (HTTP 408).

  Returns:
      The integer count of matching items.
  """
  url = build_interpro_url(
      endpoint=endpoint,
      source_db=source_db,
      accession=accession,
      linked_endpoint=linked_endpoint,
      linked_source_db=linked_source_db,
      linked_accession=linked_accession,
  )

  params_list = []
  if query_params:
    for k, v in query_params.items():
      params_list.append(f"{k}={urllib.parse.quote_plus(v)}")
  if flags:
    for flag in flags:
      params_list.append(flag)

  # Ensure page_size=1 is included, but only if not already specified.
  if not any(p.startswith("page_size=") for p in params_list):
    params_list.append("page_size=1")

  query_string = "&".join(params_list)
  full_url = f"{url}?{query_string}" if query_string else url

  data = _safe_fetch(full_url, max_minutes_to_wait_for_background_task)
  if data is None:
    return 0

  return data.get("count", 0)


def fetch_interpro_data(
    endpoint: str,
    source_db: str | None = None,
    accession: str | None = None,
    linked_endpoint: str | None = None,
    linked_source_db: str | None = None,
    linked_accession: str | None = None,
    query_params: dict[str, Any] | None = None,
    flags: list[str] | None = None,
    limit: int | None = None,
    max_minutes_to_wait_for_background_task: int = 5,
) -> Iterator[dict[str, Any]]:
  """Fetches data from the InterPro REST API.

  This function dynamically yields items as the iterator progresses, fetching
  subsequent pages only when necessary (lazy evaluation). This prevents
  downloading the entire dataset and allows you to fetch just the "first 100
  items" instantly using `itertools.islice()` or breaking early from a loop.

  Handles single-item responses and paginated list responses gracefully.
  Employs exponential back-off for HTTP 429 and 50x errors.

  Args:
      endpoint: The API endpoint (e.g., 'entry' or 'protein').
      source_db: The source database (e.g., 'interpro' or 'uniprot').
      accession: The specific accession (e.g., 'IPR0001').
      linked_endpoint: A secondary endpoint to link entities.
      linked_source_db: The database of the linked entity.
      linked_accession: The accession of the linked entity.
      query_params: Optional dictionary of query string parameters.
      flags: Optional list of boolean flags.
      limit: Optional limit on the number of items to fetch, cannot exceed
        DEFAULT_PAGE_SIZE.
      max_minutes_to_wait_for_background_task: Maximum minutes to wait for
        background queries (HTTP 408).

  Yields:
      Individual data objects (dictionaries) from the API.
  """
  current_url = build_interpro_url(
      endpoint=endpoint,
      source_db=source_db,
      accession=accession,
      linked_endpoint=linked_endpoint,
      linked_source_db=linked_source_db,
      linked_accession=linked_accession,
  )

  params_list = []
  if query_params:
    for k, v in query_params.items():
      params_list.append(f"{k}={urllib.parse.quote_plus(v)}")
  if flags:
    for flag in flags:
      params_list.append(flag)

  # Add page_size
  if not any(p.startswith("page_size=") for p in params_list):
    ps = min(limit or DEFAULT_PAGE_SIZE, DEFAULT_PAGE_SIZE)
    params_list.append(f"page_size={ps}")

  query_string = "&".join(params_list)
  if query_string:
    current_url += f"?{query_string}"

  fetched_count = 0

  while current_url:
    data = _safe_fetch(current_url, max_minutes_to_wait_for_background_task)
    if data is None:
      break

    # If the response is a paginated list
    if "results" in data and isinstance(data["results"], list):
      total_count = data.get("count")

      for item in data["results"]:
        yield item
        fetched_count += 1
        if limit is not None and fetched_count >= limit:
          return

      # Update current_url for the next iteration (lazy loading)
      current_url = data.get("next")

      # Print progress if we have to fetch another page
      if current_url:
        if limit is not None and total_count is not None:
          total_display = min(limit, total_count)
        elif limit is not None:
          total_display = limit
        elif total_count is not None:
          total_display = total_count
        else:
          total_display = "unknown"

        print(
            f"Progress: retrieved {fetched_count} / {total_display}",
            file=sys.stderr,
        )

    # Single item response
    else:
      yield data
      fetched_count += 1
      current_url = None


if __name__ == "__main__":
  parser = argparse.ArgumentParser(description="InterPro API CLI Interface")

  # Action commands
  subparsers = parser.add_subparsers(dest="command", required=True)
  fetch_parser = subparsers.add_parser(
      "fetch", help="Fetch data from InterPro API"
  )

  fetch_parser.add_argument(
      "endpoint",
      help="The primary API endpoint (e.g., 'entry', 'protein', 'structure')",
  )
  fetch_parser.add_argument(
      "--limit",
      type=int,
      help="Limit the number of results to fetch (highly recommended)",
      default=None,
  )
  fetch_parser.add_argument(
      "--output",
      required=True,
      help="Output file to write the JSON lines to",
  )

  # Optional path arguments
  fetch_parser.add_argument(
      "--source_db",
      help="Source database (e.g., 'interpro', 'pfam', 'uniprot')",
      default=None,
  )
  fetch_parser.add_argument(
      "--accession", help="Specific accession (e.g., 'IPR0001')", default=None
  )
  fetch_parser.add_argument(
      "--linked_endpoint",
      help="Secondary endpoint to link entities",
      default=None,
  )
  fetch_parser.add_argument(
      "--linked_source_db", help="Database of the linked entity", default=None
  )
  fetch_parser.add_argument(
      "--linked_accession", help="Accession of the linked entity", default=None
  )

  # Dynamic query parameters
  fetch_parser.add_argument(
      "--query_params",
      nargs="*",
      help=(
          "Query parameters as key=value pairs (e.g., tax_id=9606"
          " is_fragment=true). All parameters must include '='."
      ),
      default=None,
  )
  fetch_parser.add_argument(
      "--flags",
      nargs="*",
      help="Boolean flags (e.g., ordered exact)",
      default=None,
  )

  fetch_parser.add_argument(
      "--max_minutes_to_wait_for_background_task",
      type=int,
      help="Maximum minutes to wait for background queries (HTTP 408)",
      default=5,
  )

  count_parser = subparsers.add_parser(
      "count",
      help="Get the total count of results without downloading them",
  )
  count_parser.add_argument(
      "endpoint",
      help="The primary API endpoint (e.g., 'entry', 'protein', 'structure')",
  )
  count_parser.add_argument(
      "--output",
      required=True,
      help="Output file to write the JSON result to",
  )
  count_parser.add_argument("--source_db", help="Source database", default=None)
  count_parser.add_argument(
      "--accession", help="Specific accession", default=None
  )
  count_parser.add_argument(
      "--linked_endpoint", help="Secondary endpoint", default=None
  )
  count_parser.add_argument(
      "--linked_source_db", help="Database of the linked entity", default=None
  )
  count_parser.add_argument(
      "--linked_accession", help="Accession of the linked entity", default=None
  )
  count_parser.add_argument(
      "--query_params",
      nargs="*",
      help=(
          "Query parameters as key=value pairs. All parameters must include"
          " '='."
      ),
      default=None,
  )
  count_parser.add_argument(
      "--flags",
      nargs="*",
      help="Boolean flags (e.g., ordered exact)",
      default=None,
  )
  count_parser.add_argument(
      "--max_minutes_to_wait_for_background_task",
      type=int,
      help="Maximum minutes to wait for background queries (HTTP 408)",
      default=5,
  )

  args = parser.parse_args()

  parsed_query_params = {}
  if args.query_params:
    for param in args.query_params:
      if "=" in param:
        key, val = param.split("=", 1)
        parsed_query_params[key] = val
      else:
        print(
            f"Error: Query parameter '{param}' must be in key=value format.",
            file=sys.stderr,
        )
        sys.exit(1)

  if args.command == "fetch":
    results = fetch_interpro_data(
        endpoint=args.endpoint,
        source_db=args.source_db,
        accession=args.accession,
        linked_endpoint=args.linked_endpoint,
        linked_source_db=args.linked_source_db,
        linked_accession=args.linked_accession,
        query_params=parsed_query_params if parsed_query_params else None,
        flags=args.flags,
        limit=args.limit,
        max_minutes_to_wait_for_background_task=args.max_minutes_to_wait_for_background_task,
    )
    try:
      with open(args.output, "w") as f:
        for res in results:
          f.write(json.dumps(res) + "\n")
    except Exception as e:
      print(f"Error writing to output file {args.output}: {e}", file=sys.stderr)
      sys.exit(1)

  elif args.command == "count":
    count = get_interpro_count(
        endpoint=args.endpoint,
        source_db=args.source_db,
        accession=args.accession,
        linked_endpoint=args.linked_endpoint,
        linked_source_db=args.linked_source_db,
        linked_accession=args.linked_accession,
        query_params=parsed_query_params if parsed_query_params else None,
        flags=args.flags,
        max_minutes_to_wait_for_background_task=args.max_minutes_to_wait_for_background_task,
    )
    try:
      with open(args.output, "w") as f:
        f.write(json.dumps({"count": count}) + "\n")
    except Exception as e:
      print(f"Error writing to output file {args.output}: {e}", file=sys.stderr)
      sys.exit(1)
