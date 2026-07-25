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

"""Uniprot tools for accessing UniProtKB, UniParc, and UniRef."""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
# ]
# ///

from __future__ import annotations

import argparse
import gzip
import json
import re
import sys
import time
from typing import Any, Iterator
import urllib.parse

from polite_http import http_client


class UniProtError(Exception):
  """Custom exception for UniProt tool errors."""


BASE_URL = "https://rest.uniprot.org"
SPARQL_URL = "https://sparql.uniprot.org/sparql"
CLIENT = http_client.HttpClient(BASE_URL, qps=1.0)
SPARQL_CLIENT = http_client.HttpClient(SPARQL_URL, qps=1.0)


def _add_params_to_url(url: str, params: dict[str, Any] | None = None) -> str:
  """Adds URL parameters to a URL."""
  if params:
    sep = "&" if "?" in url else "?"
    url += f"{sep}{urllib.parse.urlencode(params, doseq=True)}"
  return url


def _get_header(resp: http_client.HttpResponse, header_name: str) -> str:
  """Returns the value of a given header, checking both lower and upper case."""
  return resp.headers.get(header_name) or resp.headers.get(header_name.lower())


def _get_decompressed_data(resp: http_client.HttpResponse) -> str:
  """Decompresses gzipped data from a response if necessary and decodes it."""
  data = resp.data
  # UniProt sometimes double-gzips content.
  if data.startswith(b"\x1f\x8b"):
    data = gzip.decompress(data)
  return data.decode(resp.encoding)


def _fetch(
    url: str, method="GET", headers=None, data=None, *, as_json=False
) -> dict[str, Any] | str:
  """Fetch JSON and parse, handling server double-gzipping content."""
  if not headers:
    headers = {}
  if as_json:
    headers |= {"Accept": "application/json"}
  response = CLIENT.fetch(url, headers=headers, method=method, data=data)
  decoded_data = _get_decompressed_data(response)
  if as_json:
    return json.loads(decoded_data)
  else:
    return decoded_data


def search_proteins(
    query: str,
    dataset: str = "uniprotkb",
    output_format: str = "json",
    limit: int | None = None,
    fields: list[str] | None = None,
) -> Iterator[dict[str, Any] | str]:
  """Search proteins in a UniProt dataset with automatic pagination."""
  url = f"{BASE_URL}/{dataset}/search"
  params: dict[str, Any] = {
      "query": query,
      "format": output_format,
  }
  # Determine if automatic pagination is needed
  # UniProt has a hard limit of 500 for the 'size' parameter.
  use_pagination = limit is None or limit > 500
  request_size = min(limit, 500) if limit is not None else 500
  params["size"] = request_size

  if fields:
    params["fields"] = ",".join(fields)

  if not use_pagination:

    def _single_request_iterator():
      full_url = _add_params_to_url(url, params)
      yield _fetch(full_url, as_json=(output_format == "json"))

    return _single_request_iterator()

  # Pagination logic
  def _paginate_generator():
    next_url = url
    current_params = params
    fetched_count = 0
    total_results = None
    header = None

    while next_url:
      full_url = _add_params_to_url(next_url, current_params)
      resp = CLIENT.fetch(full_url)
      if total_results is None:
        total_results = _get_header(resp, "X-Total-Results")
      data = _get_decompressed_data(resp)
      if output_format == "json":
        data = json.loads(data)

      # Extract results from this page to handle limits
      page_results = []

      if isinstance(data, dict) and "results" in data:
        page_results = data["results"]
      elif isinstance(data, str):
        if output_format == "fasta":
          # Split by '>' at the start of a line
          parts = re.split(r"(?m)^>", data)
          page_results = [">" + p for p in parts if p.strip()]
        elif output_format == "tsv":
          # UniProt includes TSV headers on each page.
          lines = data.strip().splitlines()
          if lines:
            if header is None:  # Store the header only from the first page.
              header = lines[0]
            page_results = lines[1:]
          else:
            page_results = []
        else:
          page_results = data.strip().splitlines()

      # Apply limit if necessary
      if limit is not None:
        remaining = limit - fetched_count
        if remaining <= 0:
          break
        if len(page_results) > remaining:
          page_results = page_results[:remaining]
          # This reconstruction only executes when we need to truncate results.
          #
          # No Trimming Needed: If limit is None, or if the current page results
          # fit within the remaining limit, data already contains the full page
          # content as received from the server (either as a parsed dict for
          # JSON or a raw string for FASTA/others). We can just yield it.
          #
          # Trimming Needed: We only need to reconstruct data if we had to slice
          # page_results to respect the limit. In that case, build a new data
          # object from the truncated page_results.
          #
          # TSV is the only exception (handled below) where we always
          # reconstruct the data, regardless of whether we applied a limit or
          # not. This is because we are actively modifying the content by
          # removing the header lines from subsequent pages, so we can never
          # just yield the raw server response for TSV after the first page.
          if isinstance(data, dict):
            data["results"] = page_results
          elif output_format == "fasta":
            data = "".join(page_results)
          elif output_format != "tsv":
            data = "\n".join(page_results)

      # Reconstruct TSV data to ensure headers are only on the first page
      if output_format == "tsv":
        page_data = "\n".join(page_results)
        if fetched_count == 0 and header:
          data = header + "\n" + page_data
        else:
          data = page_data

      fetched_count += len(page_results)

      if total_results:
        print(
            f"Progress: {fetched_count} / {total_results} fetched",
            file=sys.stderr,
        )
      else:
        print(f"Progress: {fetched_count} fetched", file=sys.stderr)

      yield data

      if limit is not None and fetched_count >= limit:
        break

      link_header = _get_header(resp, "Link")
      if link_header and 'rel="next"' in link_header:
        next_url = link_header.split(";")[0].strip("<>")
        current_params = None  # Params are already in the URL
      else:
        next_url = None

  return _paginate_generator()


def get_count(query: str, dataset: str = "uniprotkb") -> int:
  """Retrieve the total number of hits for a query."""
  url = f"{BASE_URL}/{dataset}/search"
  params = {"query": query, "size": 1, "format": "json"}
  resp = CLIENT.fetch(_add_params_to_url(url, params))
  return int(_get_header(resp, "X-Total-Results") or 0)


def get_entry(
    accession: str,
    dataset: str = "uniprotkb",
    output_format: str = "json",
) -> dict[str, Any] | str:
  """Retrieve a single UniProt entry."""
  url = f"{BASE_URL}/{dataset}/{accession}"
  params = {"format": output_format}
  full_url = _add_params_to_url(url, params)
  return _fetch(full_url, as_json=(output_format == "json"))


def run_id_mapping(ids: list[str], from_db: str, to_db: str) -> dict[str, Any]:
  """Execute the ID mapping workflow."""
  # 1. Submit job
  submit_url = f"{BASE_URL}/idmapping/run"
  form_dict = {
      "from": from_db,
      "to": to_db,
      "ids": ",".join(ids),
  }
  data = urllib.parse.urlencode(form_dict).encode("utf-8")
  headers = {"Content-Type": "application/x-www-form-urlencoded"}
  job_id = _fetch(
      submit_url, method="POST", headers=headers, data=data, as_json=True
  )["jobId"]

  # 2. Poll for status
  status_url = f"{BASE_URL}/idmapping/status/{job_id}"
  results_resp = None
  while True:
    status_resp = _fetch(status_url, as_json=True)
    if not isinstance(status_resp, dict):
      raise UniProtError(
          f"ID mapping job status response is not a dict: {status_resp}"
      )

    # Check if we were redirected to results (or results are in the status resp)
    if "results" in status_resp:
      results_resp = status_resp
      break

    job_status = status_resp.get("jobStatus")
    if job_status == "FINISHED":
      break
    if job_status == "FAILED":
      raise UniProtError(f"ID mapping job failed: {status_resp.get('errors')}")
    print(f"ID Mapping Job status: {job_status}")
    time.sleep(2)

  # 3. Get results (if not already fetched during status poll)
  if results_resp:
    return results_resp

  results_url = f"{BASE_URL}/idmapping/results/{job_id}"
  return _fetch(results_url, as_json=True)


def sparql_query(query: str) -> dict[str, Any]:
  """Execute a SPARQL query."""
  params = {"query": query, "format": "json"}
  return SPARQL_CLIENT.fetch_json(_add_params_to_url(SPARQL_URL, params))


def stream_results(
    query: str,
    dataset: str = "uniprotkb",
    output_format: str = "tsv",
    fields: list[str] | None = None,
) -> Iterator[str]:
  """Stream all results for a bulk query using the /stream endpoint.

  The /stream endpoint always returns the full result set (up to 10M entries).
  It does NOT support limiting the number of results. Use `search_proteins`
  with a `limit` parameter if you need a subset of results.

  Args:
    query: The search query.
    dataset: The dataset to search in.
    output_format: The output format.
    fields: The fields to retrieve.

  Yields:
    str: Each line of the result set.
  """
  url = f"{BASE_URL}/{dataset}/stream"
  params = {"query": query, "format": output_format}
  headers = {"Accept-Encoding": "identity"}
  if fields:
    params["fields"] = ",".join(fields)
  full_url = _add_params_to_url(url, params)
  fetched_count = 0
  for line in CLIENT.stream_lines(full_url, headers=headers):
    if line:
      fetched_count += 1
      if fetched_count % 1000 == 0:
        print(f"Progress: {fetched_count} lines fetched...", file=sys.stderr)
      yield line
  print(f"Total fetched lines: {fetched_count}", file=sys.stderr)


if __name__ == "__main__":
  parser = argparse.ArgumentParser(description=__doc__)
  subparsers = parser.add_subparsers(dest="command")

  # Search command
  s_parser = subparsers.add_parser("search", help="Search proteins")
  s_parser.add_argument("query", help="Query string")
  s_parser.add_argument(
      "--dataset",
      default="uniprotkb",
      help="Dataset to search in (e.g. uniprotkb, uniparc, unipref)",
  )
  s_parser.add_argument(
      "--limit", type=int, help="Total number of results to return"
  )
  s_parser.add_argument("--format", default="json")
  s_parser.add_argument("--fields")

  # Get command
  g_parser = subparsers.add_parser("get", help="Get protein entry")
  g_parser.add_argument("accession")
  g_parser.add_argument(
      "--dataset",
      default="uniprotkb",
      help="Dataset to search in (e.g. uniprotkb, uniparc, unipref)",
  )
  g_parser.add_argument("--format", default="json")

  # Map command
  m_parser = subparsers.add_parser("map", help="Map IDs")
  m_parser.add_argument("ids", help="Comma-separated IDs")
  m_parser.add_argument("--from_db", required=True)
  m_parser.add_argument("--to_db", required=True)

  # Count command
  c_parser = subparsers.add_parser("count", help="Count results for a query")
  c_parser.add_argument("query")
  c_parser.add_argument(
      "--dataset",
      default="uniprotkb",
      help="Dataset to search in (e.g. uniprotkb, uniparc, unipref)",
  )

  # SPARQL command
  sp_parser = subparsers.add_parser("sparql", help="Run SPARQL query")
  sp_parser.add_argument("query")

  # Stream command
  st_parser = subparsers.add_parser(
      "stream",
      help="Stream ALL results for a bulk query (up to 10M entries, no limit)",
  )
  st_parser.add_argument("query")
  st_parser.add_argument(
      "--dataset",
      default="uniprotkb",
      help="Dataset to search in (e.g. uniprotkb, uniparc, unipref)",
  )
  st_parser.add_argument("--format", default="tsv")
  st_parser.add_argument("--fields")

  args = parser.parse_args()

  # Validate that --format is lowercase (UniProt API requires lowercase).
  if hasattr(args, "format") and args.format != args.format.lower():
    parser.error(
        f"Invalid format '{args.format}': format must be lowercase"
        f" (e.g. 'json', 'tsv', 'fasta'). Got '{args.format}',"
        f" did you mean '{args.format.lower()}'?"
    )

  if args.command == "search":
    search_fields = args.fields.split(",") if args.fields else None
    result_iterator = search_proteins(
        args.query,
        args.dataset,
        output_format=args.format,
        limit=args.limit,
        fields=search_fields,
    )
    for page in result_iterator:
      if args.format == "json":
        print(json.dumps(page, indent=2))
      else:
        print(page)
  elif args.command == "get":
    result = get_entry(
        args.accession,
        args.dataset,
        output_format=args.format,
    )
    if args.format == "json":
      print(json.dumps(result, indent=2))
    else:
      print(result)
  elif args.command == "count":
    print(get_count(args.query, args.dataset))
  elif args.command == "map":
    print(
        json.dumps(
            run_id_mapping(
                args.ids.split(","),
                args.from_db,
                args.to_db,
            ),
            indent=2,
        )
    )
  elif args.command == "sparql":
    print(json.dumps(sparql_query(args.query), indent=2))
  elif args.command == "stream":
    stream_fields = args.fields.split(",") if args.fields else None
    for row in stream_results(
        args.query,
        args.dataset,
        output_format=args.format,
        fields=stream_fields,
    ):
      print(row)
  elif not args.command:
    parser.print_help()
