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

"""Searches PDB using the RCSB Search API v2.

This script allows executing structured queries against the PDB Search API
with tunable pagination, return types, and sorting.
"""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
# ]
# ///

import argparse
import json
import sys
import urllib.parse

from polite_http import http_client

CLIENT = http_client.HttpClient("https://search.rcsb.org", qps=2.0)


def search_pdb(args: argparse.Namespace):
  """Executes a search against the PDB Search API.

  Args:
    args: parsed command line arguments containing the query and options.
  """
  try:
    parsed_query = json.loads(args.query)
  except json.JSONDecodeError as e:
    print(f"Error parsing --query as JSON: {e}", file=sys.stderr)
    sys.exit(1)

  if isinstance(parsed_query, dict) and "query" in parsed_query:
    # Payload already contains "query" key, it's a full request payload
    payload = parsed_query
  else:
    # Only "query" block provided
    payload = {"query": parsed_query}

  if args.return_type is not None:
    payload["return_type"] = args.return_type

  request_options = payload.get("request_options", {})

  if args.count_only:
    # Count-only mode: request 0 rows, just get total_count from response
    request_options["paginate"] = {"start": 0, "rows": 0}
    # Remove return_all_hits if present, since we don't want all results
    request_options.pop("return_all_hits", None)
  elif args.page_start is not None or args.rows is not None:
    # Remove return_all_hits so CLI pagination flags are not silently ignored.
    request_options.pop("return_all_hits", None)
    paginate = request_options.get("paginate", {})
    if args.page_start is not None:
      paginate["start"] = args.page_start
    if args.rows is not None:
      paginate["rows"] = args.rows
    request_options["paginate"] = paginate
  else:
    # Default behavior: return all hits if no pagination is specified
    request_options["return_all_hits"] = True

  if args.sort_by is not None:
    sort_item = {"sort_by": args.sort_by}
    if args.sort_direction is not None:
      sort_item["direction"] = args.sort_direction
    request_options["sort"] = [sort_item]

  if request_options:
    payload["request_options"] = request_options

  json_payload = json.dumps(payload, separators=(",", ":"))
  encoded_query = urllib.parse.quote(json_payload)
  url = f"https://search.rcsb.org/rcsbsearch/v2/query?json={encoded_query}"

  print(f"Querying PDB Search API from {url}...", file=sys.stderr)

  content = CLIENT.fetch_bytes(url)
  if args.count_only:
    # Parse the response to extract just the total count
    response_data = json.loads(content.decode("utf-8"))
    total_count = response_data.get("total_count", 0)
    count_result = {"total_count": total_count}
    print(f"Total count: {total_count}", file=sys.stderr)
    with open(args.output, "w") as f:
      json.dump(count_result, f, indent=2)
  else:
    with open(args.output, "w") as f:
      f.write(content.decode("utf-8"))


def parse_args() -> argparse.Namespace:
  """Parse command line arguments."""
  parser = argparse.ArgumentParser(
      description="Search PDB using the RCSB Search API v2"
  )
  parser.add_argument(
      "--query",
      type=str,
      required=True,
      help="JSON string of the query object or full request payload",
  )
  parser.add_argument(
      "--return_type",
      type=str,
      required=True,
      choices=[
          "entry",
          "assembly",
          "polymer_entity",
          "non_polymer_entity",
          "polymer_instance",
          "mol_definition",
      ],
      help=(
          "Type of returned object."
          "entry = [PDB ID]"
          "assembly = [PDB ID]-[ASSEMBLY ID]"
          "polymer_entity = [PDB ID]-[ENTITY ID]"
          "non_polymer_entity = [PDB ID]-[ENTITY ID]"
          "polymer_instance = [PDB ID].[LABEL ASYM ID]"
          "mol_definition = [CHEMICAL COMP ID] or [BIRD ID]"
      ),
  )
  parser.add_argument(
      "--sort_by",
      type=str,
      help=(
          "Attribute to sort by (commonly score or "
          "rcsb_accession_info.initial_release_date)"
      ),
  )
  parser.add_argument(
      "--sort_direction",
      type=str,
      choices=["asc", "desc"],
      help="Sort direction (used with --sort_by)",
  )
  parser.add_argument(
      "--page_start",
      type=int,
      help="Start index for pagination",
  )
  parser.add_argument(
      "--rows",
      type=int,
      help="Number of rows to return",
  )
  parser.add_argument(
      "--count-only",
      action="store_true",
      help=(
          "Return only the total count of matching entries, not the full"
          " result list. Useful when you need to know how many results match"
          " without downloading them all."
      ),
  )
  parser.add_argument(
      "--output",
      type=str,
      required=True,
      help="File to write the output to",
  )

  return parser.parse_args()


if __name__ == "__main__":
  main_args = parse_args()
  search_pdb(main_args)
