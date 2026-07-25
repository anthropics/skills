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

"""A tool to query the ENCODE Portal REST API."""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
# ]
# ///

import argparse
import json

from polite_http import http_client

BASE_URL = "https://www.encodeproject.org"
_CLIENT = http_client.HttpClient(BASE_URL, qps=10)


def cmd_search(args):
  """Searches the ENCODE Portal API and saves the results.

  Args:
    args: An argparse namespace containing:
      * query: The search query string.
      * output: Optional path to save the JSON output.
  """
  query = args.query
  if not query.startswith("?"):
    query = "?" + query
  if "format=json" not in query:
    query += "&format=json"

  url = f"{BASE_URL}/search/{query}"
  print(f"[*] Querying: {url}")
  data = _CLIENT.fetch_json(url)

  print(f"[*] Found {data.get('total', 'unknown')} results.")

  # Save output
  output_path = args.output or "encode_search_output.json"
  with open(output_path, "w") as f:
    json.dump(data, f, indent=2)
  print(f"[*] Results saved to {output_path}")


def main():
  parser = argparse.ArgumentParser(description="Query ENCODE Portal API.")
  sub = parser.add_subparsers(dest="command", required=True)

  p = sub.add_parser("search", help="Search ENCODE Portal.")
  p.add_argument(
      "query", help="Query string (e.g., 'type=Experiment&target.label=ZNF549')"
  )
  p.add_argument("--output", help="Output file path")
  p.set_defaults(func=cmd_search)

  args = parser.parse_args()
  args.func(args)


if __name__ == "__main__":
  main()
