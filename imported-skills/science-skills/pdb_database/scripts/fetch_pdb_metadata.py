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

"""Gets PDB data using the RCSB Data API (GraphQL)."""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
# ]
# ///

import argparse
import sys
import urllib.parse

from polite_http import http_client

CLIENT = http_client.HttpClient("https://data.rcsb.org", qps=2.0)


def get_pdb_metadata(args: argparse.Namespace):
  """Executes a GraphQL query against the PDB Data API.

  Args:
    args: parsed command line arguments containing the query.
  """
  encoded_query = urllib.parse.quote(args.query.strip())
  url = f"https://data.rcsb.org/graphql?query={encoded_query}"
  print(f"Querying PDB Data API from {url}...", file=sys.stderr)

  content = CLIENT.fetch_bytes(url)
  with open(args.output, "w") as f:
    f.write(content.decode("utf-8"))


def parse_args() -> argparse.Namespace:
  """Parse command line arguments."""
  parser = argparse.ArgumentParser(
      description="Get PDB data using the RCSB Data API (GraphQL)"
  )
  parser.add_argument(
      "--query",
      type=str,
      required=True,
      help="GraphQL query string",
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
  get_pdb_metadata(main_args)
