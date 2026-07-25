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

"""Fetch specific bioRxiv/medRxiv metadata by DOI."""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
# ]
# ///

import argparse
import json
import sys
from polite_http import http_client

_CLIENT = http_client.HttpClient(base_url="https://api.biorxiv.org/", qps=1.0)


def search_by_doi(args):
  """Retrieves metadata for a single paper identified by its DOI."""
  # Clean up DOI string if a URL was accidentally passed
  doi = args.doi.replace("https://doi.org/", "").replace("http://doi.org/", "")
  url = f"https://api.biorxiv.org/details/{args.server}/{doi}"
  data = _CLIENT.fetch_json(url)

  collection = data.get("collection", [])
  if not collection:
    sys.exit(f"Error: No paper found for DOI '{doi}' on {args.server}.")

  paper = collection[0]
  if not args.include_abstracts:
    paper.pop("abstract", None)
  print(json.dumps(paper, indent=2))


def main():
  """Parses arguments and fetches metadata by DOI."""
  parser = argparse.ArgumentParser(
      description="Fetch specific bioRxiv/medRxiv metadata by DOI."
  )
  parser.add_argument(
      "--server",
      choices=["biorxiv", "medrxiv"],
      default="biorxiv",
      help="The preprint server to query.",
  )
  parser.add_argument("--doi", required=True, help="The DOI of the paper")
  parser.add_argument(
      "--include_abstracts",
      action="store_true",
      help="Include full abstracts in the JSON output",
  )

  args = parser.parse_args()
  search_by_doi(args)


if __name__ == "__main__":
  main()
