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

"""Provides autocomplete suggestions from the EMBL-EBI Ontology Lookup Service.

This script queries the OLS4 suggest API for term name completions,
useful for interactive term discovery and autocomplete workflows.
"""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
# ]
# ///

import argparse
import urllib.parse
import ols_utils


def suggest_ols(args: argparse.Namespace):
  """Queries the OLS suggest API and writes the results.

  Fetches autocomplete suggestions from the EMBL-EBI OLS based on the provided
  arguments and writes the formatted output to a file or stdout. Handles
  potential API and network errors.

  Args:
    args: An argparse.Namespace object containing the command-line arguments:
      * query (str): The partial term to autocomplete.
      * ontology (str, optional): Comma-separated ontology IDs for filtering.
      * rows (int): Number of suggestions to return.
      * start (int): Pagination offset.
      * output (str, optional): Path to the output file.
  """
  params = {
      "q": args.query,
      "rows": args.rows,
      "start": args.start,
  }

  query_string = urllib.parse.urlencode(params)

  if args.ontology:
    for ont in args.ontology.split(","):
      query_string += "&ontology=" + urllib.parse.quote(ont.strip().lower())

  url = f"{ols_utils.BASE_URL}/suggest?{query_string}"

  data = ols_utils.CLIENT.fetch_json(url)

  docs = data.get("response", {}).get("docs", [])
  num_found = data.get("response", {}).get("numFound", 0)

  suggestions = []
  for doc in docs:
    suggestions.append({
        "autosuggest": doc.get("autosuggest", ""),
        "label": doc.get("label", ""),
        "ontology_name": doc.get("ontology_name", ""),
        "ontology_prefix": doc.get("ontology_prefix", ""),
        "short_form": doc.get("short_form", ""),
        "obo_id": doc.get("obo_id", ""),
    })

  ols_utils.write_output(
      {
          "status": "success",
          "total_found": num_found,
          "results_count": len(suggestions),
          "pagination": {
              "start": args.start,
              "rows": args.rows,
              "has_more": (args.start + args.rows) < num_found,
          },
          "suggestions": suggestions,
      },
      args.output,
  )


def parse_args() -> argparse.Namespace:
  """Parses command-line arguments for the OLS suggest script.

  Returns:
    An argparse.Namespace containing the parsed arguments.
  """
  parser = argparse.ArgumentParser(
      description="Get autocomplete suggestions from EMBL-EBI OLS"
  )
  parser.add_argument(
      "--query",
      type=str,
      required=True,
      help="Partial term to autocomplete (e.g., 'diabet', 'apopt')",
  )
  parser.add_argument(
      "--ontology",
      type=str,
      help="Filter by ontology ID (e.g., 'go', 'doid', 'efo'), comma-separated",
  )
  parser.add_argument(
      "--rows", type=int, default=10, help="Number of suggestions to return"
  )
  parser.add_argument("--start", type=int, default=0, help="Pagination offset")
  parser.add_argument(
      "--output", type=str, required=True, help="Output file path"
  )
  return parser.parse_args()


if __name__ == "__main__":
  main_args = parse_args()
  suggest_ols(main_args)
