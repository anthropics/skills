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

"""Retrieves ontology information from the EMBL-EBI Ontology Lookup Service.

This script lists available ontologies or fetches details for a specific
ontology from the OLS4 API.
"""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
# ]
# ///

import argparse
import ols_utils
from polite_http import http_client


def get_ontology(args: argparse.Namespace):
  """Fetches and outputs ontology information based on provided arguments.

  If args.id is provided, it fetches details for that specific ontology.
  Otherwise, it lists available ontologies with pagination. The output is
  written to a file or stdout as JSON.

  Args:
    args: An argparse.Namespace containing the command-line arguments, including
      'id', 'page', 'size', and 'output'.
  """
  try:
    if args.id:
      url = f"{ols_utils.BASE_URL}/ontologies/{args.id.lower()}"
      data = ols_utils.CLIENT.fetch_json(url)

      config = data.get("config", {})
      ontology = {
          "ontologyId": data.get("ontologyId", ""),
          "title": config.get("title", ""),
          "description": config.get("description", ""),
          "namespace": config.get("namespace", ""),
          "homepage": config.get("homepage", ""),
          "numberOfTerms": data.get("numberOfTerms", 0),
          "numberOfProperties": data.get("numberOfProperties", 0),
          "numberOfIndividuals": data.get("numberOfIndividuals", 0),
          "status": data.get("status", ""),
          "loaded": data.get("loaded", ""),
          "updated": data.get("updated", ""),
      }

      ols_utils.write_output(
          {"status": "success", "ontology": ontology}, args.output
      )
    else:
      url = f"{ols_utils.BASE_URL}/ontologies?page={args.page}&size={args.size}"
      data = ols_utils.CLIENT.fetch_json(url)

      embedded = data.get("_embedded", {}).get("ontologies", [])
      page_info = data.get("page", {})

      ontologies = []
      for ont in embedded:
        config = ont.get("config", {})
        ontologies.append({
            "ontologyId": ont.get("ontologyId", ""),
            "title": config.get("title", ""),
            "description": config.get("description", ""),
            "numberOfTerms": ont.get("numberOfTerms", 0),
            "status": ont.get("status", ""),
        })

      ols_utils.write_output(
          {
              "status": "success",
              "total_ontologies": page_info.get("totalElements", 0),
              "page": page_info.get("number", 0),
              "total_pages": page_info.get("totalPages", 0),
              "results_count": len(ontologies),
              "ontologies": ontologies,
          },
          args.output,
      )

  except http_client.HttpError as e:
    if e.status_code == 404:
      ols_utils.error_exit(
          f"Ontology not found: '{args.id}'. "
          "Use --id without arguments to list available ontologies.",
          args.output,
      )
    else:
      ols_utils.error_exit(f"HTTP Error {e.status_code}: {e}", args.output)


def parse_args() -> argparse.Namespace:
  """Parses command-line arguments for the ontology script.

  Returns:
    An argparse.Namespace containing the parsed arguments.
  """
  parser = argparse.ArgumentParser(
      description="Get ontology information from EMBL-EBI OLS"
  )
  parser.add_argument(
      "--id",
      type=str,
      help="Ontology ID (e.g., 'go', 'efo', 'doid'). If omitted, lists all.",
  )
  parser.add_argument(
      "--page", type=int, default=0, help="Page number for pagination"
  )
  parser.add_argument(
      "--size", type=int, default=20, help="Number of ontologies per page"
  )
  parser.add_argument(
      "--output", type=str, required=True, help="Output file path"
  )
  return parser.parse_args()


if __name__ == "__main__":
  main_args = parse_args()
  get_ontology(main_args)
