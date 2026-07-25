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

"""A command-line tool for querying the QuickGO API.

This script provides subcommands to interact with various QuickGO API endpoints,
including searching for GO terms, ECO terms, annotations, and gene products.
Results are saved to a specified JSON file.
"""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
# ]
# ///

import argparse
import json
from typing import Any
import urllib.parse

from polite_http import http_client

BASE_URL = "https://www.ebi.ac.uk/QuickGO/services"
_CLIENT = http_client.HttpClient(BASE_URL, qps=10)


def make_request(path: str, params: dict[str, Any] | None = None) -> Any:
  """Makes a GET request to the QuickGO API.

  Args:
      path: The API endpoint path (e.g., "/ontology/go/search").
      params: Optional dictionary of query parameters.

  Returns:
      The JSON response from the API.
  """
  url = f"{BASE_URL}{path}"
  if params:
    url = f"{url}?{urllib.parse.urlencode(params, doseq=True)}"
  return _CLIENT.fetch_json(url)


def save_output(data: Any, filename: str):
  with open(filename, "w") as f:
    json.dump(data, f, indent=2)
  print(f"Successfully wrote results to {filename}")


def go_search(args: argparse.Namespace):
  limit = min(args.limit, 100) if args.limit else 25
  data = make_request(
      "/ontology/go/search",
      params={"query": args.query, "limit": limit, "page": args.page},
  )
  save_output(data, args.output)


def go_terms(args: argparse.Namespace):
  path = f"/ontology/go/terms/{args.ids}"
  if args.relation:
    path += f"/{args.relation}"
  if args.target_ids:
    path += f"/{args.target_ids}"
  data = make_request(path)
  save_output(data, args.output)


def go_slim(args: argparse.Namespace):
  params = {"slimsToIds": args.slimsToIds}
  if args.slimsFromIds:
    params["slimsFromIds"] = args.slimsFromIds
  if args.relations:
    params["relations"] = args.relations
  data = make_request("/ontology/go/slim", params=params)
  save_output(data, args.output)


def eco_search(args: argparse.Namespace):
  limit = min(args.limit, 100) if args.limit else 25
  data = make_request(
      "/ontology/eco/search",
      params={"query": args.query, "limit": limit, "page": args.page},
  )
  save_output(data, args.output)


def eco_terms(args: argparse.Namespace):
  path = f"/ontology/eco/terms/{args.ids}"
  if args.relation:
    path += f"/{args.relation}"
  data = make_request(path)
  save_output(data, args.output)


def annotation_search(args: argparse.Namespace):
  """Searches for annotations using the QuickGO API.

  Args:
      args: An argparse namespace containing the command-line arguments.
        Expected arguments include geneProductId, geneProductSubset,
        geneProductType, goId, taxonId, evidenceCode, goUsage, qualifier, limit,
        page, aspect, and output.
  """
  params = {}
  if args.geneProductId:
    params["geneProductId"] = args.geneProductId
  if args.geneProductSubset:
    params["geneProductSubset"] = args.geneProductSubset
  if args.geneProductType:
    params["geneProductType"] = args.geneProductType
  if args.goId:
    params["goId"] = args.goId
  if args.taxonId:
    params["taxonId"] = args.taxonId
  if args.evidenceCode:
    params["evidenceCode"] = args.evidenceCode
  if args.goUsage:
    params["goUsage"] = args.goUsage
  if args.qualifier:
    params["qualifier"] = args.qualifier
  if args.aspect:
    params["aspect"] = args.aspect
  if args.limit:
    params["limit"] = min(args.limit, 100)
  if args.page:
    params["page"] = args.page

  data = make_request("/annotation/search", params=params)
  save_output(data, args.output)


def geneproduct_search(args: argparse.Namespace):
  """Searches for gene products using the QuickGO API.

  Args:
      args: An argparse namespace containing the command-line arguments.
        Expected arguments include query, taxonId, limit, page, and output.
  """
  params = {}
  if args.query:
    params["query"] = args.query
  if args.taxonId:
    params["taxonId"] = args.taxonId
  if args.limit:
    params["limit"] = min(args.limit, 100)
  if args.page:
    params["page"] = args.page

  data = make_request("/geneproduct/search", params=params)
  save_output(data, args.output)


def main():
  parser = argparse.ArgumentParser(description="QuickGO API CLI Wrapper")
  subparsers = parser.add_subparsers(dest="command", required=True)

  # GO Subcommands
  go_parser = subparsers.add_parser("go", help="Gene Ontology endpoints")
  go_sub = go_parser.add_subparsers(dest="go_cmd", required=True)

  go_search_p = go_sub.add_parser("search", help="Search GO terms by text")
  go_search_p.add_argument(
      "--query", required=True, help="Text query (e.g. 'apoptosis')"
  )
  go_search_p.add_argument(
      "--limit", type=int, default=25, help="Max results per page (max 100)"
  )
  go_search_p.add_argument("--page", type=int, default=1, help="Page number")
  go_search_p.add_argument("--output", required=True, help="Output JSON file")
  go_search_p.set_defaults(func=go_search)

  go_terms_p = go_sub.add_parser("terms", help="Get GO term details")
  go_terms_p.add_argument("--ids", required=True, help="Comma-separated GO IDs")
  go_terms_p.add_argument(
      "--relation",
      choices=["ancestors", "descendants", "children", "complete", "paths"],
      help="Relationship type",
  )
  go_terms_p.add_argument(
      "--target_ids", help="Target IDs (only used with 'paths' relation)"
  )
  go_terms_p.add_argument("--output", required=True, help="Output JSON file")
  go_terms_p.set_defaults(func=go_terms)

  go_slim_p = go_sub.add_parser("slim", help="Calculate GO Slims")
  go_slim_p.add_argument("--slimsToIds", required=True, help="Target slim IDs")
  go_slim_p.add_argument("--slimsFromIds", help="Source IDs")
  go_slim_p.add_argument("--relations", help="Comma-separated relations")
  go_slim_p.add_argument("--output", required=True, help="Output JSON file")
  go_slim_p.set_defaults(func=go_slim)

  # ECO Subcommands
  eco_parser = subparsers.add_parser(
      "eco", help="Evidence & Conclusion Ontology"
  )
  eco_sub = eco_parser.add_subparsers(dest="eco_cmd", required=True)

  eco_search_p = eco_sub.add_parser("search", help="Search ECO terms by text")
  eco_search_p.add_argument("--query", required=True)
  eco_search_p.add_argument(
      "--limit", type=int, default=25, help="Max results per page (max 100)"
  )
  eco_search_p.add_argument("--page", type=int, default=1, help="Page number")
  eco_search_p.add_argument("--output", required=True)
  eco_search_p.set_defaults(func=eco_search)

  eco_terms_p = eco_sub.add_parser("terms", help="Get ECO term details")
  eco_terms_p.add_argument("--ids", required=True)
  eco_terms_p.add_argument(
      "--relation",
      choices=["ancestors", "descendants", "children", "complete", "paths"],
  )
  eco_terms_p.add_argument("--output", required=True)
  eco_terms_p.set_defaults(func=eco_terms)

  # Annotation Subcommands
  ann_parser = subparsers.add_parser(
      "annotation", help="Annotation search endpoints"
  )
  ann_sub = ann_parser.add_subparsers(dest="ann_cmd", required=True)

  ann_search_p = ann_sub.add_parser("search", help="Search annotations")
  ann_search_p.add_argument(
      "--geneProductId", help="Gene product ID (e.g. UniProtKB:P04637)"
  )
  ann_search_p.add_argument(
      "--geneProductSubset", help="Gene product subset (e.g. Swiss-Prot)"
  )
  ann_search_p.add_argument(
      "--geneProductType", help="Gene product type (e.g. protein)"
  )
  ann_search_p.add_argument("--goId", help="GO ID (e.g. GO:0006915)")
  ann_search_p.add_argument(
      "--taxonId", type=int, help="NCBI Taxon ID (e.g. 9606 for human)"
  )
  ann_search_p.add_argument(
      "--evidenceCode", help="Evidence code (e.g. ECO:0000269 for EXP)"
  )
  ann_search_p.add_argument(
      "--goUsage", choices=["exact", "slim", "desc"], help="How to use goId"
  )
  ann_search_p.add_argument(
      "--qualifier", help="Qualifier (e.g. enables, part_of, involved_in)"
  )
  ann_search_p.add_argument(
      "--aspect",
      choices=[
          "biological_process",
          "molecular_function",
          "cellular_component",
      ],
      help="GO aspect",
  )
  ann_search_p.add_argument(
      "--limit", type=int, default=25, help="Max results per page (max 100)"
  )
  ann_search_p.add_argument("--page", type=int, default=1, help="Page number")
  ann_search_p.add_argument("--output", required=True, help="Output JSON file")
  ann_search_p.set_defaults(func=annotation_search)

  # Gene Product Subcommands
  gp_parser = subparsers.add_parser(
      "geneproduct", help="Gene Product search endpoints"
  )
  gp_sub = gp_parser.add_subparsers(dest="gp_cmd", required=True)

  gp_search_p = gp_sub.add_parser("search", help="Search gene products")
  gp_search_p.add_argument(
      "--query", required=True, help="Query string (e.g. PROC)"
  )
  gp_search_p.add_argument(
      "--taxonId", type=int, help="NCBI Taxon ID (e.g. 9606 for human)"
  )
  gp_search_p.add_argument(
      "--limit", type=int, default=25, help="Max results per page (max 100)"
  )
  gp_search_p.add_argument("--page", type=int, default=1, help="Page number")
  gp_search_p.add_argument("--output", required=True, help="Output JSON file")
  gp_search_p.set_defaults(func=geneproduct_search)

  args = parser.parse_args()
  args.func(args)


if __name__ == "__main__":
  main()
