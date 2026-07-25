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

"""Searches the EMBL-EBI Ontology Lookup Service and returns results as JSON.

This script queries the OLS4 search API for ontology terms matching a keyword.
It parses the JSON response and outputs structured results.
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


def search_ols(args: argparse.Namespace):
  """Searches the OLS API with the given arguments and writes the results.

  Constructs a query URL from the provided argparse namespace, fetches the
  JSON response from the OLS search API, and parses the results. The results
  are then written to a file or stdout in JSON format.

  Args:
    args: An argparse.Namespace object containing the command-line arguments.
  """
  params = {
      "q": args.query,
      "rows": args.rows,
      "start": args.start,
  }
  if args.ontology:
    params["ontology"] = args.ontology.lower()
  if args.type:
    params["type"] = args.type
  if args.exact:
    params["exact"] = "true"
  if not args.obsolete:
    params["obsoletes"] = "false"
  if args.local:
    params["local"] = "true"
  if args.defining:
    params["is_defining_ontology"] = "true"
  if args.groupField:
    params["groupField"] = args.groupField
  if args.isLeaf:
    params["isLeaf"] = "true"
  if args.queryFields:
    params["queryFields"] = args.queryFields
  if args.fieldList:
    params["fieldList"] = args.fieldList

  query_string = urllib.parse.urlencode(params)

  if args.childrenOf:
    for iri in args.childrenOf.split(","):
      query_string += "&childrenOf=" + urllib.parse.quote(iri.strip())
  if args.allChildrenOf:
    for iri in args.allChildrenOf.split(","):
      query_string += "&allChildrenOf=" + urllib.parse.quote(iri.strip())

  url = f"{ols_utils.BASE_URL}/search?{query_string}"

  data = ols_utils.CLIENT.fetch_json(url)

  docs = data.get("response", {}).get("docs", [])
  num_found = data.get("response", {}).get("numFound", 0)

  results = []
  for doc in docs:
    term = {
        "iri": doc.get("iri", ""),
        "label": doc.get("label", ""),
        "description": doc.get("description", []),
        "ontology_name": doc.get("ontology_name", ""),
        "ontology_prefix": doc.get("ontology_prefix", ""),
        "obo_id": doc.get("obo_id", ""),
        "short_form": doc.get("short_form", ""),
        "type": doc.get("type", ""),
        "is_defining_ontology": doc.get("is_defining_ontology", False),
        "exact_synonyms": doc.get("exact_synonyms", []),
    }
    results.append(term)

  ols_utils.write_output(
      {
          "status": "success",
          "total_found": num_found,
          "results_count": len(results),
          "pagination": {
              "start": args.start,
              "rows": args.rows,
              "has_more": (args.start + args.rows) < num_found,
          },
          "terms": results,
      },
      args.output,
  )


def parse_args() -> argparse.Namespace:
  """Parses command-line arguments for the OLS search script.

  Returns:
    An argparse.Namespace object containing the parsed arguments.
  """
  parser = argparse.ArgumentParser(
      description="Search EMBL-EBI OLS for ontology terms"
  )
  parser.add_argument(
      "--query",
      type=str,
      required=True,
      help="Search query string (e.g., 'diabetes', 'apoptosis')",
  )
  parser.add_argument(
      "--ontology",
      type=str,
      help="Filter by ontology ID (e.g., 'go', 'doid', 'efo')",
  )
  parser.add_argument(
      "--type",
      type=str,
      choices=["class", "property", "individual", "ontology"],
      help="Filter by entity type",
  )
  parser.add_argument(
      "--exact",
      action="store_true",
      help=(
          "Only return exact label matches. Use this for entity resolution "
          "when mapping a user string to a specific ontology term ID."
      ),
  )
  parser.add_argument(
      "--defining",
      action="store_true",
      help=(
          "Only return terms from their defining (authoritative) ontology. "
          "E.g., GO:0005634 only from GO, not cross-referenced copies."
      ),
  )
  parser.add_argument(
      "--obsolete",
      action="store_true",
      help="Include obsolete terms in results",
  )
  parser.add_argument(
      "--local",
      action="store_true",
      help=(
          "Only return terms in their defining ontology (e.g., GO terms only"
          " from GO, not from ontologies that reference them)"
      ),
  )
  parser.add_argument(
      "--childrenOf",
      type=str,
      help="Restrict to children of given term IRI(s), comma-separated",
  )
  parser.add_argument(
      "--allChildrenOf",
      type=str,
      help=(
          "Restrict to all children of given term IRI(s), comma-separated "
          "(includes transitive relations like 'part of', 'develops from')"
      ),
  )
  parser.add_argument(
      "--queryFields",
      type=str,
      help=(
          "Comma-separated fields to search in "
          "(default: label,synonym,description,short_form,obo_id,annotations,"
          "logical_description,iri)"
      ),
  )
  parser.add_argument(
      "--fieldList",
      type=str,
      help=(
          "Comma-separated fields to return "
          "(default: iri,label,short_form,obo_id,ontology_name,ontology_prefix,"
          "description,type)"
      ),
  )
  parser.add_argument(
      "--groupField",
      type=str,
      help="Group results by unique id (IRI)",
  )
  parser.add_argument(
      "--isLeaf",
      action="store_true",
      help="Only return leaf terms (terms with no children)",
  )
  parser.add_argument(
      "--rows", type=int, default=10, help="Number of results to return"
  )
  parser.add_argument("--start", type=int, default=0, help="Pagination offset")
  parser.add_argument(
      "--output", type=str, required=True, help="Output file path"
  )
  return parser.parse_args()


if __name__ == "__main__":
  main_args = parse_args()
  search_ols(main_args)
