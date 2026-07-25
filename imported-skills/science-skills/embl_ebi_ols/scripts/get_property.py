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

"""Retrieves property information from the EMBL-EBI Ontology Lookup Service.

This script fetches ontology property details, including hierarchy
(parents, children, ancestors, descendants) and root properties.
"""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
# ]
# ///

import argparse
import sys
import ols_utils
from polite_http import http_client


def get_roots(args: argparse.Namespace):
  """Fetches and outputs the root properties for a given ontology.

  Args:
    args: An argparse.Namespace object containing the command-line arguments.
      Requires `args.ontology` to be set. The output is written based on
      `args.output`.
  """
  if not args.ontology:
    ols_utils.error_exit("--ontology is required with --roots", args.output)

  ontology = args.ontology.lower()
  url = f"{ols_utils.BASE_URL}/ontologies/{ontology}/properties/roots"

  try:
    data = ols_utils.CLIENT.fetch_json(url)
    embedded = data.get("_embedded", {}).get("properties", [])
    props = [
        {
            "iri": p.get("iri", ""),
            "label": p.get("label", ""),
            "obo_id": p.get("obo_id", ""),
            "short_form": p.get("short_form", ""),
            "has_children": p.get("has_children", False),
        }
        for p in embedded
    ]
    ols_utils.write_output(
        {
            "status": "success",
            "ontology": ontology,
            "type": "property_roots",
            "results_count": len(props),
            "properties": props,
        },
        args.output,
    )
  except http_client.HttpError as e:
    ols_utils.error_exit(f"HTTP Error {e.status_code}: {e}", args.output)


def get_property(args: argparse.Namespace):
  """Fetches and outputs details for a specific ontology property.

  Retrieves information about a property identified by either an OBO ID or IRI,
  including optional related properties like parents, children, ancestors, and
  descendants. The output is written based on `args.output`.

  Args:
    args: An argparse.Namespace object containing the command-line arguments.
      Requires either `args.obo_id` or `args.iri` to be set. If `args.iri` is
      used, `args.ontology` must also be provided. `args.relations` can specify
      which related properties to fetch.
  """
  try:
    if args.obo_id:
      ontology = ols_utils.resolve_ontology(args.obo_id, args.ontology)
      iri = ols_utils.obo_id_to_iri(args.obo_id)
    else:
      if not args.ontology:
        ols_utils.error_exit(
            "--ontology is required when using --iri", args.output
        )
      ontology = args.ontology.lower()
      iri = args.iri

    encoded_iri = ols_utils.double_encode_iri(iri)
    prop_url = (
        f"{ols_utils.BASE_URL}/ontologies/{ontology}/properties/{encoded_iri}"
    )

    data = ols_utils.CLIENT.fetch_json(prop_url)

    prop = {
        "iri": data.get("iri", ""),
        "label": data.get("label", ""),
        "description": data.get("description", []),
        "obo_id": data.get("obo_id", ""),
        "ontology_name": data.get("ontology_name", ""),
        "ontology_prefix": data.get("ontology_prefix", ""),
        "is_obsolete": data.get("is_obsolete", False),
        "has_children": data.get("has_children", False),
        "is_root": data.get("is_root", False),
        "short_form": data.get("short_form", ""),
        "synonyms": data.get("synonyms", []),
        "annotation": data.get("annotation", {}),
    }

    if args.relations:
      valid = {"parents", "children", "ancestors", "descendants"}
      requested = [r.strip().lower() for r in args.relations.split(",")]
      links = data.get("_links", {})
      for rel in requested:
        if rel not in valid:
          print(f"Warning: Skipping unknown relation '{rel}'", file=sys.stderr)
          continue
        rel_url = links.get(rel, {}).get("href")
        if not rel_url:
          rel_url = f"{ols_utils.BASE_URL}/ontologies/{ontology}/properties/{encoded_iri}/{rel}"
        try:
          rel_data = ols_utils.CLIENT.fetch_json(rel_url)
          embedded = rel_data.get("_embedded", {}).get("properties", [])
          prop[rel] = [
              {
                  "iri": p.get("iri", ""),
                  "label": p.get("label", ""),
                  "obo_id": p.get("obo_id", ""),
              }
              for p in embedded
          ]
        except http_client.HttpError:
          prop[rel] = []

    ols_utils.write_output({"status": "success", "property": prop}, args.output)

  except http_client.HttpError as e:
    if e.status_code == 404:
      identifier = args.obo_id or args.iri
      ols_utils.error_exit(
          f"Property not found: {identifier}. Check the ID.", args.output
      )
    else:
      ols_utils.error_exit(f"HTTP Error {e.status_code}: {e}", args.output)


def parse_args() -> argparse.Namespace:
  """Parses command-line arguments for the script.

  Returns:
    An argparse.Namespace containing the parsed arguments.
  """
  parser = argparse.ArgumentParser(
      description="Get property details from EMBL-EBI OLS"
  )
  group = parser.add_mutually_exclusive_group()
  group.add_argument(
      "--obo_id",
      type=str,
      help="OBO-style ID of the property (e.g., 'BFO:0000051')",
  )
  group.add_argument(
      "--iri",
      type=str,
      help="Full IRI of the property",
  )
  parser.add_argument(
      "--ontology",
      type=str,
      help="Ontology ID (required with --iri, auto-derived from --obo_id)",
  )
  parser.add_argument(
      "--relations",
      type=str,
      help="Comma-separated: parents, children, ancestors, descendants",
  )
  parser.add_argument(
      "--roots",
      action="store_true",
      help="List root properties of the ontology (requires --ontology)",
  )
  parser.add_argument(
      "--output", type=str, required=True, help="Output file path"
  )
  return parser.parse_args()


if __name__ == "__main__":
  main_args = parse_args()
  if main_args.roots:
    get_roots(main_args)
  elif not main_args.obo_id and not main_args.iri:
    ols_utils.error_exit("Must provide --obo_id, --iri, or --roots", None)
  else:
    get_property(main_args)
