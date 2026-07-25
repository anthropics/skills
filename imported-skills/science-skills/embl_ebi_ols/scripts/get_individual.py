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

"""Retrieves individual (instance) information from the EMBL-EBI OLS.

This script fetches ontology individual details from the OLS4 API,
including their types (classes they are instances of).
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


def get_individual(args: argparse.Namespace):
  """Retrieves and outputs individual information from the EMBL-EBI OLS.

  Fetches details for a specific ontology individual (instance) based on either
  an OBO ID or a full IRI. Optionally retrieves the individual's direct types
  and all types (including ancestors) from the OLS API. The results are
  written to a specified output file or standard output.

  Args:
    args: An argparse.Namespace object containing the command-line arguments:
      * obo_id: OBO-style ID of the individual.
      * iri: Full IRI of the individual.
      * ontology: Ontology ID (required with --iri).
      * types: Whether to fetch direct types.
      * alltypes: Whether to fetch all types.
      * output: Path to the output file.
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
    ind_url = (
        f"{ols_utils.BASE_URL}/ontologies/{ontology}/individuals/{encoded_iri}"
    )
    data = ols_utils.CLIENT.fetch_json(ind_url)

    individual = {
        "iri": data.get("iri", ""),
        "label": data.get("label", ""),
        "description": data.get("description", []),
        "obo_id": data.get("obo_id", ""),
        "ontology_name": data.get("ontology_name", ""),
        "ontology_prefix": data.get("ontology_prefix", ""),
        "is_obsolete": data.get("is_obsolete", False),
        "short_form": data.get("short_form", ""),
        "synonyms": data.get("synonyms", []),
        "annotation": data.get("annotation", {}),
    }

    if args.types:
      types_url = f"{ind_url}/types"
      try:
        types_data = ols_utils.CLIENT.fetch_json(types_url)
        embedded = types_data.get("_embedded", {}).get("terms", [])
        individual["types"] = [
            {
                "iri": t.get("iri", ""),
                "label": t.get("label", ""),
                "obo_id": t.get("obo_id", ""),
            }
            for t in embedded
        ]
      except http_client.HttpError:
        individual["types"] = []

    if args.alltypes:
      alltypes_url = f"{ind_url}/alltypes"
      try:
        alltypes_data = ols_utils.CLIENT.fetch_json(alltypes_url)
        embedded = alltypes_data.get("_embedded", {}).get("properties", [])
        individual["alltypes"] = [
            {
                "iri": t.get("iri", ""),
                "label": t.get("label", ""),
                "obo_id": t.get("obo_id", ""),
            }
            for t in embedded
        ]
      except http_client.HttpError:
        individual["alltypes"] = []

    ols_utils.write_output(
        {"status": "success", "individual": individual}, args.output
    )

  except http_client.HttpError as e:
    if e.status_code == 404:
      identifier = args.obo_id or args.iri
      ols_utils.error_exit(
          f"Individual not found: {identifier}. Check the ID.", args.output
      )
    else:
      ols_utils.error_exit(f"HTTP Error {e.status_code}: {e}", args.output)


def parse_args() -> argparse.Namespace:
  """Parses command-line arguments for the script.

  Returns:
    An argparse.Namespace containing the parsed arguments.
  """
  parser = argparse.ArgumentParser(
      description="Get individual details from EMBL-EBI OLS"
  )
  group = parser.add_mutually_exclusive_group(required=True)
  group.add_argument(
      "--obo_id",
      type=str,
      help="OBO-style ID (e.g., 'IAO:0000103')",
  )
  group.add_argument(
      "--iri",
      type=str,
      help="Full IRI of the individual",
  )
  parser.add_argument(
      "--ontology",
      type=str,
      help="Ontology ID (required with --iri, auto-derived from --obo_id)",
  )
  parser.add_argument(
      "--types",
      action="store_true",
      help="Also fetch the direct types (classes) of this individual",
  )
  parser.add_argument(
      "--alltypes",
      action="store_true",
      help="Fetch all types (including ancestors) of this individual",
  )
  parser.add_argument(
      "--output", type=str, required=True, help="Output file path"
  )
  return parser.parse_args()


if __name__ == "__main__":
  main_args = parse_args()
  get_individual(main_args)
