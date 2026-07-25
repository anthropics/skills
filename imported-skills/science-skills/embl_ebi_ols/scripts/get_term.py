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

"""Retrieves detailed information for a specific ontology term from OLS.

This script fetches term details from the EMBL-EBI Ontology Lookup Service
using either an OBO ID (e.g., GO:0005634) or a full IRI. It can also retrieve
hierarchical relations (parents, children, ancestors, descendants), including
hierarchical variants that follow transitive relations like 'part of'.
Additionally, it can list root terms or preferred root terms of an ontology.

Relation types:
  Direct (is-a only):
    parents, children, ancestors, descendants
  Hierarchical (is-a + transitive relations like 'part of', 'develops from'):
    hierarchicalParents, hierarchicalChildren,
    hierarchicalAncestors, hierarchicalDescendants
  Graph:
    graph — returns the full graph JSON for a term
"""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
# ]
# ///

import argparse
import sys
from typing import Any
import ols_utils
from polite_http import http_client

VALID_RELATIONS = {
    "parents",
    "children",
    "ancestors",
    "descendants",
    "hierarchicalParents",
    "hierarchicalChildren",
    "hierarchicalAncestors",
    "hierarchicalDescendants",
    "graph",
}


def format_summary(term: dict[str, Any]) -> str:
  """Formats a term dictionary into a human-readable summary string.

  Args:
    term: A dictionary containing term details fetched from OLS.

  Returns:
    A string containing a formatted summary of the term.
  """
  lines = []
  lines.append(f"Label:      {term.get('label', 'N/A')}")
  lines.append(f"OBO ID:     {term.get('obo_id', 'N/A')}")
  lines.append(f"Ontology:   {term.get('ontology_name', 'N/A')}")
  lines.append(f"IRI:        {term.get('iri', 'N/A')}")

  desc = term.get("description", [])
  if desc:
    lines.append(f"Definition: {desc[0]}")

  synonyms = term.get("synonyms", [])
  if synonyms:
    lines.append(f"Synonyms:   {', '.join(synonyms)}")

  lines.append(f"Obsolete:   {term.get('is_obsolete', False)}")
  lines.append(f"Has children: {term.get('has_children', False)}")
  lines.append(f"Is root:    {term.get('is_root', False)}")

  for rel in VALID_RELATIONS - {"graph"}:
    if rel in term:
      labels = [t.get("label", t.get("obo_id", "?")) for t in term[rel]]
      lines.append(f"{rel}: {', '.join(labels)}")

  return "\n".join(lines)


def get_roots(args: argparse.Namespace):
  """Fetches and outputs root terms for a specified ontology.

  Retrieves either all root terms or preferred root terms from the OLS
  for the ontology provided in `args.ontology`. The results are written
  to the file specified by `args.output` or to stdout.

  Args:
    args: An argparse.Namespace containing the parsed command-line arguments,
      including 'ontology', 'preferred_roots', and 'output'.
  """
  if not args.ontology:
    ols_utils.error_exit("--ontology is required with --roots", args.output)

  ontology = args.ontology.lower()
  if args.preferred_roots:
    url = f"{ols_utils.BASE_URL}/ontologies/{ontology}/terms/preferredRoots"
  else:
    url = f"{ols_utils.BASE_URL}/ontologies/{ontology}/terms/roots"

  try:
    data = ols_utils.CLIENT.fetch_json(url)
    embedded = data.get("_embedded", {}).get("terms", [])
    terms = [
        {
            "iri": t.get("iri", ""),
            "label": t.get("label", ""),
            "obo_id": t.get("obo_id", ""),
            "short_form": t.get("short_form", ""),
            "has_children": t.get("has_children", False),
        }
        for t in embedded
    ]
    ols_utils.write_output(
        {
            "status": "success",
            "ontology": ontology,
            "type": "preferred_roots" if args.preferred_roots else "roots",
            "results_count": len(terms),
            "terms": terms,
        },
        args.output,
    )
  except http_client.HttpError as e:
    ols_utils.error_exit(f"HTTP Error {e.status_code}: {e}", args.output)


def get_term(args: argparse.Namespace):
  """Fetches and outputs detailed information for a specific ontology term.

  Retrieves term details from the OLS based on either an OBO ID or an IRI.
  Optionally fetches related terms (parents, children, etc.) and can output
  a human-readable summary or the full JSON. The results are written
  to the file specified by `args.output` or to stdout.

  Args:
    args: An argparse.Namespace containing the parsed command-line arguments,
      including 'obo_id', 'iri', 'ontology', 'relations', 'summary', and
      'output'.
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
    term_url = f"{ols_utils.BASE_URL}/ontologies/{ontology}/terms/{encoded_iri}"

    data = ols_utils.CLIENT.fetch_json(term_url)

    term = {
        "iri": data.get("iri", ""),
        "label": data.get("label", ""),
        "description": data.get("description", []),
        "obo_id": data.get("obo_id", ""),
        "ontology_name": data.get("ontology_name", ""),
        "ontology_prefix": data.get("ontology_prefix", ""),
        "is_defining_ontology": data.get("is_defining_ontology", False),
        "is_obsolete": data.get("is_obsolete", False),
        "has_children": data.get("has_children", False),
        "is_root": data.get("is_root", False),
        "short_form": data.get("short_form", ""),
        "synonyms": data.get("synonyms", []),
        "annotation": data.get("annotation", {}),
        "in_subset": data.get("in_subset", []),
    }

    if args.relations:
      requested = [r.strip() for r in args.relations.split(",")]
      links = data.get("_links", {})
      for rel in requested:
        if rel not in VALID_RELATIONS:
          print(
              f"Warning: Skipping unknown relation '{rel}'",
              file=sys.stderr,
          )
          continue

        if rel == "graph":
          graph_url = links.get("graph", {}).get("href")
          if not graph_url:
            graph_url = f"{ols_utils.BASE_URL}/ontologies/{ontology}/terms/{encoded_iri}/graph"
          graph_data = ols_utils.CLIENT.fetch_json(graph_url)
          term["graph"] = graph_data
          continue

        rel_url = links.get(rel, {}).get("href")
        if not rel_url:
          rel_url = f"{ols_utils.BASE_URL}/ontologies/{ontology}/terms/{encoded_iri}/{rel}"
        try:
          term[rel] = []
          while rel_url:
            # API returns http links but client expects https to match base_url
            rel_url = rel_url.replace("http://", "https://")
            rel_data = ols_utils.CLIENT.fetch_json(rel_url)
            embedded = rel_data.get("_embedded", {}).get("terms", [])
            term[rel].extend([
                {
                    "iri": t.get("iri", ""),
                    "label": t.get("label", ""),
                    "obo_id": t.get("obo_id", ""),
                }
                for t in embedded
            ])
            rel_url = rel_data.get("_links", {}).get("next", {}).get("href")
        except http_client.HttpError:
          term[rel] = []

    result = {"status": "success", "term": term}

    if args.summary:
      print(format_summary(term))
      if args.output:
        ols_utils.write_output(result, args.output)
    else:
      ols_utils.write_output(result, args.output)

  except http_client.HttpError as e:
    if e.status_code == 404:
      identifier = args.obo_id or args.iri
      ols_utils.error_exit(
          f"Term not found: {identifier}. Check the ID.", args.output
      )
    else:
      ols_utils.error_exit(f"HTTP Error {e.status_code}: {e}", args.output)


def parse_args() -> argparse.Namespace:
  """Parses command-line arguments for the get_term script.

  Returns:
    An argparse.Namespace containing the parsed arguments.
  """
  parser = argparse.ArgumentParser(
      description="Get term details from EMBL-EBI OLS"
  )
  group = parser.add_mutually_exclusive_group()
  group.add_argument(
      "--obo_id",
      type=str,
      help="OBO-style ID (e.g., 'GO:0005634', 'DOID:9351')",
  )
  group.add_argument(
      "--iri",
      type=str,
      help="Full IRI of the term",
  )
  parser.add_argument(
      "--ontology",
      type=str,
      help="Ontology ID (auto-derived from --obo_id if not provided)",
  )
  parser.add_argument(
      "--relations",
      type=str,
      help=(
          "Comma-separated relations to fetch. "
          "Direct (is-a only): parents, children, ancestors, descendants. "
          "Hierarchical (is-a + transitive like 'part of', 'develops from'): "
          "hierarchicalParents, hierarchicalChildren, "
          "hierarchicalAncestors, hierarchicalDescendants. "
          "Also: graph"
      ),
  )
  parser.add_argument(
      "--roots",
      action="store_true",
      help="List root terms of the ontology (requires --ontology)",
  )
  parser.add_argument(
      "--preferred_roots",
      action="store_true",
      help="List preferred root terms of the ontology (requires --ontology)",
  )
  parser.add_argument(
      "--summary",
      action="store_true",
      help=(
          "Output a clean human-readable summary to stdout. "
          "If --output is also specified, the full JSON is saved to that file."
      ),
  )
  parser.add_argument(
      "--output", type=str, required=True, help="Output file path"
  )
  return parser.parse_args()


if __name__ == "__main__":
  main_args = parse_args()
  if main_args.roots or main_args.preferred_roots:
    get_roots(main_args)
  elif not main_args.obo_id and not main_args.iri:
    ols_utils.error_exit(
        "Must provide --obo_id, --iri, --roots, or --preferred_roots",
        main_args.output,
    )
  else:
    get_term(main_args)
