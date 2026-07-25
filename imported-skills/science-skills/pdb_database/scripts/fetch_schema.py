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

"""Fetches JSON PDB schemas and saves a greppable list of properties."""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
# ]
# ///

import argparse
from typing import Any

from polite_http import http_client

SEARCH_CLIENT = http_client.HttpClient("https://search.rcsb.org", qps=2.0)
DATA_CLIENT = http_client.HttpClient("https://data.rcsb.org", qps=2.0)

# Mapping of API types to their corresponding schema URLs
API_URLS = {
    "search_structure": "https://search.rcsb.org/rcsbsearch/v2/metadata/schema",
    "search_chemical": (
        "https://search.rcsb.org/rcsbsearch/v2/metadata/chemical/schema"
    ),
    "data_entry": "https://data.rcsb.org/rest/v1/schema/entry",
    "data_polymer_entity": (
        "https://data.rcsb.org/rest/v1/schema/polymer_entity"
    ),
    "data_polymer_entity_instance": (
        "https://data.rcsb.org/rest/v1/schema/polymer_entity_instance"
    ),
    "data_assembly": "https://data.rcsb.org/rest/v1/schema/assembly",
    "data_non_polymer_entity": (
        "https://data.rcsb.org/rest/v1/schema/nonpolymer_entity"
    ),
    "data_non_polymer_entity_instance": (
        "https://data.rcsb.org/rest/v1/schema/nonpolymer_entity_instance"
    ),
    "data_branched_entity_instance": (
        "https://data.rcsb.org/rest/v1/schema/branched_entity_instance"
    ),
    "data_branched_entity": (
        "https://data.rcsb.org/rest/v1/schema/branched_entity"
    ),
    "data_chemical_component": "https://data.rcsb.org/rest/v1/schema/chem_comp",
}


def _collect_definitions(
    schema: dict[str, Any], prefix: str, config: argparse.Namespace
) -> set[str]:
  """Traverses a composite schema node and collects property definitions."""
  results = set()
  if "anyOf" in schema:
    for sub in schema["anyOf"]:
      results |= _collect_definitions(sub, prefix, config)
  if "oneOf" in schema:
    for sub in schema["oneOf"]:
      results |= _collect_definitions(sub, prefix, config)
  if "allOf" in schema:
    for sub in schema["allOf"]:
      results |= _collect_definitions(sub, prefix, config)

  type_val = schema.get("type")

  # Handle implicit object type if 'properties' is present
  if type_val == "object" or "properties" in schema:
    props = schema.get("properties", {})
    for key, val in props.items():
      full_name = f"{prefix}.{key}" if prefix else key
      results |= _process_property_node(val, full_name, config)

  # Handle implicit array type if 'items' is present
  elif type_val == "array" or "items" in schema:
    items = schema.get("items")
    if items:
      # Prefix doesn't include array_name.items, so no prefix update
      results |= _collect_definitions(items, prefix, config)

  return results


def _process_property_node(
    node: dict[str, Any], full_name: str, config: argparse.Namespace
) -> set[str]:
  """Processes an individual schema node and collects property definitions."""
  results = set()

  # Handle composite types first
  if "anyOf" in node:
    for sub in node["anyOf"]:
      results |= _process_property_node(sub, full_name, config)
  if "oneOf" in node:
    for sub in node["oneOf"]:
      results |= _process_property_node(sub, full_name, config)
  if "allOf" in node:
    for sub in node["allOf"]:
      results |= _process_property_node(sub, full_name, config)

  type_val = node.get("type")

  # Normalize type to list
  types = []
  if isinstance(type_val, list):
    types = type_val
  elif type_val:
    types = [type_val]

  is_object = "object" in types or "properties" in node
  is_array = "array" in types or "items" in node

  # Check if it has any primitive aspect
  # A property is primitive if it has a type that is NOT object or array
  has_primitive = False
  for t in types:
    if t not in ["object", "array"]:
      has_primitive = True

  # For arrays of primitives, metadata might be stored in 'items'
  meta_node = node
  if is_array and "items" in node and isinstance(node["items"], dict):
    if "rcsb_search_context" in node["items"] or "description" in node["items"]:
      meta_node = node["items"]

  # Output logic
  should_output = False
  if config.searchable_only:
    if "rcsb_search_context" in meta_node or "rcsb_search_context" in node:
      should_output = True
  else:
    if "description" in meta_node or has_primitive:
      should_output = True

  if should_output:
    description = (
        meta_node.get("description", node.get("description", ""))
        .replace("\n", " ")
        .strip()
    )

    # Truncate description if requested
    if (
        config.truncate_description > 0
        and len(description) > config.truncate_description
    ):
      description = description[: config.truncate_description] + "..."

    enum_values = meta_node.get("enum", node.get("enum"))
    enum_str = ""
    if enum_values:
      # Make a copy to avoid modifying original if we truncate
      vals = list(enum_values)
      if config.truncate_enums > 0 and len(vals) > config.truncate_enums:
        # Keep first N items and append "..."
        vals = vals[: config.truncate_enums] + ["..."]
      enum_str = f" {vals}"

    prop_type = node.get("type", "")
    if is_array and not prop_type:
      prop_type = "array"
    results.add(f"{full_name} ({prop_type}): {description}{enum_str}")

  # Recurse if it has object/array structure
  if is_object or is_array:
    results |= _collect_definitions(node, full_name, config)

  return results


def main():
  parser = argparse.ArgumentParser(
      description="Fetch JSON Schema and save a greppable list of properties."
  )
  parser.add_argument(
      "--api",
      type=str,
      choices=list(API_URLS.keys()),
      help="Api to use. Options: " + ",".join(list(API_URLS.keys())),
  )
  parser.add_argument(
      "--truncate-description",
      type=int,
      default=100,
      help=(
          "Number of characters to truncate description to (default: 100). Set"
          " to 0 to disable."
      ),
  )
  parser.add_argument(
      "--truncate-enums",
      type=int,
      default=0,
      help="Number of enum items to truncate to (default: 0 = no truncation).",
  )
  parser.add_argument(
      "--output",
      type=str,
      required=True,
      help="File to write the schema to.",
  )

  args = parser.parse_args()
  if "search" in args.api:
    args.searchable_only = True
  else:
    args.searchable_only = False

  if args.api:
    url = API_URLS[args.api]
    client = DATA_CLIENT if args.api.startswith("data_") else SEARCH_CLIENT
    print(f"Fetching schema from {url}...")
    try:
      data = client.fetch_json(url, timeout=30)
    except http_client.HttpError as e:
      print(f"Error fetching data from URL: {e}")
      return
  else:
    print("Error: No API type specified.")
    return

  # Start traversal
  results = _collect_definitions(schema=data, prefix="", config=args)

  # Sort and write
  sorted_lines = sorted(results)

  with open(args.output, "w") as f:
    for line in sorted_lines:
      f.write(line + "\n")

  print(
      f"Processed {len(sorted_lines)} properties. Output written to"
      f" {args.output}"
  )


if __name__ == "__main__":
  main()
