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

"""PubChem API CLI.

This script provides command-line access to various PubChem API endpoints,
including resolving chemical names, fetching properties, synonyms, safety data,
pharmacology, images, and performing similarity/substructure searches.
"""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
# ]
# ///

import argparse
import json
import sys
import urllib.parse

from polite_http import http_client

PUBCHEM_BASE_URL = "https://pubchem.ncbi.nlm.nih.gov/rest"
_CLIENT = http_client.HttpClient(PUBCHEM_BASE_URL, qps=5)


def make_request(url):
  """Makes an HTTP GET request via http_client."""
  try:
    resp = _CLIENT.fetch(url)
    content_type = resp.headers.get("Content-Type", "")

    if "application/json" in content_type:
      return resp.json()
    elif "text/plain" in content_type or "text/csv" in content_type:
      return resp.text
    else:
      return resp.data
  except http_client.HttpError as e:
    if e.status_code == 404:
      return {"error": "Record not found (HTTP 404)."}
    elif e.status_code == 400:
      return {"error": "Bad request (HTTP 400). Please check your inputs."}
    else:
      return {"error": f"HTTP Error {e.status_code or 'Error'}: {e.body}"}


def write_output(data, output_file):
  """Writes output to a JSON file."""
  try:
    with open(output_file, "w", encoding="utf-8") as f:
      if isinstance(data, str):
        json.dump({"result": data}, f, indent=2)
      else:
        json.dump(data, f, indent=2)
    print(f"Success! Data written to: {output_file}")
  except (OSError, TypeError) as e:
    print(f"Error writing to file {output_file}: {e}")
    sys.exit(1)


def resolve(name=None, inchi=None):
  """Resolves a chemical name or InChI to CIDs and SMILES."""
  if name:
    encoded_val = urllib.parse.quote(name)
    input_type = "name"
  elif inchi:
    encoded_val = urllib.parse.quote(inchi)
    input_type = "inchi"
  else:
    return {"error": "Either name or inchi must be provided."}

  url_cids = (
      f"{PUBCHEM_BASE_URL}/pug/compound/{input_type}/{encoded_val}/cids/JSON"
  )
  url_props = f"{PUBCHEM_BASE_URL}/pug/compound/{input_type}/{encoded_val}/property/CanonicalSMILES,IsomericSMILES,InChIKey/JSON"

  cids_data = make_request(url_cids)
  if isinstance(cids_data, dict) and "error" in cids_data:
    return cids_data

  props_data = make_request(url_props)

  return {"identifiers": cids_data, "properties": props_data}


def properties(cid):
  url = f"{PUBCHEM_BASE_URL}/pug/compound/cid/{cid}/property/MolecularFormula,MolecularWeight,XLogP,TPSA,ExactMass,HBondDonorCount,HBondAcceptorCount,RotatableBondCount/JSON"
  return make_request(url)


def synonyms(cid):
  url = f"{PUBCHEM_BASE_URL}/pug/compound/cid/{cid}/synonyms/JSON"
  return make_request(url)


def safety(cid):
  url = f"{PUBCHEM_BASE_URL}/pug_view/data/compound/{cid}/JSON?heading=Safety+and+Hazards"
  return make_request(url)


def pharmacology(cid):
  url = f"{PUBCHEM_BASE_URL}/pug_view/data/compound/{cid}/JSON?heading=Pharmacology+and+Biochemistry"
  return make_request(url)


def view(cid, heading):
  encoded_heading = urllib.parse.quote(heading)
  url = f"{PUBCHEM_BASE_URL}/pug_view/data/compound/{cid}/JSON?heading={encoded_heading}"
  return make_request(url)


def xrefs(cid, xref_type):
  url = f"{PUBCHEM_BASE_URL}/pug/compound/cid/{cid}/xrefs/{xref_type}/JSON"
  return make_request(url)


def query(path):
  clean_path = path.lstrip("/")
  url = f"{PUBCHEM_BASE_URL}/{clean_path}"
  return make_request(url)


def image(cid):
  url = f"{PUBCHEM_BASE_URL}/pug/compound/cid/{cid}/PNG"
  return {"image_url": url, "markdown": f"![CID {cid} Image]({url})"}


def similarity(smiles):
  encoded_smiles = urllib.parse.quote(smiles)
  url = f"{PUBCHEM_BASE_URL}/pug/compound/fastsimilarity_2d/smiles/{encoded_smiles}/cids/JSON"
  return make_request(url)


def substructure(smiles):
  encoded_smiles = urllib.parse.quote(smiles)
  url = f"{PUBCHEM_BASE_URL}/pug/compound/fastsubstructure/smiles/{encoded_smiles}/cids/JSON"
  return make_request(url)


def assays(cid, active_only=False):
  url = f"{PUBCHEM_BASE_URL}/pug/compound/cid/{cid}/assaysummary/JSON"
  data = make_request(url)
  if active_only:
    data = filter_active_assays(data)
  return data


def filter_active_assays(data):
  if not isinstance(data, dict) or "Table" not in data:
    return data
  table = data["Table"]
  columns = table.get("Columns", {}).get("Column", [])
  try:
    outcome_idx = columns.index("Activity Outcome")
  except ValueError:
    return data
  filtered_rows = []
  for row in table.get("Row", []):
    cell = row.get("Cell", [])
    if len(cell) > outcome_idx and cell[outcome_idx] == "Active":
      filtered_rows.append(row)
  table["Row"] = filtered_rows
  return data


def range_search(feature, min_val, max_val):
  url = f"{PUBCHEM_BASE_URL}/pug/compound/{feature}/range/{min_val}/{max_val}/cids/JSON"
  return make_request(url)


def main():
  parser = argparse.ArgumentParser(description="PubChem API Wrapper Script")
  subparsers = parser.add_subparsers(dest="command", required=True)

  # Resolve
  p_resolve = subparsers.add_parser(
      "resolve", help="Resolve a chemical name or InChI to CIDs and SMILES"
  )
  group = p_resolve.add_mutually_exclusive_group(required=True)
  group.add_argument("--name", help="Chemical name")
  group.add_argument("--inchi", help="InChI string")
  p_resolve.add_argument(
      "--output", required=True, help="Output JSON file path"
  )

  # Properties
  p_props = subparsers.add_parser(
      "properties", help="Get chemical properties for a CID"
  )
  p_props.add_argument("--cid", required=True, help="Compound ID")
  p_props.add_argument("--output", required=True, help="Output JSON file path")

  # Synonyms
  p_syn = subparsers.add_parser("synonyms", help="Get synonyms for a CID")
  p_syn.add_argument("--cid", required=True, help="Compound ID")
  p_syn.add_argument("--output", required=True, help="Output JSON file path")

  # Safety
  p_safe = subparsers.add_parser("safety", help="Get GHS safety data for a CID")
  p_safe.add_argument("--cid", required=True, help="Compound ID")
  p_safe.add_argument("--output", required=True, help="Output JSON file path")

  # Pharmacology
  p_pharm = subparsers.add_parser(
      "pharmacology", help="Get pharmacology data for a CID"
  )
  p_pharm.add_argument("--cid", required=True, help="Compound ID")
  p_pharm.add_argument("--output", required=True, help="Output JSON file path")

  # View
  p_view = subparsers.add_parser(
      "view", help="Get specific PUG-View heading for a CID"
  )
  p_view.add_argument("--cid", required=True, help="Compound ID")
  p_view.add_argument(
      "--heading", required=True, help="Heading (e.g. 'Geometry')"
  )
  p_view.add_argument("--output", required=True, help="Output JSON file path")

  # Xrefs
  p_xrefs = subparsers.add_parser(
      "xrefs", help="Get cross-references (PatentID, PubMedID, etc.) for a CID"
  )
  p_xrefs.add_argument("--cid", required=True, help="Compound ID")
  p_xrefs.add_argument(
      "--type", required=True, help="Xref type (e.g. 'PatentID')"
  )
  p_xrefs.add_argument("--output", required=True, help="Output JSON file path")

  # Query
  p_query = subparsers.add_parser(
      "query", help="Execute a custom PUG-REST path"
  )
  p_query.add_argument(
      "--path",
      required=True,
      help="e.g., compound/cid/2244/xrefs/PatentID/JSON",
  )
  p_query.add_argument("--output", required=True, help="Output JSON file path")

  # Image
  p_img = subparsers.add_parser("image", help="Get image URL for a CID")
  p_img.add_argument("--cid", required=True, help="Compound ID")
  p_img.add_argument("--output", required=True, help="Output JSON file path")

  # Similarity
  p_sim = subparsers.add_parser(
      "similarity", help="Fast 2D similarity search by SMILES"
  )
  p_sim.add_argument("--smiles", required=True, help="SMILES string")
  p_sim.add_argument("--output", required=True, help="Output JSON file path")

  # Substructure
  p_sub = subparsers.add_parser(
      "substructure", help="Fast substructure search by SMILES"
  )
  p_sub.add_argument("--smiles", required=True, help="SMILES string")
  p_sub.add_argument("--output", required=True, help="Output JSON file path")

  # Assays
  p_assay = subparsers.add_parser("assays", help="Get assay summary for a CID")
  p_assay.add_argument("--cid", required=True, help="Compound ID")
  p_assay.add_argument(
      "--active-only", action="store_true", help="Filter for active assays only"
  )
  p_assay.add_argument("--output", required=True, help="Output JSON file path")

  # Range
  p_range = subparsers.add_parser("range", help="Search by property range")
  p_range.add_argument(
      "--feature", required=True, help="Property name (e.g. molecular_weight)"
  )
  p_range.add_argument("--min", required=True, help="Minimum value")
  p_range.add_argument("--max", required=True, help="Maximum value")
  p_range.add_argument("--output", required=True, help="Output JSON file path")

  args = parser.parse_args()

  if args.command == "resolve":
    data = resolve(name=args.name, inchi=args.inchi)
  elif args.command == "properties":
    data = properties(args.cid)
  elif args.command == "synonyms":
    data = synonyms(args.cid)
  elif args.command == "safety":
    data = safety(args.cid)
  elif args.command == "pharmacology":
    data = pharmacology(args.cid)
  elif args.command == "view":
    data = view(args.cid, args.heading)
  elif args.command == "xrefs":
    data = xrefs(args.cid, args.type)
  elif args.command == "query":
    data = query(args.path)
  elif args.command == "image":
    data = image(args.cid)
  elif args.command == "similarity":
    data = similarity(args.smiles)
  elif args.command == "substructure":
    data = substructure(args.smiles)
  elif args.command == "assays":
    data = assays(args.cid, active_only=args.active_only)
  elif args.command == "range":
    data = range_search(args.feature, args.min, args.max)
  else:
    print("Unknown command")
    sys.exit(1)

  write_output(data, args.output)


if __name__ == "__main__":
  main()
