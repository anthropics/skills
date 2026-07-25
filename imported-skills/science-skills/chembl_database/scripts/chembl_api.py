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

"""ChEMBL REST API client CLI.

CLI tool covering all ChEMBL web services API endpoints. Writes JSON output to
a file specified by --output. Enforces rate limiting between requests and
retries on transient errors (HTTP 429, 503) with exponential backoff.
"""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
# ]
# ///

from __future__ import annotations

import argparse
import json
import os
import sys
from typing import Any
import urllib.parse

from polite_http import http_client

BASE_URL = "https://www.ebi.ac.uk/chembl/api/data"
_CLIENT = http_client.HttpClient(BASE_URL, qps=5.0)
_LICENSE_NOTICE = (
    "Data from the ChEMBL Database. You MUST notify the user"
    " that this data comes from ChEMBL and advise them to"
    " review the ChEMBL licensing terms."
)

SEARCHABLE_ENDPOINTS = frozenset([
    "activity",
    "assay",
    "chembl_id_lookup",
    "document",
    "molecule",
    "protein_classification",
    "target",
])

ENDPOINT_MAP = {
    "activity": "activity",
    "activity_supp": "activity_supplementary_data_by_activity",
    "assay": "assay",
    "assay_class": "assay_class",
    "atc_class": "atc_class",
    "binding_site": "binding_site",
    "biotherapeutic": "biotherapeutic",
    "cell_line": "cell_line",
    "chembl_id_lookup": "chembl_id_lookup",
    "chembl_release": "chembl_release",
    "compound_record": "compound_record",
    "compound_structural_alert": "compound_structural_alert",
    "document": "document",
    "document_similarity": "document_similarity",
    "drug": "drug",
    "drug_indication": "drug_indication",
    "drug_warning": "drug_warning",
    "go_slim": "go_slim",
    "mechanism": "mechanism",
    "metabolism": "metabolism",
    "molecule": "molecule",
    "molecule_form": "molecule_form",
    "organism": "organism",
    "protein_classification": "protein_classification",
    "source": "source",
    "target": "target",
    "target_component": "target_component",
    "target_relation": "target_relation",
    "tissue": "tissue",
    "xref_source": "xref_source",
}

UNIT_CONVERSION_TO_NM = {
    "nm": 1.0,
    "um": 1e3,
    "µm": 1e3,
    "mm": 1e6,
    "m": 1e9,
    "pm": 1e-3,
    "fm": 1e-6,
}


def _write_json(data: Any, output_path: str) -> None:
  """Write a Python object as indented JSON to the given file path.

  Creates parent directories if they do not exist. Prints a short
  confirmation to stdout so the agent knows where the file was saved.

  Args:
    data: The Python object to serialize to JSON.
    output_path: The file path to write the JSON output to.
  """
  out_dir = os.path.dirname(output_path)
  if out_dir:
    os.makedirs(out_dir, exist_ok=True)

  if isinstance(data, dict):
    data["_license_notice"] = (
        "Data from the ChEMBL Database. Please review the licensing terms at"
        " https://www.ebi.ac.uk/chembl/"
    )

  with open(output_path, "w") as f:
    json.dump(data, f, indent=2)
    f.write("\n")
  print(
      json.dumps(
          {
              "status": "success",
              "output_file": output_path,
              "size_bytes": os.path.getsize(output_path),
              "license_notice": _LICENSE_NOTICE,
          },
          indent=2,
      )
  )


def _make_request(url: str) -> dict[str, Any]:
  """Send an HTTP GET to *url* and return the parsed JSON response.

  Uses HttpClient for retry logic. Non-retryable HTTP errors
  are returned as a dict with ``status=error``.

  Args:
    url: The URL to send the HTTP GET request to.

  Returns:
    The parsed JSON response as a dict or list, or a dict with
    ``status=error`` and a ``message`` key on failure.
  """
  try:
    return _CLIENT.fetch_json(url)
  except http_client.HttpError as e:
    return {
        "status": "error",
        "http_code": e.status_code,
        "message": str(e),
        "detail": (
            e.body.decode("utf-8", errors="replace")[:500] if e.body else ""
        ),
    }
  except Exception as e:
    return {
        "status": "error",
        "message": f"Network error: {e}",
    }


def _download_binary(url: str, output_path: str) -> dict[str, Any]:
  """Download binary content from *url* and save to *output_path*.

  Used for image and structure-file downloads. Uses HttpClient
  for retry logic.

  Args:
    url: The URL to download binary content from.
    output_path: The file path to save the downloaded content to.

  Returns:
    A dict with ``status=success``, ``message``, and ``size_bytes`` on
    success, or ``status=error`` and ``message`` on failure.
  """
  try:
    content = _CLIENT.fetch_bytes(url)
    out_dir = os.path.dirname(output_path)
    if out_dir:
      os.makedirs(out_dir, exist_ok=True)
    with open(output_path, "wb") as f:
      f.write(content)
    return {
        "status": "success",
        "message": f"Saved to {output_path}",
        "size_bytes": len(content),
        "license_notice": _LICENSE_NOTICE,
    }
  except Exception as e:
    return {"status": "error", "message": f"File system/Network error: {e}"}


def _build_url(
    endpoint: str,
    resource_id: str | None = None,
    ids_list: str | None = None,
    search: str | None = None,
    filters: list[str] | None = None,
    limit: int | None = None,
    offset: int | None = None,
) -> str:
  """Construct a ChEMBL API URL from components.

  Handles single-resource, batch (set/), search, filter, and
  pagination parameters.

  Args:
    endpoint: The ChEMBL API endpoint name (e.g., "molecule").
    resource_id: A single ChEMBL ID or numeric ID.
    ids_list: Semicolon-separated string of IDs for batch fetching.
    search: Free-text search query string.
    filters: List of "KEY=VALUE" filter strings.
    limit: Maximum number of results to return.
    offset: Pagination offset.

  Returns:
    A complete URL string for the ChEMBL API request.

  Raises:
    SystemExit: If a filter string does not contain '='.
  """
  parts = [BASE_URL, endpoint]
  if resource_id:
    parts.append(resource_id)
  elif ids_list:
    parts.append("set/" + ids_list)
  elif search:
    parts.append("search")
  url = "/".join(parts) + ".json"

  params: dict[str, Any] = {}
  if search:
    params["q"] = search
  if limit is not None:
    params["limit"] = limit
  if offset is not None:
    params["offset"] = offset
  if filters:
    for filt in filters:
      if "=" not in filt:
        print(
            json.dumps(
                {
                    "status": "error",
                    "message": (
                        f"Invalid filter '{filt}': expected KEY=VALUE format."
                    ),
                },
                indent=2,
            ),
        )
        sys.exit(1)
      key, val = filt.split("=", 1)
      params[key] = val
  if params:
    url += "?" + urllib.parse.urlencode(params)
  return url


def _normalize_activity(record: dict[str, Any]) -> dict[str, Any]:
  """Add normalised nM value to a single activity record.

  Reads ``standard_value`` and ``standard_units``, converts to nM
  using UNIT_CONVERSION_TO_NM, and adds ``normalized_value_nM`` and
  ``normalization_note`` keys to *record*.

  Args:
    record: An activity record dict containing ``standard_value`` and
      ``standard_units`` keys.

  Returns:
    The mutated *record* dict with ``normalized_value_nM`` and
    ``normalization_note`` keys added.
  """
  units = (record.get("standard_units") or "").strip().lower()
  value = record.get("standard_value")
  if value is None or units not in UNIT_CONVERSION_TO_NM:
    record["normalized_value_nM"] = None
    record["normalization_note"] = (
        f"Cannot normalize: units='{record.get('standard_units')}'"
        if value is not None
        else "No standard_value"
    )
    return record
  try:
    nm_value = float(value) * UNIT_CONVERSION_TO_NM[units]
    record["normalized_value_nM"] = nm_value
    record["normalization_note"] = (
        f"Converted {value} {record.get('standard_units')} -> {nm_value} nM"
    )
  except (ValueError, TypeError):
    record["normalized_value_nM"] = None
    record["normalization_note"] = f"Cannot convert value: {value}"
  return record


def cmd_generic(args: argparse.Namespace) -> None:
  """Handle all standard endpoint subcommands (molecule, target, etc.).

  Builds the URL, makes the request, optionally normalises activity
  values, and writes JSON output to args.output.

  Args:
    args: Parsed command-line arguments. Expected attributes: command, search,
      id, ids, filter, limit, offset, output, and optionally normalize (for
      activity endpoint).
  """
  api_endpoint = ENDPOINT_MAP[args.command]
  can_search = api_endpoint in SEARCHABLE_ENDPOINTS

  if args.search and not can_search:
    searchable_list = ", ".join(sorted(SEARCHABLE_ENDPOINTS))
    error = {
        "status": "error",
        "message": f"Search is not supported for endpoint '{args.command}'.",
        "suggestion": (
            f"Use --filter instead (e.g. {args.command} --filter"
            " KEY=VALUE), or search a supported endpoint:"
            f" {searchable_list}."
        ),
    }
    _write_json(error, args.output)
    sys.exit(1)

  url = _build_url(
      api_endpoint,
      resource_id=args.id,
      ids_list=args.ids,
      search=args.search if can_search else None,
      filters=args.filter,
      limit=args.limit if not args.id else None,
      offset=args.offset if not args.id else None,
  )
  result = _make_request(url)

  normalize = getattr(args, "normalize", False)
  if normalize and api_endpoint == "activity":
    if isinstance(result, dict) and "activities" in result:
      result["activities"] = [
          _normalize_activity(r) for r in result["activities"]
      ]
    elif isinstance(result, dict) and "standard_value" in result:
      result = _normalize_activity(result)

  _write_json(result, args.output)


def cmd_status(args: argparse.Namespace) -> None:
  """Check ChEMBL API status and write the result to args.output.

  Args:
    args: Parsed command-line arguments. Expected attribute: output.
  """
  url = f"{BASE_URL}/status.json"
  result = _make_request(url)
  _write_json(result, args.output)


def cmd_similarity(args: argparse.Namespace) -> None:
  """Run a server-side similarity search against the ChEMBL database.

  Requires --smiles and --similarity (threshold 0-100). Writes
  matching molecules to args.output.

  Args:
    args: An argparse.Namespace object containing the parsed command-line
      arguments. Expected attributes: smiles, similarity, limit, offset, output.
  """
  smiles_encoded = urllib.parse.quote(args.smiles, safe="")
  url = f"{BASE_URL}/similarity/{smiles_encoded}/{args.similarity}.json"
  params: dict[str, Any] = {}
  if args.limit:
    params["limit"] = args.limit
  if args.offset:
    params["offset"] = args.offset
  if params:
    url += "?" + urllib.parse.urlencode(params)
  result = _make_request(url)
  _write_json(result, args.output)


def cmd_substructure(args: argparse.Namespace) -> None:
  """Run a server-side substructure search against ChEMBL.

  Requires --smiles. Writes matching molecules to args.output.

  Args:
    args: An argparse.Namespace object containing the parsed command-line
      arguments. Expected attributes: smiles, limit, offset, and output.
  """
  smiles_encoded = urllib.parse.quote(args.smiles, safe="")
  url = f"{BASE_URL}/substructure/{smiles_encoded}.json"
  params: dict[str, Any] = {}
  if args.limit:
    params["limit"] = args.limit
  if args.offset:
    params["offset"] = args.offset
  if params:
    url += "?" + urllib.parse.urlencode(params)
  result = _make_request(url)
  _write_json(result, args.output)


def cmd_image(args: argparse.Namespace) -> None:
  """Download a compound 2D structure image (SVG or PNG).

  Binary content is saved to args.output. A JSON status summary
  is printed to stdout.

  Args:
    args: An argparse.Namespace object containing the parsed command-line
      arguments. Expected attributes: id, output, dimensions, engine, img_format
  """
  url = f"{BASE_URL}/image/{args.id}"
  params: dict[str, Any] = {}
  if args.dimensions:
    params["dimensions"] = args.dimensions
  if args.engine:
    params["engine"] = args.engine
  if args.img_format:
    params["format"] = args.img_format
  if params:
    url += "?" + urllib.parse.urlencode(params)
  result = _download_binary(url, args.output)
  print(json.dumps(result, indent=2))


def cmd_molecule_download(args: argparse.Namespace) -> None:
  """Download a molecule structure file in SDF or MOL format.

  Requires --id and --dl_format. Binary content is saved to
  args.output (or defaults to <CHEMBL_ID>.<format>).

  Args:
    args: An argparse.Namespace object containing the parsed command-line
      arguments. Expected attributes: id, dl_format, output.
  """
  fmt = args.dl_format
  chembl_id = args.id
  if not chembl_id:
    error = {
        "status": "error",
        "message": "--id is required for --dl_format",
    }
    print(json.dumps(error, indent=2))
    sys.exit(1)
  url = f"{BASE_URL}/molecule/{chembl_id}.{fmt}"
  output = args.output if args.output else f"{chembl_id}.{fmt}"
  result = _download_binary(url, output)
  print(json.dumps(result, indent=2))


def _add_common_args(parser: argparse.ArgumentParser) -> None:
  """Add shared arguments (--id, --ids, --search, etc.) to a subparser.

  Args:
    parser: The argparse subparser to add arguments to.
  """
  parser.add_argument("--id", type=str, help="Single ChEMBL ID or numeric ID")
  parser.add_argument(
      "--ids",
      type=str,
      help="Semicolon-separated list of IDs for batch fetch",
  )
  parser.add_argument(
      "--search",
      type=str,
      help="Free-text search query (only for searchable endpoints)",
  )
  parser.add_argument(
      "--limit",
      type=int,
      default=5,
      help="Max results to return (default: 5)",
  )
  parser.add_argument(
      "--offset",
      type=int,
      default=None,
      help="Pagination offset",
  )
  parser.add_argument(
      "--filter",
      type=str,
      nargs="*",
      help="Filter as KEY=VALUE pairs",
  )
  parser.add_argument(
      "--output",
      type=str,
      required=True,
      help="Output JSON file path (required)",
  )


def build_parser() -> argparse.ArgumentParser:
  """Build the top-level argparse parser with all subcommands.

  Creates subparsers for every ChEMBL endpoint plus the special
  status, similarity, substructure, and image subcommands.

  Returns:
    An argparse.ArgumentParser instance configured with all ChEMBL API
    subcommands.
  """
  parser = argparse.ArgumentParser(
      description=(
          "ChEMBL REST API client. Query bioactive molecules, targets,"
          " activities, and more. All output is written to --output file."
      )
  )
  subparsers = parser.add_subparsers(
      dest="command", help="API endpoint to query"
  )

  for cmd_name in sorted(ENDPOINT_MAP.keys()):
    api_name = ENDPOINT_MAP[cmd_name]
    searchable = " (searchable)" if api_name in SEARCHABLE_ENDPOINTS else ""
    sp = subparsers.add_parser(
        cmd_name, help=f"Query {api_name} endpoint{searchable}"
    )
    _add_common_args(sp)
    if cmd_name == "activity":
      sp.add_argument(
          "--normalize",
          action="store_true",
          help="Normalize bioactivity values to nM",
      )
    if cmd_name == "molecule":
      sp.add_argument(
          "--dl_format",
          type=str,
          choices=["sdf", "mol"],
          help="Download molecule structure file (SDF or MOL)",
      )
    sp.set_defaults(func=cmd_generic)

  sp_status = subparsers.add_parser("status", help="Check ChEMBL API status")
  sp_status.add_argument(
      "--output",
      type=str,
      required=True,
      help="Output JSON file path (required)",
  )
  sp_status.set_defaults(func=cmd_status)

  sp_sim = subparsers.add_parser(
      "similarity", help="Server-side similarity search by SMILES"
  )
  sp_sim.add_argument("--smiles", type=str, required=True, help="SMILES string")
  sp_sim.add_argument(
      "--similarity",
      type=int,
      required=True,
      help="Similarity threshold (0-100)",
  )
  sp_sim.add_argument(
      "--limit",
      type=int,
      default=5,
      help="Max results (default: 5)",
  )
  sp_sim.add_argument(
      "--offset",
      type=int,
      default=None,
      help="Pagination offset",
  )
  sp_sim.add_argument(
      "--output",
      type=str,
      required=True,
      help="Output JSON file path (required)",
  )
  sp_sim.set_defaults(func=cmd_similarity)

  sp_sub = subparsers.add_parser(
      "substructure", help="Server-side substructure search by SMILES"
  )
  sp_sub.add_argument("--smiles", type=str, required=True, help="SMILES string")
  sp_sub.add_argument(
      "--limit",
      type=int,
      default=5,
      help="Max results (default: 5)",
  )
  sp_sub.add_argument(
      "--offset",
      type=int,
      default=None,
      help="Pagination offset",
  )
  sp_sub.add_argument(
      "--output",
      type=str,
      required=True,
      help="Output JSON file path (required)",
  )
  sp_sub.set_defaults(func=cmd_substructure)

  sp_img = subparsers.add_parser(
      "image", help="Download compound image (SVG by default)"
  )
  sp_img.add_argument(
      "--id",
      type=str,
      required=True,
      help="ChEMBL ID or InChI Key",
  )
  sp_img.add_argument(
      "--output",
      type=str,
      required=True,
      help="Output file path",
  )
  sp_img.add_argument(
      "--dimensions",
      type=int,
      help="Image size in pixels (max 500, default 500)",
  )
  sp_img.add_argument(
      "--engine",
      type=str,
      default=None,
      help="Rendering engine (default: rdkit)",
  )
  sp_img.add_argument(
      "--img_format",
      type=str,
      choices=["svg", "png"],
      default=None,
      help="Image format: svg (default) or png",
  )
  sp_img.set_defaults(func=cmd_image)

  return parser


if __name__ == "__main__":
  main_parser = build_parser()
  main_args = main_parser.parse_args()

  if not main_args.command:
    main_parser.print_help()
    sys.exit(1)

  if getattr(main_args, "dl_format", None):
    cmd_molecule_download(main_args)
  else:
    main_args.func(main_args)
