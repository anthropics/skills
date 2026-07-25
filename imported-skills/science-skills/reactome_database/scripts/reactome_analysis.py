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

"""CLI for the Reactome Analysis Service and Content Service APIs.

Provides subcommands covering all endpoints of the Reactome Analysis Service
(https://reactome.org/AnalysisService/) and key Content Service endpoints
(https://reactome.org/ContentService/). Supports pathway enrichment analysis,
identifier mapping, token-based result retrieval, report/download features,
Content Service queries, diagram export, and cross-reference mapping.
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
import sys
from typing import Any
import urllib.parse

from polite_http import http_client

ANALYSIS_BASE_URL = "https://reactome.org/AnalysisService"
CONTENT_BASE_URL = "https://reactome.org/ContentService"
_CLIENT = http_client.HttpClient("https://reactome.org/", qps=1)
_ENCODE_FIELDS = frozenset({"id", "species_id", "species", "species_name"})


def _write_output(
    output_path: str,
    content: str | bytes,
    binary: bool = False,
) -> None:
  """Writes content to an output file."""
  if binary:
    with open(output_path, "wb") as f:
      f.write(content)
  else:
    with open(output_path, "w") as f:
      f.write(content)
  print(f"Output written to {output_path}")
  if len(content) > 100_000:
    print(
        "WARNING: Large output file. Do NOT read the full file into context. "
        "Use 'jq' or a script to extract relevant fields.",
    )


def _filter_pathways(
    result_text: str,
    fdr: float | None = None,
    pvalue: float | None = None,
) -> str:
  """Filter analysis result pathways by FDR/p-value."""
  if fdr is None and pvalue is None:
    return result_text
  try:
    data = json.loads(result_text)
    if "pathways" not in data:
      return result_text
    filtered = data["pathways"]
    if fdr is not None:
      filtered = [
          p for p in filtered if p.get("entities", {}).get("fdr", 1.0) <= fdr
      ]
    if pvalue is not None:
      filtered = [
          p
          for p in filtered
          if p.get("entities", {}).get("pValue", 1.0) <= pvalue
      ]
    data["pathways"] = filtered
    data["pathwaysFound"] = len(filtered)
    return json.dumps(data)
  except (json.JSONDecodeError, TypeError, KeyError):
    return result_text


def _summarize_result(result_text: str, limit: int = 100) -> str:
  """Summarizes large JSON results by truncating lists."""
  try:
    data = json.loads(result_text)
    if isinstance(data, list):
      if len(data) > limit:
        print(f"Truncating list from {len(data)} to {limit} items.")
        data = data[:limit]
    elif isinstance(data, dict):
      if "pathways" in data and isinstance(data["pathways"], list):
        if len(data["pathways"]) > limit:
          print(
              f"Truncating pathways list from {len(data['pathways'])} to"
              f" {limit} items."
          )
          data["pathways"] = data["pathways"][:limit]
          data["_truncated"] = True
    return json.dumps(data)
  except (json.JSONDecodeError, TypeError):
    return result_text


def _build_params(
    args: argparse.Namespace,
) -> dict[str, str]:
  """Builds query parameters from common analysis flags."""
  params: dict[str, str] = {}
  direct_map = {
      "species": "species",
      "page_size": "pageSize",
      "page": "page",
      "sort_by": "sortBy",
      "order": "order",
      "resource": "resource",
  }
  for arg_name, param_name in direct_map.items():
    value = getattr(args, arg_name, None)
    if value is not None:
      params[param_name] = value

  # Variables that need to be cast to lowercase strings
  lower_map = {
      "interactors": "interactors",
      "include_disease": "includeDisease",
  }
  for arg_name, param_name in lower_map.items():
    if value := getattr(args, arg_name, None):
      params[param_name] = str(value).lower()
  return params


def _read_data(
    args: argparse.Namespace,
) -> str | None:
  """Reads user-supplied data from --file or --data flags."""
  if hasattr(args, "file") and args.file:
    with open(args.file, "r") as f:
      return f.read()
  if hasattr(args, "data") and args.data:
    text = args.data.replace("\\n", "\n")
    if "\n" not in text and "," in text:
      text = text.replace(",", "\n")
    return text
  return None


def _build_multipart(
    filepath: str,
    mime: str = "text/plain",
) -> tuple[bytes, str]:
  """Builds multipart form data from a file."""
  with open(filepath, "rb") as f:
    file_data = f.read()
  boundary = "----ReactomeBoundary"
  body = (
      f"--{boundary}\r\n"
      "Content-Disposition: form-data; "
      f"name='file'; filename='{filepath}'\r\n"
      f"Content-Type: {mime}\r\n\r\n"
  ).encode("utf-8")
  body += file_data
  body += f"\r\n--{boundary}--\r\n".encode("utf-8")
  ctype = f"multipart/form-data; boundary={boundary}"
  return body, ctype


def _fill_path(
    template: str,
    args: argparse.Namespace,
) -> str:
  """Fills path template placeholders from args."""
  ns = vars(args)
  for key, val in ns.items():
    ph = "{" + key + "}"
    if ph in template and val is not None:
      s = str(val)
      if key in _ENCODE_FIELDS:
        s = urllib.parse.quote(s, safe="")
      template = template.replace(ph, s)
  return template


def _search_params(
    args: argparse.Namespace,
) -> dict[str, Any]:
  """Builds query parameters for the search command."""
  params: dict[str, Any] = {"query": args.query}
  if getattr(args, "species_name", None):
    params["species"] = args.species_name
  if getattr(args, "types", None):
    params["types"] = args.types
  if getattr(args, "cluster", None) is not None:
    params["cluster"] = str(args.cluster).lower()
  if getattr(args, "start", None) is not None:
    params["Start row"] = args.start
  if getattr(args, "rows", None) is not None:
    params["rows"] = args.rows
  return params


_OUT = {
    "name": "--output",
    "required": True,
    "help": "Output file path",
}
_ID = {
    "name": "--id",
    "required": True,
    "help": "Identifier",
}
_TOKEN = {
    "name": "--token",
    "required": True,
    "help": "Analysis token",
}
_PATHWAY = {
    "name": "--pathway",
    "required": True,
    "help": "Pathway stable ID (e.g. R-HSA-69278)",
}
_URL_ARG = {
    "name": "--url",
    "required": True,
    "help": "URL containing data to analyse",
}
_FILE_REQ = {
    "name": "--file",
    "required": True,
    "help": "File to upload",
}
_RES_OPT = {
    "name": "--resource",
    "type": str,
    "default": None,
    "help": "Resource filter",
}

COMMANDS: list[dict[str, Any]] = [
    {
        "name": "db-name",
        "help": "Get database name",
        "path": "/database/name",
        "accept": "text/plain",
        "handler": "text_wrap",
        "wrap_key": "database_name",
        "args": [_OUT],
    },
    {
        "name": "db-version",
        "help": "Get database version",
        "path": "/database/version",
        "accept": "text/plain",
        "handler": "text_wrap",
        "wrap_key": "database_version",
        "args": [_OUT],
    },
    {
        "name": "identifier",
        "help": "Analyse a single identifier",
        "path": "/identifier/{id}",
        "filterable": True,
        "common": True,
        "args": [_ID],
    },
    {
        "name": "identifier-projection",
        "help": "Analyse identifier with projection",
        "path": "/identifier/{id}/projection",
        "filterable": True,
        "common": True,
        "args": [_ID],
    },
    {
        "name": "analyze",
        "help": "Analyse identifiers (POST)",
        "method": "POST",
        "path": "/identifiers/",
        "input": "data",
        "filterable": True,
        "common": True,
        "input_flags": True,
    },
    {
        "name": "analyze-projection",
        "help": "Analyse identifiers with projection (POST)",
        "method": "POST",
        "path": "/identifiers/projection",
        "input": "data",
        "filterable": True,
        "common": True,
        "input_flags": True,
    },
    {
        "name": "analyze-form",
        "help": "Analyse identifiers from file upload",
        "method": "POST",
        "path": "/identifiers/form",
        "input": "form",
        "filterable": True,
        "common": True,
        "args": [_FILE_REQ],
    },
    {
        "name": "analyze-form-projection",
        "help": "Analyse identifiers from file with projection",
        "method": "POST",
        "path": "/identifiers/form/projection",
        "input": "form",
        "filterable": True,
        "common": True,
        "args": [_FILE_REQ],
    },
    {
        "name": "analyze-url",
        "help": "Analyse identifiers from a URL",
        "method": "POST",
        "path": "/identifiers/url",
        "input": "url",
        "filterable": True,
        "common": True,
        "args": [_URL_ARG],
    },
    {
        "name": "analyze-url-projection",
        "help": "Analyse identifiers from URL with projection",
        "method": "POST",
        "path": "/identifiers/url/projection",
        "input": "url",
        "filterable": True,
        "common": True,
        "args": [_URL_ARG],
    },
    {
        "name": "token-result",
        "help": "Retrieve result by token",
        "path": "/token/{token}",
        "filterable": True,
        "common": True,
        "args": [_TOKEN],
    },
    {
        "name": "token-filter-species",
        "help": "Filter result by species",
        "path": "/token/{token}/filter/species/{species_filter}",
        "common": True,
        "args": [
            _TOKEN,
            {
                "name": "--species-filter",
                "required": True,
                "help": "Species NCBI Taxon ID to filter by",
            },
        ],
    },
    {
        "name": "token-filter-pathways",
        "help": "Filter result by pathway IDs",
        "method": "POST",
        "path": "/token/{token}/filter/pathways",
        "input": "data",
        "common": True,
        "args": [_TOKEN],
        "input_flags": True,
    },
    {
        "name": "token-found-all",
        "help": "Summary of found identifiers for pathways",
        "method": "POST",
        "path": "/token/{token}/found/all",
        "input": "data",
        "args": [_TOKEN, _OUT],
        "input_flags": True,
    },
    {
        "name": "token-found-all-pathway",
        "help": "Summary of found identifiers for a pathway",
        "path": "/token/{token}/found/all/{pathway}",
        "param_map": [("resource", "resource")],
        "args": [_TOKEN, _PATHWAY, _OUT, _RES_OPT],
    },
    {
        "name": "token-found-entities",
        "help": "Found curated identifiers for a pathway",
        "path": "/token/{token}/found/entities/{pathway}",
        "param_map": [("resource", "resource")],
        "args": [_TOKEN, _PATHWAY, _OUT, _RES_OPT],
    },
    {
        "name": "token-found-interactors",
        "help": "Found interactors for a pathway",
        "path": "/token/{token}/found/interactors/{pathway}",
        "param_map": [("resource", "resource")],
        "args": [_TOKEN, _PATHWAY, _OUT, _RES_OPT],
    },
    {
        "name": "token-not-found",
        "help": "List identifiers not found for a token",
        "path": "/token/{token}/notFound",
        "args": [_TOKEN, _OUT],
    },
    {
        "name": "token-page",
        "help": "Get page number for a pathway in results",
        "path": "/token/{token}/page/{pathway}",
        "handler": "page_wrap",
        "common": True,
        "args": [_TOKEN, _PATHWAY],
    },
    {
        "name": "token-binned",
        "help": "Binned hit pathway sizes",
        "path": "/token/{token}/pathways/binned",
        "param_map": [
            ("bin_size", "binSize"),
            ("species", "species"),
            ("resource", "resource"),
        ],
        "args": [
            _TOKEN,
            _OUT,
            {
                "name": "--bin-size",
                "type": int,
                "default": None,
                "help": "Bin size",
            },
            {
                "name": "--species",
                "type": str,
                "default": None,
                "help": "Species filter",
            },
            _RES_OPT,
        ],
    },
    {
        "name": "token-reactions-pathway",
        "help": "Reaction IDs for a pathway",
        "path": "/token/{token}/reactions/{pathway}",
        "param_map": [("resource", "resource")],
        "args": [_TOKEN, _PATHWAY, _OUT, _RES_OPT],
    },
    {
        "name": "token-reactions-pathways",
        "help": "Reaction IDs for posted pathway IDs",
        "method": "POST",
        "path": "/token/{token}/reactions/pathways",
        "input": "data",
        "param_map": [("resource", "resource")],
        "args": [_TOKEN, _OUT, _RES_OPT],
        "input_flags": True,
    },
    {
        "name": "token-resources",
        "help": "Resources summary for a token",
        "path": "/token/{token}/resources",
        "args": [_TOKEN, _OUT],
    },
    {
        "name": "download-result",
        "help": "Download full result as JSON",
        "path": "/download/{token}/result.json",
        "args": [_TOKEN, _OUT],
    },
    {
        "name": "download-result-gz",
        "help": "Download full result as gzipped JSON",
        "path": "/download/{token}/result.json.gz",
        "handler": "binary",
        "args": [_TOKEN, _OUT],
    },
    {
        "name": "download-found",
        "help": "Download found identifiers as CSV",
        "path": "/download/{token}/entities/found/{resource}/{filename}.csv",
        "handler": "csv",
        "accept": "text/csv",
        "args": [
            _TOKEN,
            _OUT,
            {
                "name": "--resource",
                "type": str,
                "default": "TOTAL",
                "help": "Resource filter",
            },
            {
                "name": "--filename",
                "type": str,
                "default": "found",
                "help": "CSV filename",
            },
        ],
    },
    {
        "name": "download-not-found",
        "help": "Download not-found identifiers as CSV",
        "path": "/download/{token}/entities/notfound/{filename}.csv",
        "handler": "csv",
        "accept": "text/csv",
        "args": [
            _TOKEN,
            _OUT,
            {
                "name": "--filename",
                "type": str,
                "default": "notfound",
                "help": "CSV filename",
            },
        ],
    },
    {
        "name": "download-pathways",
        "help": "Download hit pathways as CSV",
        "path": "/download/{token}/pathways/{resource}/{filename}.csv",
        "handler": "csv",
        "accept": "text/csv",
        "args": [
            _TOKEN,
            _OUT,
            {
                "name": "--resource",
                "type": str,
                "default": "TOTAL",
                "help": "Resource filter",
            },
            {
                "name": "--filename",
                "type": str,
                "default": "pathways",
                "help": "CSV filename",
            },
        ],
    },
    {
        "name": "mapping",
        "help": "Map identifiers (POST)",
        "method": "POST",
        "path": "/mapping/",
        "input": "data",
        "common": True,
        "input_flags": True,
    },
    {
        "name": "mapping-projection",
        "help": "Map identifiers with projection (POST)",
        "method": "POST",
        "path": "/mapping/projection",
        "input": "data",
        "common": True,
        "input_flags": True,
    },
    {
        "name": "mapping-form",
        "help": "Map identifiers from file upload",
        "method": "POST",
        "path": "/mapping/form",
        "input": "form",
        "common": True,
        "args": [_FILE_REQ],
    },
    {
        "name": "mapping-form-projection",
        "help": "Map identifiers from file with projection",
        "method": "POST",
        "path": "/mapping/form/projection",
        "input": "form",
        "common": True,
        "args": [_FILE_REQ],
    },
    {
        "name": "mapping-url",
        "help": "Map identifiers from a URL",
        "method": "POST",
        "path": "/mapping/url",
        "input": "url",
        "common": True,
        "args": [_URL_ARG],
    },
    {
        "name": "mapping-url-projection",
        "help": "Map identifiers from URL with projection",
        "method": "POST",
        "path": "/mapping/url/projection",
        "input": "url",
        "common": True,
        "args": [_URL_ARG],
    },
    {
        "name": "import-json",
        "help": "Import a JSON result",
        "method": "POST",
        "path": "/import/",
        "input": "json_data",
        "args": [_OUT],
        "input_flags": True,
    },
    {
        "name": "import-form",
        "help": "Import a JSON file via form upload",
        "method": "POST",
        "path": "/import/form",
        "input": "form",
        "form_mime": "application/json",
        "args": [_FILE_REQ, _OUT],
    },
    {
        "name": "import-url",
        "help": "Import a JSON result from a URL",
        "method": "POST",
        "path": "/import/url",
        "input": "url",
        "args": [_URL_ARG, _OUT],
    },
    {
        "name": "report",
        "help": "Download analysis PDF report",
        "path": "/report/{token}/{species}/{filename}.pdf",
        "handler": "binary",
        "accept": "application/pdf",
        "args": [
            _TOKEN,
            _OUT,
            {
                "name": "--species",
                "type": str,
                "default": "Homo sapiens",
                "help": "Species name (default: Homo sapiens)",
            },
            {
                "name": "--filename",
                "type": str,
                "default": "report",
                "help": "Report filename (without .pdf)",
            },
        ],
    },
    {
        "name": "species-comparison",
        "help": "Compare Homo sapiens to another species",
        "path": "/species/homoSapiens/{species_id}",
        "common": True,
        "args": [
            {
                "name": "--species-id",
                "required": True,
                "help": "Species NCBI Taxon ID to compare",
            },
            {
                "name": "--summary",
                "action": "store_true",
                "help": "Only output a summary of the results",
            },
        ],
    },
    {
        "name": "participants",
        "help": "Reaction/event participants",
        "path": "/data/participants/{id}",
        "base": "content",
        "args": [_ID, _OUT],
    },
    {
        "name": "participating-entities",
        "help": "Physical entities in a reaction",
        "path": "/data/participants/{id}/participatingPhysicalEntities",
        "base": "content",
        "args": [_ID, _OUT],
    },
    {
        "name": "component-of",
        "help": "Complexes/sets containing entity",
        "path": "/data/entity/{id}/componentOf",
        "base": "content",
        "args": [_ID, _OUT],
    },
    {
        "name": "event-ancestors",
        "help": "Parent pathways (hierarchy up)",
        "path": "/data/event/{id}/ancestors",
        "base": "content",
        "args": [_ID, _OUT],
    },
    {
        "name": "contained-events",
        "help": "Sub-pathways (hierarchy down)",
        "path": "/data/pathway/{id}/containedEvents",
        "base": "content",
        "args": [_ID, _OUT],
    },
    {
        "name": "top-pathways",
        "help": "All top-level pathways",
        "path": "/data/pathways/top/{species_name}",
        "base": "content",
        "args": [
            {
                "name": "--species-name",
                "type": str,
                "default": "Homo sapiens",
                "help": "Species name (default: Homo sapiens)",
            },
            _OUT,
        ],
    },
    {
        "name": "low-pathways",
        "help": "Lower-level pathways for entity",
        "path": "/data/pathways/low/entity/{id}",
        "base": "content",
        "args": [_ID, _OUT],
    },
    {
        "name": "query",
        "help": "Retrieve entry by stable ID",
        "path": "/data/query/{id}",
        "base": "content",
        "args": [_ID, _OUT],
    },
    {
        "name": "xref-mapping",
        "help": "Cross-reference mapping for ID",
        "path": "/references/mapping/{id}/xrefs",
        "base": "content",
        "args": [_ID, _OUT],
    },
    {
        "name": "xref-mapping-batch",
        "help": "Batch cross-reference mapping",
        "method": "POST",
        "path": "/references/mapping/xrefs",
        "input": "data",
        "base": "content",
        "args": [_OUT],
        "input_flags": True,
    },
    {
        "name": "diagram",
        "help": "Export pathway diagram (PNG/SVG)",
        "path": "/exporter/diagram/{id}.{format}",
        "handler": "binary",
        "base": "content",
        "param_map": [
            ("highlight", "flg"),
            ("quality", "quality"),
        ],
        "args": [
            _ID,
            _OUT,
            {
                "name": "--format",
                "type": str,
                "default": "png",
                "choices": ["png", "svg", "jpg", "gif"],
                "help": "Image format (default: png)",
            },
            {
                "name": "--highlight",
                "type": str,
                "default": None,
                "help": "Identifiers to highlight",
            },
            {
                "name": "--quality",
                "type": int,
                "default": None,
                "help": "Image quality (1-10)",
            },
        ],
    },
    {
        "name": "reaction-diagram",
        "help": "Export reaction diagram (PNG/SVG)",
        "path": "/exporter/reaction/{id}.{format}",
        "handler": "binary",
        "base": "content",
        "param_map": [("quality", "quality")],
        "args": [
            _ID,
            _OUT,
            {
                "name": "--format",
                "type": str,
                "default": "png",
                "choices": ["png", "svg", "jpg", "gif"],
                "help": "Image format (default: png)",
            },
            {
                "name": "--quality",
                "type": int,
                "default": None,
                "help": "Image quality (1-10)",
            },
        ],
    },
    {
        "name": "search",
        "help": "Search Reactome knowledgebase",
        "path": "/search/query",
        "base": "content",
        "custom_params": _search_params,
        "args": [
            {
                "name": "--query",
                "required": True,
                "help": "Search query string",
            },
            _OUT,
            {
                "name": "--species-name",
                "type": str,
                "default": None,
                "help": "Species filter",
            },
            {
                "name": "--types",
                "type": str,
                "default": None,
                "help": "Comma-separated type filter",
            },
            {
                "name": "--cluster",
                "type": bool,
                "default": None,
                "help": "Cluster results",
            },
            {
                "name": "--start",
                "type": int,
                "default": None,
                "help": "Start row for pagination",
            },
            {
                "name": "--rows",
                "type": int,
                "default": None,
                "help": "Number of rows to return",
            },
        ],
    },
]


def _load_data(cfg, args):
  """Loads the data from the arguments."""
  data = None
  content_type = "text/plain"
  input_type = cfg.get("input")
  if input_type == "data":
    data = _read_data(args)
    if not data:
      print("Error: provide --data or --file", file=sys.stderr)
      sys.exit(1)
  elif input_type == "form":
    if not args.file:
      print("Error: --file is required for form upload", file=sys.stderr)
      sys.exit(1)
    mime = cfg.get("form_mime", "text/plain")
    data, content_type = _build_multipart(args.file, mime)
  elif input_type == "url":
    if not args.url:
      print("Error: --url is required", file=sys.stderr)
      sys.exit(1)
    data = args.url
  elif input_type == "json_data":
    data = _read_data(args)
    if not data:
      print("Error: provide --data or --file", file=sys.stderr)
      sys.exit(1)
    content_type = "application/json"

  if isinstance(data, str):
    data = data.encode("utf-8")

  return data, content_type


def _generate_url(cfg, args) -> str:
  """Generates the URL for the given config and arguments."""
  path = _fill_path(cfg["path"], args)
  base_key = cfg.get("base")
  base = CONTENT_BASE_URL if base_key == "content" else None

  url = f"{base or ANALYSIS_BASE_URL}{path}"
  params: dict[str, Any] = {}
  if cfg.get("common"):
    params = _build_params(args)
  custom_fn = cfg.get("custom_params")
  if custom_fn:
    params.update(custom_fn(args))
  for attr, api_name in cfg.get("param_map", []):
    val = getattr(args, attr, None)
    if val is not None:
      params[api_name] = val
  if params:
    url += "?" + urllib.parse.urlencode(
        {k: v for k, v in params.items() if v is not None}
    )
  return url


def _dispatch(args: argparse.Namespace) -> None:
  """Generic command handler driven by config."""
  cfg = args._cfg
  method = cfg.get("method", "GET")
  handler = cfg.get("handler", "json")

  data, content_type = _load_data(cfg, args)
  url = _generate_url(cfg, args)

  accept = cfg.get("accept", "application/json")
  if handler == "binary" and accept == "application/json":
    ext = getattr(args, "format", "png") or "png"
    mime_map = {"svg": "image/svg+xml", "jpg": "image/jpeg"}
    accept = mime_map.get(ext, f"image/{ext}")
  headers = {
      "Content-Type": content_type,
      "Accept": accept,
  }

  if handler == "binary":
    result = _CLIENT.fetch_bytes(url, method=method, headers=headers, data=data)
  else:
    result = _CLIENT.fetch_text(url, method=method, headers=headers, data=data)

  if handler == "json":
    if cfg.get("filterable"):
      result = _filter_pathways(
          result,
          getattr(args, "fdr", None),
          getattr(args, "pvalue", None),
      )
    if getattr(args, "summary", False):
      result = _summarize_result(result)
    data = json.loads(result)
    _write_output(args.output, json.dumps(data, indent=2))
  elif handler == "binary":
    if isinstance(result, str):
      result = result.encode("utf-8")
    _write_output(args.output, result, binary=True)
  elif handler == "csv":
    _write_output(args.output, result)
  elif handler == "text_wrap":
    _write_output(
        args.output,
        json.dumps({cfg["wrap_key"]: result.strip()}, indent=2),
    )
  elif handler == "page_wrap":
    _write_output(
        args.output,
        json.dumps({"page": result}, indent=2),
    )


def _add_common_flags(
    p: argparse.ArgumentParser,
) -> None:
  """Adds common flags shared by analysis subcommands."""
  p.add_argument(
      "--output",
      required=True,
      help="Output file path (required)",
  )
  p.add_argument(
      "--interactors",
      type=bool,
      default=None,
      help="Include interactors",
  )
  p.add_argument(
      "--species",
      type=str,
      default=None,
      help="Species NCBI Taxon ID or name",
  )
  p.add_argument(
      "--include-disease",
      type=bool,
      default=None,
      help="Include disease pathways",
  )
  p.add_argument(
      "--page-size",
      type=int,
      default=None,
      help="Number of results per page",
  )
  p.add_argument(
      "--limit",
      type=int,
      default=None,
      dest="page_size_alias",
      help="Alias for --page-size",
  )
  p.add_argument(
      "--page",
      type=int,
      default=None,
      help="Page number",
  )
  p.add_argument(
      "--offset",
      type=int,
      default=None,
      dest="page_alias",
      help="Alias for --page",
  )
  p.add_argument(
      "--sort-by",
      type=str,
      default=None,
      choices=[
          "NAME",
          "TOTAL_ENTITIES",
          "TOTAL_INTERACTORS",
          "TOTAL_REACTIONS",
          "FOUND_ENTITIES",
          "FOUND_INTERACTORS",
          "FOUND_REACTIONS",
          "ENTITIES_RATIO",
          "ENTITIES_PVALUE",
          "ENTITIES_FDR",
          "REACTIONS_RATIO",
      ],
      help="Sort results by field",
  )
  p.add_argument(
      "--order",
      type=str,
      default=None,
      choices=["ASC", "DESC"],
      help="Sort order",
  )
  p.add_argument(
      "--resource",
      type=str,
      default=None,
      help="Resource filter (TOTAL, UNIPROT, etc.)",
  )
  p.add_argument(
      "--fdr",
      type=float,
      default=None,
      help="Max FDR threshold for filtering",
  )
  p.add_argument(
      "--pvalue",
      type=float,
      default=None,
      help="Max p-value threshold for filtering",
  )


def _add_input_flags(
    p: argparse.ArgumentParser,
) -> None:
  """Adds --data and --file input flags to a subparser."""
  p.add_argument(
      "--data",
      type=str,
      default=None,
      help="Inline data (comma-separated identifiers)",
  )
  p.add_argument(
      "--file",
      type=str,
      default=None,
      help="Path to input file",
  )


def parse_args() -> argparse.Namespace:
  """Parses command-line arguments for the Reactome CLI."""
  parser = argparse.ArgumentParser(
      description="Reactome Analysis Service CLI",
      formatter_class=(argparse.RawDescriptionHelpFormatter),
  )
  sub = parser.add_subparsers(
      dest="command",
      help="Available commands",
  )

  for cfg in COMMANDS:
    p = sub.add_parser(cfg["name"], help=cfg["help"])

    if cfg.get("input_flags"):
      _add_input_flags(p)

    for arg_spec in cfg.get("args", []):
      name = arg_spec["name"]
      kwargs = {k: v for k, v in arg_spec.items() if k != "name"}
      p.add_argument(name, **kwargs)

    if cfg.get("common"):
      _add_common_flags(p)

    p.set_defaults(func=_dispatch, _cfg=cfg)

  return parser.parse_args()


if __name__ == "__main__":
  main_args = parse_args()
  if not main_args.command:
    print(
        "Error: subcommand required. Use --help.",
        file=sys.stderr,
    )
    sys.exit(1)
  main_args.func(main_args)
