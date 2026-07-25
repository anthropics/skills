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

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
# ]
# ///

"""Shared utilities for OLS skill scripts.

Provides common functions for HTTP requests with retry logic,
JSON output handling, and OBO ID to IRI conversion.
"""

from __future__ import annotations

import json
import sys
from typing import Any
import urllib.parse

from polite_http import http_client

RATE_LIMIT_DELAY = 0.2
MAX_RETRIES = 10
BASE_URL = "https://www.ebi.ac.uk/ols4/api"
CLIENT = http_client.HttpClient(BASE_URL, qps=5.0)

OBO_PREFIX_TO_ONTOLOGY: dict[str, str] = {
    "GO": "go",
    "DOID": "doid",
    "EFO": "efo",
    "HP": "hp",
    "CHEBI": "chebi",
    "MONDO": "mondo",
    "NCIT": "ncit",
    "CL": "cl",
    "UBERON": "uberon",
    "SO": "so",
    "PR": "pr",
    "PATO": "pato",
    "MP": "mp",
    "OBI": "obi",
    "BFO": "bfo",
    "IAO": "iao",
    "ENVO": "envo",
    "PO": "po",
    "CLO": "clo",
    "DUO": "duo",
}


def write_output(data: dict[str, Any], output_path: str | None):
  """Write `data` as indented JSON to `output_path`, or print to stdout."""
  text = json.dumps(data, indent=2)
  if output_path:
    with open(output_path, "w") as f:
      f.write(text)
    print(f"Results saved to {output_path}", file=sys.stderr)
  else:
    print(text)


def obo_id_to_iri(obo_id: str) -> str:
  """Convert an OBO-style ID (e.g. 'GO:0005634') to its canonical IRI."""
  return "http://purl.obolibrary.org/obo/" + obo_id.replace(":", "_")


def double_encode_iri(iri: str) -> str:
  """Double-URL-encode an IRI for use in OLS API path segments."""
  return urllib.parse.quote(urllib.parse.quote(iri, safe=""), safe="")


def resolve_ontology(obo_id: str, ontology: str | None) -> str:
  """Return the ontology slug from an explicit value or the OBO ID prefix."""
  if ontology:
    return ontology.lower()
  prefix = obo_id.split(":")[0].upper()
  if prefix in OBO_PREFIX_TO_ONTOLOGY:
    return OBO_PREFIX_TO_ONTOLOGY[prefix]
  return prefix.lower()


def error_exit(message: str, output_path: str | None = None):
  """Write a JSON error object and exit with status 1."""
  write_output({"status": "error", "message": message}, output_path)
  sys.exit(1)
