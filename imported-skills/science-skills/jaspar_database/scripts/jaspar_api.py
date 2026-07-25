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

"""JASPAR API skill wrapper."""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
# ]
# ///

import argparse
import math
import re
import sys
import urllib.parse
import urllib.request

from polite_http import http_client

JASPAR_URL = "https://jaspar.elixir.no/api/v1/"
_CLIENT = http_client.HttpClient(JASPAR_URL, qps=10)
_MAX_OUTPUT_CHARS = 50_000


def _print_text(text):
  """Prints text, truncating if it exceeds _MAX_OUTPUT_CHARS."""
  if len(text) > _MAX_OUTPUT_CHARS:
    print(text[:_MAX_OUTPUT_CHARS])
    print(
        f"\n... [truncated: {len(text)} chars"
        f" total, showing first {_MAX_OUTPUT_CHARS}]"
    )
  else:
    print(text)


_VALID_FORMATS = (
    "json",
    "jsonp",
    "jaspar",
    "meme",
    "transfac",
    "pfm",
    "yaml",
)


def validate_matrix_id(matrix_id: str):
  """Validates the format of a JASPAR Matrix ID."""
  if not re.match(r"^MA\d{4}\.\d+$", matrix_id):
    print(
        f"Error: Invalid Matrix ID format '{matrix_id}'. Expected format is"
        " 'MA0488.2'.",
        file=sys.stderr,
    )
    print(
        "Hint: If you have a gene symbol (e.g., 'JUN'), you must first use the"
        " 'resolve_tf_id' command.",
        file=sys.stderr,
    )
    sys.exit(1)


def resolve_tf_id(name: str, tax_id: str):
  """Resolves a TF name to a JASPAR Matrix ID."""
  url = f"{JASPAR_URL}matrix/?name={urllib.parse.quote(name)}&tax_id={tax_id}"
  print("Request url: ", url)
  data = _CLIENT.fetch_json(url)

  if not data or "results" not in data or len(data["results"]) == 0:
    print(f"No results found for TF '{name}' in tax_id {tax_id}")
    return

  print(
      f"Found {len(data['results'])} matching Matrix IDs for '{name}' (tax_id:"
      f" {tax_id}):\n"
  )
  for r in data["results"]:
    matrix_id = r.get("matrix_id")
    tf_name = r.get("name")
    family = r.get("family", [])
    species = r.get("species", [])

    family_str = ", ".join(family) if isinstance(family, list) else family
    species_str = (
        ", ".join([str(s.get("tax_id")) for s in species])
        if species
        else "Unknown"
    )

    print(f"- Matrix ID: {matrix_id}")
    print(f"  Name: {tf_name}")
    print(f"  Family: {family_str}")
    print(f"  Taxonomies: {species_str}\n")


def infer_from_sequence(sequence):
  """Infers potential TF binding matrices from a raw protein sequence."""
  url = f"{JASPAR_URL}infer/{urllib.parse.quote(sequence)}/"
  print("Request url: ", url)
  data = _CLIENT.fetch_json(url)

  if not data or "results" not in data or not data["results"]:
    print("No corresponding matrices inferred from sequence.")
    return

  print(f"Inferred {len(data['results'])} potential TF profiles:")
  for r in data["results"]:
    mid = r.get("matrix_id")
    name = r.get("name")
    print(f"- {mid} ({name}): E-value {r.get('evalue')}")


def get_tffm(tffm_id):
  """Gets TF Flexible Model (TFFM) detail information."""
  url = f"{JASPAR_URL}tffm/{urllib.parse.quote(tffm_id)}/"
  print("Request url: ", url)
  data = _CLIENT.fetch_json(url)
  print(dict_to_yaml(data))


def get_tf_motif(matrix_id, fmt="json"):
  """Gets the Position Frequency Matrix (PFM) for a specific TF."""
  validate_matrix_id(matrix_id)
  url = f"{JASPAR_URL}matrix/{matrix_id}/"
  if fmt != "json":
    url += f"?format={fmt}"
    print("Request url: ", url)
    _print_text(_CLIENT.fetch_text(url))
    return
  print("Request url: ", url)
  data = _CLIENT.fetch_json(url)

  print(f"Matrix ID: {data.get('matrix_id')}")
  print(f"Name: {data.get('name')}")
  print("PFM:")
  pfm = data.get("pfm", {})
  for base in ["A", "C", "G", "T"]:
    if base in pfm:
      vals = " ".join([str(x) for x in pfm[base]])
      print(f"{base} [ {vals} ]")


def get_tf_metadata(matrix_id, fmt="json"):
  """Gets metadata for a specific TF."""
  validate_matrix_id(matrix_id)
  url = f"{JASPAR_URL}matrix/{matrix_id}/"
  if fmt != "json":
    url += f"?format={fmt}"
    print("Request url: ", url)
    _print_text(_CLIENT.fetch_text(url))
    return
  print("Request url: ", url)
  data = _CLIENT.fetch_json(url)
  print(dict_to_yaml(data))


def get_tf_pwm(matrix_id, pseudocount=0.8):
  """Computes a Position Weight Matrix (PWM) from a PFM.

  Fetches the raw PFM for the given matrix ID and converts it to log-odds
  scores (in bits) using the standard two-step conversion:

    1. PPM[b][i] = (PFM[b][i] + pseudocount) / (N_i + 4 * pseudocount)
    2. PWM[b][i] = log2( PPM[b][i] / background[b] )

  where N_i is the total count at position i and background is uniform (0.25).

  The --pseudocount flag is a *per-base* pseudocount (default 0.8). This is
  equivalent to a total pseudocount B = 4 * pseudocount = 3.2 in the textbook
  formulation: PPM[b][i] = (count + B * p_bg) / (N + B), with uniform p_bg.

  Args:
    matrix_id: The JASPAR Matrix ID.
    pseudocount: The per-base pseudocount to use (default 0.8).
  """
  validate_matrix_id(matrix_id)
  url = f"{JASPAR_URL}matrix/{matrix_id}/"
  print("Request url: ", url)
  data = _CLIENT.fetch_json(url)

  pfm = data.get("pfm", {})
  if not pfm:
    print(f"Error: No PFM data found for {matrix_id}.", file=sys.stderr)
    sys.exit(1)

  bases = ["A", "C", "G", "T"]
  num_positions = len(pfm.get("A", []))
  background = 0.25

  print(f"Matrix ID: {data.get('matrix_id')}")
  print(f"Name: {data.get('name')}")
  print(f"Pseudocount: {pseudocount}")
  print(f"Background: {background} (uniform)")
  print(f"Positions: {num_positions}")
  print("PWM (log2 odds):")

  for base in bases:
    if base not in pfm:
      continue
    scores = []
    for i in range(num_positions):
      n_i = sum(pfm[b][i] for b in bases if b in pfm)
      freq = (pfm[base][i] + pseudocount) / (n_i + 4 * pseudocount)
      score = math.log2(freq / background)
      scores.append(f"{score:+.4f}")
    print(f"{base} [ {' '.join(scores)} ]")


def dict_to_yaml(d, indent=0):
  """Converts a dictionary to a YAML-like string."""
  res = ""
  for k, v in d.items():
    if isinstance(v, dict):
      res += f"{' ' * indent}{k}:\n{dict_to_yaml(v, indent + 2)}"
    elif isinstance(v, list):
      res += f"{' ' * indent}{k}: {', '.join([str(x) for x in v])}\n"
    else:
      res += f"{' ' * indent}{k}: {v}\n"
  return res


def main():
  parser = argparse.ArgumentParser(description="JASPAR API wrapper skill")
  subparsers = parser.add_subparsers(dest="command", required=True)

  # resolve_tf_id
  p_res = subparsers.add_parser("resolve_tf_id")
  p_res.add_argument("--name", required=True)
  p_res.add_argument("--tax-id", required=True, type=int)

  # get_tf_motif
  p_mot = subparsers.add_parser("get_tf_motif")
  p_mot.add_argument("--matrix-id", required=True)
  p_mot.add_argument(
      "--format",
      default="json",
      choices=_VALID_FORMATS,
      help="Output format (default: json)",
  )

  # get_tf_metadata
  p_meta = subparsers.add_parser("get_tf_metadata")
  p_meta.add_argument("--matrix-id", required=True)
  p_meta.add_argument(
      "--format",
      default="json",
      choices=_VALID_FORMATS,
      help="Output format (default: json)",
  )

  # get_tf_pwm
  p_pwm = subparsers.add_parser("get_tf_pwm")
  p_pwm.add_argument("--matrix-id", required=True)
  p_pwm.add_argument(
      "--pseudocount",
      type=float,
      default=0.8,
      help="Pseudocount for PWM computation (default: 0.8)",
  )

  # infer_from_sequence
  p_inf = subparsers.add_parser("infer_from_sequence")
  p_inf.add_argument("--sequence", required=True, help="Raw protein sequence")

  # get_tffm
  p_tffm = subparsers.add_parser("get_tffm")
  p_tffm.add_argument("--tffm-id", required=True)

  args = parser.parse_args()

  if args.command == "resolve_tf_id":
    resolve_tf_id(args.name, args.tax_id)
  elif args.command == "get_tf_motif":
    get_tf_motif(args.matrix_id, fmt=args.format)
  elif args.command == "get_tf_metadata":
    get_tf_metadata(args.matrix_id, fmt=args.format)
  elif args.command == "get_tf_pwm":
    get_tf_pwm(args.matrix_id, pseudocount=args.pseudocount)
  elif args.command == "infer_from_sequence":
    infer_from_sequence(args.sequence)
  elif args.command == "get_tffm":
    get_tffm(args.tffm_id)


if __name__ == "__main__":
  main()
