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

"""UniBind API skill wrapper."""

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

UNIBIND_API_PREFIX = "api/v1"
# This has to be the bare domain to support download links
CLIENT = http_client.HttpClient(f"https://unibind.uio.no/", qps=20.0)


def make_request(url: str) -> Any:
  """Makes an HTTP request to the UniBind API using HttpClient."""
  # Enforce output format as JSON if not specified in URL
  if "format=" not in url and ".json" not in url:
    separator = "&" if "?" in url else "?"
    url += f"{separator}format=json"

  return CLIENT.fetch_json(url, timeout=30)


def write_output(data: Any, output_file: str | None = None) -> None:
  """Writes data as JSON to a file or stdout.

  Args:
      data: The data to write.
      output_file: Optional path to an output JSON file. If None, prints to
        stdout.
  """
  if output_file:
    try:
      os.makedirs(os.path.dirname(os.path.abspath(output_file)), exist_ok=True)
      with open(output_file, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2)
      print(f"Output written to: {output_file}", file=sys.stderr)
    except (OSError, TypeError) as e:
      print(f"Error writing to file {output_file}: {e}", file=sys.stderr)
      sys.exit(1)
  else:
    print(json.dumps(data, indent=2))


def download_file(url: str, output_path: str) -> None:
  """Downloads a file from a URL to a local path using HttpClient."""
  data_bytes = CLIENT.fetch_bytes(url, timeout=60)
  with open(output_path, "wb") as f:
    f.write(data_bytes)
  print(f"Downloaded to {output_path} ({os.path.getsize(output_path)} bytes)")


def _build_list_url(
    endpoint: str,
    page: int | None = None,
    page_size: int | None = None,
    order: str | None = None,
    extra_params: dict[str, str] | None = None,
) -> str:
  """Builds a filtered and paginated URL for UniBind list endpoints.

  Args:
      endpoint: The API endpoint name (e.g., 'species').
      page: Optional page number.
      page_size: Optional number of items per page.
      order: Optional ordering string.
      extra_params: Optional dictionary of extra filter parameters.

  Returns:
      The fully constructed URL string.
  """
  params = {}
  if extra_params:
    params.update(extra_params)
  if page:
    params["page"] = page
  if page_size:
    params["page_size"] = page_size
  if order:
    params["order"] = order

  url = f"{UNIBIND_API_PREFIX}/{endpoint}/"
  query_string = urllib.parse.urlencode(params)
  if query_string:
    url += f"?{query_string}"
  return url


def list_species(args: argparse.Namespace) -> None:
  """Lists supported species.

  Args:
      args: Parsed command-line arguments.
  """
  url = _build_list_url(
      "species", page=args.page, page_size=args.page_size, order=args.order
  )
  data = make_request(url)
  write_output(data, getattr(args, "output", None))


def list_collections(args: argparse.Namespace) -> None:
  """Lists collections.

  Args:
      args: Parsed command-line arguments.
  """
  url = _build_list_url(
      "collections", page=args.page, page_size=args.page_size, order=args.order
  )
  data = make_request(url)
  write_output(data, getattr(args, "output", None))


def list_cell_lines(args: argparse.Namespace) -> None:
  """Lists cell lines.

  Args:
      args: Parsed command-line arguments.
  """
  url = _build_list_url(
      "celltypes", page=args.page, page_size=args.page_size, order=args.order
  )
  data = make_request(url)
  write_output(data, getattr(args, "output", None))


def list_tfs(args: argparse.Namespace) -> None:
  """Lists transcription factors.

  Args:
      args: Parsed command-line arguments.
  """
  url = _build_list_url(
      "tfs", page=args.page, page_size=args.page_size, order=args.order
  )
  data = make_request(url)
  write_output(data, getattr(args, "output", None))


def _build_dataset_filters(args: argparse.Namespace) -> dict[str, str]:
  """Extracts dataset filtering parameters from parsed arguments.

  Args:
      args: Parsed command-line arguments.

  Returns:
      A dictionary of filter parameters.
  """
  extra = {}
  filter_keys = [
      "species",
      "tf_name",
      "cell_line",
      "collection",
      "search",
      "biological_condition",
      "data_source",
      "has_pvalue",
      "identifier",
      "jaspar_id",
      "model",
      "summary",
      "threshold_pvalue",
  ]
  for key in filter_keys:
    val = getattr(args, key, None)
    if val is not None:
      extra[key] = str(val)
  return extra


def _print_dataset_list(
    endpoint: str,
    extra: dict[str, str],
    page: int | None,
    page_size: int | None,
    order: str | None,
    output_file: str | None = None,
) -> None:
  """Fetches and prints a paginated list of datasets.

  Args:
      endpoint: The API endpoint (e.g., 'datasets' or 'specific').
      extra: Dictionary of extra filtering parameters.
      page: Optional page number.
      page_size: Optional number of items per page.
      order: Optional ordering string.
      output_file: Optional path to write the output to. Prints to stdout if
        None.
  """
  url = _build_list_url(
      endpoint,
      page=page,
      page_size=page_size,
      order=order,
      extra_params=extra,
  )
  data = make_request(url)

  # Extract dataset_id from URL for convenience
  if "results" in data:
    for res in data["results"]:
      if "url" in res and "dataset_id" not in res:
        # URL format: https://unibind.uio.no/api/v1/{endpoint}/ID/
        res["dataset_id"] = res["url"].rstrip("/").split("/")[-1]

  write_output(data, output_file)


def list_datasets(args: argparse.Namespace) -> None:
  """Lists and filters datasets.

  Args:
      args: Parsed command-line arguments.
  """
  extra = _build_dataset_filters(args)
  _print_dataset_list(
      endpoint="datasets",
      extra=extra,
      page=args.page,
      page_size=args.page_size,
      order=args.order,
      output_file=getattr(args, "output", None),
  )


def list_specific_datasets(args: argparse.Namespace) -> None:
  """Lists and filters profile-specific datasets.

  Args:
      args: Parsed command-line arguments.
  """
  extra = _build_dataset_filters(args)
  _print_dataset_list(
      endpoint="specific",
      extra=extra,
      page=args.page,
      page_size=args.page_size,
      order=args.order,
      output_file=getattr(args, "output", None),
  )


def get_dataset(args: argparse.Namespace) -> None:
  """Retrieves details for a specific dataset.

  Args:
      args: Parsed command-line arguments.
  """
  url = f"{UNIBIND_API_PREFIX}/datasets/{args.dataset_id}/"
  data = make_request(url)
  write_output(data, getattr(args, "output", None))


def download_tfbs(args: argparse.Namespace) -> None:
  """Downloads TFBS BED or FASTA files for a dataset to a local directory.

  Args:
      args: Parsed command-line arguments.
  """
  dataset_id = args.dataset_id
  output_dir = args.output_dir
  file_format = args.file_format

  dataset = make_request(f"{UNIBIND_API_PREFIX}/datasets/{dataset_id}/")
  tfbs_list = dataset.get("tfbs", [])
  if not tfbs_list:
    print("No TFBS entries found for this dataset.", file=sys.stderr)
    sys.exit(1)

  url_key = f"{file_format}_url"
  os.makedirs(output_dir, exist_ok=True)
  downloaded = 0
  for model_group in tfbs_list:
    for model_name, entries in model_group.items():
      if not isinstance(entries, list):
        continue
      for entry in entries:
        url = entry.get(url_key)
        if not url:
          continue
        jaspar_id = entry.get("jaspar_id", "unknown")
        jaspar_ver = entry.get("jaspar_version", "0")
        ext = "bed" if file_format == "bed" else "fa"
        # Truncate names if necessary to stay short, but keep descriptive
        filename = f"{dataset_id}.{jaspar_id}.{jaspar_ver}.{model_name}.{ext}"
        filepath = os.path.join(output_dir, filename)
        download_file(url, filepath)
        downloaded += 1

  if downloaded == 0:
    print(f"No '{url_key}' URLs found in TFBS entries.", file=sys.stderr)
    sys.exit(1)
  print(
      f"\nDownloaded {downloaded} {file_format.upper()} file(s) to {output_dir}"
  )


def _add_pagination_args(parser: argparse.ArgumentParser) -> None:
  """Adds page, page-size, order, and optional output arguments to a parser.

  Args:
      parser: The argparse parser to add arguments to.
  """
  parser.add_argument(
      "--output",
      default=None,
      help="Output JSON file path (default: stdout).",
  )
  parser.add_argument("--page", type=int, help="Page number")
  parser.add_argument("--page-size", type=int, help="Page size (max 1000)")
  parser.add_argument(
      "--order", help="Order by field (prefix with - for descending)"
  )


def _add_dataset_filters(parser: argparse.ArgumentParser) -> None:
  """Adds dataset filtering arguments to a parser.

  Args:
      parser: The argparse parser to add arguments to.
  """
  parser.add_argument("--species", help="Filter by species")
  parser.add_argument("--tf-name", help="Filter by TF name")
  parser.add_argument("--cell-line", help="Filter by cell line")
  parser.add_argument(
      "--collection", help="Filter by collection (e.g., Permissive, Robust)"
  )

  parser.add_argument("--search", help="A search term")
  parser.add_argument(
      "--biological-condition", help="Biological condition or source"
  )
  parser.add_argument("--data-source", help="Source of the data (e.g., ENCODE)")
  parser.add_argument(
      "--has-pvalue",
      help="Select datasets meeting a p-value threshold (true/false)",
  )
  parser.add_argument("--identifier", help="Dataset identifier, e.g. GSE60130")
  parser.add_argument("--jaspar-id", help="JASPAR database profile matrix ID")
  parser.add_argument("--model", help="Prediction model")
  parser.add_argument("--summary", help="Obtain summary of TF and related data")
  parser.add_argument(
      "--threshold-pvalue", help="Threshold applying to p-value filtering"
  )
  _add_pagination_args(parser)


def main() -> None:
  """Parses command-line arguments and executes the selected command."""
  parser = argparse.ArgumentParser(description="UniBind API wrapper skill")
  subparsers = parser.add_subparsers(dest="command", required=True)

  # list_species
  p_sp = subparsers.add_parser("list_species", help="List supported species")
  _add_pagination_args(p_sp)
  p_sp.set_defaults(func=list_species)

  # list_collections
  p_col = subparsers.add_parser("list_collections", help="List collections")
  _add_pagination_args(p_col)
  p_col.set_defaults(func=list_collections)

  # list_cell_lines
  p_ct = subparsers.add_parser("list_cell_lines", help="List cell lines")
  _add_pagination_args(p_ct)
  p_ct.set_defaults(func=list_cell_lines)

  # list_tfs
  p_tf = subparsers.add_parser("list_tfs", help="List transcription factors")
  _add_pagination_args(p_tf)
  p_tf.set_defaults(func=list_tfs)

  # list_datasets
  p_list_ds = subparsers.add_parser(
      "list_datasets", help="List and filter datasets"
  )
  _add_dataset_filters(p_list_ds)
  p_list_ds.set_defaults(func=list_datasets)

  # list_specific_datasets
  p_list_spec = subparsers.add_parser(
      "list_specific_datasets", help="List and filter profile-specific datasets"
  )
  _add_dataset_filters(p_list_spec)
  p_list_spec.set_defaults(func=list_specific_datasets)

  # get_dataset
  p_get_ds = subparsers.add_parser("get_dataset", help="Get dataset details")
  p_get_ds.add_argument(
      "dataset_id", help="Dataset ID (e.g., EXP030726.neural_stem_cells.SMAD3)"
  )
  p_get_ds.add_argument(
      "--output",
      default=None,
      help="Output JSON file path (default: stdout).",
  )
  p_get_ds.set_defaults(func=get_dataset)

  # download_tfbs
  p_dl = subparsers.add_parser(
      "download_tfbs", help="Download TFBS BED/FASTA files for a dataset"
  )
  p_dl.add_argument("dataset_id", help="Dataset ID")
  p_dl.add_argument(
      "--output-dir", required=True, help="Directory to save downloaded files"
  )
  p_dl.add_argument(
      "--format",
      dest="file_format",
      choices=["bed", "fasta"],
      default="bed",
      help="File format to download (default: bed)",
  )
  p_dl.set_defaults(func=download_tfbs)

  args = parser.parse_args()
  if hasattr(args, "func"):
    args.func(args)
  else:
    parser.print_help()


if __name__ == "__main__":
  main()
