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

"""Downloads PDB coordinate files (mmCIF or PDB) from RCSB."""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
# ]
# ///


import argparse
import os
import sys

from polite_http import http_client

CLIENT = http_client.HttpClient("https://files-beta.rcsb.org", qps=5.0)


def sanitize_id(pdb_id: str) -> str:
  """Sanitize PDB ID."""
  pdb_id = pdb_id.lower().strip()
  if len(pdb_id) == 4:
    return f"pdb_0000{pdb_id}"
  return pdb_id


def download_files(args: argparse.Namespace):
  """Downloads coordinate files."""
  ids = [id.strip() for id in args.ids.split(",") if id.strip()]

  if len(ids) > 1_000:
    print(
        "Aborting: this script is not recommended for bulk downloads."
        "**Check with the user**, then consider downloading a copy of all"
        f" {args.format} files using the recommended bulk script at "
        "https://cdn.rcsb.org/wwpdb/docs/BetaArchiveBatchDownloader.py.",
        file=sys.stderr,
    )
    return

  # RCSB bulk download script suggests a higher QPS may be acceptable here (~5).
  estimated_time_secs = len(ids) / 5.0
  print(f"Estimated download time: {estimated_time_secs / 60:.1f} minutes).")

  if not os.path.exists(args.output_dir):
    os.makedirs(args.output_dir, exist_ok=True)

  for pdb_id in ids:
    sanitized_id = sanitize_id(pdb_id)
    shard_chars = sanitized_id[-3:-1]
    ext = "cif" if args.format == "mmcif" else "pdb"

    url = (
        f"/pub/wwpdb/pdb/data/entries/{shard_chars}/{sanitized_id}/"
        f"structures/{sanitized_id}.{ext}.gz"
    )

    output_path = os.path.join(args.output_dir, f"{sanitized_id}.{ext}.gz")

    print(f"Downloading {sanitized_id} from {url}...", file=sys.stderr)

    try:
      content = CLIENT.fetch_bytes(url)
      with open(output_path, "wb") as f:
        f.write(content)
      print(f"Saved to {output_path}", file=sys.stderr)
    except Exception as e:
      print(f"Failed to download {pdb_id}: {e}", file=sys.stderr)


def parse_args() -> argparse.Namespace:
  """Parse command line arguments."""
  parser = argparse.ArgumentParser(description="Download PDB coordinate files")
  parser.add_argument(
      "--format",
      type=str,
      required=True,
      choices=["mmcif", "pdb"],
      help="File format to download (mmcif or pdb)",
  )
  parser.add_argument(
      "--ids",
      type=str,
      required=True,
      help="Comma-separated list of PDB IDs",
  )
  parser.add_argument(
      "--output_dir",
      type=str,
      required=True,
      help="Directory to save files to",
  )
  return parser.parse_args()


if __name__ == "__main__":
  main_args = parse_args()
  download_files(main_args)
