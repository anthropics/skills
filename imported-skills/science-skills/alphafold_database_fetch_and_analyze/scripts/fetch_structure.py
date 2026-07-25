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

"""Fetches AlphaFold structure files (mmCIF + PAE) for a UniProt ID."""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
# ]
# ///

import argparse
import json
import os
import sys
from polite_http import http_client

CLIENT = http_client.HttpClient("https://alphafold.ebi.ac.uk", qps=1.0)


def fetch_structure(uniprot_id, output_dir):
  """Downloads the mmCIF file and PAE JSON for a given UniProt ID from AFDB."""
  uniprot_id = uniprot_id.strip().upper()
  api_url = f"https://alphafold.ebi.ac.uk/api/prediction/{uniprot_id}"
  is_fragment = False

  os.makedirs(output_dir, exist_ok=True)
  print(f"[*] Requesting AlphaFold data for UniProt ID: {uniprot_id}")

  try:
    data = CLIENT.fetch_json(api_url)
  except http_client.HttpError as e:
    if e.status_code == 404:
      print(
          f"\n[!] Error: UniProt ID '{uniprot_id}' was not found in"
          " the AlphaFold Database."
      )
      print(
          "    Please double-check the ID for typos, or verify it"
          " has an AFDB entry."
      )
    else:
      print(f"[!] HTTP error fetching API data: {e}")
    sys.exit(1)

  if not data:
    print(f"[!] No AlphaFold data returned for {uniprot_id}")
    sys.exit(1)

  # The API may return multiple entries (e.g. isoforms) for a single
  # UniProt ID. Prefer the canonical entry whose accession matches exactly.
  entry = None
  for e in data:
    if e.get("uniprotAccession") == uniprot_id:
      entry = e
      break
  # If no canonical entry exists (common for very large proteins like
  # Dystrophin), fall back to the longest available isoform so the user
  # gets the most complete structure.
  if entry is None:
    entry = max(data, key=lambda e: e.get("sequenceEnd", 0))
    entry_acc = entry.get("uniprotAccession", "unknown")
    entry_len = entry.get("sequenceEnd", 0)
    print(
        "[!] WARNING: No canonical AFDB entry found for"
        f" '{uniprot_id}'. Using longest available isoform"
        f" '{entry_acc}' ({entry_len} amino acids) instead."
        " The full-length protein may not be available in AFDB."
    )

  max_seq_len = max((e.get("sequenceEnd", 0) for e in data), default=0)
  if max_seq_len > 2700:
    print(
        f"[!] WARNING: Protein {uniprot_id} is massive"
        f" ({max_seq_len} amino acids). Only the first entry has"
        " been downloaded. The full protein may span many more"
        " fragments in AFDB."
    )
    is_fragment = True

  entry_acc = entry.get("uniprotAccession", uniprot_id)
  metadata_filename = f"AF-{entry_acc}-F1-metadata.json"
  metadata_path = os.path.join(output_dir, metadata_filename)
  with open(metadata_path, "w") as f:
    json.dump(entry, f, indent=2)
  print(f"  -> Saved API metadata to: {metadata_path}")

  cif_url = entry.get("cifUrl")
  pae_url = entry.get("paeDocUrl")

  urls_to_fetch = []
  if cif_url:
    urls_to_fetch.append(cif_url)
  if pae_url:
    urls_to_fetch.append(pae_url)

  success_count = 0

  for url in urls_to_fetch:
    filename = url.split("/")[-1]
    file_path = os.path.join(output_dir, filename)

    print(f"  -> Fetching {filename}...")

    try:
      file_bytes = CLIENT.fetch_bytes(url)
      with open(file_path, "wb") as f:
        f.write(file_bytes)

      print(f"     [+] Saved to: {file_path}")
      success_count += 1

    except http_client.HttpError as e:
      if e.status_code == 404:
        print(f"     [!] Error 404: {filename} not found.")
      else:
        print(f"     [!] Download error: {e}")

  if success_count == 0:
    print(
        f"\n[!] Failed to download any data for {uniprot_id}. Please check"
        " the ID."
    )
    sys.exit(1)
  else:
    print(
        f"\n[*] Successfully downloaded {success_count}/{len(urls_to_fetch)}"
        " files."
    )

  return {
      "uniprot_id": uniprot_id,
      "output_dir": output_dir,
      "is_fragment": is_fragment,
      "files_downloaded": success_count,
      "metadata_file": metadata_path,
  }


if __name__ == "__main__":
  parser = argparse.ArgumentParser(
      description="Download AlphaFold structure files for a UniProt ID"
  )
  parser.add_argument(
      "uniprot_id", help="The UniProt ID (e.g., P04637 or A0A1B0GX81)"
  )
  parser.add_argument(
      "-o",
      "--output-dir",
      help="Output directory to save the files (required)",
      required=True,
  )

  args = parser.parse_args()

  fetch_structure(args.uniprot_id, args.output_dir)
