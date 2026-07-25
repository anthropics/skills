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

"""Quick protein homologue search via ColabFold MMseqs2 API.

Submits a protein sequence to the ColabFold MMseqs2 server, downloads the
resulting MSA archive, parses the A3M alignment headers, and writes a
Markdown-formatted table of sequence homologues sorted by E-value to an
output file specified via the required --output flag.
"""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
# ]
# ///

import argparse
import json
import os
import shutil
import sys
import tarfile
import tempfile
import time
import urllib.parse

from polite_http import http_client

MAX_ALIGNMENT_HITS = 300
POLLING_TIMEOUT = 15 * 60  # 15 minutes.
COLABFOLD_HOST = "https://api.colabfold.com"
FASTA_COLUMNS = [
    "target",
    "bit_score",
    "identity",
    "e_value",
    "q_start",
    "q_end",
    "q_len",
    "t_start",
    "t_end",
    "t_len",
]
CLIENT = http_client.HttpClient(COLABFOLD_HOST, qps=2)


def read_sequence(query_input, tty=None):
  """Read sequence from a file path or raw string."""
  if os.path.isfile(query_input):
    print(f"[*] Reading sequence from file: {query_input}")
    if tty:
      print(f"[*] Reading sequence from file: {query_input}", file=tty)
    with open(query_input, "r") as f:
      sequence = f.read().strip()
      if sequence.startswith(">"):
        print("[*] Sequence is in FASTA format")
        if tty:
          print("[*] Sequence is in FASTA format", file=tty)
        sequence = "".join(sequence.split("\n")[1:])  # Remove FASTA header
      else:
        print("[*] Sequence is in raw format")  # No further processing needed
        if tty:
          print("[*] Sequence is in raw format", file=tty)
  else:
    print("[*] Using raw sequence string provided via command line.")
    sequence = query_input.strip()

  if not sequence:
    print("[!] Error: Empty sequence provided.")
    if tty:
      print("[!] Error: Empty sequence provided.", file=tty)
    sys.exit(1)

  return sequence


def parse_a3m(file_path, q_len):
  """Parse ColabFold-annotated A3M headers into hit dictionaries."""
  homologues = []

  with open(file_path, "r") as f:
    for line in f:
      if not line.startswith(">"):
        continue

      parts = line.strip().split()

      # Skip query header (no stat columns) or malformed lines
      if len(parts) < 10:
        continue

      try:
        hit = dict(zip(FASTA_COLUMNS, parts, strict=True))
        for col in ["q_start", "q_end", "q_len", "t_start", "t_end", "t_len"]:
          hit[col] = int(hit[col])
        for col in ["bit_score", "identity", "e_value"]:
          hit[col] = float(hit[col])

        # Query Coverage
        if q_len > 0 and hit["q_end"] > hit["q_start"]:
          aligned_residues = hit["q_end"] - hit["q_start"] + 1
          cov = min((aligned_residues / q_len) * 100, 100.0)
        else:
          cov = 0.0

        # Alignment length (target span)
        if hit["t_end"] > hit["t_start"]:
          aln_len = hit["t_end"] - hit["t_start"] + 1
        else:
          aln_len = 0

        hit |= {
            "target_id": hit["target"][1:],  # Strip leading '>'
            "q_cov": cov,
            "aln_len": aln_len,
        }
        homologues.append(hit)
      except (ValueError, IndexError):
        print(
            f"[!] Warning: Skipping malformed hit: {line.strip()}",
            file=sys.stderr,
        )
        continue

  homologues.sort(key=lambda x: x["e_value"])
  return homologues


def search_mmseqs2(query_input, output_md, json_file, include_mgnify=False):
  """Submit sequence to ColabFold MMseqs2, parse results, write output."""
  # Redirect all print output to the .md file
  original_stdout = sys.stdout
  md_file = open(output_md, "w")
  sys.stdout = md_file

  try:
    _run_mmseqs2(query_input, json_file, include_mgnify, tty=original_stdout)
  finally:
    sys.stdout = original_stdout
    md_file.close()

  print(f"[*] Results saved to: {output_md}")
  if json_file:
    print(f"[*] Results saved to: {json_file}")
  print("...done!")


def _run_mmseqs2(query_input, json_file, include_mgnify, tty):
  """Internal: runs the actual MMseqs2 search with print going to file."""
  sequence = read_sequence(query_input, tty=tty)
  q_len = len(sequence)

  # --- 1. Submit ---
  print("[*] Search method: MMseqs2 (ColabFold API)")
  print(
      f"[*] Submitting sequence ({q_len} residues) to ColabFold MMseqs2 API..."
  )
  print("[*] Search method: MMseqs2 (ColabFold API)", file=tty)

  query_fasta = f">Query_1\n{sequence}\n"
  data = urllib.parse.urlencode({
      "q": query_fasta,
      "mode": "all",
  }).encode("ascii")

  try:
    ticket = CLIENT.fetch_json(
        f"{COLABFOLD_HOST}/ticket/msa", method="POST", data=data, timeout=60
    )
  except (
      http_client.HttpError,
      TimeoutError,
      RuntimeError,
  ) as e:
    print(f"[!] MMseqs2 API Submission Failed: {e}")
    print(f"[!] MMseqs2 API Submission Failed: {e}", file=tty)
    sys.exit(2)

  ticket_id = ticket.get("id")
  if not ticket_id:
    status = ticket.get("status", "UNKNOWN")
    if status == "RATELIMIT":
      print("[!] MMseqs2 rate limit hit on submission.")
      print("[!] MMseqs2 rate limit hit on submission.", file=tty)
    else:
      print(f"[!] MMseqs2 submission failed: {ticket}")
      print(f"[!] MMseqs2 submission failed: {ticket}", file=tty)
    sys.exit(2)

  print(f"[*] Ticket ID generated: {ticket_id}")
  print(f"[*] Ticket ID: {ticket_id}", file=tty)

  # --- 2. Poll ---
  print("[*] Polling server for completion...")
  print("[*] Polling server for completion...", file=tty)

  start_time = time.monotonic()
  while time.monotonic() - start_time < POLLING_TIMEOUT:
    state = CLIENT.fetch_json(
        f"{COLABFOLD_HOST}/ticket/{ticket_id}", timeout=20
    ).get("status", "UNKNOWN")

    # States below are taken from the original ColabFold code:
    # https://github.com/sokrypton/ColabFold/blob/main/colabfold/colabfold.py:201
    if state == "COMPLETE":
      print("\n[*] Job finished successfully!")
      print("\n[*] Job finished successfully!", file=tty)
      break

    elif state in ("ERROR", "MAINTENANCE"):
      print(f"[!] MMseqs2 job failed with status: {state}")
      print(f"[!] MMseqs2 job failed with status: {state}", file=tty)
      sys.exit(2)

    elif state == "RATELIMIT":
      print("[!] Rate limit hit. Waiting...")
      print("[!] Rate limit hit. Waiting...", file=tty)

    elif state in ("PENDING", "RUNNING", "UNKNOWN"):
      sys.stdout.write(".")
      sys.stdout.flush()
      tty.write(".")
      tty.flush()
    time.sleep(10)

  else:
    print("[!] Polling timed out.")
    print("[!] Polling timed out.", file=tty)
    sys.exit(2)

  # --- 3. Download & Extract ---
  print("[*] Downloading and extracting MSA files...")
  tmp_dir = tempfile.mkdtemp(prefix="mmseqs2_")
  tar_path = os.path.join(tmp_dir, f"{ticket_id}.tar.gz")

  try:
    raw_data = CLIENT.fetch_bytes(
        f"{COLABFOLD_HOST}/result/download/{ticket_id}", timeout=120
    )
    with open(tar_path, "wb") as f:
      f.write(raw_data)

    with tarfile.open(tar_path, "r:gz") as tar:
      for member in tar.getmembers():
        if member.name.startswith("/") or ".." in member.name:
          continue
        tar.extract(member, path=tmp_dir)

    os.remove(tar_path)
  except (
      http_client.HttpError,
      TimeoutError,
      RuntimeError,
      OSError,
      tarfile.ReadError,
  ) as e:
    print(f"[!] Failed to download/extract results: {e}")
    print(f"[!] Failed to download/extract results: {e}", file=tty)
    shutil.rmtree(tmp_dir, ignore_errors=True)
    sys.exit(2)

  # --- 4. Parse A3M files ---
  all_homologues = []

  uniref_path = os.path.join(tmp_dir, "uniref.a3m")
  if os.path.exists(uniref_path):
    uniref_hits = parse_a3m(uniref_path, q_len)
    print(f"[*] Parsed {len(uniref_hits)} hits from uniref.a3m")
    all_homologues.extend(uniref_hits)
  else:
    print("[!] Warning: uniref.a3m not found in results archive.")

  if include_mgnify:
    mgnify_path = os.path.join(tmp_dir, "bfd.mgnify30.metaeuk30.smag30.a3m")
    if os.path.exists(mgnify_path):
      mgnify_hits = parse_a3m(mgnify_path, q_len)
      print(f"[*] Parsed {len(mgnify_hits)} hits from mgnify a3m")
      all_homologues.extend(mgnify_hits)
    else:
      print("[!] Warning: mgnify a3m file not found in results archive.")
      print(
          "[!] Warning: mgnify a3m file not found in results archive.", file=tty
      )

  # Cleanup temp directory
  shutil.rmtree(tmp_dir, ignore_errors=True)

  if not all_homologues:
    print("[!] No homologues found.")
    print("[!] No homologues found.", file=tty)
    sys.exit(0)

  # Sort combined results by E-value, take top hits
  all_homologues.sort(key=lambda x: x["e_value"])
  all_homologues = all_homologues[:MAX_ALIGNMENT_HITS]

  # --- 5. Save JSON ---
  if json_file:
    with open(json_file, "w") as f:
      json.dump(all_homologues, f, indent=4)
    print(f"[*] JSON results successfully saved to: {json_file}")

  # --- 6. Output Markdown Table ---
  print(f"\n### Top {len(all_homologues)} Sequence Homologues (MMseqs2)")
  print("| Target ID | Q-Cov | E-value | Seq Identity(%) | Aln Length |")
  print("|---|---|---|---|---|")

  for hit in all_homologues:
    target_id = hit["target_id"]
    q_cov = f"{hit['q_cov']:.1f}%"
    e_value = f"{hit['e_value']:.2e}"
    identity = f"{hit['identity'] * 100:.1f}%"
    aln_len = str(hit["aln_len"])

    print(f"| {target_id} | {q_cov} | {e_value} | {identity} | {aln_len} |")


def main():
  parser = argparse.ArgumentParser(
      description=(
          "Quick protein homologue search via ColabFold MMseqs2 API. "
          "Exits with code 2 on API failures to signal fallback to BLAST."
      )
  )
  parser.add_argument(
      "query_input", help="Path to a FASTA file or raw sequence string"
  )
  parser.add_argument(
      "-o",
      "--output",
      required=True,
      help="Path to save the output Markdown (.md) file (required)",
  )
  parser.add_argument(
      "-j",
      "--json",
      help="Path to save the output JSON file (optional)",
      default=None,
  )
  parser.add_argument(
      "--include-mgnify",
      action="store_true",
      help="Also parse and include hits from the mgnify/environmental database",
  )
  args = parser.parse_args()

  print(f"[*] Output: {args.output}")
  if args.json:
    print(f"[*] Output: {args.json}")

  search_mmseqs2(args.query_input, args.output, args.json, args.include_mgnify)


if __name__ == "__main__":
  main()
