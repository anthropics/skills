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

"""Runs EBI BLAST for a FASTA file or raw sequence string against UniProt.

Writes a Markdown-formatted results table to the file specified by the
required --output flag. Optionally saves raw JSON via -j/--json.
"""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
#   "python-dotenv",
# ]
# ///

import argparse
import json
import os
import sys
import time
import urllib.parse

import dotenv
from polite_http import http_client

ALLOWED_DATABASES = [
    "uniprotkb",
    "uniprotkb_swissprot",
    "uniprotkb_swissprotsv",
    "uniprotkb_reference_proteomes",
    "uniprotkb_trembl",
    "uniprotkb_refprotswissprot",
    "uniprotkb_archaea",
    "uniprotkb_arthropoda",
    "uniprotkb_bacteria",
    "uniprotkb_complete_microbial_proteomes",
    "uniprotkb_eukaryota",
    "uniprotkb_fungi",
    "uniprotkb_human",
    "uniprotkb_mammals",
    "uniprotkb_nematoda",
    "uniprotkb_rodents",
    "uniprotkb_vertebrates",
    "uniprotkb_viridiplantae",
    "uniprotkb_viruses",
    "uniprotkb_enzyme",
    "uniprotkb_covid19",
    "uniref100",
    "uniref90",
    "uniref50",
    "pdb",
]

MAX_ALIGNMENT_HITS = 300
DEFAULT_EVALUE = 1000
POLLING_TIMEOUT = 15 * 60  # 15 minutes.
BASE_URL = "https://www.ebi.ac.uk/Tools/services/rest/ncbiblast"
CLIENT = http_client.HttpClient(BASE_URL, qps=2)


def search_uniprot(query_input, output_md, json_file, databases):
  """Runs EBI BLAST search, writes results to output files."""
  # Redirect all print output to the .md file
  original_stdout = sys.stdout
  with open(output_md, "w") as md_file:
    sys.stdout = md_file
    try:
      _run_blast(query_input, json_file, databases, tty=original_stdout)
    finally:
      sys.stdout = original_stdout

  print(f"[*] Results saved to: {output_md}")
  if json_file:
    print(f"[*] Results saved to: {json_file}")
  print("...done!")


def _run_blast(query_input, json_file, databases, tty):
  """Internal: runs the actual BLAST search with print going to file."""

  # Process and validate the databases
  selected_dbs = [db.strip().lower() for db in databases.split(",")]
  invalid_dbs = [db for db in selected_dbs if db not in ALLOWED_DATABASES]

  if invalid_dbs:
    print(f"[!] Error: Invalid database(s) provided: {', '.join(invalid_dbs)}")
    print(f"[*] Allowed databases are: {', '.join(ALLOWED_DATABASES)}")
    print(
        f"[!] Error: Invalid database(s) provided: {', '.join(invalid_dbs)}",
        file=tty,
    )
    sys.exit(1)

  # Determine if input is a file path or a raw sequence string
  if os.path.isfile(query_input):
    print(f"[*] Reading sequence from file: {query_input}")
    with open(query_input, "r") as f:
      sequence = f.read().strip()
      # If it's a fasta file with a header, skip the header line
      if sequence.startswith(">"):
        sequence = "".join(sequence.split("\n")[1:])
  else:
    print("[*] Using raw sequence string provided via command line.")
    sequence = query_input.strip()

  if not sequence:
    print("[!] Error: Empty sequence provided.")
    print("[!] Error: Empty sequence provided.", file=tty)
    sys.exit(1)

  # Calculate query length for later Q-Cov math
  q_len = len(sequence)

  print("[*] Search method: EBI BLAST")
  print(f"[*] Submitting sequence ({q_len} residues) to EBI NCBI BLAST API...")
  print(f"[*] Searching databases: {', '.join(selected_dbs)}")
  print(
      f"[*] Search method: EBI BLAST — databases: {', '.join(selected_dbs)}",
      file=tty,
  )

  # 1. Submit Job
  url_run = f"{BASE_URL}/run"
  params = {
      "program": "blastp",
      "stype": "protein",
      "sequence": sequence,
      "database": ",".join(selected_dbs),
  }
  user_email = os.environ.get("USER_EMAIL")
  if user_email:
    params["email"] = user_email
  else:
    print(
        "[!] Warning: USER_EMAIL environment variable not set. Request may"
        " fail."
    )
  data = urllib.parse.urlencode(params).encode("utf-8")
  try:
    job_id = CLIENT.fetch_text(url_run, method="POST", data=data).strip()
    print(f"[*] Job ID generated: {job_id}")
    print(f"[*] Job ID: {job_id}", file=tty)
  except (
      http_client.HttpError,
      TimeoutError,
      RuntimeError,
      IOError,
  ) as e:
    print(f"[!] API Submission Failed: {e}")
    print(f"[!] API Submission Failed: {e}", file=tty)
    sys.exit(1)
  # 2. Poll the server until the search finishes
  print("[*] Polling server for completion (this may take a few minutes)...")
  print("[*] Polling server for completion...", file=tty)
  url_status = f"{BASE_URL}/status/{job_id}"

  start_time = time.monotonic()
  while time.monotonic() - start_time < POLLING_TIMEOUT:

    try:
      status = CLIENT.fetch_text(url_status, timeout=20).strip()

      if status == "FINISHED":
        print("\n[*] Job marked as FINISHED.")
        print("\n[*] Job marked as FINISHED.", file=tty)
        break
      elif status in ["ERROR", "FAILURE", "NOT_FOUND"]:
        print(f"\n[!] BLAST job failed with status: {status}")
        print(f"\n[!] BLAST job failed with status: {status}", file=tty)
        sys.exit(1)

      sys.stdout.write(".")
      sys.stdout.flush()
      tty.write(".")
      tty.flush()
      time.sleep(30)

    except (
        http_client.HttpError,
        TimeoutError,
        RuntimeError,
    ) as e:
      print(f"\n[!] Polling error: {e}")
      print(f"\n[!] Polling error: {e}", file=tty)
      sys.exit(1)

  else:
    print("\n[!] Polling timed out.")
    print("\n[!] Polling timed out.", file=tty)
    sys.exit(1)

  time.sleep(3)

  # 3. Fetch and format the results
  print("\n[*] Job complete. Fetching results...\n")
  try:
    res = CLIENT.fetch_json(f"{BASE_URL}/result/{job_id}/json", timeout=60)
  except (
      http_client.HttpError,
      TimeoutError,
      RuntimeError,
      json.JSONDecodeError,
      IOError,
  ) as e:
    print(f"[!] Failed to fetch or parse results: {e}")
    sys.exit(1)

  # Save JSON to file (optional)
  if json_file:
    with open(json_file, "w") as f:
      json.dump(res, f, indent=4)
    print(f"[*] Raw JSON results successfully saved to: {json_file}\n")

  # Output as a Markdown Table for LLM Agent parsing
  print(f"### Top {MAX_ALIGNMENT_HITS} Sequence Homologues (EBI BLAST)")
  print("| Target ID | Q-Cov | E-value | Seq Identity(%) | Aln Length |")
  print("|---|---|---|---|---|")

  # The EBI JSON wraps hits in a 'hits' array
  hits = res.get("hits", [])

  if not hits:
    print("[!] No homologues found.")
    return

  for hit in hits[:MAX_ALIGNMENT_HITS]:
    target_acc = hit.get("hit_acc", "N/A")
    target_desc = hit.get("hit_desc", hit.get("hit_def", ""))

    # Combine Accession and Description for the LLM
    target = f"{target_acc} {target_desc}".strip()

    hsps = hit.get("hit_hsps", [{}])
    best_hsp = hsps[0] if hsps else {}

    # Calculate Query Coverage
    hsp_query_from = int(best_hsp.get("hsp_query_from", 0))
    hsp_query_to = int(best_hsp.get("hsp_query_to", 0))

    if q_len > 0 and hsp_query_to > hsp_query_from:
      aligned_q_residues = (hsp_query_to - hsp_query_from) + 1
      cov_percentage = min((aligned_q_residues / q_len) * 100, 100.0)
      q_cov = f"{cov_percentage:.1f}%"
    else:
      q_cov = "N/A"

    evalue = str(best_hsp.get("hsp_expect", "N/A"))
    seq_id = str(best_hsp.get("hsp_identity", "N/A")) + "%"
    aln_len = str(best_hsp.get("hsp_align_len", "N/A"))

    # Print Markdown row without truncation
    print(f"| {target} | {q_cov} | {evalue} | {seq_id} | {aln_len} |")


def main():
  dotenv.load_dotenv(os.path.expanduser("~/.env"))
  parser = argparse.ArgumentParser(
      description=(
          "Query EBI NCBI BLAST with a FASTA file or raw sequence string."
      )
  )
  parser.add_argument(
      "query_input", help="Path to the FASTA file or raw sequence string"
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
      "--databases",
      help="Comma-separated list of databases to search",
      default="uniprotkb",
  )
  args = parser.parse_args()

  print(f"[*] Output: {args.output}")
  if args.json:
    print(f"[*] Output: {args.json}")

  search_uniprot(args.query_input, args.output, args.json, args.databases)


if __name__ == "__main__":
  main()
