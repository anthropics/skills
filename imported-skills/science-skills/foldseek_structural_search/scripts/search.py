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

"""Runs Foldseek search for a PDB/mmCIF file against different databases."""

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
import time
import uuid

from polite_http import http_client

ALLOWED_DATABASES = [
    "afdb50",
    "afdb-swissprot",
    "pdb100",
    "BFVD",
    "mgnify_esm30",
    "cath50",
    "gmgcl_id",
    "bfmd",
    "afdb-proteome",
]

MAX_ALIGNMENT_HITS = 300
DEFAULT_EVALUE = 1000

# Respect 0.1 queries per second requirement.
CLIENT = http_client.HttpClient("https://search.foldseek.com", qps=1)


def build_multipart_payload(fields, files):
  """Manually constructs a multipart/form-data byte payload."""
  boundary = uuid.uuid4().hex
  body = bytearray()

  # Add standard form fields (handling lists for multiple databases)
  for key, values in fields.items():
    if not isinstance(values, list):
      values = [values]
    for value in values:
      body.extend(f"--{boundary}\r\n".encode("utf-8"))
      body.extend(
          f'Content-Disposition: form-data; name="{key}"\r\n\r\n'.encode(
              "utf-8"
          )
      )
      body.extend(f"{value}\r\n".encode("utf-8"))

  # Add file data
  for key, filepath in files.items():
    filename = os.path.basename(filepath)
    with open(filepath, "rb") as f:
      content = f.read()
    body.extend(f"--{boundary}\r\n".encode("utf-8"))
    body.extend(
        f'Content-Disposition: form-data; name="{key}";'
        f' filename="{filename}"\r\n'.encode("utf-8")
    )
    body.extend(b"Content-Type: application/octet-stream\r\n\r\n")
    body.extend(content)
    body.extend(b"\r\n")

  body.extend(f"--{boundary}--\r\n".encode("utf-8"))
  return boundary, body


# ---------------------------------------------------


def main():
  # Set up command line argument parsing
  parser = argparse.ArgumentParser(
      description="Query Foldseek with a PDB/mmCIF file and save the results."
  )
  parser.add_argument("input_file", help="Path to the mmCIF or PDB file")
  parser.add_argument(
      "-o",
      "--output",
      help="Path to save the output JSON file",
      default="foldseek_results.json",
  )
  parser.add_argument(
      "--databases",
      help="Comma-separated list of databases to search",
      default="pdb100,afdb50",
  )
  args = parser.parse_args()

  file_path = args.input_file
  output_path = args.output
  ticket_url = "https://search.foldseek.com/api/ticket"

  # Process and validate the databases
  selected_dbs = [db.strip() for db in args.databases.split(",")]
  invalid_dbs = [db for db in selected_dbs if db not in ALLOWED_DATABASES]

  if invalid_dbs:
    print(f"[!] Error: Invalid database(s) provided: {', '.join(invalid_dbs)}")
    print(f"[*] Allowed databases are: {', '.join(ALLOWED_DATABASES)}")
    sys.exit(1)

  # Standard headers for all requests
  headers = {
      "User-Agent": "",
      "Accept": "application/json",
  }

  print(f"[*] Submitting {file_path} to Foldseek API...")
  print(f"[*] Searching databases: {', '.join(selected_dbs)}")

  # 1. Submit Ticket
  try:
    if not os.path.exists(file_path):
      raise FileNotFoundError(f"No such file: '{file_path}'")

    boundary, body = build_multipart_payload(
        fields={"mode": "3diaa", "database[]": selected_dbs},
        files={"q": file_path},
    )

    headers["Content-Type"] = f"multipart/form-data; boundary={boundary}"
    response = CLIENT.fetch_json(
        ticket_url, method="POST", data=body, headers=headers, timeout=30
    )
    ticket_id = response["id"]
    print(f"[*] Ticket ID generated: {ticket_id}")

  except FileNotFoundError as e:
    print(f"[!] Error: {e}")
    sys.exit(1)
  except http_client.HttpError as e:
    print(f"[!] API Submission Failed: {e}")
    sys.exit(1)

  # 2. Poll the server until the job finishes
  print("[*] Polling server for completion...")
  while True:
    status_res = CLIENT.fetch_json(
        f"{ticket_url}/{ticket_id}", headers=headers, timeout=20
    )
    status = status_res.get("status")

    if status == "COMPLETE":
      print("\n[*] Job marked as COMPLETE.")
      break
    elif status == "ERROR":
      print("\n[!] Foldseek job failed on the server.")
      sys.exit(1)

    sys.stdout.write(".")
    sys.stdout.flush()
    time.sleep(10)

  time.sleep(3)  # Brief pause to allow server-side result finalization.

  # 3. Fetch and format the results
  print(
      "[*] Fetching results (this might take a moment for large databases)...\n"
  )
  result_url = f"https://search.foldseek.com/api/result/{ticket_id}/0"
  res = CLIENT.fetch_json(result_url, headers=headers, timeout=120)

  # Save the JSON response to the specified local file
  with open(output_path, "w") as json_file:
    json.dump(res, json_file, indent=4)
  print(f"[*] Raw JSON results successfully saved to: {output_path}\n")

  # Output as a Markdown Table for LLM Agent parsing
  print("### All Structural Matches")
  print("| Target ID | Q-Cov | Prob | E-value | Seq Identity | Aln Length |")
  print("|---|---|---|---|---|---|")

  alignments_list = []
  if isinstance(res, dict):
    if "results" in res:
      for result_group in res.get("results", []):
        for db_alignments in result_group.get("alignments", []):
          if isinstance(db_alignments, list):
            alignments_list.extend(db_alignments)
          elif isinstance(db_alignments, dict):
            alignments_list.append(db_alignments)
    elif "alignments" in res:
      alignments_list = res["alignments"]
  elif isinstance(res, list):
    alignments_list = res

  def get_evalue(hit):
    # This field must not be empty as it is used for sorting the results
    # If the field is missing or empty, we assign a default value that is
    # larger than any reasonable E-value (puts it at the end of the sorted
    # list).
    try:
      return float(
          hit.get("eval", hit.get("eValue", hit.get("evalue", DEFAULT_EVALUE)))
      )
    except ValueError:
      return float(DEFAULT_EVALUE)

  # Sort all hits first, then take the top MAX_ALIGNMENT_HITS
  alignments_list.sort(key=get_evalue)
  alignments_list = alignments_list[:MAX_ALIGNMENT_HITS]

  for hit in alignments_list:
    target = hit.get("target", "N/A")

    # --- Corrected Query Coverage Logic ---
    q_len = hit.get("qLen", hit.get("qlen", 0))
    q_start = hit.get("qStartPos", 0)
    q_end = hit.get("qEndPos", 0)

    if q_len > 0 and q_end > q_start:
      # Calculate the actual number of query residues involved, ignoring gaps
      aligned_q_residues = (q_end - q_start) + 1

      # Cap at 100.0% to handle any minor index shifting in the API
      cov_percentage = min((aligned_q_residues / q_len) * 100, 100.0)
      q_cov = f"{cov_percentage:.1f}%"
    else:
      q_cov = "N/A"

    # Extract Probability
    prob = hit.get("prob", hit.get("probability", "N/A"))
    if isinstance(prob, (float, int)):
      prob = f"{prob:.3f}"
    else:
      prob = str(prob)

    evalue = str(hit.get("eval", hit.get("eValue", hit.get("evalue", "N/A"))))
    seq_id = str(
        hit.get("seqId", hit.get("seqIdentity", hit.get("fident", "N/A")))
    )
    aln_len = str(
        hit.get("alnLength", hit.get("alnLen", hit.get("alnlen", "N/A")))
    )

    # Print Markdown row without any truncation
    print(f"| {target} | {q_cov} | {prob} | {evalue} | {seq_id} | {aln_len} |")


if __name__ == "__main__":
  main()
