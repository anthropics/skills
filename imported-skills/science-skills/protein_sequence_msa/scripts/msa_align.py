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
#   "python-dotenv",
# ]
# ///

"""Runs EBI Clustal Omega for MSA computation.

Takes a file with multiple sequences and provides the alignment.
"""

import argparse
import os
import sys
import time
import urllib.parse

import dotenv
from polite_http import http_client

_POLLING_TIMEOUT_SECS = 15 * 60  # 15 minutes.

_CLIENT = http_client.HttpClient(
    "https://www.ebi.ac.uk/Tools/services/rest/clustalo/", qps=1
)


def _prepare_payload(email: str, title: str, sequences: str) -> bytes:
  """Prepares the payload for the EBI Clustal Omega API."""
  params = {
      "email": email,
      "title": title,
      "sequence": sequences,
  }
  return urllib.parse.urlencode(params).encode("utf-8")


def _align_sequences(
    *, input_file: str, output_file: str, dry_run: bool = False
) -> None:
  """Runs EBI Clustal Omega alignment for sequences in a FASTA file.

  This function takes a FASTA formatted file, submits the sequences to the
  EBI Clustal Omega web service, polls for the alignment completion, and
  saves the resulting alignment in FASTA format to the specified output file.

  Args:
    input_file: Path to the input file containing sequences in FASTA format.
    output_file: Path where the resulting MSA in FASTA format will be saved.
    dry_run: If True, print the payload and exit without submitting the job.
  """
  if not os.path.exists(input_file):
    print(f"[!] Error: Input file not found: {input_file}")
    sys.exit(1)

  max_size_bytes = 4 * 1024 * 1024  # 4 MB
  file_size = os.path.getsize(input_file)
  if file_size > max_size_bytes:
    print(
        "[!] Error: At most 4 MB file size supported. Found"
        f" {file_size / (1024 * 1024):.2f} MB."
    )
    sys.exit(1)

  with open(input_file, "r") as f:
    sequences = f.read().strip()

  if not sequences:
    print("[!] Error: Empty input file.")
    sys.exit(1)

  num_sequences = sequences.count(">")
  if num_sequences < 2:
    print(f"[!] Error: At least 2 sequences required. Found {num_sequences}.")
    sys.exit(1)
  if num_sequences > 4000:
    print(
        f"[!] Error: At most 4000 sequences supported. Found {num_sequences}."
    )
    sys.exit(1)

  print("[*] Submitting sequences to EBI Clustal Omega API...")

  # 1. Submit Job
  user_email = os.environ.get("USER_EMAIL")
  if not user_email:
    print("[!] Error: USER_EMAIL environment variable is required.")
    sys.exit(1)
  data = _prepare_payload(user_email, "MSA", sequences)

  if dry_run:
    print(data)
    sys.exit(0)

  job_id = _CLIENT.fetch_text(
      "run", method="POST", data=data, headers={"Accept": "text/plain"}
  ).strip()
  print(f"[*] Job ID generated: {job_id}")

  # 2. Poll the server
  print("[*] Polling server for completion...")

  start_time = time.time()
  while time.time() - start_time < _POLLING_TIMEOUT_SECS:
    status = _CLIENT.fetch_text(
        f"status/{job_id}", headers={"Accept": "text/plain"}, timeout=20
    ).strip()
    sys.stdout.write(".")
    sys.stdout.flush()

    if status == "FINISHED":
      print("\n[*] Job marked as FINISHED.")
      break
    elif status in ["ERROR", "FAILURE", "NOT_FOUND"]:
      print(f"\n[!] Job failed with status: {status}")
      sys.exit(1)
    time.sleep(10)

  else:
    print(f"\n[!] Job timed out after {_POLLING_TIMEOUT_SECS // 60} minutes.")
    sys.exit(1)

  # 3. Fetch Results
  print("\n[*] Job complete. Fetching results...\n")

  result_text = _CLIENT.fetch_text(f"result/{job_id}/fa", timeout=60)

  with open(output_file, "w") as f:
    f.write(result_text)
  print(f"[*] Alignment results saved to: {output_file}")


def main() -> None:
  dotenv.load_dotenv(os.path.expanduser("~/.env"))
  parser = argparse.ArgumentParser(
      description="MSA computation using EBI Clustal Omega."
  )
  parser.add_argument(
      "input", help="Path to FASTA file containing multiple sequences"
  )
  parser.add_argument(
      "-o",
      "--output",
      required=True,
      help="Path to save the output alignment file",
  )
  parser.add_argument(
      "--dry-run",
      action="store_true",
      help="Dry run: print payload and exit without submitting job",
  )
  args = parser.parse_args()

  _align_sequences(
      input_file=args.input, output_file=args.output, dry_run=args.dry_run
  )


if __name__ == "__main__":
  main()
