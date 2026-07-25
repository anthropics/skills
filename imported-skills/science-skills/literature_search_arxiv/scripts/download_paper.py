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

"""Downloads a paper from arXiv given its ID.

This script allows downloading arXiv papers in either PDF or HTML format
and saving them to a specified output file path.
"""

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

_CLIENT = http_client.HttpClient("https://arxiv.org/", qps=1.0 / 3.0)


def parse_args() -> argparse.Namespace:
  """Parses command-line arguments for the download script.

  Returns:
    argparse.Namespace: An object containing the parsed arguments.
  """
  parser = argparse.ArgumentParser(
      description="Download paper from arXiv (PDF or HTML)"
  )
  parser.add_argument(
      "--id", type=str, required=True, help="arXiv ID (e.g., 2305.10601)"
  )
  parser.add_argument(
      "--format",
      type=str,
      choices=["pdf", "html"],
      required=True,
      help="Download format",
  )
  parser.add_argument(
      "--output", type=str, required=True, help="Output file path"
  )
  return parser.parse_args()


def download_paper(args: argparse.Namespace):
  """Downloads a paper from arXiv based on the provided arguments.

  This function fetches a paper (either PDF or HTML) from arXiv using the
  specified ID and format, saving it to the given output path. It includes
  error handling for common issues like 404 Not Found and network errors,
  and enforces a rate limit after each download attempt.

  Args:
    args: An argparse.Namespace object containing: id (str) -- The arXiv ID of
      the paper; format (str) -- The desired format ("pdf" or "html"); output
      (str) -- The file path where the paper will be saved.
  """
  # Ensure ID is clean
  paper_id = args.id.strip()

  if args.format == "pdf":
    url = f"https://arxiv.org/pdf/{paper_id}.pdf"
  elif args.format == "html":
    url = f"https://arxiv.org/html/{paper_id}"
  else:
    raise ValueError(f"Unsupported format: {args.format}")

  print(f"Attempting to download {args.format.upper()} from {url}...")

  try:
    content = _CLIENT.fetch_bytes(url)
    out_dir = os.path.dirname(args.output)
    if out_dir:
      os.makedirs(out_dir, exist_ok=True)
    with open(args.output, "wb") as f:
      f.write(content)
    print(f"Success! Saved to {args.output}")

  except http_client.HttpError as e:
    if e.status_code == 404:
      if args.format == "html":
        print(
            "Error 404: HTML format is not available for this paper (ID:"
            f" {paper_id}). Older papers may only have PDFs. Try downloading"
            " with --format pdf",
            file=sys.stderr,
        )
      else:
        print(
            f"Error 404: Paper not found (ID: {paper_id}). Check the ID.",
            file=sys.stderr,
        )
    else:
      raise


if __name__ == "__main__":
  main_args = parse_args()
  download_paper(main_args)
