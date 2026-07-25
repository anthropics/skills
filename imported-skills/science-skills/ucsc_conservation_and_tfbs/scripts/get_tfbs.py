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

"""Fetches Transcription Factor Binding Sites (TFBS) from UCSC Database."""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
# ]
# ///

import argparse
import json
import re
import sys
from typing import Any
from polite_http import http_client

UCSC_API_URL = "https://api.genome.ucsc.edu/getData/track"

api_client = http_client.HttpClient("https://api.genome.ucsc.edu/", qps=0.05)


def parse_coordinate(coord_str: str) -> tuple[str, int, int]:
  """Parses a coordinate string like 'chr1:100-200' or 'chr1:100'."""
  match = re.match(r"^(chr[0-9XYM]+|\w+):(\d+)(?:-(\d+))?$", coord_str)
  if not match:
    print(
        f"Error: Invalid coordinate format '{coord_str}'. Expected"
        " 'chr:start-end' or 'chr:pos'."
    )
    sys.exit(1)

  chrom = match.group(1)
  start = int(match.group(2))
  if match.group(3):
    end = int(match.group(3))
  else:
    # If no end provided, assume a 1bp region (start and start+1)
    end = start + 1
  return chrom, start, end


def get_tfbs_data(
    chrom: str, start: int, end: int, track: str, genome: str = "hg38"
) -> dict[str, Any]:
  """Fetches track data for a given region."""
  url = f"{UCSC_API_URL}?genome={genome}&track={track}&chrom={chrom}&start={start}&end={end}"
  print(f"Requesting URL: {url}")
  return api_client.fetch_json(url)


def main():
  parser = argparse.ArgumentParser(
      description=(
          "Fetch Transcription Factor Binding Sites (TFBS) from UCSC Database."
      )
  )
  parser.add_argument(
      "--coordinates",
      required=True,
      nargs="+",
      help=(
          "One or more genomic coordinates (e.g., 'chr1:100-200' or"
          " 'chr1:100')."
      ),
  )
  parser.add_argument(
      "--tracks",
      required=True,
      nargs="+",
      help=(
          "One or more track names or aliases (e.g., 'encRegTfbsClustered',"
          " 'jaspar2026', 'ReMapTFs')."
      ),
  )
  parser.add_argument(
      "--tf-filter",
      default=None,
      help=(
          "Optional case-insensitive filter on the TFName field. Only items"
          " whose TFName contains this substring are kept (e.g., 'TP53')."
      ),
  )
  parser.add_argument(
      "--output",
      required=True,
      help="Filename where all successful output is written in JSON format.",
  )
  parser.add_argument(
      "--genome", default="hg38", help="Genome assembly. Defaults to hg38."
  )

  args = parser.parse_args()

  results = {}
  for coord in args.coordinates:
    chrom, start, end = parse_coordinate(coord)
    region_result = {"coordinate": f"{chrom}:{start}-{end}", "tracks": {}}

    for track in args.tracks:
      print(f"Fetching {track} for region {chrom}:{start}-{end}...")
      data = get_tfbs_data(chrom, start, end, track, genome=args.genome)

      # Extract actual track data items from the JSON.
      if "error" in data:
        print(f"API Error for track '{track}': {data['error']}")
        region_result["tracks"][track] = {"error": data["error"]}
        continue

      # Try both track name and chromosome as key
      track_items = data.get(track, [])
      if not track_items and chrom in data:
        track_items = data.get(chrom, [])

      # Fallback to look for ANY list that looks like data
      if not track_items:
        for k, v in data.items():
          if isinstance(v, list) and k not in [
              "downloadTime",
              "downloadTimeStamp",
              "dataTime",
              "dataTimeStamp",
              "genome",
              "track",
              "chrom",
              "start",
              "end",
          ]:
            track_items = v
            break

      # Apply TF name filter if specified.
      if args.tf_filter and track_items:
        tf_filter_lower = args.tf_filter.lower()
        filtered = [
            item
            for item in track_items
            if tf_filter_lower in item.get("TFName", "").lower()
        ]
        print(
            f"  Filtered {len(track_items)} items to {len(filtered)} matching"
            f" TFName containing '{args.tf_filter}'."
        )
        track_items = filtered

      region_result["tracks"][track] = track_items

    results[coord] = region_result

  # Dump final output to specified file
  with open(args.output, "w") as f:
    json.dump(results, f, indent=2)
  print(f"Output written to {args.output}")


if __name__ == "__main__":
  main()
