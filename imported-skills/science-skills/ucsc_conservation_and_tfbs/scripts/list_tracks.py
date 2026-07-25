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

"""Script to list available tracks from the UCSC Genome Database."""

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
from typing import Any
from polite_http import http_client

UCSC_API_URL = "https://api.genome.ucsc.edu/list/tracks"

api_client = http_client.HttpClient("https://api.genome.ucsc.edu/", qps=0.05)


def flatten_tracks(track_dict: dict[str, Any]) -> list[dict[str, Any]]:
  """Flattens the deeply nested track structure into a list of tracks."""
  tracks = []

  def traverse(d: dict[str, Any]):
    for key, value in d.items():
      if not isinstance(value, dict):
        continue
      if key in (
          "downloadTime",
          "downloadTimeStamp",
          "dataTime",
          "dataTimeStamp",
      ):
        continue

      # If it's a track (has shortLabel or type)
      if "shortLabel" in value:
        tracks.append({
            "track": key,
            "shortLabel": value.get("shortLabel", ""),
            "longLabel": value.get("longLabel", ""),
            "group": value.get("group", ""),
            "type": value.get("type", ""),
        })

      # Recurse for child tracks
      traverse(value)

  traverse(track_dict)
  return tracks


def filter_tracks(
    tracks: list[dict[str, Any]], search: str = None, group: str = None
) -> list[dict[str, Any]]:
  """Filters tracks based on search string and group."""
  filtered = []
  seen = set()

  for track in tracks:
    track_id = track["track"]
    if track_id in seen:
      continue

    # Filter by group
    if group and track["group"] and group.lower() not in track["group"].lower():
      continue

    # Filter by search term
    if search:
      s = search.lower()
      if not (
          s in track_id.lower()
          or s in track["shortLabel"].lower()
          or s in track["longLabel"].lower()
      ):
        continue

    filtered.append(track)
    seen.add(track_id)

  return filtered


def main():
  parser = argparse.ArgumentParser(
      description="List available tracks from UCSC."
  )
  parser.add_argument(
      "--genome",
      default="hg38",
      help="Genome assembly to query (e.g., hg38, hg19). Defaults to hg38.",
  )
  parser.add_argument(
      "--search",
      help=(
          "Substring to search for in trackName, shortLabel, or longLabel"
          " (case-insensitive)."
      ),
  )
  parser.add_argument(
      "--group",
      help=(
          "Substring to search for in track group (e.g., 'genes', 'regulation',"
          " 'varRep'). Case-insensitive."
      ),
  )
  parser.add_argument(
      "--output",
      required=True,
      help="Path where the output matches will be saved in JSON format.",
  )

  args = parser.parse_args()

  url = f"{UCSC_API_URL}?genome={args.genome}"
  print(f"Requesting URL: {url}")
  data = api_client.fetch_json(url)

  genome_data = data.get(args.genome, {})
  if not genome_data:
    print(f"No track data found for genome {args.genome}.")
    sys.exit(1)

  all_tracks = flatten_tracks(genome_data)
  filtered_tracks = filter_tracks(all_tracks, args.search, args.group)

  print(f"Found {len(filtered_tracks)} tracks matching criteria.")

  # Dump output
  out_dir = os.path.dirname(os.path.abspath(args.output))
  if out_dir:
    os.makedirs(out_dir, exist_ok=True)

  with open(args.output, "w") as f:
    json.dump(
        {
            "genome": args.genome,
            "search": args.search,
            "group": args.group,
            "matchCount": len(filtered_tracks),
            "tracks": filtered_tracks,
        },
        f,
        indent=2,
    )


if __name__ == "__main__":
  main()
