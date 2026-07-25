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

"""Fetches Evolutionary Conservation scores from UCSC Database."""

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
CLIENT = http_client.HttpClient("https://api.genome.ucsc.edu/", qps=0.05)


def parse_coordinate(coord_str: str) -> tuple[str, int, int]:
  """Parses a coordinate string like 'chr1:100-200' or 'chr1:100'.

  User-facing coordinates are 1-based (matching the UCSC Genome Browser
  display). The UCSC REST API uses 0-based half-open coordinates, so we
  convert by subtracting 1 from the start position.
  """
  match = re.match(r"^(chr[0-9XYM]+|\w+):(\d+)(?:-(\d+))?$", coord_str)
  if not match:
    print(
        f"Error: Invalid coordinate format '{coord_str}'. Expected"
        " 'chr:start-end' or 'chr:pos'."
    )
    sys.exit(1)

  chrom = match.group(1)
  start_1based = int(match.group(2))
  # Convert from 1-based to 0-based half-open for the UCSC API.
  start = start_1based - 1
  if match.group(3):
    # End is already correct: 1-based inclusive end == 0-based half-open end.
    end = int(match.group(3))
  else:
    # Single position: 1-based pos N -> 0-based [N-1, N).
    end = start_1based
  return chrom, start, end


def get_conservation_data(
    chrom: str, start: int, end: int, track: str, genome: str = "hg38"
) -> dict[str, Any]:
  """Fetches track data for a given region."""
  url = f"{UCSC_API_URL}?genome={genome}&track={track}&chrom={chrom}&start={start}&end={end}"
  print(f"Requesting URL: {url}")
  return CLIENT.fetch_json(url)


def merge_results(
    coords: list[str],
    collection: str,
    fetch_conserved: bool,
    genome: str,
    analyze: bool,
) -> dict[str, dict[str, Any]]:
  """Main fetching and merging logic."""
  if genome == "hg38":
    if collection == "vertebrate":
      # UCSC 100-vertebrate Multiz alignment (default comparative genomics
      # track on the UCSC Genome Browser for hg38).
      phylo_track = "phyloP100way"
      phast_track = "phastCons100way"

    elif collection == "mammal":
      # Hiller Lab 470-way mammalian alignment.
      phylo_track = "phyloP470wayBW"
      phast_track = "phastCons470way"

    elif collection == "primate":
      # UCSC 30-primate Multiz alignment.
      phylo_track = "phyloP30way"
      phast_track = "phastCons30way"

    else:
      raise ValueError(
          f"Unsupported collection: {collection} for hg38. Supported:"
          " vertebrate (100-way, default), mammal (Hiller 470-way),"
          " primate (30-way)."
      )

  elif genome == "hg19":
    if collection == "vertebrate":
      # UCSC 100-vertebrate Multiz alignment (default for hg19).
      phylo_track = "phyloP100way"
      phast_track = "phastCons100way"

    elif collection == "vertebrate46":
      # UCSC 46-vertebrate Multiz alignment (legacy hg19 track).
      phylo_track = "phyloP46wayAll"
      phast_track = "phastCons46way"

    elif collection == "mammal":
      # 46-way placental mammal subset.
      phylo_track = "phyloP46wayPlacental"
      phast_track = "phastCons46wayPlacental"

    elif collection == "primate":
      # 46-way primate subset.
      phylo_track = "phyloP46wayPrimates"
      phast_track = "phastCons46wayPrimates"

    else:
      raise ValueError(
          f"Unsupported collection: {collection} for hg19. Supported:"
          " vertebrate (100-way, default), vertebrate46 (46-way),"
          " mammal (46-way placental), primate (46-way primates)."
      )

  else:
    raise ValueError(
        f"Unsupported genome: {genome}. Only hg38 and hg19 are supported."
    )

  tracks_to_fetch = [phylo_track, phast_track]
  if fetch_conserved:
    tracks_to_fetch.append(phast_track.replace("Cons", "ConsElements"))
    # Note: 'haqer' and 'ucne' might exist depending on genome build,
    # but we stick to the core phastConsElements for robustness here.
    # Can add others if needed and verified exist.

  results = {}
  for coord in coords:
    chrom, start, end = parse_coordinate(coord)
    region_result = {"coordinate": f"{chrom}:{start}-{end}", "tracks": {}}

    for track in tracks_to_fetch:
      print(f"Fetching {track} for region {chrom}:{start}-{end}...")
      data = get_conservation_data(chrom, start, end, track, genome=genome)

      # Extract actual track data items from the JSON
      # (which usually places them under the chromosome name key or similar)
      track_items = data.get(chrom, [])
      if not track_items and track in data:
        # fallback for some tracks
        track_items = data.get(track, [])
      region_result["tracks"][track] = track_items

      if analyze and track.startswith("phyloP"):
        scores = [i.get("value") for i in track_items if i.get("value")]
        if scores:
          mean_score = sum(scores) / len(scores)
          min_score = min(scores)
          max_score = max(scores)
          # Heuristic for acceleration: strong negative scores
          is_accelerated = mean_score < -0.3 or min_score < -2.0

          region_result["analysis"] = {
              "track": track,
              "mean_phyloP": round(mean_score, 4),
              "min_phyloP": round(min_score, 4),
              "max_phyloP": round(max_score, 4),
              "is_accelerated": is_accelerated,
          }
    results[coord] = region_result

  return results


def main():
  parser = argparse.ArgumentParser(
      description="Fetch Evolutionary Conservation scores from UCSC Database."
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
      "--collection",
      choices=["vertebrate", "mammal", "primate", "vertebrate46"],
      default="vertebrate",
      help=(
          "Evolutionary depth of alignment. For hg38: vertebrate (100-way,"
          " default), mammal (Hiller 470-way), primate (30-way). For hg19:"
          " vertebrate (100-way, default), vertebrate46 (46-way legacy),"
          " mammal (46-way placental), primate (46-way primates)."
      ),
  )
  parser.add_argument(
      "--output",
      required=True,
      help="Filename where all successful output is written in JSON format.",
  )
  parser.add_argument(
      "--conserved-elements",
      action="store_true",
      help="Also fetch predefined highly-conserved blocks within the region.",
  )
  parser.add_argument(
      "--genome", default="hg38", help="Genome assembly. Defaults to hg38."
  )
  parser.add_argument(
      "--analyze",
      action="store_true",
      help="Analyze phyloP scores for signals of evolutionary acceleration.",
  )

  args = parser.parse_args()

  results = merge_results(
      args.coordinates,
      args.collection,
      args.conserved_elements,
      args.genome,
      args.analyze,
  )

  # Dump final output to specified file
  with open(args.output, "w") as f:
    json.dump(results, f, indent=2)


if __name__ == "__main__":
  main()
