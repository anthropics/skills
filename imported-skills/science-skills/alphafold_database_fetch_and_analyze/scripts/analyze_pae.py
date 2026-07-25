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

"""Analyzes Predicted Aligned Error (PAE) and detects domain boundaries."""

# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///

import argparse
import itertools
import json
import os


def find_sub_domains(pae_matrix, distance_cutoff=7.0, min_domain_size=40):
  """Identifies structurally independent sub-domains based on the PAE matrix."""
  n_res = len(pae_matrix)
  domains = []
  current_domain = []

  for i in range(n_res):
    if not current_domain:
      current_domain.append(i)
      continue

    window_size = min(20, len(current_domain))
    recent_res = current_domain[-window_size:]

    pae_sum = sum(pae_matrix[r][i] + pae_matrix[i][r] for r in recent_res)
    avg_pae = pae_sum / (2.0 * window_size)

    if avg_pae < distance_cutoff:
      current_domain.append(i)
    else:
      if len(current_domain) >= min_domain_size:
        domains.append(current_domain)
      current_domain = [i]

  if len(current_domain) >= min_domain_size:
    domains.append(current_domain)

  domain_boundaries = []
  for comp in domains:
    start = comp[0] + 1
    end = comp[-1] + 1
    domain_boundaries.append([start, end])

  return domain_boundaries


def merge_global_domains(boundaries, pae_matrix, merge_cutoff=15.0):
  """Merges sub-domains if the average PAE between them is below cutoff."""
  if not boundaries:
    return []

  if len(boundaries) == 1:
    merged = boundaries
  else:
    merged = [boundaries[0]]

    for i in range(1, len(boundaries)):
      prev_end = merged[-1][1] - 1
      curr_start = boundaries[i][0] - 1

      lookback = max(merged[-1][0] - 1, prev_end - 30)
      lookfwd = min(boundaries[i][1] - 1, curr_start + 30)

      pae_sum = 0
      n_pairs = 0
      for r1 in range(lookback, prev_end + 1):
        for r2 in range(curr_start, lookfwd + 1):
          pae_sum += pae_matrix[r1][r2] + pae_matrix[r2][r1]
          n_pairs += 2

      if n_pairs > 0 and (pae_sum / n_pairs) < merge_cutoff:
        merged[-1][1] = boundaries[i][1]
      else:
        merged.append(boundaries[i])

  filtered_merged = [dom for dom in merged if (dom[1] - dom[0] + 1) > 50]

  return filtered_merged


def analyze_pae(pae_file):
  """Parses a PAE JSON file and calculates structural domain metrics."""
  print(
      "\n[*] Analyzing Predicted Aligned Error (PAE) from"
      f" {os.path.basename(pae_file)}..."
  )
  try:
    with open(pae_file, "r") as f:
      data = json.load(f)[0]

    if "predicted_aligned_error" in data:
      pae = data["predicted_aligned_error"]
    elif "distance" in data:
      pae = data["distance"]
    else:
      print(
          "     [!] Could not locate PAE matrix in JSON keys:"
          f" {list(data.keys())}"
      )
      return

    flat_pae = list(itertools.chain.from_iterable(pae))
    if not flat_pae:
      print("     [!] PAE matrix is empty.")
      return

    mean_pae = sum(flat_pae) / len(flat_pae)
    max_pae = max(flat_pae)
    min_pae = min(flat_pae)
    confident_pairs = sum(1 for p in flat_pae if p < 5.0) / len(flat_pae) * 100

    print(f"  -> PAE Matrix Shape: {len(pae)}x{len(pae[0])}")
    print(f"  -> Mean Error: {mean_pae:.2f} Å")
    print(
        f"  -> Max Error: {max_pae:.2f} Å (suggests max possible distance"
        " between domains)"
    )
    print(f"  -> Min Error: {min_pae:.2f} Å")
    print(
        "  -> Fraction of confident residue pairs (<5Å PAE):"
        f" {confident_pairs:.1f}%"
    )

    sub_domains = find_sub_domains(pae, distance_cutoff=7.0, min_domain_size=40)
    global_domains = merge_global_domains(sub_domains, pae, merge_cutoff=15.0)

    print("\n[*] Domain Boundary Analysis:")
    if not global_domains:
      print("  -> No distinct rigidly-folded domains detected (>50 AAs).")
    else:
      print(
          "  -> Number of distinct Global Domains detected:"
          f" {len(global_domains)}"
      )
      for i, (start, end) in enumerate(global_domains, 1):
        print(
            f"     Domain {i}: residues {start} - {end} (Length:"
            f" {end - start + 1} AAs)"
        )

    print("\n[*] PAE Structural Conclusion:")
    if len(global_domains) == 1:
      conclusion = (
          "The protein consists of a single well-folded, rigid composite"
          " domain."
      )
    elif len(global_domains) > 1:
      conclusion = (
          f"The protein has {len(global_domains)} independently positioned"
          " global domains separated by truly flexible joints."
      )
    else:
      conclusion = (
          "The protein is likely entirely disordered or lacks rigid"
          " tertiary structure."
      )
    print(f"  -> {conclusion}")

    return {
        "pae_file": os.path.basename(pae_file),
        "matrix_shape": f"{len(pae)}x{len(pae[0])}",
        "mean_pae": round(mean_pae, 2),
        "max_pae": round(max_pae, 2),
        "min_pae": round(min_pae, 2),
        "confident_pairs_pct": round(confident_pairs, 1),
        "domains": [
            {"start": s, "end": e, "length": e - s + 1}
            for s, e in global_domains
        ],
        "conclusion": conclusion,
    }

  except (IOError, json.JSONDecodeError) as e:
    print(f"     [!] Failed to analyze PAE file: {e}")
    return None


if __name__ == "__main__":
  parser = argparse.ArgumentParser(
      description=(
          "Analyze PAE matrix and detect domain boundaries from an AlphaFold"
          " PAE JSON file"
      )
  )
  parser.add_argument(
      "pae_file",
      help=(
          "Path to the PAE JSON file (e.g.,"
          " AF-P04637-F1-predicted_aligned_error_v6.json)"
      ),
  )

  args = parser.parse_args()

  analyze_pae(args.pae_file)
