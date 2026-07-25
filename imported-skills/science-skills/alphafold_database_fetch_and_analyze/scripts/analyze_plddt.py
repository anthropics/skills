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

"""Analyzes pLDDT confidence metrics from a saved AFDB metadata JSON file."""

# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///

import argparse
import json
import sys

CONFIDENT_THRESHOLD = 0.7
MODERATE_THRESHOLD = 0.4
NOTABLE_DISORDER_THRESHOLD = 0.15
MIXED_DISORDER_THRESHOLD = 0.3
MOSTLY_DISORDERED_THRESHOLD = 0.5


def analyze_plddt(metadata_file):
  """Loads an AFDB metadata JSON and analyzes pLDDT metrics."""
  try:
    with open(metadata_file, "r") as f:
      entry = json.load(f)
  except (IOError, json.JSONDecodeError) as e:
    print(f"[!] Error reading metadata file: {e}")
    sys.exit(1)

  return _analyze_entry(entry)


def _analyze_entry(entry):
  """Parses and analyzes pLDDT confidence metrics from the API payload."""
  accession = entry.get("uniprotAccession", "Unknown")
  print(f"\n[*] AlphaFold pLDDT Metrics for Accession: {accession}")
  global_plddt = entry.get("globalMetricValue", 0.0)
  frac_vlow = entry.get("fractionPlddtVeryLow", 0.0)
  frac_low = entry.get("fractionPlddtLow", 0.0)
  frac_conf = entry.get("fractionPlddtConfident", 0.0)
  frac_vhigh = entry.get("fractionPlddtVeryHigh", 0.0)

  print("-" * 65)
  print(f"  -> Overall Global pLDDT   : {global_plddt:.2f}")
  print(f"  -> Fraction Very Low (<50): {frac_vlow:.3f} ({frac_vlow*100:.1f}%)")
  print(f"  -> Fraction Low (50-70)   : {frac_low:.3f} ({frac_low*100:.1f}%)")
  print(f"  -> Fraction Confident     : {frac_conf:.3f} ({frac_conf*100:.1f}%)")
  print(
      f"  -> Fraction Very High     : {frac_vhigh:.3f} ({frac_vhigh*100:.1f}%)"
  )
  print("-" * 65)

  conf_total = frac_conf + frac_vhigh

  print("[*] pLDDT Conclusion:")
  if conf_total >= CONFIDENT_THRESHOLD:
    if frac_vlow > NOTABLE_DISORDER_THRESHOLD:
      conclusion = (
          "Protein is mostly confidently predicted, but contains notable"
          " disordered regions."
      )
    else:
      conclusion = (
          "Protein is confidently predicted and likely fully"
          " ordered/structured."
      )
  elif conf_total >= MODERATE_THRESHOLD:
    if frac_vlow >= MIXED_DISORDER_THRESHOLD:
      conclusion = (
          "Protein has a mixture of confidently predicted structured"
          " domains and significant intrinsically disordered regions."
      )
    else:
      conclusion = (
          "Protein has moderate prediction confidence. Certain regions"
          " might be flexible or poorly predicted."
      )
  else:
    if frac_vlow >= MOSTLY_DISORDERED_THRESHOLD:
      conclusion = (
          "Protein is mostly poorly predicted, likely being highly"
          " intrinsically disordered."
      )
    else:
      conclusion = "Protein prediction is of low confidence overall."
  print(f"  -> {conclusion}")
  print()

  return {
      "uniprot_id": accession,
      "global_plddt": global_plddt,
      "fractions": {
          "very_low": frac_vlow,
          "low": frac_low,
          "confident": frac_conf,
          "very_high": frac_vhigh,
      },
      "conclusion": conclusion,
  }


if __name__ == "__main__":
  parser = argparse.ArgumentParser(
      description="Analyze pLDDT confidence metrics from an AFDB metadata file"
  )
  parser.add_argument(
      "metadata_file",
      help="Path to the metadata JSON file (e.g., AF-P04637-F1-metadata.json)",
  )

  args = parser.parse_args()

  analyze_plddt(args.metadata_file)
