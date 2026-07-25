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

"""Fetches variant frequency from gnomAD."""

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

from polite_http import http_client

# Respect 10 queries per minute requirement.
CLIENT = http_client.HttpClient("https://gnomad.broadinstitute.org", qps=0.1666)


def resolve_rsid(rsid: str, dataset: str) -> str:
  """Resolves an rsID to a variant ID."""
  url = "https://gnomad.broadinstitute.org/api"
  query = """
  query($query: String!, $dataset: DatasetId!) {
    variant_search(query: $query, dataset: $dataset) {
      variant_id
    }
  }
  """
  variables = {"query": rsid, "dataset": dataset}
  response_data = CLIENT.fetch_json(
      url, method="POST", json_body={"query": query, "variables": variables}
  )

  variants = response_data.get("data", {}).get("variant_search", [])
  if not variants:
    print(
        json.dumps({"error": f"Could not resolve rsID {rsid}"}), file=sys.stderr
    )
    sys.exit(1)

  # For simplicity, return the first match if multiple
  return variants[0]["variant_id"]


def get_variant_frequency(
    variant_id: str,
    rsid: str,
    dataset: str,
    output_path: str,
):
  """Fetches variant frequency from gnomAD."""
  if rsid and not variant_id:
    variant_id = resolve_rsid(rsid, dataset)
  elif not variant_id:
    print(
        json.dumps({"error": "Must provide either variant_id or rsid"}),
        file=sys.stderr,
    )
    sys.exit(1)

  url = "https://gnomad.broadinstitute.org/api"
  # GraphQL query for variant frequency and filtering allele frequency
  query = """
  query($variantId: String!, $dataset: DatasetId!) {
    variant(variantId: $variantId, dataset: $dataset) {
      variant_id
      rsids
      exome {
        ac
        an
        af
        homozygote_count
        hemizygote_count
        faf95 {
          popmax
          popmax_population
        }
        faf99 {
          popmax
          popmax_population
        }
        populations {
          id
          ac
          an
          homozygote_count
          hemizygote_count
        }
      }
      genome {
        ac
        an
        af
        homozygote_count
        hemizygote_count
        faf95 {
          popmax
          popmax_population
        }
        faf99 {
          popmax
          popmax_population
        }
        populations {
          id
          ac
          an
          homozygote_count
          hemizygote_count
        }
      }
      joint {
        ac
        an
        homozygote_count
        hemizygote_count
        faf95 {
          popmax
          popmax_population
        }
        faf99 {
          popmax
          popmax_population
        }
      }
    }
  }
  """

  variables = {"variantId": variant_id, "dataset": dataset}

  response_data = CLIENT.fetch_json(
      url, method="POST", json_body={"query": query, "variables": variables}
  )
  result = json.dumps(response_data, indent=2)
  os.makedirs(os.path.dirname(output_path), exist_ok=True)
  with open(output_path, "w") as f:
    f.write(result)
    f.write("\n")


if __name__ == "__main__":
  parser = argparse.ArgumentParser(
      description="Fetch variant frequency from gnomAD"
  )
  parser.add_argument(
      "--variant_id",
      help="Variant ID in chrom-pos-ref-alt format",
  )
  parser.add_argument(
      "--rsid",
      help="Variant rsID (e.g. rs121918506)",
  )
  parser.add_argument(
      "--dataset", default="gnomad_r4", help="gnomAD dataset to query"
  )
  parser.add_argument(
      "--output",
      "-o",
      required=True,
      help="Output file path.",
  )
  args = parser.parse_args()

  get_variant_frequency(args.variant_id, args.rsid, args.dataset, args.output)
