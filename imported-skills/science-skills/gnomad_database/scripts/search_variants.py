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

"""Searches for variants in a gene or region from gnomAD."""

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


def search_variants_gene(
    gene_symbol: str,
    consequence: str,
    dataset: str,
    output_path: str,
):
  """Searches for variants in a gene from gnomAD."""
  url = "https://gnomad.broadinstitute.org/api"
  query = """
  query($geneSymbol: String!, $dataset: DatasetId!, $referenceGenome: ReferenceGenomeId!) {
    gene(gene_symbol: $geneSymbol, reference_genome: $referenceGenome) {
      variants(dataset: $dataset) {
        variant_id
        rsids
        consequence
        exome {
          ac
          an
          af
          homozygote_count
          hemizygote_count
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
          populations {
            id
            ac
            an
            homozygote_count
            hemizygote_count
          }
        }
      }
    }
  }
  """

  variables = {
      "geneSymbol": gene_symbol,
      "dataset": dataset,
      "referenceGenome": "GRCh38",
  }

  response_data = CLIENT.fetch_json(
      url, method="POST", json_body={"query": query, "variables": variables}
  )
  data = response_data
  if "data" in data and data["data"].get("gene"):
    variants = data["data"]["gene"].get("variants", [])
    if consequence:
      variants = [
          v
          for v in variants
          if consequence.lower() in (v.get("consequence") or "").lower()
      ]
    data["data"]["gene"]["variants"] = variants

  result = json.dumps(data, indent=2)
  os.makedirs(os.path.dirname(output_path), exist_ok=True)
  with open(output_path, "w") as f:
    f.write(result)
    f.write("\n")


def search_variants_region(
    chrom: str,
    start: int,
    stop: int,
    dataset: str,
    output_path: str,
):
  """Searches for variants in a region from gnomAD."""
  url = "https://gnomad.broadinstitute.org/api"
  query = """
  query($chrom: String!, $start: Int!, $stop: Int!, $dataset: DatasetId!, $referenceGenome: ReferenceGenomeId!) {
    region(chrom: $chrom, start: $start, stop: $stop, reference_genome: $referenceGenome) {
      variants(dataset: $dataset) {
        variant_id
        rsids
        consequence
        exome {
          ac
          an
          af
          homozygote_count
          hemizygote_count
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
          populations {
            id
            ac
            an
            homozygote_count
            hemizygote_count
          }
        }
      }
    }
  }
  """

  variables = {
      "chrom": str(chrom),
      "start": int(start),
      "stop": int(stop),
      "dataset": dataset,
      "referenceGenome": "GRCh38",
  }

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
      description="Search variants in a gene or region from gnomAD"
  )
  parser.add_argument("--gene", help="Gene symbol (e.g. PCSK9)")
  parser.add_argument("--chrom", help="Chromosome")
  parser.add_argument("--start", type=int, help="Start position")
  parser.add_argument("--end", type=int, help="End position")
  parser.add_argument(
      "--consequence", help="Filter by consequence (e.g. pLoF, missense)"
  )
  parser.add_argument(
      "--dataset", default="gnomad_r4", help="gnomAD dataset to query"
  )
  parser.add_argument("--output", "-o", required=True, help="Output file path.")
  args = parser.parse_args()

  if args.gene:
    search_variants_gene(args.gene, args.consequence, args.dataset, args.output)
  elif args.chrom and args.start and args.end:
    search_variants_region(
        args.chrom, args.start, args.end, args.dataset, args.output
    )
  else:
    print(
        json.dumps({
            "error": "Must provide either --gene OR --chrom, --start, and --end"
        }),
        file=sys.stderr,
    )
    sys.exit(1)
