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

"""CLI wrapper for GTEx API V2.

Follows GTEx Portal Terms of Use by fetching sequentially and handling
pagination.
"""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
# ]
# ///

import argparse
import json
import sys
import urllib.parse

from polite_http import http_client

BASE_URL = 'https://gtexportal.org/api/v2'
DATASET_ID = 'gtex_v10'
GENCODE_VERSION = 'v39'
CLIENT = http_client.HttpClient(BASE_URL, qps=1.0)

# Optional cache for tissues to avoid fetching repeatedly
TISSUE_CACHE = None


def _fetch(url, params=None):
  """Fetches URL, with optional query parameters, using HttpClient."""
  if params:
    # Filter out None values
    params = {k: v for k, v in params.items() if v is not None}
    query_string = urllib.parse.urlencode(params, doseq=True)
    full_url = f'{url}?{query_string}'
  else:
    full_url = url

  return CLIENT.fetch_json(full_url)


def _fetch_paginated(url, params=None):
  """Fetches all pages from a paginated endpoint."""
  if params is None:
    params = {}

  all_data = []
  page = 0
  while True:
    params['page'] = page
    response = _fetch(url, params)

    # Some endpoints don't use 'data' wrapping or 'paging_info'
    if 'paging_info' not in response:
      return response

    data = response.get('data', [])
    all_data.extend(data)

    paging = response.get('paging_info', {})
    total_pages = paging.get('numberOfPages', 0)

    if page >= total_pages - 1:
      break
    page += 1

  return all_data


def get_tissue_mapping():
  """Fetches the list of tissues and maps names to tissueSiteDetailId."""
  global TISSUE_CACHE
  if TISSUE_CACHE is not None:
    return TISSUE_CACHE

  url = f'{BASE_URL}/dataset/tissueSiteDetail'
  data = _fetch_paginated(url, {'datasetId': DATASET_ID})

  mapping = {}
  for t in data:
    id_ = t.get('tissueSiteDetailId')
    name = t.get('tissueSiteDetail')
    if id_ and name:
      mapping[id_.lower()] = id_
      mapping[name.lower()] = id_
      # Allow "Esophagus - Muscularis" instead of "Esophagus_Muscularis", etc.
      mapping[id_.replace('_', ' ').lower()] = id_
      mapping[name.replace('-', ' ').lower()] = id_

  TISSUE_CACHE = mapping
  return mapping


def resolve_tissue(tissue_str):
  mapping = get_tissue_mapping()
  cleaned = tissue_str.strip().lower()
  if cleaned in mapping:
    return mapping[cleaned]
  # Try more fuzzy matching if needed
  cleaned_no_hyphen = cleaned.replace('-', ' ')
  if cleaned_no_hyphen in mapping:
    return mapping[cleaned_no_hyphen]
  sys.stderr.write(f"Error: Unknown tissue '{tissue_str}'.\n")
  sys.exit(1)


def resolve_gencode_id(gene_symbol, output_file):
  """Maps a standard gene symbol to its Versioned GENCODE ID."""
  url = f'{BASE_URL}/reference/gene'
  data = _fetch_paginated(
      url, {'geneId': gene_symbol, 'gencodeVersion': GENCODE_VERSION}
  )
  if not data:
    sys.stderr.write(f"Error: Could not find GENCODE ID for '{gene_symbol}'.\n")
    sys.exit(1)

  # Return the first matching exact symbol if possible, else just the first one
  best_match = data[0]
  for d in data:
    if d.get('geneSymbol', '').lower() == gene_symbol.lower():
      best_match = d
      break

  result = {
      'gene_symbol': best_match.get('geneSymbol'),
      'gencode_id': best_match.get('gencodeId'),
      'chromosome': best_match.get('chromosome'),
      'start': best_match.get('start'),
      'end': best_match.get('end'),
      'gene_type': best_match.get('geneType'),
  }

  with open(output_file, 'w') as f:
    json.dump(result, f, indent=2)


def get_median_expression(gencode_id, tissues, output_file):
  """Returns the median expression (TPM) for a gene across tissues."""
  url = f'{BASE_URL}/expression/medianGeneExpression'
  params = {'gencodeId': gencode_id, 'datasetId': DATASET_ID}

  if tissues:
    tissue_list = [t.strip() for t in tissues.split(',')]
    resolved_tissues = [resolve_tissue(t) for t in tissue_list]
    # The API accepts multiple tissueSiteDetailId parameters.
    # urllib.urlencode with doseq=True handles list correctly.
    params['tissueSiteDetailId'] = resolved_tissues

  data = _fetch_paginated(url, params)

  with open(output_file, 'w') as f:
    json.dump(data, f, indent=2)


def get_top_expressed_tissues(gencode_id, n, output_file):
  url = f'{BASE_URL}/expression/medianGeneExpression'
  params = {'gencodeId': gencode_id, 'datasetId': DATASET_ID}

  data = _fetch_paginated(url, params)
  # Sort by median expression, descending
  sorted_data = sorted(data, key=lambda x: x.get('median', 0), reverse=True)

  top_n = sorted_data[:n]
  with open(output_file, 'w') as f:
    json.dump(top_n, f, indent=2)


def get_gene_eqtls(gencode_id, tissues, output_file):
  """Returns all significant eQTLs for a gene across tissues."""
  url = f'{BASE_URL}/association/singleTissueEqtl'
  params = {'gencodeId': gencode_id, 'datasetId': DATASET_ID}

  if tissues:
    tissue_list = [t.strip() for t in tissues.split(',')]
    resolved_tissues = [resolve_tissue(t) for t in tissue_list]
    params['tissueSiteDetailId'] = resolved_tissues

  data = _fetch_paginated(url, params)

  with open(output_file, 'w') as f:
    json.dump(data, f, indent=2)


def get_eqtls_in_region(chromosome, start, end, tissue, output_file):
  """Returns all significant eQTLs for a region in a tissue."""
  url = f'{BASE_URL}/association/singleTissueEqtlByLocation'
  resolved_tissue = resolve_tissue(tissue)

  params = {
      'chromosome': chromosome,
      'start': start,
      'end': end,
      'tissueSiteDetailId': resolved_tissue,
      'datasetId': DATASET_ID,
  }

  # This endpoint is NOT paginated per API docs and does not return paging_info.
  data = _fetch(url, params)

  with open(output_file, 'w') as f:
    json.dump(data, f, indent=2)


def main():
  parser = argparse.ArgumentParser(description='GTEx Portal API V2 CLI')
  subparsers = parser.add_subparsers(dest='command', required=True)

  p_resolve = subparsers.add_parser(
      'resolve-gencode-id',
      help='Map a standard gene symbol to its Versioned GENCODE ID',
  )
  p_resolve.add_argument('gene_symbol', help='Gene symbol (e.g. TNF)')
  p_resolve.add_argument('--output', default='/tmp/gtex_output.json')

  p_median = subparsers.add_parser(
      'get-median-expression', help='Get median expression (TPM)'
  )
  p_median.add_argument('gencode_id', help='Versioned GENCODE ID')
  p_median.add_argument('--tissues', help='Comma-separated list of tissue IDs')
  p_median.add_argument('--output', default='/tmp/gtex_output.json')

  p_top = subparsers.add_parser(
      'get-top-expressed-tissues', help='Get top expressed tissues for a gene'
  )
  p_top.add_argument('gencode_id', help='Versioned GENCODE ID')
  p_top.add_argument(
      '--n', type=int, default=5, help='Number of tissues to return'
  )
  p_top.add_argument('--output', default='/tmp/gtex_output.json')

  p_eqtls = subparsers.add_parser(
      'get-gene-eqtls', help='Get all significant eQTLs for a gene'
  )
  p_eqtls.add_argument('gencode_id', help='Versioned GENCODE ID')
  p_eqtls.add_argument('--tissues', help='Comma-separated list of tissue IDs')
  p_eqtls.add_argument('--output', default='/tmp/gtex_output.json')

  p_region = subparsers.add_parser(
      'get-eqtls-in-region', help='Get significant eQTLs in a region'
  )
  p_region.add_argument('chromosome', help='Chromosome (e.g. chr17)')
  p_region.add_argument('start', type=int, help='Start position')
  p_region.add_argument('end', type=int, help='End position')
  p_region.add_argument('tissue_id', help='Target tissue ID')
  p_region.add_argument('--output', default='/tmp/gtex_output.json')

  args = parser.parse_args()

  if args.command == 'resolve-gencode-id':
    resolve_gencode_id(args.gene_symbol, args.output)
  elif args.command == 'get-median-expression':
    get_median_expression(args.gencode_id, args.tissues, args.output)
  elif args.command == 'get-top-expressed-tissues':
    get_top_expressed_tissues(args.gencode_id, args.n, args.output)
  elif args.command == 'get-gene-eqtls':
    get_gene_eqtls(args.gencode_id, args.tissues, args.output)
  elif args.command == 'get-eqtls-in-region':
    get_eqtls_in_region(
        args.chromosome, args.start, args.end, args.tissue_id, args.output
    )
  else:
    parser.print_help()


if __name__ == '__main__':
  main()
