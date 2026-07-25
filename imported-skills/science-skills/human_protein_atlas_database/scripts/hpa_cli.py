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

"""CLI wrapper for the Human Protein Atlas (HPA).

Follows HPA Terms of Use by fetching sequentially and handling requests.
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
import xml.etree.ElementTree as ET

from polite_http import http_client

BASE_URL = 'https://www.proteinatlas.org/'
CLIENT = http_client.HttpClient(BASE_URL, qps=2.0)


def _fetch_json(params):
  """Fetches data from the HPA search API."""
  params['format'] = 'json'
  params['compress'] = 'no'
  query_string = urllib.parse.urlencode(params)
  base_api_url = urllib.parse.urljoin(BASE_URL, 'api/search_download.php')
  full_url = f'{base_api_url}?{query_string}'
  content = CLIENT.fetch_bytes(full_url)
  if not content:
    return []
  return json.loads(content.decode('utf-8'))


def _fetch_xml(ensembl_id):
  """Fetches and parses the XML entry for a given Ensembl ID."""
  full_url = urllib.parse.urljoin(BASE_URL, f'{ensembl_id}.xml')
  content = CLIENT.fetch_bytes(full_url)
  return ET.fromstring(content)


def resolve_ensembl_id(gene_symbol, output_file):
  """Maps a common gene symbol to its Ensembl ID."""
  params = {'search': gene_symbol, 'columns': 'g,eg,gs,gd'}
  data = _fetch_json(params)
  if not data:
    sys.stderr.write(f"Error: Could not find Ensembl ID for '{gene_symbol}'.\n")
    sys.exit(1)

  # Return the best exact match if possible
  best_match = data[0]
  for d in data:
    if d.get('Gene', '').lower() == gene_symbol.lower():
      best_match = d
      break

  result = {
      'gene_symbol': best_match.get('Gene'),
      'ensembl_id': best_match.get('Ensembl'),
      'synonyms': best_match.get('Gene synonym'),
      'description': best_match.get('Gene description'),
  }

  with open(output_file, 'w') as f:
    json.dump(result, f, indent=2)


def get_tissue_expression(ensembl_id, tissues, output_file):
  """Returns tissue protein expression levels (IHC)."""
  root = _fetch_xml(ensembl_id)

  # The XML namespace is usually specified, e.g.,
  # xmlns="http://www.proteinatlas.org/search/download/proteinatlas.xsd"
  # But we can search without namespace by using local name or wildcards if
  # needed. We clean the tags by stripping namespaces for easier parsing.
  for elem in root.iter():
    if '}' in elem.tag:
      elem.tag = elem.tag.split('}', 1)[1]

  expression_data = []

  # Find <tissueExpression source="HPA" technology="IHC" assayType="tissue">
  for te in root.findall('.//tissueExpression'):
    if te.get('technology') == 'IHC':
      for data_node in te.findall('./data'):
        tissue_node = data_node.find('tissue')
        level_node = data_node.find('level')

        if tissue_node is not None and level_node is not None:
          tissue_name = tissue_node.text
          level = level_node.text
          expression_data.append({
              'tissue': tissue_name,
              'organ': tissue_node.get('organ'),
              'level': level,
          })

  if tissues:
    tissue_filter = [t.strip().lower() for t in tissues.split(',')]
    expression_data = [
        d for d in expression_data if d['tissue'].lower() in tissue_filter
    ]

  with open(output_file, 'w') as f:
    json.dump(expression_data, f, indent=2)


def get_subcellular_location(ensembl_id, output_file):
  """Retrieves subcellular locations for a protein."""
  params = {'search': ensembl_id, 'columns': 'g,eg,scl,scml,scal'}
  data = _fetch_json(params)

  result = {}
  if data:
    result = {
        'ensembl_id': data[0].get('Ensembl'),
        'gene_symbol': data[0].get('Gene'),
        'subcellular_locations': data[0].get('Subcellular location', []),
        'main_locations': data[0].get('Subcellular main location', []),
        'additional_locations': (
            data[0].get('Subcellular additional location', [])
        ),
    }

  with open(output_file, 'w') as f:
    json.dump(result, f, indent=2)


def get_atlas_entry(ensembl_id, format_type, output_file):
  """Fetches the full metadata entry."""
  if format_type.lower() == 'json':
    # Let's fetch all relevant columns for the entry
    cols = [
        'g',
        'gs',
        'eg',
        'gd',
        'up',
        'scl',
        'scml',
        'scal',
        'pc',
        'ccdp',
        'ectissue',
        'rnats',
        'rnatd',
        'rnatss',
    ]
    params = {'search': ensembl_id, 'columns': ','.join(cols)}
    data = _fetch_json(params)
    entry = data[0] if data else {}

    # Also fetch the XML to get the verification reliability
    try:
      root = _fetch_xml(ensembl_id)
      for elem in root.iter():
        if '}' in elem.tag:
          elem.tag = elem.tag.split('}', 1)[1]

      ver = root.find('.//tissueExpression/verification')
      if ver is not None:
        entry['RNA_protein_agreement'] = {
            'reliability': ver.text,
            'description': ver.get('description'),
        }
    except (ET.ParseError, AttributeError, TypeError):
      # If XML fetching or parsing fails, just ignore and return the JSON entry
      pass

    with open(output_file, 'w') as f:
      json.dump(entry, f, indent=2)
  else:
    sys.stderr.write(
        f"Error: Format '{format_type}' not supported currently. Only JSON is"
        ' supported.\n'
    )
    sys.exit(1)


def search_hpa(query, output_file):
  """Searches HPA based on specific criteria."""
  params = {'search': query, 'columns': 'g,eg,gd,scl,ectissue'}
  data = _fetch_json(params)

  with open(output_file, 'w') as f:
    json.dump(data, f, indent=2)


def main():
  parser = argparse.ArgumentParser(description='Human Protein Atlas CLI')
  subparsers = parser.add_subparsers(dest='command', required=True)

  p_resolve = subparsers.add_parser(
      'resolve-ensembl-id', help='Map a standard gene symbol to its Ensembl ID'
  )
  p_resolve.add_argument('gene_symbol', help='Gene symbol (e.g. TP53)')
  p_resolve.add_argument('--output', default='/tmp/hpa_output.json')

  p_tissue = subparsers.add_parser(
      'get-tissue-expression', help='Get tissue protein levels'
  )
  p_tissue.add_argument('ensembl_id', help='Ensembl Gene ID')
  p_tissue.add_argument(
      '--tissues', help='Comma-separated list of tissue names'
  )
  p_tissue.add_argument('--output', default='/tmp/hpa_output.json')

  p_subcell = subparsers.add_parser(
      'get-subcellular-location', help='Get subcellular location'
  )
  p_subcell.add_argument('ensembl_id', help='Ensembl Gene ID')
  p_subcell.add_argument('--output', default='/tmp/hpa_output.json')

  p_entry = subparsers.add_parser(
      'get-atlas-entry', help='Get full HPA metadata entry'
  )
  p_entry.add_argument('ensembl_id', help='Ensembl Gene ID')
  p_entry.add_argument(
      '--format',
      default='json',
      help='Format of the returned entry (e.g., json)',
  )
  p_entry.add_argument('--output', default='/tmp/hpa_output.json')

  p_search = subparsers.add_parser('search-hpa', help='Search HPA by attribute')
  p_search.add_argument('--query', required=True, help='Search query string')
  p_search.add_argument('--output', default='/tmp/hpa_output.json')

  args = parser.parse_args()

  if args.command == 'resolve-ensembl-id':
    resolve_ensembl_id(args.gene_symbol, args.output)
  elif args.command == 'get-tissue-expression':
    get_tissue_expression(args.ensembl_id, args.tissues, args.output)
  elif args.command == 'get-subcellular-location':
    get_subcellular_location(args.ensembl_id, args.output)
  elif args.command == 'get-atlas-entry':
    get_atlas_entry(args.ensembl_id, args.format, args.output)
  elif args.command == 'search-hpa':
    search_hpa(args.query, args.output)
  else:
    parser.print_help()


if __name__ == '__main__':
  main()
