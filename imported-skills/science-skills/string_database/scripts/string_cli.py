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

"""STRING Database CLI Wrapper.

Provides access to STRING API v12.0 endpoints.
"""

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
import time
from typing import Any
import urllib.parse

from polite_http import http_client

CALLER_IDENTITY = 'google-science-skills'
URL_TEMPLATE = (
    'https://version-{api_version}-0.string-db.org/api/{format_type}/{endpoint}'
)
_CLIENT = None


class _DummyResponse:

  def __init__(self, content):
    self.content = content

  def json(self):
    return json.loads(self.content.decode('utf-8'))


def call_api(url: str, params: dict[str, Any], output_file: str):
  """Calls the STRING API and writes the response to a file.

  Args:
    url: The API URL to call.
    params: A dictionary of parameters to send with the request.
    output_file: The file path where the API response will be written.

  Returns:
    A dummy response object with a .json() method if the call is successful.
    Exits the program on API errors.
  """
  params['caller_identity'] = CALLER_IDENTITY
  data = urllib.parse.urlencode(params).encode('utf-8')
  assert _CLIENT is not None
  content = None
  try:
    content = _CLIENT.fetch_bytes(url, method='POST', data=data)
  except http_client.HttpError as e:
    print(f'API Error (HTTP {e.status_code}): {e}', file=sys.stderr)
    sys.exit(1)

  os.makedirs(os.path.dirname(os.path.abspath(output_file)), exist_ok=True)
  with open(output_file, 'wb') as f:
    f.write(content)
  print(f'Success: Output written to {output_file}')
  return _DummyResponse(content)


def main():
  parser = argparse.ArgumentParser(description='STRING Database CLI wrapper')
  parser.add_argument(
      '--api_version', default='12', help='STRING API version (default: 12)'
  )
  subparsers = parser.add_subparsers(dest='command', required=True)

  # Common parent parser for output
  parent_out = argparse.ArgumentParser(add_help=False)
  parent_out.add_argument(
      '--output', required=True, help='File to write output to'
  )

  # Common parent for identifiers and species
  parent_id = argparse.ArgumentParser(add_help=False)
  parent_id.add_argument(
      '--identifiers',
      nargs='+',
      required=True,
      help='List of protein names/IDs',
  )
  parent_id.add_argument(
      '--species', type=int, help='NCBI Taxon ID (e.g. 9606 for human)'
  )

  # map
  p_map = subparsers.add_parser(
      'map',
      parents=[parent_out, parent_id],
      help='Map identifiers to STRING IDs',
  )
  p_map.add_argument('--echo_query', type=int, choices=[0, 1], default=1)

  # network
  p_net = subparsers.add_parser(
      'network', parents=[parent_out, parent_id], help='Get interaction network'
  )
  p_net.add_argument('--required_score', type=int, help='0-1000 threshold')
  p_net.add_argument(
      '--network_type', choices=['functional', 'physical'], default='functional'
  )
  p_net.add_argument('--add_nodes', type=int, help='Number of nodes to add')

  # image
  p_img = subparsers.add_parser(
      'image', parents=[parent_out, parent_id], help='Get network image'
  )
  p_img.add_argument(
      '--format', choices=['image', 'highres_image', 'svg'], default='image'
  )
  p_img.add_argument(
      '--network_flavor',
      choices=['evidence', 'confidence', 'actions'],
      default='evidence',
  )
  p_img.add_argument('--add_color_nodes', type=int)

  # partners
  p_part = subparsers.add_parser(
      'partners',
      parents=[parent_out, parent_id],
      help='Get interaction partners',
  )
  p_part.add_argument('--limit', type=int, help='Max partners per protein')

  # homology
  subparsers.add_parser(
      'homology', parents=[parent_out, parent_id], help='Get homology scores'
  )

  # homology_best
  p_homb = subparsers.add_parser(
      'homology-best', parents=[parent_out, parent_id], help='Best homology hit'
  )
  p_homb.add_argument(
      '--species_b', help='Comma-separated target species (e.g., 10090,7227)'
  )

  # enrichment
  subparsers.add_parser(
      'enrichment',
      parents=[parent_out, parent_id],
      help='Functional enrichment',
  )

  # functional_annotation
  p_fa = subparsers.add_parser(
      'functional-annotation',
      parents=[parent_out, parent_id],
      help='Functional annotations',
  )
  p_fa.add_argument('--allow_pubmed', type=int, choices=[0, 1], default=0)

  # functional_terms (uses term_text instead of identifiers)
  p_ft = subparsers.add_parser(
      'functional-terms', parents=[parent_out], help='Search proteins by term'
  )
  p_ft.add_argument(
      '--term_text', required=True, help='e.g. Melanoma, GO:0008543'
  )
  p_ft.add_argument('--species', type=int, default=9606)

  # ppi_enrichment
  subparsers.add_parser(
      'ppi-enrichment', parents=[parent_out, parent_id], help='PPI enrichment'
  )

  # version
  subparsers.add_parser(
      'version', parents=[parent_out], help='Get STRING version'
  )

  # valuesranks API key
  subparsers.add_parser(
      'valuesranks-key',
      parents=[parent_out],
      help='Get API key for Values/Ranks',
  )

  # valuesranks submit
  p_vr_sub = subparsers.add_parser(
      'valuesranks-submit', parents=[parent_out], help='Submit Values/Ranks job'
  )
  p_vr_sub.add_argument('--api_key', required=True)
  p_vr_sub.add_argument(
      '--input_file', required=True, help='Tab-separated file of ID and value'
  )
  p_vr_sub.add_argument('--species', type=int, required=True)
  p_vr_sub.add_argument('--ge_fdr', type=float, default=0.01)

  # valuesranks status
  p_vr_stat = subparsers.add_parser(
      'valuesranks-status', parents=[parent_out], help='Check job status'
  )
  p_vr_stat.add_argument('--api_key', required=True)
  p_vr_stat.add_argument('--job_id', help='Omit to list all jobs')
  p_vr_stat.add_argument(
      '--wait',
      action='store_true',
      help='Wait for job to complete and download final TSV',
  )

  args = parser.parse_args()

  global _CLIENT
  base_url = f'https://version-{args.api_version}-0.string-db.org/'
  _CLIENT = http_client.HttpClient(base_url, qps=1)

  def _url(endpoint, *, format_type='tsv'):
    return URL_TEMPLATE.format(
        api_version=args.api_version, format_type=format_type, endpoint=endpoint
    )

  requires_species = [
      'map',
      'network',
      'image',
      'partners',
      'homology',
      'homology-best',
      'enrichment',
      'functional-annotation',
      'ppi-enrichment',
  ]
  if args.command in requires_species and (
      not hasattr(args, 'species') or args.species is None
  ):
    print(
        f"Error: Command '{args.command}' requires --species", file=sys.stderr
    )
    sys.exit(1)

  params = {}
  if hasattr(args, 'identifiers') and args.identifiers:
    params['identifiers'] = '\r'.join(args.identifiers)
  if hasattr(args, 'species') and args.species is not None:
    params['species'] = args.species

  if args.command == 'map':
    params['echo_query'] = args.echo_query
    call_api(_url('get_string_ids'), params, args.output)

  elif args.command == 'network':
    if args.required_score:
      params['required_score'] = args.required_score
    params['network_type'] = args.network_type
    if args.add_nodes:
      params['add_nodes'] = args.add_nodes
    call_api(_url('network'), params, args.output)

  elif args.command == 'image':
    params['network_flavor'] = args.network_flavor
    if args.add_color_nodes:
      params['add_color_nodes'] = args.add_color_nodes
    call_api(_url('network', format_type=args.format), params, args.output)

  elif args.command == 'partners':
    if args.limit:
      params['limit'] = args.limit
    call_api(_url('interaction_partners'), params, args.output)

  elif args.command == 'homology-best':
    if args.species_b:
      params['species_b'] = args.species_b.replace(',', '\r')
    call_api(_url('homology_best'), params, args.output)

  elif args.command == 'functional-annotation':
    params['allow_pubmed'] = args.allow_pubmed
    call_api(_url('functional_annotation'), params, args.output)

  elif args.command == 'functional-terms':
    params['term_text'] = args.term_text
    call_api(_url('functional_terms'), params, args.output)

  elif args.command == 'valuesranks-key':
    call_api(_url('get_api_key', format_type='json'), {}, args.output)

  elif args.command in ['enrichment', 'homology', 'ppi-enrichment', 'version']:
    call_api(_url(args.command.replace('-', '_')), params, args.output)

  elif args.command == 'valuesranks-submit':
    params['api_key'] = args.api_key
    params['species'] = args.species
    params['ge_fdr'] = args.ge_fdr
    try:
      with open(args.input_file, 'r') as f:
        lines = f.readlines()
      valid_lines = []
      for i, line in enumerate(lines):
        parts = line.strip().split('\t')
        if len(parts) >= 2:
          try:
            float(parts[1])
            valid_lines.append(f'{parts[0]}\t{parts[1]}')
          except ValueError:
            print(
                f"Skipping line {i+1} as it doesn't contain a valid numeric"
                f' value: {line.strip()}',
                file=sys.stderr,
            )
        elif line.strip():
          print(
              f"Skipping line {i+1} as it doesn't contain at least 2"
              f' tab-separated columns: {line.strip()}',
              file=sys.stderr,
          )
      params['identifiers'] = '\r'.join(valid_lines)
      if not params['identifiers']:
        print('Error: No valid data found in input file.', file=sys.stderr)
        sys.exit(1)
    except OSError as e:
      print(f'Error reading {args.input_file}: {e}', file=sys.stderr)
      sys.exit(1)
    url = _url('valuesranks_enrichment_submit', format_type='json')
    call_api(url, params, args.output)

  elif args.command == 'valuesranks-status':
    url = _url('valuesranks_enrichment_status', format_type='json')
    params['api_key'] = args.api_key
    if args.job_id:
      params['job_id'] = args.job_id

    if not args.wait or not args.job_id:
      call_api(url, params, args.output)
      return

    # Loop until the call completes.
    while True:
      response = call_api(url, params, args.output)
      try:
        data = response.json()
      except ValueError:
        print('Error parsing status response.', file=sys.stderr)
        sys.exit(1)

      if not isinstance(data, list) or len(data) == 0:
        print(f'Unexpected response format: {data}', file=sys.stderr)
        sys.exit(1)

      job_info = data[0]
      status = job_info.get('status')
      if status == 'success':
        if download_url := job_info.get('download_url'):
          print(
              f'Job success. Downloading from {download_url} to {args.output}'
          )
          try:
            content = _CLIENT.fetch_bytes(download_url)
          except http_client.HttpError as e:
            print(
                f'Download Error (HTTP {e.status_code}): {e}',
                file=sys.stderr,
            )
            sys.exit(1)
          with open(args.output, 'wb') as f:
            f.write(content)
          break
        else:
          print('Success but no download URL found.', file=sys.stderr)
          break
      elif status == 'running' or status == 'queued':
        print(f'Job still {status}... waiting 5 seconds.')
        time.sleep(5)
      else:
        print(f'Job failed or unknown status: {status}', file=sys.stderr)
        sys.exit(1)


if __name__ == '__main__':
  main()
