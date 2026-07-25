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

"""Generates tissue_ontology_mapping.json from the AlphaGenome API.

Usage:
 uv run scripts/generate_ontology_mapping.py

Can be imported and called programmatically:
  from generate_ontology_mapping import generate_mapping_file
  generate_mapping_file('/path/to/output.json')
"""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "alphagenome",
#   "pandas",
#   "python-dotenv",
# ]
# ///

import json
import logging
import os

import dotenv

logger = logging.getLogger(__name__)

from alphagenome.models import dna_client
import pandas as pd


def clean_list(series: pd.Series) -> list[str]:
  """Clean a pandas series to a sorted list of unique non-empty values."""
  vals = set(series.dropna().astype(str))
  vals = {
      v
      for v in vals
      if v.strip() and v.lower() not in ('none', 'nan', 'null', '')
  }
  return sorted(list(vals))


def prune_empty(d):
  """Recursively remove empty values from nested dicts and lists."""
  if not isinstance(d, (dict, list)):
    return d
  if isinstance(d, list):
    return [
        v for v in (prune_empty(v) for v in d) if v not in (None, [], {}, '')
    ]
  if isinstance(d, dict):
    return {
        k: v
        for k, v in ((k, prune_empty(v)) for k, v in d.items())
        if v not in (None, [], {}, '')
    }


def create_biological_mapping(df: pd.DataFrame) -> dict:
  """Create a mapping from ontology CURIEs to biosample metadata."""
  df_proc = df.drop(
      columns=['genetically_modified', 'nonzero_mean', 'name'], errors='ignore'
  ).copy()
  df_proc['output_type'] = (
      df_proc['output_type']
      .astype(str)
      .str.replace('OutputType.', '', regex=False)
  )
  mapping = {}
  for curie, group in df_proc.groupby('ontology_curie'):
    if pd.isna(curie):
      continue
    entry = {
        'biosample': {
            'name': group['biosample_name'].iloc[0],
            'type': group['biosample_type'].iloc[0],
            'life': clean_list(group['biosample_life_stage']),
            'sources': clean_list(group['data_source']),
        },
        'molecular': {
            'histones': clean_list(group['histone_mark']),
            'tfs': clean_list(group['transcription_factor']),
        },
        'assays': {
            assay: {
                'tracks': clean_list(ag['output_type']),
                'marks': (
                    clean_list(ag['histone_mark'])
                    + clean_list(ag['transcription_factor'])
                ),
            }
            for assay, ag in group.groupby('Assay title')
        },
    }
    mapping[curie] = prune_empty(entry)
  return mapping


def generate_mapping_file(output_path: str) -> dict:
  """Fetches AlphaGenome metadata and writes the ontology mapping JSON.

  Args:
    output_path: Path to write the tissue_ontology_mapping.json file.

  Returns:
    The generated mapping dictionary.

  Raises:
    RuntimeError: If ALPHAGENOME_API_KEY is not set.
  """
  api_key = os.environ.get('ALPHAGENOME_API_KEY')
  if not api_key:
    raise RuntimeError(
        'ALPHAGENOME_API_KEY not set. '
        'Ensure the `.env` file contains ALPHAGENOME_API_KEY=<key> and '
        'use uv run to run this script.'
    )

  logger.info('Fetching output metadata from AlphaGenome API...')
  dna_model = dna_client.create(api_key=api_key)
  df = dna_model.output_metadata(dna_client.Organism.HOMO_SAPIENS).concatenate()
  logger.info('Got %d rows.', len(df))

  logger.info('Building ontology mapping...')
  mapping = create_biological_mapping(df)
  logger.info('Created %d entries.', len(mapping))

  os.makedirs(os.path.dirname(output_path), exist_ok=True)
  with open(output_path, 'w') as f:
    json.dump(mapping, f, indent=2)
  logger.info('Wrote mapping to %s', output_path)

  return mapping


def get_tissue_ontology_mapping_path(resource_dir: str) -> str:
  """Returns the path to the tissue ontology mapping JSON file.

  Args:
    resource_dir: Directory where the resources are stored.

  Returns:
    Absolute path to tissue_ontology_mapping.json.
  """
  return os.path.join(resource_dir, 'tissue_ontology_mapping.json')


def main():
  dotenv.load_dotenv(os.path.expanduser('~/.env'))
  script_dir = os.path.dirname(os.path.abspath(__file__))
  resource_dir = os.path.join(script_dir, '..', 'resources')
  generate_mapping_file(get_tissue_ontology_mapping_path(resource_dir))


if __name__ == '__main__':
  main()
