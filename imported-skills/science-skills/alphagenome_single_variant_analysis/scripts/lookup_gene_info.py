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

"""Comprehensive gene and transcript lookup tool using GTF data.

Usage:
  # 1. Lookup gene symbol or coordinate to get ID and location
  uv run scripts/lookup_gene_info.py --genes='TP53,BRCA1'
  uv run scripts/lookup_gene_info.py --genes='chr17:7675148'

  # 2. Find genes near a coordinate
  uv run scripts/lookup_gene_info.py --coord='chr17:7675148' --window=50000

  # 3. List and filter transcripts for a gene
  uv run scripts/lookup_gene_info.py --genes='EGFR' --transcripts --mane
"""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "alphagenome",
#   "pandas",
#   "python-dotenv",
# ]
# ///

from __future__ import annotations

import argparse
import os
import re
from typing import Sequence

from alphagenome.data import gene_annotation
import dotenv
import pandas as pd

GTF_URL = (
    'https://storage.googleapis.com/alphagenome/reference/gencode/'
    'hg38/gencode.v46.annotation.gtf.gz.feather'
)


def load_gtf() -> pd.DataFrame:
  """Loads the GTF feather file."""
  print(f'Loading GTF from {GTF_URL}...')
  return pd.read_feather(GTF_URL)


def parse_gene_input(genes: list[str]) -> list[str]:
  """Parses comma-separated gene input and deduplicates."""
  parsed = set()
  for gene in genes:
    parsed |= {x.strip() for x in gene.split(',') if x.strip()}
  return sorted(parsed)


def classify_queries(queries: list[str]) -> tuple[list[str], list[str]]:
  """Classifies queries into coordinates and gene symbols."""
  coords = []
  symbols = []
  for query in queries:
    if re.match(r'^chr[0-9XYM]+:\d+', query):
      coords.append(query)
    else:
      symbols.append(query)
  return coords, symbols


def parse_coord(coord_str: str) -> tuple[str, int, int]:
  """Parses coordinate string like chr1:100-200 or chr1:150."""
  chrom, pos_part = coord_str.split(':', 1)

  if '-' in pos_part:
    start_str, end_str = pos_part.split('-')
    return chrom, int(start_str), int(end_str)
  else:
    pos = int(pos_part)
    return chrom, pos, pos


# --- Mode 1: Gene Symbol <-> Coord Lookup (from lookup_ensg_gtf) ---
def run_gene_lookup(gtf: pd.DataFrame, genes_input: list[str]) -> None:
  """Looks up gene symbols or coordinates in GTF."""
  genes_of_interest = parse_gene_input(genes_input)
  coords_to_lookup, symbols_to_lookup = classify_queries(genes_of_interest)

  results = []

  # Handle symbols
  if symbols_to_lookup:
    mask = gtf['gene_name'].isin(symbols_to_lookup)
    result_df = gtf[mask][
        ['gene_name', 'gene_id_nopatch', 'Chromosome', 'Start', 'End', 'Strand']
    ]
    results.append(result_df)

  # Handle coordinates
  for coord in coords_to_lookup:
    chrom, pos, _ = parse_coord(coord)
    mask = (
        (gtf['Chromosome'] == chrom)
        & (gtf['Start'] <= pos)
        & (gtf['End'] >= pos)
    )
    result_df = gtf[mask][
        ['gene_name', 'gene_id_nopatch', 'Chromosome', 'Start', 'End', 'Strand']
    ]
    results.append(result_df)

  if not results:
    print('No matches found.')
    return

  df = pd.concat(results).drop_duplicates()
  if df.empty:
    print('No matches found.')
  else:
    print(df.to_string(index=False))


# --- Mode 2: Find Genes at Coordinate (from lookup_gene_at_coord) ---
def run_coord_search(gtf: pd.DataFrame, coord: str, window: int) -> None:
  """Finds genes near a coordinate."""
  chrom, start, end = parse_coord(coord)

  if start == end:
    search_start = start - window
    search_end = end + window
  else:
    search_start, search_end = start, end

  print(f'\nSearching for genes at {chrom}:{search_start:,}-{search_end:,}')
  print('-' * 50)

  mask = (
      (gtf['Chromosome'] == chrom)
      & (gtf['Start'] <= search_end)
      & (gtf['End'] >= search_start)
  )

  matching_genes = gtf[mask].copy()

  if matching_genes.empty:
    print('No genes found in this region.')
    return

  # Calculate distance if it's a single point query
  if start == end:

    def calc_dist(row):
      if row['Start'] <= start <= row['End']:
        return 0
      return min(abs(row['Start'] - start), abs(row['End'] - start))

    matching_genes['Distance'] = matching_genes.apply(calc_dist, axis=1)
    matching_genes = matching_genes.sort_values('Distance')
    cols = [
        'gene_name',
        'gene_id_nopatch',
        'Chromosome',
        'Start',
        'End',
        'Distance',
    ]
  else:
    matching_genes = matching_genes.sort_values('Start')
    cols = ['gene_name', 'gene_id_nopatch', 'Chromosome', 'Start', 'End']

  # Keep only gene features to avoid duplicate rows for exons/transcripts
  feature_col = 'Feature' if 'Feature' in matching_genes.columns else 'feature'
  if feature_col in matching_genes.columns:
    matching_genes = matching_genes[matching_genes[feature_col] == 'gene']

  if matching_genes.empty:
    print(
        'No gene features found (only exons/transcripts). Showing unique gene'
        ' names:'
    )
    print(matching_genes['gene_name'].unique())
  else:
    print(matching_genes[cols].drop_duplicates().to_string(index=False))


# --- Mode 3: List and Filter Transcripts (from lookup_transcripts) ---
def run_transcript_lookup(
    gtf: pd.DataFrame,
    genes_input: list[str],
    mane: bool,
    protein_coding: bool,
    transcript_support_level: str | None,
    longest: bool,
    details: bool,
) -> None:
  """Lists and filters transcripts for genes."""
  genes_list = parse_gene_input(genes_input)

  filtered = gtf[gtf['gene_name'].isin(genes_list)].copy()

  if filtered.empty:
    print(f'No data found for genes: {genes_list}')
    return

  if mane:
    print('Filtering to MANE transcripts...')
    filtered = gene_annotation.filter_to_mane_select_transcript(filtered)

  if protein_coding:
    print('Filtering to protein coding transcripts...')
    filtered = gene_annotation.filter_to_protein_coding_transcript(filtered)

  if transcript_support_level:
    print(
        f'Filtering to Transcript Support Level: {transcript_support_level}...'
    )
    tsl_list = [x.strip() for x in transcript_support_level.split(',')]
    if 'transcript_support_level' in filtered.columns:
      filtered['tsl_clean'] = (
          filtered['transcript_support_level'].astype(str).str.extract(r'^(\d)')
      )
      filtered = filtered[filtered['tsl_clean'].isin(tsl_list)]
    else:
      print(
          'Warning: "transcript_support_level" column not found. Cannot filter'
          ' by TSL.'
      )

  if longest:
    print('Filtering to longest transcript per gene...')
    filtered = gene_annotation.filter_to_longest_transcript(filtered)

  cols = ['gene_name', 'transcript_id']
  if details:
    for column in [
        'transcript_type',
        'transcript_support_level',
        'Chromosome',
        'Start',
        'End',
    ]:
      if column in filtered.columns:
        cols.append(column)

  print('\nResults:')
  if 'Feature' in filtered.columns:
    transcript_features = filtered[filtered['Feature'] == 'transcript']
    if not transcript_features.empty:
      filtered = transcript_features

  print(filtered[cols].drop_duplicates().to_string(index=False))


def main(argv: Sequence[str] | None = None) -> None:
  dotenv.load_dotenv(os.path.expanduser('~/.env'))
  parser = argparse.ArgumentParser(
      description='Lookup gene and transcript info using GTF data.'
  )

  group = parser.add_mutually_exclusive_group(required=True)
  group.add_argument(
      '--genes', help='Comma-separated gene symbols or coordinates to lookup.'
  )
  group.add_argument(
      '--coord', help='Genomic coordinate for search (e.g. chr17:7675148).'
  )

  parser.add_argument(
      '--window',
      type=int,
      default=50000,
      help='Window size for coordinate search (default 50kb).',
  )
  parser.add_argument(
      '--transcripts',
      action='store_true',
      help='List transcripts instead of gene info.',
  )

  # Transcript filters
  parser.add_argument(
      '--mane', action='store_true', help='Filter to MANE transcripts.'
  )
  parser.add_argument(
      '--protein_coding',
      action='store_true',
      help='Filter to protein coding transcripts.',
  )
  parser.add_argument(
      '--transcript_support_level',
      help='Filter by Transcript Support Level (e.g. 1,2).',
  )
  parser.add_argument(
      '--longest',
      action='store_true',
      help='Filter to longest transcript per gene.',
  )
  parser.add_argument(
      '--details', action='store_true', help='Show full transcript details.'
  )

  args = parser.parse_args(argv)

  gtf = load_gtf()

  if args.coord is not None:
    run_coord_search(gtf, args.coord, args.window)
  elif args.genes is not None:
    genes_list = [x.strip() for x in args.genes.split(',')]
    if args.transcripts:
      run_transcript_lookup(
          gtf,
          genes_list,
          args.mane,
          args.protein_coding,
          args.transcript_support_level,
          args.longest,
          args.details,
      )
    else:
      run_gene_lookup(gtf, genes_list)
  else:
    parser.error('Please specify either --genes or --coord. See --help.')


if __name__ == '__main__':
  main()
