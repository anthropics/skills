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

"""Quantitative analysis of splicing effects (Splice Sites & Junctions).

This script provides high-resolution, quantitative analysis of splicing changes.
While discovery scans give summary scores, this script analyzes specific
junctions to detect events like exon skipping or cryptic splicing.

Design Note:
  This tool provides quantitative analysis of specific splice junctions,
  complementary to analyze_ism.py which can be used to analyze motifs affecting
  splice site usage. While ISM helps identify *why* a site was lost or gained
  (motif disruption), this script reveals *what* structural changes occurred
  (e.g., exon skipping or cryptic junction usage). It offloads final judgment
  to the agent but provides heuristic flags (e.g., GAIN/LOSS) to guide the analysis.

Usage:
  uv run scripts/interpret_splicing.py --chrom=chr21 --pos=46126238 --ref=G --alt=C \
      --ontology_id=CL:0002545
"""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "alphagenome",
#   "numpy",
#   "pandas",
#   "python-dotenv",
# ]
# ///

from __future__ import annotations

import argparse
import os
from typing import Any, Sequence

from alphagenome.data import genome
from alphagenome.models import dna_client
import dotenv
import numpy as np
import pandas as pd

API_ADDRESS = 'dns:///gdmscience.googleapis.com:443'


def get_track(obj: Any, attr: str, curie: str) -> Any:
  """Retrieves a track filtered by ontology CURIE."""
  if not hasattr(obj, attr):
    print(f"Warning: Object missing attribute '{attr}'.")
    return None
  data = getattr(obj, attr)
  if hasattr(data, 'filter_by_ontology'):
    return data.filter_by_ontology(curie)
  mask = data.metadata['ontology_curie'] == curie
  if not mask.any():
    print(f"Info: No data found for ontology term '{curie}' in track '{attr}'.")
    return None
  return data.filter_tracks(mask.values)


def junctions_to_df(junc_track: Any) -> pd.DataFrame:
  """Converts a JunctionTrack to a DataFrame."""
  if junc_track is None or len(junc_track.junctions) == 0:
    return pd.DataFrame()

  scores = None
  if hasattr(junc_track, 'values'):
    vals = junc_track.values
    # Handle different shapes of values array from API
    if vals.shape[0] == len(junc_track.junctions):
      scores = vals.mean(axis=1)
    elif len(vals.shape) > 1 and vals.shape[1] == len(junc_track.junctions):
      scores = vals.mean(axis=0)
    elif len(vals.shape) == 1 and len(vals) == len(junc_track.junctions):
      scores = vals

  if scores is None:
    print('Warning: Failed to parse scores for junctions.')
    return pd.DataFrame()

  rows = []
  for junction, score in zip(junc_track.junctions, scores):
    rows.append({
        'start': junction.start,
        'end': junction.end,
        'score': float(score),
        'strand': junction.strand,
    })
  return pd.DataFrame(rows)


def analyze_splicing(
    chrom: str,
    pos: int,
    ref: str,
    alt: str,
    ontology_id: str,
    window: int,
) -> None:
  """Runs the splicing analysis for a specific variant."""
  api_key = os.environ.get('ALPHAGENOME_API_KEY')
  if not api_key:
    raise ValueError('ALPHAGENOME_API_KEY environment variable not set.')

  dna_model = dna_client.create(api_key=api_key, address=API_ADDRESS)

  variant = genome.Variant(chrom, pos, ref, alt)
  zoom_interval = genome.Interval(chrom, pos - window // 2, pos + window // 2)
  pred_interval = zoom_interval.resize(131072)

  print(
      f'Quantifying splicing changes for {chrom}:{pos}:{ref}>{alt} in'
      f' {ontology_id}...'
  )

  requested_outputs = [
      dna_client.OutputType.SPLICE_JUNCTIONS,
      dna_client.OutputType.SPLICE_SITE_USAGE,
      dna_client.OutputType.RNA_SEQ,
  ]

  prediction = dna_model.predict_variant(
      interval=pred_interval,
      variant=variant,
      requested_outputs=requested_outputs,
      ontology_terms=[ontology_id],
  )

  print('\n--- Splice Site Usage Analysis ---')
  ss_ref = get_track(prediction.reference, 'splice_site_usage', ontology_id)
  ss_alt = get_track(prediction.alternate, 'splice_site_usage', ontology_id)

  if ss_ref and ss_alt:
    start = pred_interval.start
    idx = pos - start

    for offset in range(-2, 3):
      position = pos + offset
      index = idx + offset
      try:
        val_ref = (
            ss_ref.values[index].mean()
            if ss_ref.values.ndim > 1
            else ss_ref.values[index]
        )
        val_alt = (
            ss_alt.values[index].mean()
            if ss_alt.values.ndim > 1
            else ss_alt.values[index]
        )

        diff = val_alt - val_ref
        if abs(diff) > 0.05:
          print(
              f'Position {position} (Offset {offset}): REF={val_ref:.3f},'
              f' ALT={val_alt:.3f}, Delta={diff:.3f}'
          )
          if val_ref > 0.5 and val_alt < 0.1:
            print(f'  -> Loss of strong splice site at {position}!')
          elif val_ref < 0.1 and val_alt > 0.5:
            print(f'  -> Gain of new splice site at {position}!')
      except (IndexError, AttributeError, ValueError) as e:
        if not isinstance(e, IndexError):
          print(f'Warning: Error during splice site diff calculation: {e}')
        pass
  else:
    print('Splice site usage track missing.')

  print('\n--- Junction Analysis ---')
  junc_ref = prediction.reference.splice_junctions.filter_by_ontology(
      ontology_id
  )
  junc_alt = prediction.alternate.splice_junctions.filter_by_ontology(
      ontology_id
  )

  df_ref = junctions_to_df(junc_ref)
  df_alt = junctions_to_df(junc_alt)

  if not df_ref.empty and not df_alt.empty:
    merged = pd.merge(
        df_ref,
        df_alt,
        on=['start', 'end', 'strand'],
        how='outer',
        suffixes=('_REF', '_ALT'),
    ).fillna(0)
    merged['delta'] = merged['score_ALT'] - merged['score_REF']

    # Junctions overlapping variant
    variant_overlapping = merged[
        (merged['start'] < pos) & (merged['end'] > pos)
    ]

    print(f'Junctions overlapping variant ({pos}):')
    if variant_overlapping.empty:
      print('  None found.')
    else:
      for _, row in variant_overlapping.iterrows():
        print(
            f"  {int(row['start'])}-{int(row['end'])} (Strand {row['strand']}):"
            f" REF={row['score_REF']:.2f}, ALT={row['score_ALT']:.2f},"
            f" Delta={row['delta']:.2f}"
        )
        if row['score_REF'] > 5 and row['score_ALT'] < 1:
          print('  -> Skipping/Loss of canonical intron (Exon skipping?)')

    # Cryptic Junctions (Gain in ALT)
    cryptic = merged[(merged['score_ALT'] > 5) & (merged['score_REF'] < 1)]
    if not cryptic.empty:
      print('\nPotential Cryptic Junctions (Gain in ALT):')
      for _, row in cryptic.iterrows():
        print(
            f"  {int(row['start'])}-{int(row['end'])}:"
            f" REF={row['score_REF']:.2f} -> ALT={row['score_ALT']:.2f}"
        )

    print('\nTop 5 Most Changed Junctions:')
    top_changes = merged.reindex(
        merged['delta'].abs().sort_values(ascending=False).index
    ).head(5)
    print(top_changes[['start', 'end', 'score_REF', 'score_ALT', 'delta']])
  else:
    print('No junctions found or failed to parse.')

  print('\n--- RNA-seq Analysis ---')
  rna_ref = get_track(prediction.reference, 'rna_seq', ontology_id)
  rna_alt = get_track(prediction.alternate, 'rna_seq', ontology_id)

  if rna_ref and rna_alt:
    start_idx = pos - pred_interval.start - 50
    end_idx = pos - pred_interval.start + 50

    def safe_mean(arr: np.ndarray) -> np.ndarray:
      if arr.ndim > 1:
        return arr.mean(axis=1)
      return arr

    ref_vals = safe_mean(rna_ref.values)
    alt_vals = safe_mean(rna_alt.values)

    ref_window = ref_vals[start_idx:end_idx]
    alt_window = alt_vals[start_idx:end_idx]

    print(
        f'Mean RNA Coverage (+/- 50bp): REF={ref_window.mean():.2f},'
        f' ALT={alt_window.mean():.2f}'
    )
    if ref_window.mean() > 0:
      log2fc = np.log2((alt_window.mean() + 1e-3) / (ref_window.mean() + 1e-3))
      print(f'Log2 Fold Change at variant: {log2fc:.2f}')
  else:
    print('RNA-seq track missing.')


def main(argv: Sequence[str] | None = None) -> None:
  """Main entry point for the splicing analysis CLI tool."""
  dotenv.load_dotenv(os.path.expanduser('~/.env'))
  parser = argparse.ArgumentParser(
      description='Quantitative analysis of splicing effects.'
  )
  parser.add_argument(
      '--chrom', required=True, help='Chromosome (e.g., chr21).'
  )
  parser.add_argument(
      '--pos', type=int, required=True, help='Position (1-based).'
  )
  parser.add_argument('--ref', required=True, help='Reference allele.')
  parser.add_argument('--alt', required=True, help='Alternate allele.')
  parser.add_argument(
      '--ontology_id', required=True, help='Ontology CURIE (e.g., CL:0002545).'
  )
  parser.add_argument(
      '--window',
      type=int,
      default=1500,
      help='Window size around variant for analysis.',
  )
  args = parser.parse_args(argv)

  analyze_splicing(
      args.chrom,
      args.pos,
      args.ref,
      args.alt,
      args.ontology_id,
      args.window,
  )


if __name__ == '__main__':
  main()
