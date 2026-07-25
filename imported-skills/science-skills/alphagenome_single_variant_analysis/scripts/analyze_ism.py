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

r"""Generate ISM Sequence Logo for a variant.

Design Note:
  This tool generates ISM Sequence Logos to identify disrupted motifs at the
  variant position, helping explain *why* a regulatory or splicing site was
  lost or gained (mechanistic cause).

  The script extracts the top k-mer and prints its reverse complement.
  The agent must use its own knowledge about transcription factor binding
  motifs to identify candidate TFs that match the extracted motif or its
  reverse complement.

Usage:
  uv run analyze_ism.py --chrom=chr17 --pos=7675148 --ref=G --alt=A \
    --tissue=liver --ontology=UBERON:0002107 --modality=DNASE

Examples:
  uv run analyze_ism.py --chrom=chr17 --pos=7675148 --ref=G --alt=A \
    --tissue=liver --ontology=UBERON:0002107 --modality=DNASE

  uv run analyze_ism.py --chrom=chr21 --pos=46126238 --ref=G --alt=C \
    --tissue='skeletal muscle' --ontology=CL:0002545 --modality=SPLICE_SITE_USAGE \
    --gene=COL6A2

  uv run analyze_ism.py --chrom=chr7 --pos=5529776 --ref=C --alt=T \
    --tissue=HepG2 --ontology=EFO:0001187 --modality=CHIP_TF --gene=ACTB \
    --output_dir=./ism_plots
"""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "alphagenome",
#   "numpy",
#   "python-dotenv",
# ]
# ///

from __future__ import annotations

import argparse
import os
from typing import Any, Sequence

from alphagenome.data import genome
from alphagenome.interpretation import ism
from alphagenome.models import dna_client
from alphagenome.models import variant_scorers
from alphagenome.visualization import plot_components
import dotenv
import numpy as np


def _reverse_complement(seq: str) -> str:
  """Returns the reverse complement of a DNA sequence."""
  return seq[::-1].translate(str.maketrans('ACGTacgt', 'TGCAtgca'))


def extract_ontology_scores(
    ism_results: list[tuple[Any, ...]],
    ontology_id: str,
    gene_name: str | None = None,
) -> tuple[list[float], list[Any]]:
  """Extracts scores for a specific ontology ID from ISM results."""
  scores_flat: list[float] = []
  variants_flat: list[Any] = []

  for adata, *_ in ism_results:
    var_obj = adata.uns['variant']
    score = 0.0

    if 'ontology_curie' in adata.var.columns:
      col_mask = adata.var['ontology_curie'] == ontology_id
      if col_mask.any():
        row_mask = slice(None)  # All rows
        if gene_name and 'gene_name' in adata.obs.columns:
          gene_mask = adata.obs['gene_name'] == gene_name
          if gene_mask.any():
            row_mask = gene_mask
        score = np.nanmean(adata.X[row_mask, col_mask])
      else:
        print(
            'Info: No scores found for ontology term'
            f' {ontology_id!r} in ISM result.'
        )

    scores_flat.append(score)
    variants_flat.append(var_obj)

  return scores_flat, variants_flat


def interpret_ism_matrix(
    ref_ism_mat: np.ndarray,
    bases: list[str],
    kmer_length: int,
    min_threshold: float,
) -> None:
  """Prints interpretation summary from an ISM matrix."""
  print('\n--- ISM Interpretation Summary ---')
  if not np.any(ref_ism_mat):
    print('ISM matrix is all zeros. No relevant tracks or scores found.')
    return

  max_scores_per_pos = np.max(np.abs(ref_ism_mat), axis=1)
  top_pos_idx = int(np.argmax(max_scores_per_pos))
  top_score = ref_ism_mat[top_pos_idx, :]
  center_idx = ref_ism_mat.shape[0] // 2

  print(
      f'Top Disrupted Position: {top_pos_idx - center_idx} (Relative to'
      ' Variant)'
  )
  print(f'Scores at Top Position: {dict(zip(bases, top_score))}')

  # Use relative threshold but ensure it's at least min_threshold
  threshold = max(np.max(np.abs(ref_ism_mat)) * 0.1, min_threshold)

  consensus_seq: list[str] = []
  for i in range(ref_ism_mat.shape[0]):
    row = ref_ism_mat[i, :]
    best_idx = np.argmax(np.abs(row))
    if abs(row[best_idx]) > threshold:
      consensus_seq.append(bases[best_idx])
    else:
      consensus_seq.append('.')

  consensus_str = ''.join(consensus_seq)
  print(f'Consensus Motif: {consensus_str}')
  print(f'Reverse Compl  : {_reverse_complement(consensus_str)}')

  if ref_ism_mat.shape[0] >= kmer_length:
    best_kmer_score = -1.0
    best_kmer_seq = ''
    best_kmer_start = 0
    for i in range(ref_ism_mat.shape[0] - kmer_length + 1):
      window = ref_ism_mat[i : i + kmer_length, :]
      score = np.sum(np.max(np.abs(window), axis=1))
      if score > best_kmer_score:
        best_kmer_score = score
        best_kmer_start = i
        seq = ''
        for j in range(kmer_length):
          w_row = window[j, :]
          seq += bases[np.argmax(np.abs(w_row))]
        best_kmer_seq = seq
    print(
        f'Top {kmer_length}-mer: {best_kmer_seq}'
        f' (Start: {best_kmer_start - center_idx},'
        f' Score: {best_kmer_score:.3f})'
    )
    print(f'RevComp {kmer_length}-mer: {_reverse_complement(best_kmer_seq)}')
  print('----------------------------------\n')


def analyze_ism(
    chrom: str,
    pos: int,
    ref: str,
    alt: str,
    tissue: str,
    ontology: str,
    modality: str,
    gene: str,
    output_dir: str,
    kmer_length: int,
    min_threshold: float,
) -> None:
  """Runs In-Silico Mutagenesis (ISM) analysis and plots the results."""
  api_key = os.environ.get('ALPHAGENOME_API_KEY')
  if not api_key:
    raise ValueError('ALPHAGENOME_API_KEY not found.')

  print('Initializing AlphaGenome Client...')
  dna_model = dna_client.create(
      api_key=api_key,
      address='dns:///gdmscience.googleapis.com:443',
  )

  variant = genome.Variant(chrom, pos, ref, alt)
  print(f'Variant: {variant}')

  ism_interval = variant.reference_interval.resize(32)
  sequence_interval = ism_interval.resize(dna_client.SEQUENCE_LENGTH_1MB)

  try:
    output_type = dna_client.OutputType[modality.upper()]
  except KeyError as e:
    raise ValueError(
        f'Unknown modality: {modality}. Valid options:'
        f' {[o.name for o in dna_client.OutputType]}'
    ) from e

  if output_type == dna_client.OutputType.SPLICE_JUNCTIONS:
    raise ValueError(
        'SPLICE_JUNCTIONS is NOT supported for ISM. Please use'
        ' SPLICE_SITE_USAGE instead.'
    )

  print(f'Scoring ISM for {tissue} ({output_type.name})...')

  modality_key = modality.upper()
  if modality_key in variant_scorers.RECOMMENDED_VARIANT_SCORERS:
    ism_scorer = variant_scorers.RECOMMENDED_VARIANT_SCORERS[modality_key]
  else:
    raise ValueError(
        f'No recommended scorer found for modality: {modality_key}. '
        'Available recommended scorers: '
        f'{list(variant_scorers.RECOMMENDED_VARIANT_SCORERS.keys())}'
    )

  print('Running ISM on REF background...')
  ref_ism_results = dna_model.score_ism_variants(
      interval=sequence_interval,
      ism_interval=ism_interval,
      variant_scorers=[ism_scorer],
  )

  ref_scores, ref_variants = extract_ontology_scores(
      ref_ism_results, ontology, gene_name=gene
  )
  ref_ism_mat = ism.ism_matrix(ref_scores, variants=ref_variants)

  max_score = np.max(np.abs(ref_ism_mat))
  if max_score == 0:
    print('WARNING: ISM matrix is empty (all zeros). Check ontology ID.')
  elif max_score < min_threshold:
    print(
        f'WARNING: Max ISM score is very low ({max_score:.3f}), below'
        f' threshold {min_threshold}. The result may not be reliable.'
    )

  print('Generating SeqLogo...')
  fig = plot_components.plot(
      [
          plot_components.SeqLogo(
              scores=ref_ism_mat,
              scores_interval=ism_interval,
              ylabel=f'ISM {tissue}\n{output_type.name}',
          )
      ],
      interval=ism_interval,
      fig_width=15,
      title=f'ISM Motif Analysis: {gene} {chrom}:{pos} ({tissue})',
      annotations=[plot_components.VariantAnnotation([variant], alpha=0.5)],
  )

  safe_tissue = tissue.replace(' ', '_').replace('/', '_')
  filename = os.path.join(output_dir, f'ism_{safe_tissue}_{modality}.png')
  os.makedirs(output_dir, exist_ok=True)
  fig.savefig(filename)
  print(f'Saved ISM SeqLogo to {filename}')

  bases = ['A', 'C', 'G', 'T']
  interpret_ism_matrix(ref_ism_mat, bases, kmer_length, min_threshold)


def main(argv: Sequence[str] | None = None) -> None:
  """Main entry point for the ISM analysis CLI tool."""
  dotenv.load_dotenv(os.path.expanduser('~/.env'))
  parser = argparse.ArgumentParser(
      description='Generate ISM Sequence Logo for a variant.'
  )
  parser.add_argument(
      '--chrom',
      required=True,
      help='Chromosome (e.g., chr17).',
  )
  parser.add_argument(
      '--pos', type=int, required=True, help='Position (1-based).'
  )
  parser.add_argument('--ref', required=True, help='Reference allele.')
  parser.add_argument('--alt', required=True, help='Alternate allele.')
  parser.add_argument(
      '--tissue', required=True, help='Tissue name for labeling.'
  )
  parser.add_argument(
      '--ontology', required=True, help='Ontology CURIE (e.g., UBERON:0002107).'
  )
  parser.add_argument(
      '--modality',
      required=True,
      help='Output modality (e.g., DNASE, CHIP_TF).',
  )
  parser.add_argument(
      '--gene', default='Unknown', help='Gene name for plot title.'
  )
  parser.add_argument('--output_dir', default='.', help='Output directory.')
  parser.add_argument(
      '--kmer_length',
      type=int,
      default=8,
      help='Length of k-mer to scan for top score.',
  )
  parser.add_argument(
      '--min_threshold',
      type=float,
      default=0.05,
      help='Minimum absolute score threshold for motif extraction.',
  )

  args = parser.parse_args(argv)

  analyze_ism(
      args.chrom,
      args.pos,
      args.ref,
      args.alt,
      args.tissue,
      args.ontology,
      args.modality,
      args.gene,
      args.output_dir,
      args.kmer_length,
      args.min_threshold,
  )


if __name__ == '__main__':
  main()
