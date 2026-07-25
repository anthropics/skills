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

r"""Visualize regional model predictions.

Usage:
  uv run scripts/visualize_genome_tracks.py --chrom=chr19 --start=11089363 --end=11133820 \
      --ontology=UBERON:0002107 --output_dir=./region_plots

Examples:
  uv run scripts/visualize_genome_tracks.py --chrom=chr19 --start=11089363 --end=11133820 \
      --ontology=UBERON:0002107 --output_dir=./region_plots
  uv run scripts/visualize_genome_tracks.py --chrom=chr19 --start=11089363 --end=11133820 \
      --ontology=UBERON:0002107 --output_dir=./region_plots \
      --zoom_genes=LDLR
  uv run scripts/visualize_genome_tracks.py --chrom=chr17 --start=7661779 --end=7687538 \
      --ontology=UBERON:0000310 --output_dir=./plots \
      --zoom_genes=TP53
"""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "alphagenome",
#   "numpy",
#   "pandas",
#   "pyarrow",
#   "python-dotenv",
# ]
# ///

from __future__ import annotations

import argparse
import os

from alphagenome.data import gene_annotation
from alphagenome.data import genome
from alphagenome.data import transcript as transcript_utils
from alphagenome.models import dna_client
from alphagenome.visualization import plot_components
import dotenv
import numpy as np
import pandas as pd

GTF_URL = (
    'https://storage.googleapis.com/alphagenome/reference/gencode/'
    'hg38/gencode.v46.annotation.gtf.gz.feather'
)
API_ADDRESS = 'dns:///gdmscience.googleapis.com:443'


def create_client() -> dna_client.DnaClient:
  """Creates an AlphaGenome DNA client."""
  api_key = os.environ.get('ALPHAGENOME_API_KEY')
  if not api_key:
    raise ValueError('ALPHAGENOME_API_KEY environment variable not set.')
  return dna_client.create(
      api_key=api_key,
      address=API_ADDRESS,
  )


def safe_filter_tracks(track: object, mask: object) -> object | None:
  """Safely filters tracks using integer indices."""
  if track is None:
    return None
  if isinstance(mask, (list, np.ndarray, pd.Series)):
    mask = np.array(mask)
    if mask.dtype == bool:
      mask = np.flatnonzero(mask)
  return track.filter_tracks(mask)


def filter_tracks_by_ontology(
    track: object, ontology_curie: str
) -> object | None:
  """Filters tracks to those matching the given ontology CURIE."""
  if track is None or track.metadata.empty:
    return track

  if 'ontology_curie' in track.metadata.columns:
    # track.metadata is a DataFrame where each row is one track (e.g. one
    # tissue/cell-type). We compare each row's ontology_curie string against
    # the target to build a boolean mask selecting only matching tracks.
    vals = track.metadata['ontology_curie'].astype(str).str.strip().values
    target = str(ontology_curie).strip()
    mask = vals == target
    if np.sum(mask) == 0:
      return None
    return safe_filter_tracks(track, mask)
  return track


def add_track_component(
    components: list[object],
    track: object,
    ontology: str,
    separate_strands: bool = False,
    track_type: str = 'Track',
) -> None:
  """Filters a track by ontology and appends to the component list."""
  if track is None:
    return
  filt = filter_tracks_by_ontology(track, ontology)
  if filt is None:
    return

  if separate_strands and 'strand' in filt.metadata.columns:
    for strand in ['+', '-']:
      s_track = filt.filter_tracks(
          np.flatnonzero(filt.metadata['strand'] == strand)
      )
      if not s_track.metadata.empty:
        if len(s_track.metadata) > 5:
          s_track = safe_filter_tracks(s_track, np.arange(5))
        components.append(
            plot_components.Tracks(
                s_track, ylabel_template=f'{track_type} ({strand})'
            )
        )
  else:
    if len(filt.metadata) > 5:
      filt = safe_filter_tracks(filt, np.arange(5))
    components.append(
        plot_components.Tracks(filt, ylabel_template=f'{track_type}')
    )


def render_broad_view(
    client: dna_client.DnaClient,
    gtf: pd.DataFrame,
    chrom: str,
    start: int,
    end: int,
    ontology: str,
    output_dir: str,
) -> None:
  """Renders the broad region overview plot."""
  region = genome.Interval(chrom, start, end)
  print(f'Analyzing Region: {region}')

  center = (start + end) // 2
  model_len = 1_048_576  # Always use 2**20 for full context

  pred_start = center - (model_len // 2)
  pred_end = center + (model_len // 2)
  pred_interval = genome.Interval(chrom, pred_start, pred_end)
  print(f'Broad Prediction Interval (Model-Compatible): {pred_interval}')

  broad_outputs = [
      dna_client.OutputType.RNA_SEQ,
      dna_client.OutputType.ATAC,
      dna_client.OutputType.DNASE,
      dna_client.OutputType.CHIP_HISTONE,
      dna_client.OutputType.CHIP_TF,
      dna_client.OutputType.CONTACT_MAPS,
  ]

  print('Running Broad Prediction...')
  prediction = client.predict_interval(
      interval=pred_interval,
      requested_outputs=broad_outputs,
      ontology_terms=[ontology],
  )

  components: list[object] = []
  longest_gtf = gene_annotation.filter_to_longest_transcript(gtf)
  tx_extractor = transcript_utils.TranscriptExtractor(longest_gtf)
  transcripts = tx_extractor.extract(pred_interval)
  if transcripts:
    components.append(
        plot_components.TranscriptAnnotation(
            transcripts, label_name='gene_name'
        )
    )

  ref_preds = prediction
  add_track_component(
      components,
      ref_preds.rna_seq,
      ontology,
      separate_strands=True,
      track_type='RNA',
  )
  add_track_component(components, ref_preds.atac, ontology, track_type='ATAC')
  add_track_component(components, ref_preds.dnase, ontology, track_type='DNASE')
  add_track_component(
      components, ref_preds.chip_histone, ontology, track_type='Histone'
  )
  add_track_component(components, ref_preds.chip_tf, ontology, track_type='TF')

  if hasattr(ref_preds, 'contact_maps') and ref_preds.contact_maps:
    if hasattr(plot_components, 'ContactMaps'):
      filt_cmap = filter_tracks_by_ontology(ref_preds.contact_maps, ontology)
      if filt_cmap and not filt_cmap.metadata.empty:
        components.append(
            plot_components.ContactMaps(filt_cmap, ylabel_template='Hi-C')
        )
    else:
      print(
          'WARNING: plot_components.ContactMaps not found. Skipping Contact'
          ' Maps.'
      )

  if components:
    print('Rendering Broad Plot...')
    fig = plot_components.plot(components, interval=pred_interval)
    fig.set_size_inches(20, len(components) * 2 + 2)
    fig.savefig(
        os.path.join(output_dir, 'broad_view.png'),
        bbox_inches='tight',
        dpi=150,
    )
    print(f"Saved {os.path.join(output_dir, 'broad_view.png')}")
  else:
    print('No components to plot for broad view.')


def render_zoom_view(
    client: dna_client.DnaClient,
    gtf: pd.DataFrame,
    chrom: str,
    gene: str,
    ontology: str,
    output_dir: str,
) -> None:
  """Renders a zoomed-in splicing plot for a specific gene."""
  print(f'\nProcessing Zoom for {gene}...')
  gene_df = gtf[gtf['gene_name'] == gene]
  if gene_df.empty:
    print(f'Gene {gene} not found.')
    return

  gene_interval = gene_annotation.get_gene_interval(gene_df, gene_symbol=gene)
  padding = 2000
  zoom_interval = gene_interval.resize(gene_interval.width + 2 * padding)

  # Ensure at least 50kb context for small genes.
  if zoom_interval.width < 50000:
    zoom_interval = zoom_interval.resize(50000)

  print(f'Zoom Interval (Requested): {zoom_interval}')

  model_len = 1_048_576  # Always use 2**20 for full context
  z_center = (zoom_interval.start + zoom_interval.end) // 2
  pred_interval = genome.Interval(
      chrom, z_center - (model_len // 2), z_center + (model_len // 2)
  )
  print(f'Prediction Interval (Model-Compatible): {pred_interval}')

  zoom_outputs = [
      dna_client.OutputType.RNA_SEQ,
      dna_client.OutputType.SPLICE_SITES,
      dna_client.OutputType.SPLICE_SITE_USAGE,
      dna_client.OutputType.SPLICE_JUNCTIONS,
  ]

  zoom_predictions = client.predict_interval(
      interval=pred_interval,
      requested_outputs=zoom_outputs,
      ontology_terms=[ontology],
  )

  zoom_components: list[object] = []
  longest_gtf = gene_annotation.filter_to_longest_transcript(gtf)
  tx_extractor = transcript_utils.TranscriptExtractor(longest_gtf)
  zoom_transcripts = tx_extractor.extract(zoom_interval)
  if zoom_transcripts:
    zoom_components.append(
        plot_components.TranscriptAnnotation(
            zoom_transcripts, label_name='gene_name'
        )
    )

  gene_strand = gene_df['Strand'].iloc[0]

  if zoom_predictions.rna_seq:
    r_filt = filter_tracks_by_ontology(zoom_predictions.rna_seq, ontology)
    if r_filt:
      r_strand = safe_filter_tracks(
          r_filt, r_filt.metadata['strand'] == gene_strand
      )
      if r_strand and not r_strand.metadata.empty:
        zoom_components.append(
            plot_components.Tracks(
                r_strand, ylabel_template=f'RNA ({gene_strand})'
            )
        )

  if zoom_predictions.splice_sites:
    ss_filt = filter_tracks_by_ontology(zoom_predictions.splice_sites, ontology)
    if ss_filt:
      zoom_components.append(
          plot_components.Tracks(ss_filt, ylabel_template='Sites')
      )

  if zoom_predictions.splice_site_usage:
    su_filt = filter_tracks_by_ontology(
        zoom_predictions.splice_site_usage, ontology
    )
    if su_filt:
      zoom_components.append(
          plot_components.Tracks(su_filt, ylabel_template='Usage')
      )

  if zoom_predictions.splice_junctions:
    j_filt = filter_tracks_by_ontology(
        zoom_predictions.splice_junctions, ontology
    )
    if j_filt and not j_filt.metadata.empty:
      zoom_components.append(
          plot_components.Sashimi(
              j_filt,
              ylabel_template='Junctions',
              normalize_values=False,
          )
      )

  if zoom_components:
    print(f'Rendering Zoom Plot for {gene}...')
    fig = plot_components.plot(zoom_components, interval=zoom_interval)
    fig.set_size_inches(20, len(zoom_components) * 2)
    fig.savefig(
        os.path.join(
            output_dir,
            f'zoom_{gene}_{zoom_interval.start}-{zoom_interval.end}.png',
        ),
        bbox_inches='tight',
        dpi=150,
    )
    print(f'Saved zoom plot to {output_dir}')


def main(argv: list[str] | None = None) -> None:
  """Main entry point for the region visualization CLI tool."""
  dotenv.load_dotenv(os.path.expanduser('~/.env'))
  parser = argparse.ArgumentParser(
      description='Visualize regional model predictions.'
  )
  parser.add_argument(
      '--chrom', required=True, help='Chromosome (e.g., chr19).'
  )
  parser.add_argument(
      '--start', type=int, required=True, help='Region start position.'
  )
  parser.add_argument(
      '--end', type=int, required=True, help='Region end position.'
  )
  parser.add_argument(
      '--ontology',
      required=True,
      help='Ontology CURIE (e.g., UBERON:0002107).',
  )
  parser.add_argument('--output_dir', required=True, help='Output directory.')
  parser.add_argument(
      '--zoom_genes', help='Comma-separated genes to zoom into.'
  )
  args = parser.parse_args(argv)

  os.makedirs(args.output_dir, exist_ok=True)
  client = create_client()

  print('Loading GTF...')
  gtf = pd.read_feather(GTF_URL)

  render_broad_view(
      client,
      gtf,
      args.chrom,
      args.start,
      args.end,
      args.ontology,
      args.output_dir,
  )

  if args.zoom_genes:
    zoom_genes = [g.strip() for g in args.zoom_genes.split(',')]
    for gene in zoom_genes:
      render_zoom_view(
          client,
          gtf,
          args.chrom,
          gene,
          args.ontology,
          args.output_dir,
      )


if __name__ == '__main__':
  main()
