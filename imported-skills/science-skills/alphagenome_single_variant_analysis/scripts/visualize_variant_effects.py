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

r"""Visualize variant effects using AlphaGenome predictions.

Compares REF and ALT alleles, overlays them for clarity, and handles custom
coloring for Sashimi plots.

Design Note:
  This tool produces variant-effect visualizations for analysis reports.
  It handles complex track filtering to ensure Ref/Alt pairing and applies
  preferences (e.g., Total RNA over PolyA RNA) to reduce noise.

Usage:
  uv run visualize_variant_effects.py --chrom=chr21 --pos=46126238 --ref=G \
      --alt=C --gene=COL6A2 --tissue=muscle --ontology=UBERON:0001134 \
      --output_dir=./plots --tracks=splicing

Examples:
  uv run visualize_variant_effects.py --chrom=chr21 --pos=46126238 --ref=G \
      --alt=C --gene=COL6A2 --tissue=muscle --ontology=UBERON:0001134 \
      --output_dir=./plots --tracks=splicing
  uv run visualize_variant_effects.py --chrom=chr7 --pos=5529776 --ref=C \
      --alt=T --gene=ACTB --tissue=HepG2 --ontology=EFO:0001187 \
      --output_dir=./plots --view=whole_gene
"""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#     "alphagenome",
#     "matplotlib",
#     "numpy",
#     "pandas",
#     "pyarrow",  # Required by pandas to read .feather files
#     "python-dotenv",
# ]
# ///

from __future__ import annotations

import argparse
import os
from typing import Any

from alphagenome.data import gene_annotation
from alphagenome.data import genome
from alphagenome.data import junction_data
from alphagenome.data import transcript as transcript_utils
from alphagenome.models import dna_client
from alphagenome.visualization import plot_components
import dotenv
import matplotlib as mpl
import matplotlib.pyplot as plt
import numpy as np
import pandas as pd

GTF_URL = (
    'https://storage.googleapis.com/alphagenome/reference/gencode/'
    'hg38/gencode.v46.annotation.gtf.gz.feather'
)
API_ADDRESS = 'dns:///gdmscience.googleapis.com:443'

COLOR_REF = '#22AAE1'
COLOR_ALT = 'red'


def colored_sashimi_plot(
    junctions: Any,
    ax: Any,
    interval: Any = None,
    filter_threshold: float = 0.01,
    annotate_counts: bool = True,
    rng: Any = None,
    color: str | None = None,
) -> None:
  """Modified sashimi_plot that accepts a color argument.

  Args:
    junctions: List of junctions to plot.
    ax: Matplotlib axis.
    interval: Genomic interval.
    filter_threshold: Threshold for filtering junctions.
    annotate_counts: Whether to annotate junction counts.
    rng: Random number generator.
    color: Color of the sashimi plot.
  """
  rng = rng or np.random.default_rng()
  total = np.sum([junction.k for junction in junctions])
  # Random jitter position to avoid overlap.
  jitters = rng.uniform(low=0.05, high=0.15, size=len(junctions))

  for junction, jt in zip(junctions, jitters):
    if junction.k < filter_threshold:
      continue
    k = junction.k / total
    verts = [
        (junction.start, 0.0),
        (junction.start, jt),
        (junction.end, jt),
        (junction.end, 0.0),
    ]

    path = mpl.path.Path(
        verts,
        [
            mpl.path.Path.MOVETO,
            mpl.path.Path.CURVE4,
            mpl.path.Path.CURVE4,
            mpl.path.Path.CURVE4,
        ],
    )
    # Use provided color or default
    edgecolor = color if color else 'black'
    # Scale width by relative abundance, but enforce min width for visibility
    min_lw = 0.5
    calc_lw = min(k * 30, 5)
    lw = max(calc_lw, min_lw)
    patch = mpl.patches.PathPatch(
        path, facecolor='none', lw=lw, edgecolor=edgecolor
    )
    ax.add_patch(patch)

    if annotate_counts:
      text_pos = junction.center()
      if interval is not None:
        if text_pos < interval.start or text_pos > interval.end:
          continue
      text_format = '{:.1f}' if total < 10 else '{:.0f}'
      ax.text(
          text_pos,
          0.8 * jt,
          text_format.format(junction.k),
          horizontalalignment='center',
          color=edgecolor,
      )
  ax.set_ylim(0, 0.15)


class ColoredSashimi(plot_components.Sashimi):
  """Sashimi component with color and forced strand options."""

  def __init__(
      self,
      *args: Any,
      color: str | None = None,
      forced_strand: str | None = None,
      **kwargs: Any,
  ) -> None:
    super().__init__(*args, **kwargs)
    self._color = color
    self._forced_strand = forced_strand

  @property
  def num_axes(self) -> int:
    if self._forced_strand:
      return self._junction_track.num_tracks
    return super().num_axes

  def _get_strand_and_metadata_index(self, axis_index: int) -> tuple[str, int]:
    if self._forced_strand:
      return self._forced_strand, axis_index
    return super()._get_strand_and_metadata_index(axis_index)

  def get_junctions(self, interval: Any) -> Any:
    """Returns the list of junctions that would be plotted in given interval."""
    # Mimic plot_ax logic to ensure consistency
    # We need a dummy axis index, usually 0 is fine if we have 1 track
    strand, metadata_index = self._get_strand_and_metadata_index(0)
    track_name = self._junction_track.metadata.iloc[metadata_index]['name']
    junction_track = self._junction_track.intersect_with_interval(interval)

    junctions = junction_data.get_junctions_to_plot(
        predictions=junction_track,
        strand=strand,
        name=track_name,
        k_threshold=self._filter_threshold,
    )
    return junctions

  def plot_ax(self, ax: Any, axis_index: int, interval: Any) -> None:
    # We override plot_ax to call our colored_sashimi_plot
    strand, metadata_index = self._get_strand_and_metadata_index(axis_index)
    track_name = self._junction_track.metadata.iloc[metadata_index]['name']

    junction_track = self._junction_track.intersect_with_interval(interval)

    junctions = junction_data.get_junctions_to_plot(
        predictions=junction_track,
        strand=strand,
        name=track_name,
        k_threshold=self._filter_threshold,
    )

    if self._interval_contained:
      junctions = [j for j in junctions if interval.contains(j)]
    else:
      junctions = [j for j in junctions if j.overlaps(interval)]

    colored_sashimi_plot(
        junctions,
        ax=ax,
        interval=interval,
        filter_threshold=0,  # Filtering done above
        annotate_counts=self._annotate_counts,
        rng=self._rng,
        color=self._color,
    )
    ax.set_yticklabels([])
    ax.set_yticks([])
    ax.spines['left'].set_visible(False)

    # Manually set ylabel since we might have overridden strand logic
    if self._ylabel_template:
      row = self._junction_track.metadata.iloc[metadata_index].to_dict()
      row['strand'] = strand
      ylabel = self._ylabel_template.format(**row)

      if self._ylabel_horizontal:
        ax.set_ylabel(
            ylabel,
            rotation=0,
            multialignment='center',
            va='center',
            ha='right',
            labelpad=5,
        )
      else:
        ax.set_ylabel(ylabel)


def dynamic_label(track: Any, label_suffix: str = '') -> str:
  """Constructs a label based on available metadata columns."""
  if track is None or track.metadata.empty:
    return f'Track {label_suffix}'

  cols = track.metadata.columns
  parts = []

  # Get first row for labeling
  row = track.metadata.iloc[0]

  # Assay / Output Type
  if 'Assay title' in cols:
    title = str(row['Assay title'])
    # Clean up long titles for display
    if 'total RNA-seq' in title:
      title = 'Total RNA'
    elif 'polyA plus RNA-seq' in title:
      title = 'PolyA RNA'
    parts.append(title)

  # Target / Antibody (Critically important for ChIP)
  # Check common column names for TF/Histone targets
  target_cols = [
      'target',
      'antibody',
      'bio_target',
      'experiment_target',
      'target_label',
  ]
  for c in target_cols:
    if c in cols:
      val = str(row[c]).strip()
      if val and val.lower() != 'nan' and val.lower() != 'none':
        parts.append(val)
        break  # Use the first valid target column found

  # Clean up name if it contains weird characters like $
  # (User reported "$aorta" in labels)
  name = row.get('name', '')
  if isinstance(name, str):
    name = name.lstrip('$')  # Remove leading $
    if name and name.lower() != 'nan':
      # Only add name if it provides new info (not just a duplicate of target)
      if name not in parts:
        parts.append(name)

  parts.append(label_suffix)
  return ' '.join(parts).strip()


def filter_preference(track: Any) -> Any:
  """Prefers 'total RNA-seq' over 'polyA plus RNA-seq' if both exist.

  Also aggressively dedups if 'Assay title' is not present but 'biosample_type'
  or implicit duplicates exist.

  Args:
    track: The track to filter.

  Returns:
    The filtered track.
  """
  if track is None or len(track.metadata) < 2:
    return track

  cols = track.metadata.columns
  # Check for 'Assay title' or 'Assay Title'
  title_col = None
  if 'Assay title' in cols:
    title_col = 'Assay title'
  elif 'Assay Title' in cols:
    title_col = 'Assay Title'

  if title_col:
    titles = track.metadata[title_col].unique()
    # Case insensitive check
    titles_lower = [t.lower() for t in titles if isinstance(t, str)]

    has_total = any('total rna-seq' in t for t in titles_lower)
    has_polya = any('polya plus rna-seq' in t for t in titles_lower)

    if has_total and has_polya:
      # Filter to total RNA-seq only
      mask = track.metadata[title_col].str.contains(
          'total RNA-seq', case=False, na=False
      )
      return track.filter_tracks(np.flatnonzero(mask.values))

  return track


def get_deduplicated_indices(
    track: Any, label_suffix: str = '', max_tracks: int = 5
) -> list[int]:
  """Returns indices of tracks with unique labels.

  When multiple tracks produce the same label (via `dynamic_label`), only the
  index of the first track with that label is kept.

  Args:
    track: The track to deduplicate.
    label_suffix: Suffix to append to the label.
    max_tracks: Maximum number of tracks to keep.

  Returns:
    List of integer indices to keep.
  """
  if track is None or track.metadata.empty:
    return []

  keep_indices = []
  seen_labels = set()

  for i in range(len(track.metadata)):
    sub_track = track.filter_tracks([i])
    label = dynamic_label(sub_track, label_suffix)

    if label not in seen_labels:
      seen_labels.add(label)
      keep_indices.append(i)

  if len(keep_indices) > max_tracks:
    print(
        f'Warning: Limiting {len(keep_indices)} tracks to top {max_tracks}'
        ' for clarity.'
    )
    keep_indices = keep_indices[:max_tracks]

  return keep_indices


def deduplicate_tracks(
    track: Any, label_suffix: str = '', max_tracks: int = 5
) -> Any:
  """Deduplicates tracks based on their generated label."""
  keep_indices = get_deduplicated_indices(track, label_suffix, max_tracks)
  return track.filter_tracks(keep_indices)


def filter_and_create_overlay(
    ref_track: Any,
    alt_track: Any,
    ontology_curie: str,
    strand: str | None = None,
    label_suffix: str = '',
    color_ref: str = COLOR_REF,
    color_alt: str = COLOR_ALT,
    target_tf: str | None = None,
) -> list[Any] | None:
  """Filters tracks by ontology and strand and returns OverlaidTracks."""
  if ref_track is None or ref_track.metadata.empty:
    return []

  # Start with all True
  valid_mask = np.ones(len(ref_track.metadata), dtype=bool)

  # Filter by Ontology if column exists
  if 'ontology_curie' in ref_track.metadata.columns:
    # Robust comparison: cast to string and strip
    vals = ref_track.metadata['ontology_curie'].astype(str).str.strip().values
    target = str(ontology_curie).strip()
    valid_mask = valid_mask & (vals == target)

  # Filter by TF if provided
  if target_tf:
    target_cols = [
        'target',
        'antibody',
        'bio_target',
        'experiment_target',
        'target_label',
    ]
    tf_cols = [c for c in target_cols if c in ref_track.metadata.columns]
    if tf_cols:
      target = str(target_tf).strip().lower()
      # Succinct pandas-based row-wise check across TF columns
      tf_mask = (
          ref_track.metadata[tf_cols]
          .astype(str)
          .apply(lambda s: s.str.contains(target, case=False, na=False))
          .any(axis=1)
          .values
      )
      valid_mask = valid_mask & tf_mask

  # Filter by Strand if provided and column exists
  if strand and 'strand' in ref_track.metadata.columns:
    strand_mask = (ref_track.metadata['strand'] == strand).values
    # Fallback: if strand filtering removes all tracks, ignore it
    if np.sum(valid_mask & strand_mask) > 0:
      valid_mask = valid_mask & strand_mask

  if np.sum(valid_mask) == 0:
    return []

  ref_filt = ref_track.filter_tracks(valid_mask)
  alt_filt = alt_track.filter_tracks(valid_mask)

  # Apply Preference Filter (Total > PolyA)
  ref_filt = filter_preference(ref_filt)
  alt_filt = filter_preference(alt_filt)

  # Deduplicate by label. We skip deduplicate_tracks() here and inline the
  # logic so we can filter BOTH ref and alt by the same indices, preserving
  # Ref/Alt pairing required by OverlaidTracks.
  if ref_filt is None or ref_filt.metadata.empty:
    return []

  keep_indices = get_deduplicated_indices(ref_filt, label_suffix)

  ref_filt = ref_filt.filter_tracks(keep_indices)
  alt_filt = alt_filt.filter_tracks(keep_indices)

  if ref_filt.metadata.empty:
    return []

  components = []
  # Create individual component for each unique track to ensure correct labeling
  for i in range(len(ref_filt.metadata)):
    # Extract single track (row)
    r_track = ref_filt.filter_tracks([i])
    a_track = alt_filt.filter_tracks([i])

    # Generate specific label for this track
    label = dynamic_label(r_track, label_suffix)

    try:
      comp = plot_components.OverlaidTracks(
          tdata={'REF': r_track, 'ALT': a_track},
          colors={'REF': color_ref, 'ALT': color_alt},
          ylabel_template=label,
      )
      components.append(comp)
    except (ValueError, RuntimeError) as e:
      print(f'Warning: OverlaidTracks init failed for {label}: {e}')

  return components


def compute_splicing_zoom(
    chrom: str,
    variant_start: int,
    ref_allele: str,
    gene_gtf: pd.DataFrame,
    ref_sashimi: Any,
    alt_sashimi: Any,
    clamp_interval: Any,
) -> genome.Interval | None:
  """Computes a zoom interval that includes flanking exons and junctions.

  Expands the view to show the nearest upstream and downstream exons relative
  to the variant, plus any significant splice junctions overlapping the region.

  Args:
    chrom: Chromosome string.
    variant_start: Variant start position.
    ref_allele: Reference allele string (used to compute variant end).
    gene_gtf: GTF DataFrame filtered to the target gene.
    ref_sashimi: Reference ColoredSashimi component.
    alt_sashimi: Alternate ColoredSashimi component.
    clamp_interval: Outer interval to clamp results within.

  Returns:
    A genome.Interval for the zoom view, or None if exons are unavailable.
  """
  feature_col = 'Feature' if 'Feature' in gene_gtf.columns else 'feature'
  if feature_col not in gene_gtf.columns:
    return None

  exons = gene_gtf[gene_gtf[feature_col] == 'exon'].copy()
  if exons.empty:
    return None

  exons = exons.sort_values('Start')
  v_start = variant_start
  v_end = variant_start + len(ref_allele)

  # Start with a small window around the variant.
  new_start = v_start - 200
  new_end = v_end + 200

  # Extend to the nearest flanking exons.
  upstream_exons = exons[exons['End'] < v_start]
  if not upstream_exons.empty:
    new_start = min(new_start, upstream_exons.iloc[-1]['Start'] - 100)

  downstream_exons = exons[exons['Start'] > v_end]
  if not downstream_exons.empty:
    new_end = max(new_end, downstream_exons.iloc[0]['End'] + 100)

  # Include any exons overlapping the variant itself.
  overlapping = exons[(exons['Start'] <= v_end) & (exons['End'] >= v_start)]
  if not overlapping.empty:
    new_start = min(new_start, overlapping['Start'].min() - 100)
    new_end = max(new_end, overlapping['End'].max() + 100)

  # Expand to include significant splice junctions.
  all_juncs = []
  try:
    all_juncs.extend(ref_sashimi.get_junctions(clamp_interval))
    all_juncs.extend(alt_sashimi.get_junctions(clamp_interval))
  except (ValueError, IndexError, AttributeError) as e:
    print(f'Warning: Failed to fetch junctions for zoom: {e}')

  if all_juncs:
    max_score = max(j.k for j in all_juncs)
    base_interval_obj = genome.Interval(chrom, new_start, new_end)
    significant_juncs = [
        j
        for j in all_juncs
        if (j.k >= 5 or (max_score > 0 and j.k / max_score > 0.1))
        and genome.Interval(chrom, j.start, j.end).overlaps(base_interval_obj)
    ]

    if significant_juncs:
      j_min = min(j.start for j in significant_juncs)
      j_max = max(j.end for j in significant_juncs)
      new_start = min(new_start, j_min)
      new_end = max(new_end, j_max)

      # Snap to exon boundaries near junction anchors.
      up_anchor = exons[
          (exons['End'] >= j_min - 100) & (exons['End'] <= j_min + 100)
      ]
      if not up_anchor.empty:
        new_start = min(new_start, up_anchor['Start'].min() - 100)

      down_anchor = exons[
          (exons['Start'] >= j_max - 100) & (exons['Start'] <= j_max + 100)
      ]
      if not down_anchor.empty:
        new_end = max(new_end, down_anchor['End'].max() + 100)

  # Clamp to the prediction interval to prevent out-of-bounds errors.
  new_start = max(new_start, clamp_interval.start)
  new_end = min(new_end, clamp_interval.end)

  return genome.Interval(chrom, new_start, new_end)


def resolve_tracks_argument(tracks_arg: str | None) -> dict[str, Any]:
  """Resolves --tracks argument to list of OutputTypes and flags."""
  if not tracks_arg:
    # Default: RNA_SEQ and DNASE if nothing specified
    return {
        'outputs': [dna_client.OutputType.RNA_SEQ, dna_client.OutputType.DNASE],
        'show_splicing': False,
        'show_regulatory': True,
    }

  arg_list = [t.strip().lower() for t in tracks_arg.split(',')]
  outputs = set()
  show_splicing = False
  show_regulatory = False

  # Macros
  if 'all' in arg_list:
    arg_list = ['splicing', 'regulatory']

  if 'splicing' in arg_list:
    outputs.update([
        dna_client.OutputType.RNA_SEQ,
        dna_client.OutputType.SPLICE_JUNCTIONS,
        dna_client.OutputType.SPLICE_SITE_USAGE,
        dna_client.OutputType.SPLICE_SITES,
    ])
    show_splicing = True

  if 'regulatory' in arg_list:
    outputs.update([
        dna_client.OutputType.DNASE,
        dna_client.OutputType.CHIP_TF,
        dna_client.OutputType.CHIP_HISTONE,
    ])
    show_regulatory = True

  # Individual output type overrides (e.g. --tracks=dnase,chip_tf)
  if 'rna_seq' in arg_list or 'expression' in arg_list:
    outputs.add(dna_client.OutputType.RNA_SEQ)
  if 'dnase' in arg_list:
    outputs.add(dna_client.OutputType.DNASE)
    show_regulatory = True
  if 'chip' in arg_list or 'chip_tf' in arg_list:
    outputs.add(dna_client.OutputType.CHIP_TF)
    show_regulatory = True
  if 'chip_histone' in arg_list:
    outputs.add(dna_client.OutputType.CHIP_HISTONE)
    show_regulatory = True

  return {
      'outputs': list(outputs),
      'show_splicing': show_splicing,
      'show_regulatory': show_regulatory,
  }


def load_target_gene_info(
    gtf: pd.DataFrame, gene_name: str, interval_1mb: genome.Interval
) -> tuple[genome.Interval, str | None, list[Any], pd.DataFrame]:
  """Loads gene info from GTF and returns interval, strand, transcripts, and filtered GTF."""
  gene_gtf = gtf[gtf['gene_name'] == gene_name]
  if gene_gtf.empty:
    print(f'Gene {gene_name} not found.')
    gene_interval = interval_1mb
    strand = None
    transcripts = []
  else:
    gene_interval = gene_annotation.get_gene_interval(
        gene_gtf, gene_symbol=gene_name
    )
    strand = gene_gtf['Strand'].iloc[0]
    print(f'Target Gene: {gene_name} ({strand})')

    # Extract transcripts
    print('Filtering to longest transcripts...')
    longest_gene_gtf = gene_annotation.filter_to_longest_transcript(gene_gtf)
    transcript_extractor = transcript_utils.TranscriptExtractor(
        longest_gene_gtf
    )
    transcripts = transcript_extractor.extract(
        gene_interval.resize(gene_interval.width + 10000)
    )
    # Filter transcripts to gene strand
    transcripts = [t for t in transcripts if t.strand == strand]

    if not transcripts:
      print(
          'WARNING: No transcripts found for gene on the expected strand.'
          ' Transcript track will be missing.'
      )

  return gene_interval, strand, transcripts, gene_gtf


def get_rna_seq_components(
    prediction: Any,
    requested_outputs: list[dna_client.OutputType],
    ontology: str,
    strand: str | None,
    pretty_id: str,
) -> list[Any]:
  """Returns RNA-seq overlay components."""
  if dna_client.OutputType.RNA_SEQ not in requested_outputs:
    return []
  rna_comps = filter_and_create_overlay(
      prediction.reference.rna_seq,
      prediction.alternate.rna_seq,
      ontology,
      strand=strand,
      label_suffix=f'\n{pretty_id}\nRNA',
  )
  return rna_comps or []


def add_splicing_components(
    prediction: Any,
    requested_outputs: list[dna_client.OutputType],
    show_splicing: bool,
    variant: genome.Variant,
    variant_args: Any,
    gene_gtf: pd.DataFrame,
    interval_1mb: genome.Interval,
    strand: str | None,
    pretty_id: str,
    components: list[Any],
    zoom_interval: genome.Interval,
) -> genome.Interval:
  """Adds splicing components and updates zoom interval."""
  if not show_splicing:
    return zoom_interval

  # WHOLE GENE ZOOM
  if variant_args.view == 'whole_gene':
    if not gene_gtf.empty:
      gene_interval = gene_annotation.get_gene_interval(
          gene_gtf, gene_symbol=variant_args.gene
      )
      padding = max(1000, int(gene_interval.width * 0.05))
      zoom_interval = gene_interval.resize(gene_interval.width + padding * 2)
      print(f'Zooming to Whole Gene: {zoom_interval}')
    else:
      print(
          'WARNING: --view whole_gene requested but gene not found in GTF.'
          ' Falling back to default zoom.'
      )

  # Pre-calculate Sashimi for Zoom
  try:
    if (
        'ontology_curie'
        in prediction.reference.splice_junctions.metadata.columns
    ):
      ref_junc = prediction.reference.splice_junctions.filter_by_ontology(
          variant_args.ontology
      )
      alt_junc = prediction.alternate.splice_junctions.filter_by_ontology(
          variant_args.ontology
      )
    else:
      print(
          'WARNING: Splicing tracks missing "ontology_curie" metadata.'
          ' Skipping ontology filtering.'
      )
      ref_junc = prediction.reference.splice_junctions
      alt_junc = prediction.alternate.splice_junctions
  except (KeyError, ValueError, AttributeError) as e:
    print(
        f'WARNING: Splicing ontology filtering failed: {e}. Using all'
        ' returned junctions.'
    )
    ref_junc = prediction.reference.splice_junctions
    alt_junc = prediction.alternate.splice_junctions

  ref_junc = filter_preference(ref_junc)
  alt_junc = filter_preference(alt_junc)

  ref_sashimi = ColoredSashimi(
      ref_junc,
      ylabel_template=f"Ref Junc\n{pretty_id}\n({strand if strand else ''})",
      color=COLOR_REF,
      normalize_values=False,
      forced_strand=strand,
  )
  alt_sashimi = ColoredSashimi(
      alt_junc,
      ylabel_template=f"Alt Junc\n{pretty_id}\n({strand if strand else ''})",
      color=COLOR_ALT,
      normalize_values=False,
      forced_strand=strand,
  )

  # Dynamic zoom: expand the zoom interval to include flanking exons
  # and significant splice junctions around the variant.
  if not gene_gtf.empty:
    computed_zoom = compute_splicing_zoom(
        chrom=variant_args.chrom,
        variant_start=variant.start,
        ref_allele=variant_args.ref,
        gene_gtf=gene_gtf,
        ref_sashimi=ref_sashimi,
        alt_sashimi=alt_sashimi,
        clamp_interval=interval_1mb,
    )
    if computed_zoom is not None:
      zoom_interval = computed_zoom

  # Splice Usage
  if dna_client.OutputType.SPLICE_SITE_USAGE in requested_outputs:
    usage_comps = filter_and_create_overlay(
        prediction.reference.splice_site_usage,
        prediction.alternate.splice_site_usage,
        variant_args.ontology,
        strand=strand,
        label_suffix=f'\n{pretty_id}\nUsage',
    )
    if usage_comps:
      components.extend(usage_comps)

  # Splice Sites
  if dna_client.OutputType.SPLICE_SITES in requested_outputs:
    ref_sites = filter_preference(prediction.reference.splice_sites)
    alt_sites = filter_preference(prediction.alternate.splice_sites)

    def split_sites(track: Any, pattern: str) -> Any:
      if track is None or track.metadata.empty:
        return None
      mask = np.zeros(len(track.metadata), dtype=bool)
      if 'name' in track.metadata.columns:
        mask |= track.metadata['name'].str.contains(
            pattern, case=False, na=False
        )
      if 'Assay title' in track.metadata.columns:
        mask |= track.metadata['Assay title'].str.contains(
            pattern, case=False, na=False
        )
      return (
          track.filter_tracks(np.flatnonzero(mask.values))
          if np.any(mask)
          else None
      )

    ref_donor = split_sites(ref_sites, 'Donor')
    alt_donor = split_sites(alt_sites, 'Donor')
    if ref_donor:
      donor_comps = filter_and_create_overlay(
          ref_donor,
          alt_donor,
          variant_args.ontology,
          strand=strand,
          label_suffix=f'\n{pretty_id}\nSites (Donor, {strand})',
      )
      if donor_comps:
        components.extend(donor_comps)

    ref_acceptor = split_sites(ref_sites, 'Acceptor')
    alt_acceptor = split_sites(alt_sites, 'Acceptor')
    if ref_acceptor:
      acc_comps = filter_and_create_overlay(
          ref_acceptor,
          alt_acceptor,
          variant_args.ontology,
          strand=strand,
          label_suffix=f'\n{pretty_id}\nSites (Acceptor, {strand})',
      )
      if acc_comps:
        components.extend(acc_comps)

  components.append(ref_sashimi)
  components.append(alt_sashimi)

  return zoom_interval


def get_regulatory_components(
    prediction: Any,
    requested_outputs: list[dna_client.OutputType],
    show_regulatory: bool,
    variant_args: Any,
    pretty_id: str,
) -> list[Any]:
  """Returns regulatory overlay components (DNase, ChIP-TF)."""
  if not show_regulatory:
    return []

  components = []
  if dna_client.OutputType.DNASE in requested_outputs:
    dnase_comp = filter_and_create_overlay(
        prediction.reference.dnase,
        prediction.alternate.dnase,
        variant_args.ontology,
        strand=None,
        label_suffix=f'\n{pretty_id}\nDNASE',
    )
    if dnase_comp:
      components.extend(dnase_comp)

  if dna_client.OutputType.CHIP_TF in requested_outputs:
    chip_tf_comps = filter_and_create_overlay(
        prediction.reference.chip_tf,
        prediction.alternate.chip_tf,
        variant_args.ontology,
        strand=None,
        label_suffix=f'\n{pretty_id}\nCHIP_TF',
        target_tf=variant_args.tf,
    )
    if chip_tf_comps:
      components.extend(chip_tf_comps)

  return components


def render_plots(
    variant_args: Any,
    prediction: Any,
    components: list[Any],
    zoom_interval: genome.Interval,
    variant: genome.Variant,
    requested_outputs: list[dna_client.OutputType],
    gene_gtf: pd.DataFrame,
    gene_interval: genome.Interval,
) -> None:
  """Renders default, detail, and whole-gene plots."""
  print('Generating plot...')
  plot_path = os.path.join(
      variant_args.output_dir,
      f"plot_{variant_args.tissue.replace(' ', '_')}"
      f'_{variant_args.gene}_effects.png',
  )

  max_diff = 0.0
  if (
      prediction.reference.rna_seq is not None
      and not prediction.reference.rna_seq.metadata.empty
      and prediction.alternate.rna_seq is not None
      and not prediction.alternate.rna_seq.metadata.empty
  ):
    try:
      diff = np.max(
          np.abs(
              prediction.alternate.rna_seq.values
              - prediction.reference.rna_seq.values
          )
      )
      max_diff = max(max_diff, diff)
    except (ValueError, TypeError) as e:
      print(f'Warning: Could not compute RNA diff summary: {e}')

  summary_text = (
      variant_args.description
      if variant_args.description
      else f'Max DNASE/RNA Diff: {max_diff:.2f}'
  )

  try:
    plot_components.plot(
        components=components,
        interval=zoom_interval,  # Tighter zoom or dynamic zoom
        annotations=[plot_components.VariantAnnotation([variant], alpha=0.8)],
    )
    plt.suptitle(
        f'{variant_args.gene} {variant_args.tissue}'
        f' {variant_args.chrom}:{variant_args.pos}'
        f':{variant_args.ref}>{variant_args.alt}'
        f'\n{summary_text}\nZoom:'
        f' {zoom_interval}'
    )
    plt.savefig(plot_path, dpi=150, bbox_inches='tight')
    plt.close()
    print(f'Saved plot to {plot_path}')
  except (ValueError, RuntimeError, OSError) as e:
    print(f'Failed to plot: {e}')

  print('Generating Detail View (+/- 50bp)...')
  detail_path = os.path.join(
      variant_args.output_dir,
      f"plot_{variant_args.tissue.replace(' ', '_')}"
      f'_{variant_args.gene}_detail.png',
  )

  detail_interval = genome.Interval(
      variant_args.chrom, variant_args.pos - 50, variant_args.pos + 50
  )

  try:
    plot_components.plot(
        components=components,
        interval=detail_interval,
        annotations=[plot_components.VariantAnnotation([variant], alpha=0.8)],
    )
    plt.suptitle(
        f'{variant_args.gene} {variant_args.tissue}'
        f' {variant_args.chrom}:{variant_args.pos} Detail View (+/- 50bp)'
    )
    plt.savefig(detail_path, dpi=150, bbox_inches='tight')
    plt.close()
    print(f'Saved detail plot to {detail_path}')
  except (ValueError, RuntimeError, OSError) as e:
    print(f'Failed to plot detail view: {e}')

  if dna_client.OutputType.RNA_SEQ in requested_outputs and not gene_gtf.empty:
    print('Generating Whole-Gene View (RNA-seq requested)...')
    filename = (
        f"plot_{variant_args.tissue.replace(' ', '_')}"
        f'_{variant_args.gene}_wholegene.png'
    )
    wholegene_path = os.path.join(variant_args.output_dir, filename)

    pad = int(gene_interval.width * 0.1)
    wholegene_interval = gene_interval.resize(gene_interval.width + pad)

    try:
      plot_components.plot(
          components=components,
          interval=wholegene_interval,
          annotations=[plot_components.VariantAnnotation([variant], alpha=0.8)],
      )
      plt.suptitle(
          f'{variant_args.gene} {variant_args.tissue} Whole Gene'
          f' View\n{summary_text}'
      )
      plt.savefig(wholegene_path, dpi=150, bbox_inches='tight')
      plt.close()
      print(f'Saved whole-gene plot to {wholegene_path}')
    except (ValueError, RuntimeError, OSError) as e:
      print(f'Failed to plot whole-gene view: {e}')


def visualize_variant_effects(variant_args: Any) -> None:
  """Main function to visualize variant effects."""
  # Setup Output
  os.makedirs(variant_args.output_dir, exist_ok=True)

  # Initialize Client
  api_key = os.environ.get('ALPHAGENOME_API_KEY')
  if not api_key:
    raise ValueError('ALPHAGENOME_API_KEY environment variable not set.')

  dna_model = dna_client.create(
      api_key=api_key,
      address=API_ADDRESS,
  )

  # Variant Setup
  variant = genome.Variant(
      variant_args.chrom, variant_args.pos, variant_args.ref, variant_args.alt
  )

  # Context Interval (1Mb)
  seq_length = 2**20
  interval_1mb = genome.Interval(
      variant_args.chrom,
      variant_args.pos - seq_length // 2,
      variant_args.pos + seq_length // 2,
  )

  # Determine requested tracks
  track_config = resolve_tracks_argument(variant_args.tracks)
  requested_outputs = track_config['outputs']
  show_splicing = track_config['show_splicing']
  show_regulatory = track_config['show_regulatory']

  print(
      f'Predicting variant effects for {variant_args.tissue}'
      f' ({variant_args.ontology})...'
  )
  print(f'Requested Outputs: {[o.name for o in requested_outputs]}')

  # Load GTF for Gene Info
  print('Loading GTF...')
  gtf = pd.read_feather(GTF_URL)

  gene_interval, strand, transcripts, gene_gtf = load_target_gene_info(
      gtf, variant_args.gene, interval_1mb
  )

  # Predict
  prediction = dna_model.predict_variant(
      interval=interval_1mb,
      variant=variant,
      requested_outputs=requested_outputs,
      ontology_terms=[variant_args.ontology],
  )

  # --- Plotting ---
  components = []

  # 1. Transcripts (Verified: User wants these AT THE TOP)
  if transcripts:
    components.append(
        plot_components.TranscriptAnnotation(
            transcripts, label_name='gene_name'
        )
    )

  # Formatted Label for User Readability
  pretty_id = f'{variant_args.tissue}\n({variant_args.ontology})'

  # 2. RNA-seq (Stranded)
  components.extend(
      get_rna_seq_components(
          prediction,
          requested_outputs,
          variant_args.ontology,
          strand,
          pretty_id,
      )
  )

  # Default Zoom: +/- 1000bp around variant (total 2000bp window).
  zoom_interval = variant.reference_interval.resize(2000)

  # 3. Splicing Tracks (Conditional)
  zoom_interval = add_splicing_components(
      prediction,
      requested_outputs,
      show_splicing,
      variant,
      variant_args,
      gene_gtf,
      interval_1mb,
      strand,
      pretty_id,
      components,
      zoom_interval,
  )
  # 4. Regulatory Tracks (DNASE, CHIP_TF, CHIP_HISTONE)
  components.extend(
      get_regulatory_components(
          prediction,
          requested_outputs,
          show_regulatory,
          variant_args,
          pretty_id,
      )
  )

  render_plots(
      variant_args,
      prediction,
      components,
      zoom_interval,
      variant,
      requested_outputs,
      gene_gtf,
      gene_interval,
  )


def main(argv: list[str] | None = None) -> None:
  """Main entry point for the variant effects visualization CLI tool."""
  dotenv.load_dotenv(os.path.expanduser('~/.env'))
  parser = argparse.ArgumentParser(
      description='Visualize variant effects using AlphaGenome predictions.'
  )
  parser.add_argument(
      '--chrom',
      required=True,
      help='Chromosome (e.g., chr17).',
  )
  parser.add_argument(
      '--pos',
      type=int,
      required=True,
      help='Position (1-based).',
  )
  parser.add_argument(
      '--ref',
      required=True,
      help='Reference allele.',
  )
  parser.add_argument(
      '--alt',
      required=True,
      help='Alternate allele.',
  )
  parser.add_argument(
      '--gene',
      required=True,
      help='Gene symbol.',
  )
  parser.add_argument(
      '--tissue',
      required=True,
      help='Tissue name for labeling.',
  )
  parser.add_argument(
      '--ontology', required=True, help='Ontology CURIE (e.g., UBERON:0002107).'
  )
  parser.add_argument('--output_dir', required=True, help='Output directory.')
  parser.add_argument(
      '--tracks',
      default='regulatory',
      help='Comma-separated track types: splicing, regulatory, all.',
  )
  parser.add_argument(
      '--tf', default=None, help='TF name to filter CHIP_TF tracks.'
  )
  parser.add_argument(
      '--view',
      choices=['default', 'whole_gene'],
      default='default',
      help="Zoom level. 'whole_gene' plots the entire gene interval.",
  )
  parser.add_argument(
      '--description',
      default=None,
      help='Natural language summary of the variant effect.',
  )
  args = parser.parse_args(argv)

  visualize_variant_effects(args)


if __name__ == '__main__':
  main()
