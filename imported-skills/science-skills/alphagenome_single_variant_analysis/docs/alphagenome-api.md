# AlphaGenome API Reference

Pip package: `alphagenome`

## Setup and Imports

Standard imports for AlphaGenome workflows:

```python
from alphagenome.data import gene_annotation
from alphagenome.data import genome
from alphagenome.data import track_data
from alphagenome.data import transcript as transcript_utils
from alphagenome.interpretation import ism
from alphagenome.models import dna_client
from alphagenome.models import variant_scorers
from alphagenome.visualization import plot_components
import matplotlib.pyplot as plt
import pandas as pd
```

### Client Initialization

The API key is automatically loaded by `dotenv` from the
`.env` file in the agent configuration dir.

To initialize a client:

```python
from alphagenome.models import dna_client

dna_model = dna_client.create(
    api_key=os.environ.get('ALPHAGENOME_API_KEY'),
    address='dns:///gdmscience.googleapis.com:443',
)
```

## Core Data Types

### genome.Interval

0-based half-open interval (includes `start`, excludes `end`).

```python
interval = genome.Interval(chromosome='chr1', start=1_000, end=1_010)

interval.center()     # Returns center position (int)
interval.width        # Returns 10
interval.resize(100)  # Resizes around center
interval.overlaps(other_interval)
interval.contains(other_interval)
interval.intersect(other_interval)
```

### genome.Variant

Position is **1-based** (VCF-compatible).

```python
variant = genome.Variant(
    chromosome='chr22',
    position=36201698,  # 1-based!
    reference_bases='A',
    alternate_bases='C',
)
# Get interval around variant
interval = variant.reference_interval.resize(dna_client.SEQUENCE_LENGTH_1MB)
```

## Predictions

### Predict from DNA Sequence

```python
output = dna_model.predict_sequence(
    sequence='GATTACA'.center(dna_client.SEQUENCE_LENGTH_1MB, 'N'),
    requested_outputs=[dna_client.OutputType.DNASE],
    ontology_terms=['UBERON:0002048'],  # Lung
)
# Access predictions
print(output.dnase.values.shape)  # (sequence_length, num_tracks)
print(output.dnase.metadata)      # Track metadata DataFrame
```

### Predict from Genome Interval

```python
interval = genome.Interval('chr1', 1000000, 1000001)
interval = interval.resize(dna_client.SEQUENCE_LENGTH_1MB)

output = dna_model.predict_interval(
    interval=interval,
    requested_outputs=[dna_client.OutputType.RNA_SEQ],
    ontology_terms=['UBERON:0001114'],  # Right liver lobe
)
```

### Mouse Predictions

Specify `organism=dna_client.Organism.MUS_MUSCULUS` for mouse models.

```python
output = dna_model.predict_sequence(
    ...,
    organism=dna_client.Organism.MUS_MUSCULUS,
)
```

## Variant Analysis

### Predict Variant Effects (Raw Tracks)

Compare predictions for Reference (REF) vs Alternate (ALT) alleles.

```python
variant_output = dna_model.predict_variant(
    interval=interval,
    variant=variant,
    requested_outputs=[dna_client.OutputType.RNA_SEQ],
    ontology_terms=['UBERON:0001157'],  # Colon - Transverse
)

ref_tracks = variant_output.reference.rna_seq
alt_tracks = variant_output.alternate.rna_seq
```

### Score Variants (Aggregated Scores)

Get aggregated scores using recommended scorers.

```python
scorer = variant_scorers.RECOMMENDED_VARIANT_SCORERS['RNA_SEQ']

variant_scores_list = dna_model.score_variant(
    interval=interval,
    variant=variant,
    variant_scorers=[scorer],
)
scores = variant_scores_list[0]

# Tidy scores to DataFrame
df = variant_scorers.tidy_scores([scores], match_gene_strand=True)
print(df[['gene_symbol', 'raw_score', 'quantile_score']])
```

**Available recommended scorers:** `ATAC`, `CAGE`, `DNASE`, `PROCAP`, `RNA_SEQ`,
`CHIP_TF`, `CHIP_HISTONE`, `SPLICE_SITES`, `SPLICE_SITE_USAGE`,
`SPLICE_JUNCTIONS`, `POLYADENYLATION`, `CONTACT_MAPS`

### Batch Variant Scoring

```python
# Parse variants from VCF-like DataFrame
for _, row in vcf_df.iterrows():
    variant = genome.Variant(
        chromosome=str(row.CHROM),
        position=int(row.POS),
        reference_bases=row.REF,
        alternate_bases=row.ALT,
    )
    interval = variant.reference_interval.resize(
        dna_client.SEQUENCE_LENGTH_1MB
    )
    scores = dna_model.score_variant(
        interval=interval,
        variant=variant,
        variant_scorers=list(
            variant_scorers.RECOMMENDED_VARIANT_SCORERS.values()
        ),
    )
```

### In Silico Mutagenesis (ISM)

Systematically mutate a region to find important motifs.

```python
from alphagenome.interpretation import ism

sequence_interval = genome.Interval(
    'chr20', 3_753_000, 3_753_400
).resize(dna_client.SEQUENCE_LENGTH_16KB)
ism_interval = sequence_interval.resize(256)  # Mutate center 256bp

scorer = variant_scorers.CenterMaskScorer(
    requested_output=dna_client.OutputType.DNASE,
    width=501,
    aggregation_type=variant_scorers.AggregationType.DIFF_MEAN,
)

variant_scores = dna_model.score_ism_variants(
    interval=sequence_interval,
    ism_interval=ism_interval,
    variant_scorers=[scorer],
)
```

## TrackData Operations

### Properties

```python
tdata = output.dnase
tdata.values      # numpy array (sequence_length, num_tracks)
tdata.metadata    # pandas DataFrame with track info
tdata.resolution  # bp per position
tdata.interval    # genome.Interval
```

### Filtering by Strand

```python
pos_tracks = tdata.filter_to_positive_strand()
neg_tracks = tdata.filter_to_negative_strand()
unstranded = tdata.filter_to_unstranded()
```

### Filtering by Track Name

```python
track1_tdata = tdata.select_tracks_by_name(names='track1')
```

### Filtering by Metadata (Manual)

```python
mask = tracks.metadata['histone_mark'] == 'H3K27ac'
filtered_tracks = track_data.TrackData(
    values=tracks.values[:, mask],
    metadata=tracks.metadata[mask],
    resolution=tracks.resolution,
    interval=tracks.interval,
    uns=tracks.uns,
)
```

### Slicing

```python
# By position indices
tdata.slice_by_positions(start=2, end=4)

# By genomic interval
tdata.slice_by_interval(
    genome.Interval(chromosome='chr1', start=1_002, end=1_004)
)
```

### Resizing

```python
tdata.resize(width=2)  # Crop to center 2 positions
tdata.resize(width=8)  # Pad with zeros
```

### Resolution Conversion

```python
tdata.change_resolution(resolution=128)  # Downsample
tdata.change_resolution(resolution=1)    # Upsample
```

## Track Metadata Reference

Modality          | Key Column       | Example Values
----------------- | ---------------- | --------------------------------
`CHIP_HISTONE`    | `histone_mark`   | `H3K27ac`, `H3K4me3`, `H3K27me3`
`CHIP_TF`         | `target`         | `CTCF`, `JUND`, `POLR2A`
`RNA_SEQ`, `CAGE` | `strand`         | `+`, `-`
All               | `ontology_curie` | `UBERON:0002107`, `EFO:0001187`
All               | `biosample_name` | `liver`, `HepG2`

> [!CAUTION] `CHIP_HISTONE` uses `histone_mark`, NOT `target`. `target` is for
> `CHIP_TF`.

## Visualization

```python
plot_components.plot(
    components=[
        plot_components.TranscriptAnnotation(transcripts),
        plot_components.Tracks(output.rna_seq),
        plot_components.OverlaidTracks(
            tdata={'REF': ref_tracks, 'ALT': alt_tracks},
            colors={'REF': 'dimgrey', 'ALT': 'red'},
        ),
    ],
    interval=interval,
    annotations=[plot_components.VariantAnnotation([variant], alpha=0.8)],
)
plt.show()
```

> [!CAUTION] `VariantAnnotation` must be in `annotations=`, NOT `components`.
> Putting it in components causes `AttributeError: 'VariantAnnotation' object
> has no attribute 'num_axes'`.

### Get Human-Readable Tissue Names

```python
tissue = tracks.metadata[
    tracks.metadata['ontology_curie'] == ontology_id
]['biosample_name'].iloc[0]
plt.title(f"{gene_symbol} - {tissue} - {modality.name}")
```

## Gene Annotations (GTF)

```python
gtf = pd.read_feather(
    'https://storage.googleapis.com/alphagenome/reference/gencode/'
    'hg38/gencode.v46.annotation.gtf.gz.feather'
)

# Filter for MANE Select transcripts
gtf_transcripts = gene_annotation.filter_protein_coding(gtf)
gtf_transcripts = gene_annotation.filter_to_mane_select_transcript(
    gtf_transcripts
)

# Get stranded interval for a gene
interval = gene_annotation.get_gene_interval(gtf, gene_symbol='CYP2B6')
```

GTF feather uses **capitalized** column names for core fields:

Correct      | Incorrect
------------ | ---------
`Feature`    | `feature`
`Chromosome` | `seqname`
`Start`      | `start`
`End`        | `end`
`Strand`     | `strand`

Other columns (`gene_name`, `gene_id`, `gene_type`) remain lowercase.

## Best Practices

1.  **Interval Resizing**: Always resize to a supported length before
    prediction. Use `dna_client.SUPPORTED_SEQUENCE_LENGTHS.keys()` for options.

2.  **Efficient Predictions**: Always specify `requested_outputs` and
    `ontology_terms` to reduce compute and data transfer.

3.  **Variant Scoring**: Use `tidy_scores(..., match_gene_strand=True)` to
    filter irrelevant strand matches. `quantile_score` allows comparison across
    different scorers.

4.  **ISM**: Expensive (scores 3 variants per position). Use shorter context
    intervals (16KB) and narrower mutation regions.

5.  **Saving Figures**: Use `plt.savefig('plot.png', bbox_inches='tight')` to
    prevent cut-off labels.

## Common Pitfalls

### OverlaidTracks has no `title` argument

```python
# Wrong:
plot_components.OverlaidTracks(..., title="My Title")  # ERROR!

# Correct:
plot_components.plot([plot_components.OverlaidTracks(...)], interval=...)
plt.suptitle("My Title")
```

### TrackData has no `subset()` method

Use manual filtering with boolean masks on `metadata`, or use
`select_tracks_by_name()` for name-based selection.

### `uv run` fails

Clear the cached environment and retry: `uv cache clean && uv run
<script_name>`. If the issue persists, check that `pyproject.toml` exists in the
skill root and contains `alphagenome>=0.6.1` in `dependencies`.

### Client initialization needs correct address

Always use the production address for API access: `address='dns:///gdmscience.googleapis.com:443'`

--------------------------------------------------------------------------------

## Output Types

Defined as `dna_client.OutputType`, used in `requested_outputs`:

OutputType          | Description
------------------- | -----------------------------------------------------
`ATAC`              | ATAC-seq: chromatin accessibility
`CAGE`              | Cap Analysis of Gene Expression
`DNASE`             | DNase I hypersensitive sites: chromatin accessibility
`RNA_SEQ`           | RNA sequencing: gene expression
`CHIP_HISTONE`      | ChIP-seq: histone modifications
`CHIP_TF`           | ChIP-seq: transcription factor binding
`SPLICE_SITES`      | Donor and acceptor splice sites
`SPLICE_SITE_USAGE` | Fraction of time each splice site is used
`SPLICE_JUNCTIONS`  | Split read RNA-seq counts for each junction
`CONTACT_MAPS`      | 3D DNA-DNA contact probabilities
`PROCAP`            | Precision Run-On sequencing and capping

--------------------------------------------------------------------------------

## Variant Scoring Details

### Gene Expression (RNA-seq)

Quantifies impact on overall gene transcript abundance.

-   **Comparison**: Predicted RNA coverage between REF and ALT alleles.
-   **Mask**: Exons for a gene of interest.
-   **Aggregation**: Log-fold change: `log(mean(ALT) + 0.001) - log(mean(REF) +
    0.001)`.

### Polyadenylation Site (PAS) Usage

Captures variant's impact on RNA isoform production (paQTLs).

-   **Mask**: Local 400bp windows around 3' cleavage junctions.
-   **Aggregation**: Maximum absolute log-fold change of isoform ratios
    (distal/proximal PAS usage).

### TSS Activity (CAGE, PRO-cap)

Quantifies local changes at TSSs.

-   **Mask**: Local 501bp window centered at variant.
-   **Aggregation**: `log2[(sum(ALT) + 1) / (sum(REF) + 1)]`.

### Chromatin Accessibility (ATAC-seq, DNase-seq)

-   **Mask**: Local 501bp window centered at variant.
-   **Aggregation**: `log2[(sum(ALT) + 1) / (sum(REF) + 1)]`.

### Transcription Factor Binding (ChIP-TF)

-   **Mask**: Local 501bp window centered at variant.
-   **Aggregation**: `log2[(sum(ALT) + 1) / (sum(REF) + 1)]`.

### Histone Modifications (ChIP-Histone)

-   **Mask**: Local 2001bp window centered at variant.
-   **Aggregation**: `log2[(sum(ALT) + 1) / (sum(REF) + 1)]`.

### Splicing (Splice Sites)

Changes in class assignment probabilities (acceptor, donor) across gene body.

-   **Aggregation**: `max(|ALT - REF|)` across gene body.

### Splicing (Splice Site Usage)

Changes in fraction of splice site usage.

-   **Aggregation**: `max(|ALT - REF|)` across gene body.

### Splicing (Splice Junctions)

Changes in predicted RNA-seq reads spanning junctions.

-   **Aggregation**: `max(|log(ALT) - log(REF)|)` across splice site pairs.

### 3D Genome Contact (Contact Maps)

Local contact disruption.

-   **Mask**: Local 1MB window centered at variant.
-   **Aggregation**: Mean absolute difference of contact frequencies for
    variant-containing bin.

### Active Allele Scorers

Capture absolute activity level (not REF/ALT difference):
`max(aggregated_signal(ALT), aggregated_signal(REF))` over masked region.

### Quantile Scores

Quantile scores are empirical percentile ranks vs common variants (MAF>0.01 in
gnomAD v3). A quantile of 0.99 means the score is at the 99th percentile.
Maximum value is ±0.999990 (~300K variant background). For signed scorers,
quantiles are linearly mapped to [-1, 1] to preserve directionality.

**Practical rule**: Use quantile as significance indicator; use raw_score for
magnitude comparison within the same scorer.
