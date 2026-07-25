---
name: alphagenome-single-variant-analysis
description: >
  Analyzes genetic variant effects on gene expression (RNA-seq), chromatin
  accessibility (DNASE), histone marks (ChIP), and transcription factors
  using the AlphaGenome API. Use when the user asks about non-coding variant effects,
  pathogenicity, clinical significance, disease associations, functional
  effects, gene expression changes, splicing disruption, or regulatory effects
  in promoters and enhancers. Also use for resolving biological terms to
  tissue/cell-type ontologies (UBERON/CL) or analyzing variants in
  chr:pos:ref>alt format.
---

# Variant Analysis using AlphaGenome

## Prerequisites

1.  **`uv`**: Read the `uv` skill and follow its Setup instructions to ensure
    `uv` is installed and on PATH.
2.  **User Notification**: If
    .licenses/alphagenome_single_variant_analysis_LICENSE.txt does not already
    exist in the workspace root directory then (1) prominently notify the user
    to check the terms at https://deepmind.google.com/science/alphagenome/, then
    (2) create the file recording the notification text and timestamp.
3.  **`.env` file**: Make sure the `.env` file exists in your home directory.
    Create one if it does not exist.
4.  **`ALPHAGENOME_API_KEY`**: This skill requires an API key to function.
    You can register for a key at https://deepmind.google.com/science/alphagenome/.
    You **MUST** use the safe credentials protocol in the `credentials` skill to
    check for and request this key if this skill looks relevant to the user's request.

## Core Rules

-   **NEVER run `python3` or `python3 -c` directly.** The system Python does not
    necessarily have pandas, numpy, and other key dependencies. ALWAYS use `uv
    run` to run ALL Python code — including scripts, ad-hoc analysis files, and
    one-liners. Do not attempt to `pip install` or create new venvs — `uv`
    manages an isolated environment automatically.
-   **Offline Only**: NEVER use external APIs (e.g., MyGene.info, Ensembl REST)
    for gene/transcript lookup. Use `lookup_gene_info.py` with the local GTF. If
    it fails, fix the environment/paths, do not switch to external APIs.
-   **API Key is required**: `ALPHAGENOME_API_KEY` must be set before running
    any script.
-   **Notification**: If this skill is used, ensure this is mentioned in the
    output.
-   **Report Format**: Always use the templates in `docs/report-templates.md`
    for generating analysis reports, and ensure to include the table of top hits
    from the discovery scan.

## Environment Setup & Troubleshooting

### Python Environment

All scripts must be executed using `uv run`, which manages an isolated virtual
environment with the correct dependencies via `uv`.

```bash
uv run <script_name> [args...]
```

For ad-hoc scripts (e.g., inline analysis code saved to a temp file), pass the
full path instead of a short name:

```bash
uv run --project $SKILL_DIR /tmp/my_analysis.py --arg1 val1
```

> [!NOTE] The first invocation resolves and installs dependencies (~10s).
> Subsequent runs use the cached environment and start instantly. The cache
> lives in `~/.cache/uv/`.

### Common Issues

-   **Column Names**: `tidy_scores` and metadata often use `gene_name` (not
    `gene_symbol`) and `output_type` (not `modality`). Always inspect
    `df.columns` before filtering.
-   **Large Genes**: Genes > 500kb (e.g., `USH2A`) break the `whole_gene` view.
    Use `--view detail` or manual regional windows instead.
-   **Sashimi Strand Error**: `plot_components.Sashimi` does NOT accept a
    `strand` argument directly. Filter input tracks instead.
-   **KeyError: 'ontology_curie'**: Not all tracks have `ontology_curie`. Check
    `track.metadata.columns` before filtering.
-   **Python Path**: If `exec: "python": executable file not found` occurs,
    ensure you are using `uv run` instead of bare `python`/`python3`.
-   **NotImplementedError (pandas)**: "iLocation based boolean indexing on an
    integer type is not available". This occurs when using boolean masks with
    `.iloc` on integer-indexed DataFrames in newer pandas versions. **Fix**:
    Convert boolean masks to integer indices using `np.flatnonzero(mask)`.
-   **GTF Feather Case Sensitivity**: The AlphaGenome GTF Feather file uses
    **Capitalized** column names (`Feature`, `Start`, `End`, `Strand`) unlike
    standard GTF files. Always check `df.columns` if getting KeyErrors.
-   **`score_variant` ontology filtering**: `score_variant` does NOT accept
    `ontology_terms` as an argument. You must filter the returned AnnData
    objects manually by inspecting `adata.var` columns. In contrast,
    `predict_variant` DOES accept `ontology_terms` directly.
-   **Sashimi Zoom Logic**: To ensure "skipping" arcs are visible, expand the
    zoom to include the **flanking exons** rather than relying on junction
    overlap alone.
-   **Junction Scores**: Raw `Junction` objects from `prediction` may be simple
    Intervals. Use `junction_data.get_junctions_to_plot(predictions=...,
    name=...)` to retrieve objects with the `.k` (abundance/score) attribute.
-   **`uv` Not Found**: If `exec: uv: not found`, follow the installation
    instructions in [Prerequisites](#prerequisites).
-   **Registry Authentication Error (401)**: If `uv` fails with 401 Unauthorized
    for a private registry, set `UV_INDEX_URL=https://pypi.org/simple` before
    running the script.

## References

-   [alphagenome-api.md](docs/alphagenome-api.md) — API reference and code
    patterns
-   [interpretation-guide.md](docs/interpretation-guide.md) — Interpretation
    guide, score magnitude rules, ISM, and checklist.
-   [report-templates.md](docs/report-templates.md) — Full report templates
-   [`scripts/visualize_variant_effects.py`](scripts/visualize_variant_effects.py)
    — Single-variant visualization template (Ref/Alt comparisons, Splicing).
    -   **Splicing Zoom Strategy**: Uses a **Hybrid Approach** for optimal
        visibility:
        1.  **Base Interval**: Variant +/- 1 downstream and upstream exon
            (Structural Context).
        2.  **Junction Expansion**: Expands to include the full span of any
            **significant splicing junction** (e.g., exon skipping events that
            span multiple exons).
        3.  **Anchor Enforcement**: Ensures the exons *anchoring* these long
            junctions are fully visible. *Lesson*: Simple fixed windows (e.g.,
            2kb) or nearest-exon logic often fail for skipping events. Always
            use the *observed junction data* to drive zoom levels.
-   [`examples/splicing/`](docs/examples/splicing/) — Splicing analysis examples
-   [`examples/model_limitation_RNU4ATAC/`](docs/examples/model_limitation_RNU4ATAC/)
    — ncRNA structure limitation case study
-   [`examples/polyadenylation_HBA2/`](docs/examples/polyadenylation_HBA2/) — 3'
    UTR / Polyadenylation case study
-   [`examples/regulatory/`](docs/examples/regulatory/) — Regulatory variant
    examples
-   [`examples/negative_result_GATA4/`](docs/examples/negative_result_GATA4/) —
    Negative results (mathematical artefact)
-   [`examples/negative_result_TGFB3/`](docs/examples/negative_result_TGFB3/) —
    Negative results (proxies)
-   [`scripts/lookup_gene_info.py`](scripts/lookup_gene_info.py) — Gene &
    transcript lookup
-   [`scripts/resolve_ontology_terms.py`](scripts/resolve_ontology_terms.py) —
    Ontology term resolution (UBERON/CL IDs)

--------------------------------------------------------------------------------

## Code Patterns

### Broad Discovery Scan

Use `score_variant` across **differential scorers only** to discover unexpected
tissue effects.

```python
from alphagenome.models import dna_client
from alphagenome.models import variant_scorers
from alphagenome.data import genome
import os
import pandas as pd
import dotenv

# Load environment variables from ~/.env
dotenv.load_dotenv(os.path.expanduser('~/.env'))

# Setup API Key and Client
dna_model = dna_client.create(api_key=os.environ.get('ALPHAGENOME_API_KEY'),
                              address='dns:///gdmscience.googleapis.com:443')

# Define Variant (example)
variant_str = "chr2:1234:A>C"
chrom, pos_str, ref_alt = variant_str.split(':')
ref, alt = ref_alt.split('>')
pos = int(pos_str)

# Use supported sequence length (e.g., 2**20 for optimal performance)
SEQ_LENGTH = 2**20
interval = genome.Interval(chrom, pos - SEQ_LENGTH // 2, pos + SEQ_LENGTH // 2)
variant = genome.Variant(chrom, pos, ref, alt)

scorers = [
    variant_scorers.RECOMMENDED_VARIANT_SCORERS[m]
    for m in variant_scorers.RECOMMENDED_VARIANT_SCORERS
    if "ACTIVE" not in m and "CAGE" not in m and "PROCAP" not in m
]

print(f"Scoring variant {variant_str}...")
scores_list = dna_model.score_variant(interval=interval, variant=variant, variant_scorers=scorers)

# Process and Display Results
all_dfs = []
for score_adata in scores_list:
    df = variant_scorers.tidy_scores([score_adata], match_gene_strand=True)
    if df is not None:
        all_dfs.append(df)

if all_dfs:
    df = pd.concat(all_dfs)
    significant = df[df['quantile_score'].abs() > 0.995]
    ranked = significant.sort_values('raw_score', key=abs, ascending=False)
    print("Top Significant Hits:")
    print(ranked[['biosample_name', 'gene_name', 'output_type', 'quantile_score', 'raw_score']])
```

### Extended Search for Disease-Relevant Tissues

```python
# Define keywords based on disease context
disease_keywords = ["liver", "hepatocyte"]

# Filter for any match
mask = df['biosample_name'].str.contains('|'.join(disease_keywords), case=False, na=False)

relevant_hits = df[mask].sort_values('raw_score', key=abs, ascending=False)
print(f"\n--- Extended Analysis (Keywords: {disease_keywords}) ---")
print(relevant_hits.head(20)[['biosample_name', 'output_type', 'raw_score', 'quantile_score']])
```

## Workflow Checklist

```
Variant Analysis Progress:
- [ ] Step 0: Review Golden Examples (MANDATORY)
- [ ] Step 1: Create Output Folder and Setup
- [ ] Step 2: Parse User Query & Research
- [ ] Step 3: Resolve Tissues & Modalities
- [ ] Step 4: Visualize & Save Plots
- [ ] Step 5: Analyze Predictions (view plots, no code). MANDATORY: Read [interpretation-guide.md](docs/interpretation-guide.md) before interpreting results.
- [ ] Step 6: Write Report, save it as `report.md` (MANDATORY)
- [ ] Step 7: Self-Critique (view `report.md` to verify links & claims)
- [ ] Step 8: Make artifact out of `report.md`
```

--------------------------------------------------------------------------------

## Multi-Variant Workflow

If multiple variants are specified, spawn sub-agents to run each variant
analysis and then synthesize each `report.md` into a single report.

### Script Reference

| Script                      | Purpose                                        |
| --------------------------- | ---------------------------------------------- |
| `lookup_gene_info`          | Comprehensive gene and transcript lookup using |
:                             : GTF data                                       :
| `resolve_ontology_terms`    | Biological terms → UBERON/CL/EFO IDs           |
| `visualize_variant_effects` | REF/ALT visualization (expression, regulatory, |
:                             : splicing)                                      :
| `analyze_ism`               | In-Silico Mutagenesis SeqLogo generation       |
| `interpret_splicing`        | Quantitative splicing analysis (delta scores,  |
:                             : junctions)                                     :
| `visualize_genome_tracks`   | Genomic track visualization for a region       |
