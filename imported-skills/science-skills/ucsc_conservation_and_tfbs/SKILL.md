---
name: ucsc-conservation-and-tfbs
description: >
  Fetch Evolutionary Conservation scores (phyloP, phastCons) and Transcription
  Factor Binding Sites (TFBS) from the UCSC Genome Browser. Use when analyzing
  whether genomic variants or regions are evolutionarily conserved, functionally
  important, or bounded by TF regulators across major projects (ENCODE, JASPAR,
  ReMap).
---

# Conservation Scores & TFBS Lookup (UCSC)

This skill provides access to evolutionary constraint scores and conserved
elements from the UCSC Genome Browser. It retrieves scores from the PHAST
package — specifically `phastCons` (identifying functional blocks) and `phyloP`
(measuring individual site constraint) — calculated from multiple alignments.

Use this skill to determine if a non-coding variant hits a site that hasn't
changed since a common ancestor (which is a strong signal for pathogenicity) or
to find conservation peaks across a regulatory element.

## Prerequisites

1.  **`uv`**: Read the `uv` skill and follow its Setup instructions to ensure
    `uv` is installed and on PATH.
2.  **User Notification**: If .licenses/ucsc_conservation_and_tfbs_LICENSE.txt
    does not already exist in the workspace root directory then (1) prominently
    notify the user to check the terms at
    https://genome.ucsc.edu/conditions.html and
    https://genome.ucsc.edu/goldenPath/help/api.html, then (2) create the file
    recording the notification text and timestamp.

## Core Rules

-   **Use the Wrapper**: ALWAYS execute the provided helper scripts to query the
    database rather than accessing the database directly. The scripts
    automatically enforce the required rate limit gracefully.
-   **Large Output Handling**: Always pass --output to redirect output to a
    file. Parse it separately (using jq or your own code).
-   **Notification**: If this skill is used, ensure this is mentioned in the
    output.

## Utility Scripts

This skill includes scripts to query different types of genomic data from UCSC:

1.  **`scripts/get_conservation.py`**: For Evolutionary Conservation scores
    (phyloP, phastCons).
2.  **`scripts/get_tfbs.py`**: For Transcription Factor Binding Sites (TFBS).
3.  **`scripts/list_tracks.py`**: For listing available tracks based on search
    or group constraints.

Always use the `hg38` genome assembly by default, unless the user has specified
otherwise.

### Fetching Conservation for Specific Variants

To get the evolutionary constraint at a single base, or a list of specific
bases. This is optimal for single nucleotide variants (SNVs). `phyloP` is the
best metric for individual bases.

```bash
uv run scripts/get_conservation.py --coordinates "chr1:215867804" "chr1:215867823" --output /tmp/cons_output.json
```

### Fetching Regions and Conserved Elements

To identify "conservation peaks" across a non-coding regulatory element (like an
enhancer) to see if an ISM-predicted importance peak aligns with evolutionary
history. `phastCons` is best for functional windows due to HMM smoothing. The
`--conserved-elements` flag will also retrieve predefined blocks under extreme
constraint.

```bash
uv run scripts/get_conservation.py --coordinates "chr8:11748914-11749085" --conserved-elements --output /tmp/region_cons.json
```

### Lineage-Specific Constraints

You can control the evolutionary depth using the `--collection` flag. The
default (`vertebrate`) uses the **100-vertebrate Multiz alignment** for both
hg38 and hg19, matching the UCSC Genome Browser's default comparative genomics
tracks.

#### hg38 Collections

-   **`vertebrate`** (default): UCSC 100-vertebrate Multiz alignment. phyloP:
    `phyloP100way`, phastCons: `phastCons100way`.
-   **`mammal`**: Hiller Lab 470-way mammalian alignment. phyloP:
    `phyloP470wayBW`, phastCons: `phastCons470way`.
-   **`primate`**: UCSC 30-primate Multiz alignment. phyloP: `phyloP30way`,
    phastCons: `phastCons30way`.

#### hg19 Collections

-   **`vertebrate`** (default): UCSC 100-vertebrate Multiz alignment. phyloP:
    `phyloP100way`, phastCons: `phastCons100way`.
-   **`vertebrate46`**: UCSC 46-vertebrate Multiz alignment (legacy). phyloP:
    `phyloP46wayAll`, phastCons: `phastCons46way`.
-   **`mammal`**: 46-way placental mammal subset. phyloP:
    `phyloP46wayPlacental`, phastCons: `phastCons46wayPlacental`.
-   **`primate`**: 46-way primate subset. phyloP: `phyloP46wayPrimates`,
    phastCons: `phastCons46wayPrimates`.

```bash
# hg38 mammal (Hiller 470-way)
uv run scripts/get_conservation.py --coordinates "chr5:1045330-1046172" --collection mammal --output /tmp/mammal_cons.json

# hg19 with legacy 46-vertebrate alignment
uv run scripts/get_conservation.py --coordinates "chr5:1045330-1046172" --genome hg19 --collection vertebrate46 --output /tmp/vert46_cons.json
```

### Analyzing Evolutionary Acceleration

To analyze whether a specific locus is undergoing evolutionary acceleration
(i.e. evolving more rapidly than the neutral drift baseline), use `--analyze`.
This will compute scalar statistics (mean, min, max) for `phyloP` scores and
provide a heuristic boolean `is_accelerated` to simplify your evaluation.

```bash
uv run scripts/get_conservation.py --coordinates "chr5:1045330-1046172" --analyze --output /tmp/accelerated_cons.json
```

### Fetching Transcription Factor Binding Sites (TFBS)

To identify transcription factor binding sites for a given genomic interval.
This is useful for interpreting non-coding variants that might disrupt TF
binding.

Run `scripts/get_tfbs.py` with `--coordinates` and `--tracks`. You can query
multiple tracks at once.

```bash
uv run scripts/get_tfbs.py --coordinates "chr11:1001000-1010000" --tracks encRegTfbsClustered --output /tmp/tfbs_encode.json
```

JASPAR tracks may return very large result sets. Use `--tf-filter` to keep only
items whose `TFName` field contains the given substring (case-insensitive):

```bash
uv run scripts/get_tfbs.py --coordinates "chr6:36670000-36690000" --tracks jaspar2024 --tf-filter TP53 --output /tmp/tp53_sites.json
```

#### Common Verified Tracks (hg38)

-   **ENCODE**: `encRegTfbsClustered` (TF Clusters)
-   **JASPAR**: `jaspar2026`, `jaspar2024` (Predicted TFBS)
-   **ReMap**: `ReMapTFs` (ChIP-seq Atlas)

> [!CAUTION] Tracks like `jaspar` or `ReMap` without years are often "container"
> tracks and will fail with a 400 error. Always use the specific subtrack name
> (e.g., `jaspar2026`).

### Listing Available Tracks

To list available tracks (such as different versions of JASPAR, or purely to
discover what tracks exist for a particular genome assembly):

```bash
uv run scripts/list_tracks.py --search "jaspar" --output /tmp/jaspar_tracks.json
```

You can also filter by functional group:

```bash
uv run scripts/list_tracks.py --group "regulation" --output /tmp/regulation_tracks.json
```

## Anti-Patterns

*   **DON'T** query mammalian (`--collection mammal`) constraint if you are
    explicitly looking for deep evolutionary roots across all vertebrates. Use
    the default `vertebrate` collection.
*   **DON'T** use this skill for determining the ancestral state reconstruction
    of a nucleotide (this skill provides measures of *how much* sites have
    changed, not *what* the ancestral nucleotide was).
*   **DON'T** assume low conservation strictly means neutral/useless sequence;
    it could also reflect a high local mutation rate which conservation scores
    alone cannot distinguish.
*   **DON'T** print output on standard out, or run cat on output to files. The
    output is too large. Use jq or write your own code to parse the output
    files.
*   **DON'T** use hg19 unless the user has explicitly asked for it. The default
    should be to always use hg38.
