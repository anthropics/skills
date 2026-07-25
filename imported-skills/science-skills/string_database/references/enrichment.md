# Functional & PPI Enrichment

Use these commands for determining Gene Ontology, KEGG pathway enrichment, and
general Protein-Protein Interaction (PPI) statistical enrichment.

## Command: `enrichment`

Identifies enriched functional terms (GO, KEGG, Pfam, InterPro, SMART) for a set
of proteins.

```bash
uv run scripts/string_cli.py enrichment \
  --identifiers trpA trpB trpC trpE \
  --species 511145 \
  --output /tmp/enrichment.tsv
```

**Output fields:** `category`, `term`, `p_value`, `fdr` (False Discovery Rate),
`description`.

## Command: `ppi-enrichment`

Determines if a network has significantly more interactions than expected by
chance, comparing it to the background proteome-wide distribution.

```bash
uv run scripts/string_cli.py ppi-enrichment \
  --identifiers Trp53 Mdm2 Cdkn1a Cdk2 Cdk4 Ccnd1 Rb1 E2f1 \
  --species 10090 \
  --output /tmp/ppi_enrichment.tsv
```

**Output fields:** `number_of_nodes`, `number_of_edges`,
`expected_number_of_edges`, `p_value`.

## Command: `functional-terms`

Searches for all proteins associated with a specific functional term or disease
(e.g., "Melanoma" or "GO:0008543"). *Note: This API takes `--term_text` instead
of `--identifiers`.*

```bash
uv run scripts/string_cli.py functional-terms \
  --term_text "Melanoma" \
  --species 9606 \
  --output /tmp/melanoma_proteins.tsv
```

## Command: `functional-annotation`

Retrieves all functional annotations (not just enriched ones) for the given
proteins.

```bash
uv run scripts/string_cli.py functional-annotation \
  --identifiers CDC28 CLB1 CLB2 CLB3 CKS1 \
  --species 4932 \
  --output /tmp/annotations.tsv
```
