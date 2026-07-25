# Interactions & Networks

Use these commands to retrieve protein interaction networks, topologies,
mediators, and homology scores.

## Command: `network`

Retrieves interactions between the provided input proteins. If `--add_nodes` is
provided, it extends the neighborhood.

```bash
uv run scripts/string_cli.py network \
  --identifiers Trp53 Mdm2 \
  --species 10090 \
  --add_nodes 10 \
  --network_type physical \
  --output /tmp/p53_neighborhood.tsv
```

*   **Options:**
    *   `--required_score` (0-1000 threshold, e.g. 400 for medium confidence)
    *   `--network_type` (`functional` or `physical`)
    *   `--add_nodes` (number of closely interacting proteins to add to the
        network).
*   **Output columns:** `score` (combined confidence), `escore` (experimental
    evidence), `dscore` (database), `nscore` (neighborhood), `fscore` (fusion),
    `pscore` (phylogenetic), `tscore` (textmining), `ascore` (coexpression).

## Command: `partners`

Gets the top interaction partners against the entire database for the provided
proteins.

```bash
uv run scripts/string_cli.py partners \
  --identifiers BRCA1 \
  --species 9606 \
  --limit 10 \
  --output /tmp/partners.tsv
```

## Command: `image`

Generates a visual map of the network. Output can be a PNG or SVG.

```bash
uv run scripts/string_cli.py image \
  --identifiers Trp53 Mdm2 Atm Atr Chek2 Brca1 Cdkn1a \
  --species 10090 \
  --format highres_image \
  --output /tmp/p53_pathway_network.png
```

## Command: `homology`

Gets Smith-Waterman homology (similarity) scores between the input proteins.

```bash
uv run scripts/string_cli.py homology \
  --identifiers CDK1 CDK2 \
  --species 9606 \
  --output /tmp/homology.tsv
```

## Command: `homology-best`

Gets best homology similarity hits between the input proteins and proteins in
other specified species. **Note: Target species must be exact comma-separated
taxon IDs with no spaces.**

```bash
uv run scripts/string_cli.py homology-best \
  --identifiers CDK1 \
  --species 9606 \
  --species_b 10090,7227 \
  --output /tmp/best_homology.tsv
```
