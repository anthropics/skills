# Mapping Identifiers

Before querying for networks or enrichments, it is highly recommended to map
common protein names (e.g., "TP53", "CDK2") to STRING's internal identifiers.
Using mapped identifiers guarantees much faster server responses.

## Command: `map`

```bash
uv run scripts/string_cli.py map \
  --identifiers sna twi dl \
  --species 7227 \
  --output /tmp/mapped_ids.tsv
```

**Parameters:**

*   `--identifiers`: Space-separated list of protein names or UniProt IDs.
*   `--species`: NCBI Taxon ID (e.g., `9606` for Human).
*   `--output`: File to save the TSV results.

**Output Fields:**

The resulting TSV contains columns like `queryItem`, `stringId`, `ncbiTaxonId`,
`taxonName`, `preferredName`, and `annotation`.
