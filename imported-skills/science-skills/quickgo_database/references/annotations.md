# Gene Ontology Annotations Reference

## QuickGO `annotation` Subcommand

Use the `annotation` subcommand to search for GO annotations linked to gene
products. This is the primary functional mapper linking a gene directly to
Biological Processes, Molecular Functions, and Cellular Components.

### Searching Annotations

```bash
# Find experimentally-validated (EXP=ECO:0000269) annotations for a specific UniProtKB ID
uv run scripts/quickgo_tool.py annotation search --geneProductId "UniProtKB:P04070" --taxonId 9606 --evidenceCode "ECO:0000269" --limit 50 --output annotations.json

# Find all annotations for a specific GO ID (e.g. apoptosis)
uv run scripts/quickgo_tool.py annotation search --goId "GO:0006915" --goUsage desc --taxonId 9606 --limit 50 --output apoptosis_annotations.json

# Find Biological Process annotations for a specific UniProtKB ID
uv run scripts/quickgo_tool.py annotation search --geneProductId "UniProtKB:P04637" --aspect "biological_process" --limit 50 --output p53_bp_annotations.json
```

**Parameters:**

-   `--geneProductId`: The database identifier for the gene product (e.g.,
    `UniProtKB:P04637`).
-   `--goId`: The Gene Ontology ID (e.g., `GO:0006915`).
-   `--aspect`: Filter by GO aspect (`biological_process`, `molecular_function`,
    `cellular_component`).
-   `--taxonId`: NCBI Taxonomy ID (e.g., `9606` for Human).
-   `--evidenceCode`: The ECO ID corresponding to the evidence type (e.g.,
    `ECO:0000269` for EXP, experimental evidence). Note that many electronic
    annotations are assigned `ECO:0000501` (IEA).
-   `--goUsage`: How to use the `goId` parameter. Can be `exact` (only
    annotations exactly matching the ID), `desc` (annotations matching the ID or
    any of its descendants), or `slim` (treat the IDs as a GO slim).
-   `--qualifier`: Qualifier such as `enables`, `part_of`, `involved_in`,
    `acts_upstream_of`, etc.
-   `--limit`: Maximum number of results to return per page (max: 100, default:
    25).
-   `--page`: Page number for pagination (default: 1).
-   `--output`: The JSON file to save the results.
