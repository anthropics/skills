# Gene Product Reference

## QuickGO `geneproduct` Subcommand

Use the `geneproduct` subcommand to search for gene products across databases
like UniProtKB, RNAcentral, and ComplexPortal. This is useful when you have a
common gene symbol (e.g., "PROC") but you need its formal database identifier
(e.g., "UniProtKB:P04070") to perform a strict annotation search.

### Searching Gene Products

```bash
# Find gene product by symbol
uv run scripts/quickgo_tool.py geneproduct search --query "PROC" --limit 5 --output proc_gene_products.json
```

**Parameters:**

-   `--query`: The text you are looking for (e.g., a gene symbol like "PROC" or
    "TP53").
-   `--limit`: Maximum number of results to return per page (max: 100, default:
    25).
-   `--page`: Page number for pagination (default: 1).
-   `--output`: The JSON file to save the results.
