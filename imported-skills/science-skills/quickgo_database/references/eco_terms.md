# Evidence & Conclusion Ontology (ECO) Terms Reference

## QuickGO `eco` Subcommand

Use the `eco` subcommand to search and retrieve details about Evidence &
Conclusion Ontology terms. These terms are used as evidence codes in GO
annotations (e.g. ECO:0000269 for "experimental evidence used in manual
assertion").

### 1. Searching for ECO Terms

Search the Evidence & Conclusion Ontology for a specific query string.

```bash
uv run scripts/quickgo_tool.py eco search --query "experimental" --limit 5 --output eco_search_results.json
```

**Parameters:**

-   `--query`: The text you are looking for.
-   `--limit`: Maximum number of results to return per page (max: 100, default:
    25).
-   `--page`: Page number for pagination (default: 1).
-   `--output`: The JSON file to save the results.

### 2. Getting ECO Term Details

Fetch detailed information about a specific ECO term or a set of ECO terms by
their IDs.

```bash
# Get core attributes of an ECO term
uv run scripts/quickgo_tool.py eco terms --ids "ECO:0000269" --output eco_term_details.json

# Get ancestors of an ECO term
uv run scripts/quickgo_tool.py eco terms --ids "ECO:0000269" --relation ancestors --output eco_term_ancestors.json
```

**Parameters:**

-   `--ids`: Comma-separated list of ECO IDs (e.g., "ECO:0000269").
-   `--relation`: Optional. Can be `ancestors`, `descendants`, `children`,
    `complete`, or `paths`.
-   `--output`: The JSON file to save the results.
