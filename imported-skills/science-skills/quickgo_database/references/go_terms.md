# Gene Ontology (GO) Terms Reference

## QuickGO `go` Subcommand

Use the `go` subcommand to search and retrieve details about Gene Ontology
terms.

### 1. Searching for GO Terms

Search the Gene Ontology for a specific query string (e.g., biological
processes, molecular functions, or cellular components).

```bash
uv run scripts/quickgo_tool.py go search --query "apoptosis" --limit 5 --output go_search_results.json
```

**Parameters:**

-   `--query`: The text you are looking for (e.g., "apoptosis", "transcription
    factor").
-   `--limit`: Maximum number of results to return per page (max: 100, default:
    25).
-   `--page`: Page number for pagination (default: 1).
-   `--output`: The JSON file to save the results.

### 2. Getting GO Term Details

Fetch detailed information about a specific GO term or a set of GO terms by
their IDs.

```bash
# Get core attributes of a GO term
uv run scripts/quickgo_tool.py go terms --ids "GO:0006915" --output term_details.json

# Get all children (direct descendants) of a GO term
uv run scripts/quickgo_tool.py go terms --ids "GO:0042995" --relation children --output term_children.json

# Get complete ancestry of a GO term
uv run scripts/quickgo_tool.py go terms --ids "GO:0001917" --relation ancestors --output term_ancestors.json
```

**Parameters:**

-   `--ids`: Comma-separated list of GO IDs (e.g., "GO:0006915").
-   `--relation`: Optional. Can be `ancestors`, `descendants`, `children`,
    `complete`, or `paths`.
-   `--output`: The JSON file to save the results.

### 3. GO Slims

GO Slims are a cut-down version of the Gene Ontology containing a subset of the
terms. They give a broad overview of the ontology content without the detail of
the specific fine-grained terms.

```bash
uv run scripts/quickgo_tool.py go slim --slimsToIds "GO:0005575,GO:0008150,GO:0003674" --output slim_results.json
```

**Parameters:**

-   `--slimsToIds`: Target GO IDs forming the slim set.
-   `--slimsFromIds`: Optional source GO IDs from which slimming information is
    applied.
-   `--output`: The JSON file to save the results.
