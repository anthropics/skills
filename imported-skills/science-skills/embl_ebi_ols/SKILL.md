---
name: embl-ebi-ols
description: >
  Query and search the EMBL-EBI Ontology Lookup Service (OLS) for biomedical
  ontology terms, definitions, and hierarchies across 250+ ontologies (e.g., GO,
  DOID, HP). Use when the user asks to search for terms, retrieve details,
  navigate hierarchies (parents, children, ancestors), look up properties and
  individuals, get autocomplete suggestions, or access ontology metadata and
  statistics.
---

# EMBL-EBI Ontology Lookup Service (OLS)

## Prerequisites

1.  **`uv`**: Read the `uv` skill and follow its Setup instructions to ensure
    `uv` is installed and on PATH.
2.  **User Notification**: If .licenses/embl_ebi_ols_LICENSE.txt does not
    already exist in the workspace root directory then (1) prominently notify
    the user to check the terms at https://www.ebi.ac.uk/ols4/api-docs, then (2)
    create the file recording the notification text and timestamp.

## Core Rules

-   [!IMPORTANT] **Use the Utility Scripts**: You MUST ALWAYS use the provided
    utility script under `scripts/` for all API interactions, including checking
    status. NEVER use `curl` or custom Python requests to query API directly.

-   **Rate Limiting & Resilience**: You MUST respect EBI's Terms of Use with a
    maximum 5 requests per second. The provided utility scripts automatically
    enforce this.

-   **Notification**: If this skill is used, ensure this is mentioned in the
    output.

## When to Use — Quick Recipes

Use this skill whenever a user query matches one of these patterns:

-   **Definition** of a disease, phenotype, or term → `get_term.py --obo_id <ID>
    --summary`
-   **Subtypes** or **children** of a term → `get_term.py --obo_id <ID>
    --relations children`
-   **Parent** of a term → `get_term.py --obo_id <ID> --relations parents`
-   **Ancestors** / disease **categories** / **classified under** → `get_term.py
    --obo_id <ID> --relations ancestors`
-   **Root terms** of an ontology → `get_term.py --ontology <id> --roots`
-   **Hierarchical** parents (is-a + part-of) → `get_term.py --obo_id <ID>
    --relations hierarchicalParents`
-   **Structures part of** / hierarchical children → `get_term.py --obo_id <ID>
    --relations hierarchicalChildren`
-   **Compare** direct vs hierarchical parents → `get_term.py --obo_id <ID>
    --relations parents,hierarchicalParents`
-   Search for a term (e.g., "apoptosis" in GO) → `search_ols.py --query "..."
    --ontology <id>`
-   Find a **GO term** matching a function → `search_ols.py --query "..."
    --ontology go --exact`
-   Search in **MONDO**, **CHEBI**, **CL**, **UBERON** → `search_ols.py --query
    "..." --ontology <id> --defining`
-   **Paginate** search results / next page → `search_ols.py --query "..."
    --rows N --start <offset>`
-   Autocomplete a partial name → `suggest_ols.py --query "..."`
-   Ontology metadata (e.g., EFO info) → `get_ontology.py --id <id>`
-   OLS index statistics → `get_stats.py`

> **Multi-step queries** (e.g., "What is the parent of myocardial infarction?"):
> When the user names a term but you don't know its OBO ID, complete in
> **exactly 2 steps** — do NOT search across multiple ontologies:
>
> 1.  **Search** in the single most appropriate ontology: `search_ols.py --query
>     "myocardial infarction" --ontology doid --exact --rows 1 --output
>     /tmp/step1.json`
> 2.  **Get relations** using the OBO ID from step 1: `get_term.py --obo_id
>     DOID:5844 --relations parents --output /tmp/step2.json`
>
> **Ontology selection rule**: ALWAYS use `doid` for common human diseases
> (e.g., diabetes, cancer), `hp` for phenotypes, `go` for gene functions,
> `chebi` for chemicals, `uberon` for anatomy, `cl` for cell types. Use `mondo`
> ONLY when cross-species context is explicitly mentioned or needed.

## Utility Scripts

**1. Search Terms Across Ontologies**

Search for ontology terms by keyword and return clean JSON.

```bash
uv run scripts/search_ols.py --query "diabetes" \
  --rows 5 --output /tmp/ols_search_results.json 2>/dev/null
```

> **Important**: `--output` is required for all scripts. Results are always
> written to the specified file. For larger output, you can limit `--rows`
> (e.g., 5-10) or paginate using `--start`.

*Returned Fields:* JSON results include `iri`, `label`, `description`,
`ontology_name`, `ontology_prefix`, `obo_id`, `short_form`, `type`,
`is_defining_ontology`, and `exact_synonyms`.

*Pagination:* Output includes a `pagination` block with `start`, `rows`, and
`has_more` so you can decide whether to fetch more results.

*Options:*

-   `--query`: Search string (required). Searches labels, synonyms,
    descriptions, and identifiers.
-   `--ontology`: Filter by ontology ID (e.g., `go`, `doid`, `efo`, `hp`).
    **Recommended** when you know which ontology to search — avoids noise from
    250+ ontologies.
-   `--type`: Filter by entity type: `class`, `property`, `individual`, or
    `ontology`.
-   `--exact`: Flag for exact label match only. **Use this for entity
    resolution** when mapping a user's string to a specific ontology term ID.
-   `--defining`: Only return terms from their defining (authoritative)
    ontology. E.g., `GO:0005634` only from GO, not cross-referenced copies.
-   `--obsolete`: Flag to include obsolete terms in results.
-   `--local`: Only return terms in their defining ontology.
-   `--childrenOf`: Restrict to children of given term IRI(s), comma-separated.
-   `--allChildrenOf`: Restrict to all children including transitive relations
    (part of, develops from), comma-separated IRIs.
-   `--queryFields`: Comma-separated fields to search in (e.g.,
    `label,synonym,description`).
-   `--fieldList`: Comma-separated fields to return.
-   `--groupField`: Group results by unique IRI.
-   `--isLeaf`: Only return leaf terms (no children).
-   `--rows`: Number of results to return (default 10).
-   `--start`: Pagination offset (default 0).
-   `--output`: File path to save results (**required**).

**2. Autocomplete / Suggest**

Get autocomplete suggestions for partial term names.

```bash
uv run scripts/suggest_ols.py --query "diabet" --rows 5 \
  --output /tmp/ols_suggest.json 2>/dev/null
```

*Options:*

-   `--query`: Partial term to autocomplete (required).
-   `--ontology`: Filter by ontology ID(s), comma-separated.
-   `--rows`: Number of suggestions (default 10).
-   `--start`: Pagination offset (default 0).
-   `--output`: File path to save results (default: stdout).

**3. Get Term Details**

Retrieve full details for a specific ontology term by its OBO ID or IRI.

```bash
uv run scripts/get_term.py --obo_id "GO:0005634" \
  --output /tmp/ols_term.json 2>/dev/null
```

*Returned Fields:* JSON includes `iri`, `label`, `description`, `obo_id`,
`synonyms`, `ontology_name`, `is_obsolete`, `is_defining_ontology`,
`has_children`, `is_root`, `annotation`, `in_subset`, and any requested
relations.

*Summary Mode:* Use `--summary` to get a clean, human-readable block on stdout
(Label, OBO ID, Ontology, Definition, Synonyms). The full JSON is always saved
to the `--output` file.

```bash
uv run scripts/get_term.py --obo_id "GO:0005634" --summary \
  --output /tmp/nucleus_full.json
```

*Options:*

-   `--obo_id`: OBO-style identifier (e.g., `GO:0005634`, `DOID:9351`). Mutually
    exclusive with `--iri`. Auto-converts to IRI with double encoding.
-   `--iri`: Full IRI of the term. Mutually exclusive with `--obo_id`.
-   `--ontology`: Ontology ID (auto-derived from `--obo_id` if not provided).
-   `--relations`: Comma-separated list of relations to fetch.

    -   **Direct (is-a only):** `parents`, `children`, `ancestors`,
        `descendants`
    -   **Hierarchical (is-a + transitive like "part of", "develops from"):**
        `hierarchicalParents`, `hierarchicalChildren`, `hierarchicalAncestors`,
        `hierarchicalDescendants`
    -   **Graph:** `graph` — full graph JSON for a term

    > **Note**: Use hierarchical variants for anatomical/developmental
    > ontologies (UBERON, CL) where transitive relations like "part of" and
    > "develops from" are critical for navigating the hierarchy.

-   `--roots`: List root terms of the ontology (requires `--ontology`).

-   `--preferred_roots`: List preferred root terms (requires `--ontology`).

-   `--summary`: Human-readable summary on stdout, full JSON to `--output`.

-   `--output`: File path to save results (default: stdout).

**4. Get Property Details**

Retrieve details for an ontology property (relation type) with hierarchy.

```bash
uv run scripts/get_property.py --obo_id "BFO:0000051" --ontology go \
  --output /tmp/ols_property.json 2>/dev/null
```

*Options:*

-   `--obo_id`: OBO-style ID of the property. Mutually exclusive with `--iri`.
-   `--iri`: Full IRI of the property. Mutually exclusive with `--obo_id`.
-   `--ontology`: Ontology ID (required with `--iri`).
-   `--relations`: Comma-separated: `parents`, `children`, `ancestors`,
    `descendants`.
-   `--roots`: List root properties of the ontology (requires `--ontology`).
-   `--output`: File path to save results (default: stdout).

**5. Get Individual Details**

Retrieve details for an ontology individual (instance).

```bash
uv run scripts/get_individual.py --obo_id "IAO:0000103" --ontology iao --types \
  --output /tmp/ols_individual.json 2>/dev/null
```

*Options:*

-   `--obo_id`: OBO-style ID. Mutually exclusive with `--iri`.
-   `--iri`: Full IRI. Mutually exclusive with `--obo_id`.
-   `--ontology`: Ontology ID (required with `--iri`).
-   `--types`: Fetch the direct types (classes) of this individual.
-   `--alltypes`: Fetch all types including ancestor classes.
-   `--output`: File path to save results (default: stdout).

**6. Get Ontology Information**

List available ontologies or retrieve details for a specific one.

```bash
uv run scripts/get_ontology.py --id go \
  --output /tmp/ols_ontology.json 2>/dev/null
```

*Options:*

-   `--id`: Specific ontology ID (e.g., `go`, `efo`, `doid`). If omitted, lists
    all ontologies.
-   `--page`: Page number for pagination (default 0).
-   `--size`: Number of ontologies per page (default 20).
-   `--output`: File path to save results (default: stdout).

**7. Get OLS Statistics**

Retrieve index statistics (total ontologies, classes, properties, individuals).

```bash
uv run scripts/get_stats.py --output /tmp/ols_stats.json 2>/dev/null
```

*Options:*

-   `--output`: File path to save results (default: stdout).

## Reference

-   **API Reference**: See
    [references/api_reference.md](references/api_reference.md) for common ontology
    IDs, OBO ID format, and key API endpoints.

## Workflow

1.  Use `suggest_ols.py` for autocomplete when you have a partial term name.
2.  Search for terms using `search_ols.py`. Use `--defining` to prioritize
    authoritative definitions. Use `--exact` for entity resolution.
3.  If full details are needed, use `get_term.py` with the OBO ID or IRI. Use
    `--summary` for a concise view.
4.  To explore a term's hierarchy, use `get_term.py --relations
    parents,children` for is-a only, or `--relations
    hierarchicalParents,hierarchicalChildren` for "part of" etc.
5.  To explore from the top down, use `get_term.py --ontology go --roots`.
6.  For properties or individuals, use `get_property.py` or `get_individual.py`.
7.  To discover available ontologies, use `get_ontology.py`.
8.  To check OLS index status, use `get_stats.py`.
