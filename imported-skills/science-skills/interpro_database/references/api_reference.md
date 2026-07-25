# InterPro API Query Parameters Reference

This document provides a comprehensive list of all query parameters available
for the InterPro API endpoints, based on the official InterPro Swagger
documentation
(https://www.ebi.ac.uk/interpro/api/static_files/interpro7-swagger.yml) These
parameters can be passed into the `query_params` dictionary in
`fetch_interpro_data`.

## Global Parameters

*Available on all endpoints.*

*   `page_size`: (`int`) Number of results per page (typically defaults to 20,
    max is 200). Use `page_size=1` with `get_interpro_count` for rapid bulk
    aggregations without downloading pages.

--------------------------------------------------------------------------------

## 1. `/entry` Parameters

*For exploring protein entries (genes, domains, families, repeats).*

### General Filters

*   `type`: (`str`) Filter by entry type (e.g., `family`, `domain`,
    `active_site`, `binding_site`, `conserved_site`, `ptms`, `repeat`,
    `homologous_superfamily`).
*   `integrated`: (`str`) Comma-separated list of Member Databases (e.g.,
    `pfam`, `smart`) to filter integrated status. *(Fails if
    source_db=interpro)*
*   `go_term`: (`str`) Filter by exact Gene Ontology term (e.g., `GO:0016301`).
*   `annotation`: (`str`) Filter by annotation type (`logo`, `alignment`,
    `hmm`). *(Works only when `source_db` is a member database).*
*   `group_by`: (`str`) Aggregation method. *Note: Valid values depend on the
    context!*
    -   `/entry` (and `/entry/integrated`, `/entry/unintegrated`, `/entry/all`):
        `type`, `source_database`, `tax_id`, `go_terms`.
    -   `/entry/interpro`: `type`, `tax_id`, `source_database`,
        `member_databases`, `go_terms`, `go_categories`.
    -   `/entry/{sourceDB}`: `type`, `tax_id`, `source_database`, `go_terms`,
        `go_categories`.
*   `sort_by`: (`str`) Sort criteria (e.g., `accession`, `name`).
*   `interpro_status`: (`str`) Value `"interpro_status"` counts how many entries
    are integrated and how many are not. *(Fails unless sourceDB is a member
    Database)*.
*   `ida`: (`str`) Included architectures strings.
*   `extra_fields`: (`str`) Include additional data (e.g., `counters`,
    `entry_id`, `short_name`, `description`, `wikipedia`, `literature`,
    `hierarchy`, `cross_references`, `entry_date`, `is_featured`,
    `overlaps_with`). *(Only available for `/entry/{sourceDB}` and
    `/entry/{sourceDB}/{accession}`).*

### InterPro-Specific (`source_db="interpro"`)

*   `go_category`: (`str`) Filter by top-level GO (`biological_process`,
    `molecular_function`, `cellular_component`).
*   `signature_in`: (`str`) Filter to entries matching a given member database.
*   `latest_entries`: (`str`) Pass `"latest_entries"` to filter for entries
    modified in the most recent release.
*   `interactions`: (`str`) Pass `"interactions"` to limit to entries with known
    structural interactions.
*   `pathways`: (`str`) Pass `"pathways"` to filter for entries linked to
    pathway datasets.
*   `has_model`: (`str`) Pass `"has_model"` to filter for entries with
    structural models.

### Source-DB Specific

*   `subfamilies` / `subfamily`: (`str`) Filter specifically against Panther
    subfamilies. *(Fails unless `source_db="panther"`)*.
*   `model`: (`str`) Included models from `interpro` or `pfam`.

### IDA (Domain Architecture) Search

*(Can ONLY be used on the root `/entry` endpoint. Invalidates aggregations).*

*   `ida_search`: (`str`) Comma-separated list of domain accessions (InterPro or
    Pfam) to find architectures containing them.
*   `ida_ignore`: (`str`) Architectures to ignore. *(Requires `ida_search`)*.
*   `ordered`: (`str`) Pass `"ordered"` to mandate domains appear sequentially.
    *(Requires `ida_search`)*.
*   `exact`: (`str`) Pass `"exact"` to mandate exact composition (no surplus
    domains). *(Requires `ida_search` and `ordered`)*.

--------------------------------------------------------------------------------

## 2. `/protein` Parameters

*For finding proteins matching specific entries or properties.*

*   `tax_id`: (`str`) Filter by NCBI Taxonomy ID (e.g., `9606` for Human). Does
    not automatically resolve lineage.
*   `match_presence`: (`str`) `"true"` or `"false"`. Filters proteins
    definitively known to have (or lack) InterPro matches.
*   `is_fragment`: (`str`) `"true"` (fragmented sequences) or `"false"`
    (complete sequences).
*   `protein_evidence`: (`str`) Filter proteins by existence evidence level
    (e.g., `protein`, `transcript`).
*   `ida`: (`str`) Used only to retrieve architectures alongside a protein or
    `/entry/{db}/{accession}` call. *Not used for filtering.*
*   `id`: (`str`) Protein primary accession/ID.
*   `go_term`: (`str`) Filter by specific Gene Ontology term.
*   `conservation`: (`str`) Appends residue conservation flags. *(Only available
    for `/protein/{source_db}/{accession}` endpoints).*
*   `isoforms`: (`str`) Included isoforms in output.
*   `extra_fields`: (`str`) Include additional data (e.g., `counters`,
    `identifier`, `description`, `sequence`, `gene`, `go_terms`,
    `evidence_code`, `residues`, `tax_id`, `proteome`, `extra_features`,
    `structure`, `is_fragment`, `ida_id`, `ida`). *(Only available for
    `/protein/{sourceDB}` and `/protein/{sourceDB}/{accession}`).*
*   `extra_features`: (`str`) Gets a JSON containing additional features (e.g.,
    `mobidb`, `coil`, etc.) of the selected protein. *(Only available for
    `/protein/{source_db}/{accession}` endpoints).*
*   `residues` / `structureinfo`: (`str`) Append sequence residue flags or
    linked structural data.
*   `group_by`: (`str`) Aggregation method (e.g., `taxonomy`).

--------------------------------------------------------------------------------

## 3. `/structure` Parameters

*For PDB structures linked to InterPro entries.*

*   `experiment_type`: (`str`) Filter by the experimental method (e.g., `"X-RAY
    DIFFRACTION"`, `"NMR"`, `"ELECTRON MICROSCOPY"`).
*   `resolution`: (`str`) Filter by resolution limit limit (e.g., `<=2.0`).
*   `group_by`: (`str`) Aggregation method.
*   `extra_fields`: (`str`) Include additional data (e.g., `release_date`,
    `literature`, `chains`, `secondary_structures`, `counters`). *(Only
    available for `/structure/{sourceDB}` and
    `/structure/{sourceDB}/{accession}`).*

--------------------------------------------------------------------------------

## 4. `/taxonomy` Parameters

*For phylogenetic breakdowns and nodes.*

*   `key_species`: (`str`) `"true"` or `"false"`. Limits distribution to major
    model organisms.
*   `with_names`: (`str`) `"true"` or `"false"`. Includes full scientific names
    rather than just node logic. *(Cannot combine with cross-filters below).*
*   `filter_by_entry`: (`str`) Limits taxonomic nodes strictly to those
    containing a given accession.
*   `filter_by_entry_db`: (`str`) Limits nodes to those intersecting with a
    specific member DB.
*   `extra_fields`: (`str`) Include additional data (e.g., `counters`,
    `scientific_name`, `full_name`, `lineage`, `rank`). *(Only available for
    `/taxonomy/{sourceDB}`).*

--------------------------------------------------------------------------------

## 5. `/proteome` Parameters

*For specific, whole-proteome breakdowns.*

*   `is_reference`: (`str`) `"true"` or `"false"`. Filter specifically for
    UniProt Reference Proteomes.
*   `group_by`: (`str`) Aggregation method.
*   `extra_fields`: (`str`) Include additional data (e.g., `counters`, `strain`,
    `assembly`). *(Only available for `/proteome/{sourceDB}`).*

--------------------------------------------------------------------------------

## 6. `/set` Parameters

*For curated entry clans (like Pfam clans).*

*   `extra_fields`: (`str`) Include additional data (e.g., `counters`,
    `description`, `relationships`). *(Only available for `/set/{sourceDB}`).*
