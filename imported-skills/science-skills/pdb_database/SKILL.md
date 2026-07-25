---
name: pdb-database
description: >
  Use when you want to search for or download experimentally-determined 3D
  structures for biomolecules (proteins, nucleic acids, bound ligands).
  Supports searching by sequence similarity, structure similarity, chemical
  and other attributes. Also use to get metadata about biomolecular structure
  experiments.
---

# RCSB Protein Data Bank skill

## Prerequisites

1.  **`uv`**: Read the `uv` skill and follow its Setup instructions to ensure
    `uv` is installed and on PATH.
2.  **User Notification**: If .licenses/pdb_database_LICENSE.txt does not
    already exist in the workspace root directory then (1) prominently notify
    the user to check the terms at https://www.rcsb.org/pages/usage-policy, then
    (2) create the file recording the notification text and timestamp.

## Core Rules

-   **Always prefer to use the provided scripts**. Only as a last resort use
    `curl`, `urllib`, raw HTTP requests, or any other method to access PDB APIs.
    The scripts automatically enforce required rate limits.
-   **Always redirect output to a file**. Parse output with e.g. `jq`, `grep`,
    or a short Python snippet. Do NOT print large API responses to stdout to
    avoid truncation.
-   **Notification**: If this skill is used, ensure this is mentioned in the
    output.
-   **Explain your queries** On completing a task that used PDB JSON/GraphQL
    queries, explain in clear language what your query did so the user can
    correct any bad assumptions.

## Attribute-based search workflow

1.  **Fetch the relevant schema** to discover searchable attribute names. For
    structure attributes: `uv run scripts/fetch_schema.py --api search_structure
    --output schema_structure.txt` For chemical attributes: `uv run
    scripts/fetch_schema.py --api search_chemical --output schema_chemical.txt`

2.  **Grep the schema** to find relevant attributes. Grep one keyword at a time
    and examine many lines — there are lots of similar attributes and you must
    choose the **best match** for the user's intent.

3.  **Compose and run a JSON search query** using the discovered attributes: `uv
    run scripts/search_pdb.py --query '<JSON>' --return_type <RETURN_TYPE>
    --output results.json` Pass the `--count_only` flag to get just the number
    of matching entries.

### For step 2: some basic PDB concepts (helpful for attribute choice)

-   **Entity**: A unique molecule found in a structure.
-   **Instance / Chain**: A particular copy of an entity. E.g. if a structure
    contains two protein chains with the same sequence, they are the same entity
    but different instances / chains.
-   **Assembly**: A biologically relevant collection of instances / chains. This
    may be the same as the deposited structure, a subset, or multiple copies.
-   **Label vs Auth**: Polymer instances get letter labels ("A", "B", "AA") and
    their monomers are numbered. There are author-assigned ("auth") and
    PDB-internal ("label") schemes. The label scheme is more consistent and is
    always used in scripts and APIs. However, users and papers may refer to the
    author scheme (clarify which scheme is being used if necessary).
-   **Chemical component**: A small molecule / monomer, with an ID matching
    `[A-Z]{1,3}`
-   **Primary citation**: The main publication about a structure. Prefer
    `primary_citation` attributes over `citation` attributes.
-   **Resolution**: Frequently used measure of structure quality (lower is
    better). Usually prefer `rcsb_entry_info.resolution_combined`, which
    accounts for different experimental methods.

### For step 3: Example queries

```bash
# Non-human proteins published in Nature, newest first
uv run scripts/search_pdb.py --query '{ "type": "group", "logical_operator": "and", "nodes": [ { "type": "terminal", "service": "text", "parameters": { "operator": "exact_match", "negation": true, "value": "Homo sapiens", "attribute": "rcsb_entity_source_organism.taxonomy_lineage.name" } }, { "type": "terminal", "service": "text", "parameters": { "operator": "exact_match", "value": "Nature", "attribute": "rcsb_primary_citation.rcsb_journal_abbrev" } } ] }' --return_type entry --sort_by rcsb_accession_info.initial_release_date --sort_direction desc --page_start 0 --rows 100 --output results.json
```

```bash
# Structures containing the chemical component CA (Ca2+ ion)
uv run scripts/search_pdb.py --query '{ "type": "terminal", "service": "text_chem", "parameters": { "operator": "exact_match", "value": "CA", "attribute": "rcsb_chem_comp_container_identifiers.comp_id" } }' --return_type entry --output results.json
```

```bash
# Number of entries with disulfide bonds
uv run scripts/search_pdb.py --query '{ "type": "terminal", "service": "text", "parameters": { "operator": "exact_match", "value": "disulfide bridge", "attribute": "rcsb_polymer_struct_conn.connect_type" } }' --return_type entry --count-only --output count.json
```

Common operators: `exact_match`, `equals`, `exists`, `contains_phrase`,
`contains_words`, `in`, `greater`, `less`

## Similarity-based search workflow

Similarity searches do not require a schema fetch. Basic examples:

```bash
# Sequence similarity
uv run scripts/search_pdb.py --query '{ "query": { "type": "terminal", "service": "sequence", "parameters": { "evalue_cutoff": 1, "identity_cutoff": 0.9, "sequence_type": "protein", "value": "MTEYKLVVVGAGGVGKSALTIQLIQNHFVDEYDPTIEDSYRKQ" } }, "request_options": { "scoring_strategy": "sequence" } }' --return_type polymer_entity --output results.json
```

```bash
# Structure similarity
uv run scripts/search_pdb.py --query '{ "type": "terminal", "service": "structure", "parameters": { "value": {"entry_id": "6LU7", "asym_id": "A"}, "number_of_candidates": 2000 } }' --return_type polymer_entity --output results.json
```

```bash
# Sequence motif match
uv run scripts/search_pdb.py --query '{ "type": "terminal", "service": "seqmotif", "parameters": { "value": "C-x(2,4)-C-x(3)-[LIVMFYWC]-x(8)-H-x(3,5)-H.", "pattern_type": "prosite", "sequence_type": "protein" } }' --return_type polymer_entity --output results.json
```

```bash
# Chemical descriptor match
uv run scripts/search_pdb.py --query '{ "type": "terminal", "service": "chemical", "parameters": { "value": "InChI=1S/C8H9NO2/c1-6(10)9-7-2-4-8(11)5-3-7/h2-5,11H,1H3,(H,9,10)", "type": "descriptor", "descriptor_type": "InChI", "match_type": "graph-strict" } }' --return_type mol_definition --output results.json
```

See https://search.rcsb.org/#search-services for more details.

## Full text search workflow

Searches **all** text associated with an entry. Example:

```bash
uv run scripts/search_pdb.py --query '{ "type": "terminal", "service": "full_text", "parameters": { "value": "isopeptide + ( collagen | fibrinogen )" } }' --return_type entry --output results.json
```

> **Important**: use `full_text` search as a **last resort** when there's no
> more precise attribute search available. Consider using the `struct.title` or
> `rcsb_pubmed_abstract_text` attributes instead.

## File download workflow

To download full PDB entries, use the `download_coordinate_files.py` script. Use
this when you need access to atomic coordinates, when asked for a pdb / mmcif
file, or when non-specifically asked to fetch a PDB code. Example:

```bash
uv run scripts/download_coordinate_files.py --ids "4HHB,6BEA" --format "mmcif" --output_dir <OUTPUT_DIR>
```

## Metadata query workflow

This flow is significantly more efficient than downloading full coordinate files
when you only need a few pieces of metadata about each entry / entity.

1.  **Fetch the schema** for the relevant object type. E.g. `uv run
    scripts/fetch_schema.py --api data_entry --output schema_entry.txt`

2.  **Grep the schema** for relevant fields (one keyword at a time, many lines).

3.  **Compose and run a GraphQL metadata query**: `uv run
    scripts/fetch_pdb_metadata.py --query '<GraphQL>' --output results.json`

### For step 3: Example queries

```bash
# Fetch structure titles and experimental methods
uv run scripts/fetch_pdb_metadata.py --query '{ entries(entry_ids: ["1STP", "2JEF", "1CDG"]) { rcsb_id struct { title } exptl { method } } }' --output results.json
```

```bash
# Fetch polymer entity taxonomy and cluster membership
uv run scripts/fetch_pdb_metadata.py --query '{ polymer_entities(entity_ids:["2CPK_1","3WHM_1","2D5Z_1"]) { rcsb_id rcsb_entity_source_organism { ncbi_taxonomy_id ncbi_scientific_name } rcsb_cluster_membership { cluster_id identity } } }' --output results.json
```

```bash
# Fetch polymer entity external sequence database accessions
uv run scripts/fetch_pdb_metadata.py --query '{ entries(entry_ids:["7NHM", "5L2G"]){ polymer_entities { rcsb_id rcsb_polymer_entity_container_identifiers { reference_sequence_identifiers { database_accession database_name } } } } }' --output results.json
```
