---
name: pubchem-database
description: >
  Query PubChem, search by name/CID/SMILES, retrieve properties,
  similarity/substructure searches, bioactivity, for cheminformatics. Use when a
  user asks about a specific chemical, drug, or molecule.
---

# PubChem Database

## Prerequisites

1.  **`uv`**: Read the `uv` skill and follow its Setup instructions to ensure
    `uv` is installed and on PATH.
2.  **User Notification**: If .licenses/pubchem_database_LICENSE.txt does not
    already exist in the workspace root directory then (1) prominently notify
    the user to check the terms at
    https://pubchem.ncbi.nlm.nih.gov/docs/citation-guidelines and
    https://pubchem.ncbi.nlm.nih.gov/docs/pug-rest, then (2) create the file
    recording the notification text and timestamp.

## Quick Start

PubChem queries are executed via a robust Python wrapper script to respect
terms-of-service and handle complex JSON parsing. This script allows safe
multi-agent use of APIs.

Example: Resolve a chemical name to its Compound ID (CID)

```bash
uv run scripts/pubchem_api.py resolve --name "aspirin" --output result.json
```

## Core Rules

-   **Use the Wrapper**: ALWAYS execute the provided helper scripts to query the
    database rather than accessing the database directly. The scripts
    automatically enforce the required rate limit gracefully.
-   Read the generated JSON output file, and process it with jq or code.
-   **Verify Facts**: ALWAYS verify information retrieved from memory with a
    database query if the user asks for a specific fact that can be checked in
    PubChem. Do not rely solely on internal knowledge.
-   **Notification**: If this skill is used, ensure this is mentioned in the
    output.

## Core Capabilities

**1. Compound Resolution (Name or InChI to Identifiers)** Convert chemical/trade
names or InChI strings into PubChem CIDs, SMILES, and InChIKeys.

```bash
uv run scripts/pubchem_api.py resolve --name "ibuprofen" --output result.json
# OR
uv run scripts/pubchem_api.py resolve --inchi "InChI=1S/C3/c1-3-2/i1+1" --output result.json
```

**2. Physical & Chemical Property Retrieval** Fetch computed properties (e.g.,
MolecularWeight, XLogP, TPSA).

```bash
uv run scripts/pubchem_api.py properties --cid 2244 --output result.json
```

**3. Synonyms and Trade Names** Find alternative names and brand names.

```bash
uv run scripts/pubchem_api.py synonyms --cid 2244 --output result.json
```

## Advanced Context

**4. Safety and Hazard Information (GHS)** Retrieve Global Harmonized System
hazard statements and handling precautions (uses PUG-View).

```bash
uv run scripts/pubchem_api.py safety --cid 2244 --output result.json
```

**5. Drug and Medication Information** Fetch FDA pharmacology data, mechanism of
action, and therapeutic uses (uses PUG-View).

```bash
uv run scripts/pubchem_api.py pharmacology --cid 2244 --output result.json
```

**6. Custom Heading (PUG-View)** Retrieve any specific heading from the PUG-View
system (e.g., 'Geometry', 'Crystal Structures').

```bash
uv run scripts/pubchem_api.py view --cid 3939 --heading "Crystal Structures" --output result.json
```

**7. Image Generation** Retrieve 2D chemical structure images. The script
returns a Markdown-formatted image link.

```bash
uv run scripts/pubchem_api.py image --cid 2244 --output result.json
```

## Complex Search & Biology

**8. Structure-Based Searching (Similarity & Substructure)** Find molecules
similar to a SMILES string or containing a specific substructure.

```bash
uv run scripts/pubchem_api.py similarity --smiles "CC(=O)OC1=CC=CC=C1C(=O)O" --output result.json
```

and

```bash
uv run scripts/pubchem_api.py substructure --smiles "C1=CC=CC=C1" --output result.json
```

**9. BioAssay & Target Interactions** Identify genes or proteins a chemical
interacts with.

```bash
uv run scripts/pubchem_api.py assays --cid 2244 --output result.json
```

## Advanced Usage & Workflows

**10. Cross-references (Xrefs)** Fetch identifiers cross-referenced with a CID
(e.g., PatentID, PubMedID).

```bash
uv run scripts/pubchem_api.py xrefs --cid 2244 --type "PatentID" --output result.json
```

**11. Property Range Search** Find CIDs within a specific property range.
Supported features include: `molecular_weight`, `heavy_atom_count`, `xlogp`,
`tpsa`, `h_bond_donor_count`, `h_bond_acceptor_count`, `rotatable_bond_count`,
`exact_mass`, `monoisotopic_mass`, and `complexity`.

```bash
uv run scripts/pubchem_api.py range --feature molecular_weight --min 400.0 --max 400.05 --output result.json
```

**12. Custom PUG-REST Query** Execute a raw path against the PUG-REST API.

```bash
uv run scripts/pubchem_api.py query --path "compound/cid/2244/xrefs/PatentID/JSON" --output result.json
```

## Fallback Search Strategies

If direct resolution by name or formula fails (e.g., for complex compounds or
specific ions):

-   **Search for parent/neutral molecule**: If searching for an ion or salt, try
    searching for the neutral parent compound.
-   **Deconstruct complex formulas**: If a complex formula returns no results,
    try searching for major components or ligands.
-   **Use substructure or similarity search**: If you have a SMILES string or
    can generate one for a component, use it to find related compounds.

## Complex Queries and Multi-Step Tasks

*   **Custom/Complex Queries**: For more details, read
    [references/endpoints.md](references/endpoints.md) to construct raw PUG-REST
    URLs.
*   **Multi-Step Tasks**: For complex tasks like drug discovery pipelines,
    follow the checklists in [references/workflows.md](references/workflows.md).
