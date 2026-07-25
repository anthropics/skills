# Advanced PubChem API Reference

This file documents the raw PUG-REST and PUG-View APIs for cases where the
`pubchem_api.py` wrapper does not support your specific query.

## PUG-REST (Computed Properties & Search)

**Base URL:** `https://pubchem.ncbi.nlm.nih.gov/rest/pug`

The URL path always follows this structure:
`/<domain>/<namespace>/<identifiers>/<operation>/<output>[?options]`

### 1. Domain
The core data type: `compound`, `substance`, `assay`, `gene`, `protein`,
`pathway`, `taxonomy`, `cell`.

### 2. Namespace & Identifiers
How you are identifying the target record(s):

- `cid/<cid>`: Compound ID
- `name/<name>`: Exact chemical name
- `smiles/<smiles>`: Exact SMILES match
- `inchikey/<inchikey>`: Exact InChIKey match
- `formula/<formula>`: Exact molecular formula
- Search namespaces (use `fast` prefix for synchronous):
  - `fastsubstructure/smiles/<smiles>`
  - `fastsimilarity_2d/smiles/<smiles>`
  - `fastidentity/smiles/<smiles>`

### 3. Operation
What data you want to extract:

- `record` (default): The full raw record.
- `property/<property_list>`: Specific properties (e.g.,
  `MolecularWeight,XLogP,TPSA`).
- `synonyms`: List of synonyms.
- `cids`: Return only the CIDs (useful after a search).
- `assaysummary`: Summary of bioassays.
- `xrefs/<xref_type>`: Cross-references (e.g., `PatentID`, `PubMedID`).

### 4. Output
Format for the response: `JSON`, `XML`, `CSV`, `TXT`, `PNG`.

### Examples

*   **Properties by CID (JSON)**: `https://pubchem.ncbi.nlm.nih.gov/rest/pug/compound/cid/2244/property/MolecularWeight,MolecularFormula/JSON`
*   **Mass Range Search (JSON)**: `https://pubchem.ncbi.nlm.nih.gov/rest/pug/compound/molecular_weight/range/400.0/400.05/cids/JSON`
*   **Patents by SID (JSON)**: `https://pubchem.ncbi.nlm.nih.gov/rest/pug/substance/sid/137349406/xrefs/PatentID/JSON`

---

## PUG-View (Third-Party Annotations & Text)

Used for retrieving comprehensive textual annotations (like GHS Safety,
Pharmacology, Toxicity) compiled from external sources.

**Base URL:** `https://pubchem.ncbi.nlm.nih.gov/rest/pug_view`

The standard structure for retrieving specific sections:
`https://pubchem.ncbi.nlm.nih.gov/rest/pug_view/data/compound/<cid>/JSON?heading=<Section+Heading>`

*Note: Spaces in headings must be replaced with `+`.*

### Common Headings

*   `Safety+and+Hazards`
*   `Pharmacology+and+Biochemistry`
*   `Toxicity`
*   `Drug+and+Medication+Information`
*   `Experimental+Properties`

