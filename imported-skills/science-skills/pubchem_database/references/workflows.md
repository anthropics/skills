# PubChem Workflows

Follow these checklists for complex, multi-step queries to ensure accurate
results.

## Workflow 1: Comprehensive Chemical Profiling

When asked to provide a complete profile of a chemical (e.g., "Tell me
everything about Aspirin"):

1.  **Resolve Name**: Run `pubchem_api.py resolve` to get the primary CID.
2.  **Get Properties**: Run `pubchem_api.py properties` using the CID to get
    basic chemical traits (Weight, XLogP).
3.  **Check Safety**: Run `pubchem_api.py safety` to fetch GHS hazard
    information.
4.  **Check Pharmacology**: Run `pubchem_api.py pharmacology` to understand its
    biological/medical use.
5.  **Synthesize**: Read all output JSON files and compile a comprehensive
    markdown report.

## Workflow 2: Structure-Based BioAssay Lookup

When asked to find targets or assays for compounds similar to a given structure:

1.  **Search Structure**: Run `pubchem_api.py similarity` (for 2D similarity)
    or `pubchem_api.py substructure` using the target SMILES string.
2.  **Filter Results**: Read the resulting JSON file. The search may return
    hundreds of CIDs. Select the top 5-10 most relevant CIDs.
3.  **Fetch Assays**: For each selected CID, run `pubchem_api.py assays`.
4.  **Analyze**: Review the assay summaries to identify common biological
    targets (e.g., specific genes or proteins) that these compounds interact
    with.
