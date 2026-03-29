# Follow the Data

Search the full 1,900+ tool catalog for every entity. Don't pre-decide which tools matter -- let the catalog tell you.

## How to Search

For every entity you encounter, run multiple catalog queries:

```
grep_tools(pattern="ENTITY_NAME")           -- exact name matches
grep_tools(pattern="ENTITY_TYPE")           -- type matches (gene, drug, pathway...)
grep_tools(pattern="SYNONYM")              -- aliases, alternative names
find_tools(query="what I want to know")     -- semantic search
list_tools(mode="by_category")             -- browse all categories
```

**Multiple queries per entity.** A drug entity should trigger searches for: the drug name, "adverse event", "drug safety", "clinical trial", "drug label", "pharmacology", "drug interaction", "drug approval", "pharmacogenomics", "toxicity", and any related concept the results suggest. Each query surfaces different tools.

**Batch get_tool_info.** Once you have a list of candidate tools, call `get_tool_info(tool_names=[list])` in batch to get all parameter schemas at once.

## Entity Search Strategies

For each entity type, these are the search terms and categories to query. The named tools are examples of what you'll find -- the catalog contains many more.

### Gene

Search terms: gene symbol, "gene", "protein", "target", "expression", "variant", "pathway", "interaction", "ontology", "homolog"

Categories to browse: `opentarget`, `string_network`, `string_ext`, `ppi`, `kegg`, `kegg_ext`, `kegg_conv_link`, `uniprot`, `reactome`, `clinvar`, `ensembl`, `pubmed`

Example tools (not exhaustive): OpenTargets_get_dise_phen_by_targ_ense, STRING_get_network, STRING_get_interaction_partners, STRING_get_functional_annotations, KEGG_get_gene_pathways, KEGG_link_entries, UniProt_get_function_by_accession, Reactome_map_uniprot_to_pathways, ClinVar_search_variants, PubMed_search_articles, ensembl_lookup_gene

### Drug

Search terms: drug name, "drug", "adverse event", "FAERS", "safety", "clinical trial", "drug label", "FDA", "approval", "pharmacology", "interaction", "indication", "mechanism", "ChEMBL", "PubChem"

Categories to browse: `opentarget`, `ChEMBL`, `fda_drug_adverse_event`, `fda_drug_adverse_event_detail`, `fda_drug_label`, `clinical_trials`, `kegg_disease_drug`, `pubchem`, `pubmed`

Example tools (not exhaustive): OpenTargets_get_drug_indications_by_chemblId, ChEMBL_get_molecule, ChEMBL_get_molecule_targets, FAERS_count_reactions_by_drug_event, FAERS_search_adverse_event_reports, FDA_get_adverse_reactions_by_drug_name, ClinicalTrials_search_by_intervention, KEGG_get_drug, PubMed_search_articles

### Disease

Search terms: disease name, "disease", "syndrome", "disorder", "phenotype", "clinical trial", "treatment", "gene association", "epidemiology", "guideline"

Categories to browse: `opentarget`, `kegg_disease_drug`, `clinical_trials`, `clinvar`, `pubmed`, `guidelines`

Example tools (not exhaustive): OpenTargets_get_asso_targ_by_dise_efoI, OpenTargets_get_asso_drug_by_dise_efoI, KEGG_get_disease, KEGG_get_disease_genes, ClinicalTrials_search_studies, ClinVar_search_variants, PubMed_Guidelines_Search

### Pathway

Search terms: pathway name, "pathway", "signaling", "metabolic", "reaction", "enrichment", "network"

Categories to browse: `kegg`, `kegg_ext`, `kegg_network_variant`, `reactome`, `string_ext`, `ppi`

Example tools: kegg_get_pathway_info, KEGG_get_pathway_genes, Reactome_get_pathway, STRING_functional_enrichment

### Variant

Search terms: rsID, gene symbol + "variant", "mutation", "pathogenic", "clinical significance", "SNP"

Categories to browse: `clinvar`, `kegg_network_variant`, `opentarget`, `pubmed`

Example tools: ClinVar_search_variants, ClinVar_get_clinical_significance, KEGG_search_variant, KEGG_get_variant

### Company

Search terms: company name, "SEC", "EDGAR", "filing", "sponsor", "manufacturer", "approval"

Categories to browse: `sec_edgar`, `clinical_trials`, `fda_drug_label`, `fda_drug_adverse_event`, `pubmed`

Example tools: SEC_EDGAR_search_filings, SEC_EDGAR_get_company_submissions, ClinicalTrials_search_by_sponsor, OpenFDA_search_drug_approvals

### Publication

Search terms: PMID, author name, topic keywords, "citation", "preprint"

Categories to browse: `pubmed`, `crossref`, `openalex`, `europepmc`, `semantic_scholar`, `biorxiv`

Example tools: PubMed_search_articles, PubMed_get_cited_by, openalex_literature_search, Crossref_search_works, EuropePMC_search_articles

## The Expanding Frontier

Every tool call returns data containing new entities. Each new entity triggers its own catalog search:

```
Gene query -> returns drug names
  -> search catalog for those drugs
    -> drug results mention clinical trials
      -> search catalog for trial tools
        -> trial data names a company
          -> search catalog for SEC/EDGAR tools
```

This is how you find FDA and EDGAR tools starting from a gene. You don't predict the path -- you follow the data.

## Fallback Strategy

When a tool fails or returns empty:

1. Search the catalog for alternative tools in the same category
2. Search with synonyms or broader terms
3. Try a different entity type (e.g., drug name instead of ChEMBL ID)
4. Document the gap in research_state.json with what you tried

## ID Resolution

Same entity, different IDs across databases. Resolve before cross-referencing:

| From | To | Tool |
|------|----|------|
| Gene symbol | Ensembl ID | ensembl_lookup_gene |
| Ensembl ID | KEGG/UniProt | KEGG_convert_ids |
| Any prefix:ID | Provider URLs | Bioregistry_resolve_reference |
| Drug name | ChEMBL ID | OpenTargets_get_drug_chembId_by_generic_name |
| Drug name | PubChem CID | PubChem_get_CID_by_compound_name |
| Disease name | EFO ID | OpenTargets_get_dise_id_desc_by_name |
| UniProt acc | Ensembl/NCBI | UniProt_id_mapping |

Store all resolved IDs in the entity's `ids{}` map in research_state.json.
