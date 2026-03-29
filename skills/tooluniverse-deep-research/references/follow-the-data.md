# Follow the Data: Direct-Call Playbook

Call tools directly. Don't discover -- execute.

For every tool call: `get_tool_info` first (parameter schemas vary), then `execute_tool`.

## Gene Playbook (~25 tools)

When you find a gene, call ALL of these. Requires: gene symbol and/or Ensembl ID.

**Resolve IDs first**:

- `ensembl_lookup_gene` -- gene symbol -> Ensembl ID
- `KEGG_convert_ids` -- Ensembl -> KEGG/UniProt
- `UniProt_id_mapping` -- cross-database ID conversion

**T1 (Regulatory/Curated)**:

- `OpenTargets_get_asso_targ_by_dise_efoI` -- diseases for this gene (needs efoId from disease)
- `OpenTargets_get_dise_phen_by_targ_ense` -- diseases/phenotypes for gene (ensemblId)
- `OpenTargets_get_evidence_by_datasource` -- evidence filtered by source type
- `OpenTargets_get_targ_gene_onto_by_ense` -- GO annotations
- `OpenTargets_get_targ_safe_prof_by_ense` -- safety liabilities
- `OpenTargets_get_targ_trac_by_ense` -- tractability (is it druggable?)
- `OpenTargets_get_targ_inte_by_ense` -- interaction partners
- `OpenTargets_get_asso_drug_by_targ_ense` -- drugs targeting this gene
- `OpenTargets_get_biol_mous_mode_by_ense` -- mouse models
- `OpenTargets_get_targ_homo_by_ense` -- homologs
- `ClinVar_search_variants` -- pathogenic variants (gene=SYMBOL)
- `ClinVar_get_clinical_significance` -- per-variant pathogenicity

**T2 (Peer-Reviewed)**:

- `PubMed_search_articles` -- literature (query=GENE_SYMBOL)
- `PubMed_get_related` -- expand from key PMIDs

**T4 (Computational)**:

- `STRING_get_network` -- PPI network (identifiers=SYMBOL, species=9606)
- `STRING_get_interaction_partners` -- ranked partner list
- `STRING_get_functional_annotations` -- GO/KEGG/Reactome annotations
- `KEGG_get_gene_pathways` -- all pathways (kegg_id=hsa:NCBI_ID)
- `KEGG_link_entries` -- link to diseases, drugs, compounds
- `Reactome_map_uniprot_to_pathways` -- pathways via UniProt accession
- `Reactome_map_uniprot_to_reactions` -- reactions involving this protein
- `UniProt_get_function_by_accession` -- protein function
- `UniProt_get_disease_variants_by_accession` -- disease-associated variants
- `UniProt_get_subcellular_location_by_accession` -- localization

## Drug Playbook (~30 tools)

When you find a drug, call ALL of these. Requires: drug name, ChEMBL ID, and/or PubChem CID.

**Resolve IDs first**:

- `OpenTargets_get_drug_chembId_by_generic_name` -- name -> ChEMBL ID
- `PubChem_get_CID_by_compound_name` -- name -> PubChem CID

**T1 (Regulatory/Curated)**:

- `OpenTargets_get_drug_indications_by_chemblId` -- approved indications
- `OpenTargets_get_drug_mech_of_acti_by_chem` -- mechanism of action
- `OpenTargets_get_asso_targ_by_drug_chem` -- protein targets
- `OpenTargets_get_asso_dise_by_drug_chem` -- associated diseases
- `OpenTargets_get_drug_warnings_by_chemblId` -- safety warnings
- `OpenTargets_get_drug_blac_stat_by_chem_ID` -- black-box/withdrawn status
- `OpenTargets_get_drug_adve_even_by_chem` -- significant adverse events
- `OpenTargets_get_drug_appr_stat_by_chem` -- approval status
- `OpenTargets_drug_pharmacogenomics_data` -- pharmacogenomics
- `OpenTargets_get_drug_description_by_chemblId` -- year approved, type, phase
- `OpenTargets_get_drug_names_by_chemblId` -- generic + brand names
- `ClinicalTrials_search_by_intervention` -- all trials for this drug
- `ClinicalTrials_search_studies` -- trials by drug + disease
- `FAERS_count_reactions_by_drug_event` -- all adverse reactions
- `FAERS_count_seriousness_by_drug_event` -- serious vs non-serious
- `FAERS_count_outcomes_by_drug_event` -- outcomes (fatal, recovered...)
- `FAERS_count_death_related_by_drug` -- death-associated events
- `FAERS_count_patient_age_distribution` -- age distribution of AEs
- `FDA_get_adverse_reactions_by_drug_name` -- label adverse reactions
- `FDA_get_dosa_and_stor_info_by_drug_name` -- dosage from label

**T2 (Peer-Reviewed)**:

- `ChEMBL_get_molecule` -- molecular properties, structure
- `ChEMBL_get_molecule_targets` -- all targets with activity data
- `ChEMBL_search_similar_molecules` -- structural analogs
- `PubMed_search_articles` -- literature (query=DRUG_NAME)

**T4 (Computational)**:

- `KEGG_get_drug` -- KEGG drug details, targets, pathways
- `KEGG_get_drug_targets` -- gene targets from KEGG
- `OpenTargets_get_simi_enti_by_drug_chem` -- similar drugs (PubMed model)

## Disease Playbook (~20 tools)

When you find a disease. Requires: disease name and/or EFO ID.

**Resolve IDs first**:

- `OpenTargets_get_dise_id_desc_by_name` -- name -> EFO ID
- `OSL_get_efo_id_by_disease_name` -- alternative EFO resolver
- `KEGG_search_disease` -- name -> KEGG disease ID

**T1 (Regulatory/Curated)**:

- `OpenTargets_get_asso_targ_by_dise_efoI` -- associated genes (scored)
- `OpenTargets_get_asso_drug_by_dise_efoI` -- associated drugs
- `OpenTargets_get_asso_phen_by_dise_efoI` -- HPO phenotypes
- `OpenTargets_get_disease_description_by_efoId` -- description, cross-refs
- `OpenTargets_get_dise_ther_area_by_efoI` -- therapeutic area
- `OpenTargets_get_dise_ance_pare_by_efoI` -- disease hierarchy (parents)
- `OpenTargets_get_dise_desc_chil_by_efoI` -- disease hierarchy (children)
- `OpenTargets_get_disease_synonyms_by_efoId` -- synonyms
- `ClinicalTrials_search_studies` -- trials for this disease
- `ClinVar_search_variants` -- variants (condition=DISEASE_NAME)
- `KEGG_get_disease` -- KEGG disease details
- `KEGG_get_disease_genes` -- genes linked to KEGG disease

**T2 (Peer-Reviewed)**:

- `PubMed_search_articles` -- literature
- `PubMed_Guidelines_Search` -- clinical guidelines

**T4 (Computational)**:

- `OpenTargets_get_simi_enti_by_dise_efoI` -- similar diseases (PubMed model)
- `KEGG_search_network` -- disease signaling networks

## Pathway Playbook (~15 tools)

When you find a pathway. Requires: KEGG pathway ID and/or Reactome stable ID.

- `kegg_get_pathway_info` -- full pathway details
- `KEGG_get_pathway_genes` -- all member genes
- `KEGG_link_entries` -- link to drugs, diseases, compounds
- `kegg_search_pathway` -- find related pathways by keyword
- `KEGG_search_network` -- disease-associated signaling networks
- `Reactome_get_pathway` -- Reactome pathway details
- `Reactome_get_pathway_reactions` -- all reactions in pathway
- `Reactome_get_participants` -- proteins/molecules involved
- `Reactome_get_pathway_hierarchy` -- parent pathways
- `STRING_functional_enrichment` -- enrichment for pathway gene set
- `STRING_ppi_enrichment` -- are pathway proteins more connected than chance?

## Variant Playbook (~8 tools)

When you find a variant. Requires: gene symbol, rsID, or HGVS notation.

- `ClinVar_search_variants` -- search by gene or variant ID
- `ClinVar_get_variant_details` -- accession, genes, location
- `ClinVar_get_clinical_significance` -- pathogenicity classification
- `KEGG_search_variant` -- KEGG variant entries
- `KEGG_get_variant` -- mutation details, ClinVar/dbSNP cross-refs, drugs
- `OpenTargets_target_disease_evidence` -- IntOGen somatic driver evidence
- `PubMed_search_articles` -- literature on this variant

## Company Playbook (~15 tools)

When you find a company. Requires: company name.

- `SEC_EDGAR_search_filings` -- recent SEC filings
- `SEC_EDGAR_get_company_submissions` -- full filing history, CIK/ticker
- `ClinicalTrials_search_by_sponsor` -- trials they sponsor
- `ClinicalTrials_search_studies` -- trials mentioning company
- `FDA_OrangeBook_search_drug` -- approved drugs (by brand name)
- `OpenFDA_search_drug_approvals` -- approvals by sponsor name
- `OpenFDA_search_device_510k` -- device clearances
- `OpenFDA_search_drug_enforcement` -- recalls/enforcement
- `FAERS_count_reactions_by_drug_event` -- safety for each of their drugs
- `PubMed_search_articles` -- publications mentioning company
- `Wikipedia_search` / `Wikipedia_get_content` -- company profile
- WebSearch -- leadership, news, competitive landscape

## Fallback Chains

When a tool is broken or returns no data:

| Entity | Primary | Fallback 1 | Fallback 2 | Last resort |
|--------|---------|------------|------------|-------------|
| Gene function | OpenTargets | KEGG gene info | UniProt function | PubMed search |
| Protein info | UniProt | PDB | AlphaFold | Ensembl |
| Drug targets | OpenTargets + ChEMBL | KEGG drug targets | DrugBank | PubMed search |
| Drug safety | FAERS | FDA labels | OpenTargets warnings | PubMed search |
| Clinical trials | ClinicalTrials | EuropePMC (trial filter) | WebSearch | -- |
| Disease genes | OpenTargets | ClinVar | KEGG disease genes | GWAS Catalog |
| Pathways | KEGG | Reactome | WikiPathways | STRING enrichment |
| PPI network | STRING network | STRING partners | humanbase_ppi | IntAct |
| Literature | PubMed | OpenAlex | EuropePMC | Semantic Scholar |
| Variants | ClinVar | KEGG variant | gnomAD | GWAS Catalog |
| Company data | SEC EDGAR | WebSearch | Wikipedia | -- |

## The Unexpected Path Rule

If a connection leads to a domain not covered above:

1. **Then and only then** use `grep_tools` or `find_tools` to discover tools in the new domain
2. Execute whatever you find
3. Record the new tools in research_state.json `tools_discovered` for future reference

The playbook above covers the core 150+ tools. The other 1,750 are for edge cases -- microbiome, plant genomics, structural biology, etc. Discovery is for those edges, not the core.
