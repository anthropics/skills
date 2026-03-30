---
name: tooluniverse
description: Router skill for ToolUniverse tasks. First checks if specialized tooluniverse skills (58+ skills covering disease/drug/target research, clinical decision support, genomics, epigenomics, chemical safety, systems biology, and more) can solve the problem, then falls back to general strategies for using 1400+ scientific tools. Covers tool discovery, multi-hop queries, comprehensive research workflows, disambiguation, evidence grading, and report generation. Use when users need to research any scientific topic, find biological data, or explore drug/target/disease relationships.
---

# ToolUniverse Router

Route user questions to specialized skills. If no skill matches, use general strategies from [references/general-strategies.md](references/general-strategies.md).

## Routing Workflow

1. **Extract keywords** from user's question
2. **Scan routing table** below for keyword matches
3. **Take action**:
   - **1 clear match** → invoke that skill NOW using the Skill tool
   - **Multiple matches** → ask user which they prefer (AskUserQuestion)
   - **No match** → use general strategies (load [references/general-strategies.md](references/general-strategies.md))
4. **If ambiguous** (e.g., "Tell me about aspirin") → ask user to clarify intent

**CRITICAL**: Actually INVOKE skills — don't describe them or show the routing table to the user.

**Language**: If the user writes in a non-English language, extract keywords for routing but respond in their language. All tool calls use English terms.

---

## Routing Table

### 1. Data Retrieval

| Keywords | Action |
|----------|--------|
| "get", "retrieve", "**chemical compound**", "PubChem", "ChEMBL", "drug molecule", "SMILES", "InChI" | `Skill(skill="tooluniverse-chemical-compound-retrieval")` |
| "get", "retrieve", "**expression data**", "gene expression", "omics dataset", "ArrayExpress", "RNA-seq", "microarray" | `Skill(skill="tooluniverse-expression-data-retrieval")` |
| "get", "retrieve", "**protein structure**", "PDB", "AlphaFold", "crystal structure", "3D model" | `Skill(skill="tooluniverse-protein-structure-retrieval")` |
| "get", "retrieve", "**sequence**", "DNA sequence", "RNA sequence", "protein sequence", "FASTA" | `Skill(skill="tooluniverse-sequence-retrieval")` |

### 2. Research & Profiling

| Keywords | Action |
|----------|--------|
| "research", "profile", "**disease**", "syndrome", "disorder", "comprehensive report on [disease]" | `Skill(skill="tooluniverse-disease-research")` |
| "research", "profile", "**drug**", "medication", "therapeutic agent", "tell me about [drug]" | `Skill(skill="tooluniverse-drug-research")` |
| "**literature review**", "papers about", "publications on", "research articles", "recent studies" | `Skill(skill="tooluniverse-literature-deep-research")` |
| "research", "profile", "**target**", "protein target", "gene target", "target validation" | `Skill(skill="tooluniverse-target-research")` |

### 3. Clinical Decision Support

| Keywords | Action |
|----------|--------|
| "**drug safety**", "adverse events", "side effects", "pharmacovigilance", "pharmacogenomics", "FAERS", "black box warning" | `Skill(skill="tooluniverse-pharmacovigilance")` |
| "**adverse event signal**", "safety signal detection", "disproportionality", "PRR", "ROR" | `Skill(skill="tooluniverse-adverse-event-detection")` |
| "**drug safety profile**", "drug safety assessment", "comprehensive safety" | `Skill(skill="tooluniverse-drug-safety-profiling")` |
| "**chemical safety**", "ADMET", "chemical toxicity", "environmental toxicity", "toxic effects" | `Skill(skill="tooluniverse-chemical-safety")` |
| "**cancer treatment**", "precision oncology", "tumor mutation", "targeted therapy", "EGFR", "KRAS", "BRAF" | `Skill(skill="tooluniverse-precision-oncology")` |
| "**cancer driver**", "driver gene", "driver mutation", "IntOGen", "cBioPortal" | `Skill(skill="tooluniverse-cancer-driver-analysis")` |
| "**somatic mutation interpretation**", "cancer variant", "oncogenic variant", "tumor variant" | `Skill(skill="tooluniverse-cancer-variant-interpretation")` |
| "**immunotherapy response**", "checkpoint inhibitor response", "TMB", "MSI", "PD-L1", "ICI response" | `Skill(skill="tooluniverse-immunotherapy-response-prediction")` |
| "**rare disease diagnosis**", "differential diagnosis", "phenotype matching", "HPO", "patient with [symptoms]" | `Skill(skill="tooluniverse-rare-disease-diagnosis")` |
| "**variant interpretation**", "VUS", "pathogenicity", "clinical significance", "is [variant] pathogenic" | `Skill(skill="tooluniverse-variant-interpretation")` |
| "**clinical guidelines**", "practice guidelines", "treatment guidelines", "dosing recommendations", "standard of care" | `Skill(skill="tooluniverse-clinical-guidelines")` |
| "**patient stratification**", "precision medicine", "biomarker stratification", "treatment selection" | `Skill(skill="tooluniverse-precision-medicine-stratification")` |

### 4. Discovery & Design

| Keywords | Action |
|----------|--------|
| "**find binders**", "virtual screening", "hit identification", "compounds for [target]", "**IC50**", "**bioactivity**", "**binding affinity**", "**potency**", "**selectivity**", "**SAR**", "**structure-activity**", "**lead optimization**", "**hit-to-lead**" | `Skill(skill="tooluniverse-binder-discovery")` |
| "**drug repurposing**", "new indication", "existing drugs for [disease]", "repurpose [drug]" | `Skill(skill="tooluniverse-drug-repurposing")` |
| "**drug target validation**", "target druggability", "validate target", "target assessment" | `Skill(skill="tooluniverse-drug-target-validation")` |
| "**network pharmacology**", "polypharmacology", "compound-target network", "multi-target" | `Skill(skill="tooluniverse-network-pharmacology")` |
| "**design protein**", "protein binder", "de novo protein", "RFdiffusion", "ProteinMPNN" | `Skill(skill="tooluniverse-protein-therapeutic-design")` |
| "**antibody engineering**", "antibody design", "humanization", "affinity maturation" | `Skill(skill="tooluniverse-antibody-engineering")` |

### 5. Genomics & Variant Analysis

| Keywords | Action |
|----------|--------|
| "**GWAS study**", "genome-wide association", "GWAS catalog", "GWAS for [trait]" | `Skill(skill="tooluniverse-gwas-study-explorer")` |
| "**GWAS trait to gene**", "trait-associated genes", "causal genes", "genes for [trait]" | `Skill(skill="tooluniverse-gwas-trait-to-gene")` |
| "**fine-mapping**", "credible sets", "causal variants", "statistical refinement" | `Skill(skill="tooluniverse-gwas-finemapping")` |
| "**SNP interpretation**", "rsID", "rs[number]", "variant annotation" | `Skill(skill="tooluniverse-gwas-snp-interpretation")` |
| "**polygenic risk**", "PRS", "genetic risk", "risk score for [disease]" | `Skill(skill="tooluniverse-polygenic-risk-score")` |
| "**structural variant**", "SV", "CNV", "deletion", "duplication", "chromosomal rearrangement" | `Skill(skill="tooluniverse-structural-variant-analysis")` |
| "**VCF**", "variant calling", "mutation analysis", "variant annotation pipeline" | `Skill(skill="tooluniverse-variant-analysis")` |

### 6. Systems & Network Analysis

| Keywords | Action |
|----------|--------|
| "**protein interactions**", "PPI", "interactome", "binding partners", "protein complexes" | `Skill(skill="tooluniverse-protein-interactions")` |
| "**systems biology**", "pathway analysis", "network analysis", "gene set enrichment" | `Skill(skill="tooluniverse-systems-biology")` |
| "**metabolomics**", "metabolite identification", "metabolic pathway" | `Skill(skill="tooluniverse-metabolomics")` |
| "**epigenomics**", "gene regulation", "transcription factor", "TF binding", "enhancers", "chromatin", "ChIP-seq" | `Skill(skill="tooluniverse-epigenomics")` |
| "**gene enrichment**", "pathway enrichment", "GO enrichment", "GSEA", "overrepresentation", "gene list analysis" | `Skill(skill="tooluniverse-gene-enrichment")` |
| "**multi-omics**", "omics integration", "transcriptomics + proteomics", "integrated analysis" | `Skill(skill="tooluniverse-multi-omics-integration")` |
| "**multi-omic disease**", "disease characterization", "genomic + transcriptomic + proteomic" | `Skill(skill="tooluniverse-multiomic-disease-characterization")` |

### 7. Screening & Functional Genomics

| Keywords | Action |
|----------|--------|
| "**CRISPR screen**", "genetic screen", "screen hits", "essential genes" | `Skill(skill="tooluniverse-crispr-screen-analysis")` |
| "**drug-drug interaction**", "DDI", "drug combination", "polypharmacy" | `Skill(skill="tooluniverse-drug-drug-interaction")` |
| "**differential expression**", "DESeq2", "RNA-seq analysis", "DE genes", "fold change" | `Skill(skill="tooluniverse-rnaseq-deseq2")` |
| "**proteomics**", "mass spectrometry", "protein quantification", "TMT", "iTRAQ", "label-free" | `Skill(skill="tooluniverse-proteomics-analysis")` |
| "**immune repertoire**", "TCR", "BCR", "T-cell receptor", "B-cell receptor", "clonotype" | `Skill(skill="tooluniverse-immune-repertoire-analysis")` |
| "**spatial transcriptomics**", "Visium", "MERFISH", "seqFISH", "Slide-seq", "spatial gene expression" | `Skill(skill="tooluniverse-spatial-transcriptomics")` |
| "**spatial omics**", "spatial proteomics", "spatial multi-omics" | `Skill(skill="tooluniverse-spatial-omics-analysis")` |
| "**microscopy**", "image analysis", "cell counting", "colony morphometry", "fluorescence quantification" | `Skill(skill="tooluniverse-image-analysis")` |
| "**phylogenetics**", "phylogenetic tree", "sequence alignment", "evolutionary analysis" | `Skill(skill="tooluniverse-phylogenetics")` |
| "**statistical modeling**", "regression analysis", "logistic regression", "survival analysis", "Cox" | `Skill(skill="tooluniverse-statistical-modeling")` |
| "**metabolomics analysis**", "LC-MS analysis", "metabolite quantification", "metabolic flux" | `Skill(skill="tooluniverse-metabolomics-analysis")` |

### 8. Clinical Trials & Study Design

| Keywords | Action |
|----------|--------|
| "**clinical trial design**", "trial protocol", "study design", "endpoint selection" | `Skill(skill="tooluniverse-clinical-trial-design")` |
| "**clinical trial matching**", "patient-to-trial", "trial eligibility", "find trials for patient" | `Skill(skill="tooluniverse-clinical-trial-matching")` |
| "**GWAS drug discovery**", "genetic target validation", "GWAS to drug" | `Skill(skill="tooluniverse-gwas-drug-discovery")` |

### 9. Outbreak Response

| Keywords | Action |
|----------|--------|
| "**pathogen**", "infectious disease", "outbreak", "emerging infection", "novel virus" | `Skill(skill="tooluniverse-infectious-disease")` |

### 10. Infrastructure & Setup

| Keywords | Action |
|----------|--------|
| "**llm finder**", "**llm search**", "**smart search**", "**reason about tools**", "**tool combination**", "**which tools**", "**multi-step**" | `Skill(skill="tu-llm")` |
| "**setup**", "install", "configure", "API keys", "upgrade", "**how to use**", "**get started**", "**CLI**", "**tu command**", "MCP vs CLI vs SDK", "**what is ToolUniverse**", "**what can this do**", "**what databases**", "**demo**", "**tutorial**", "**quickstart**", "**I'm new**" | `Skill(skill="setup-tooluniverse")` |
| "**SDK**", "Python SDK", "build AI scientist", "programmatic access", "**import tooluniverse**", "**coding API**", "**tu build**", "**typed wrappers**" | `Skill(skill="tooluniverse-sdk")` |
| "**install skills**", "missing skills", "skill not found", "add skills" | `Skill(skill="tooluniverse-install-skills")` |

---

## Tie-Breaking Rules

1. **Domain Over Setup**: When "how do I", "help me", "explain", or "what is" co-occurs with a **domain entity** (drug, gene, protein, disease, variant, pathway name), route to the **domain skill**, NOT setup.
   - "how do I find interactions for TP53?" → protein-interactions
   - "help me research metformin" → drug-research
   - "what is EGFR?" → target-research
   - "I'm new, can you research diabetes?" → disease-research
   - Only route to setup when NO domain entity present ("how do I use this?")

2. **Specificity Rule**: More specific beats general.
   - "cancer treatment" → precision-oncology (not disease-research)

3. **Data Type Rule**: "get/retrieve/fetch" → retrieval skills.
   - "get compound structure" → chemical-compound-retrieval (not drug-research)

4. **Still ambiguous**: Ask user with AskUserQuestion.

---

## When to Use General Strategies

Only when no specialized skill matches:


- Meta-questions about ToolUniverse itself (no domain entity)
- Custom workflows combining multiple skills
- User explicitly says "don't use specialized skills"

**WARNING**: "how do I find interactions for TP53?" is NOT a meta-question — route to protein-interactions.

When using general strategies, load [references/general-strategies.md](references/general-strategies.md) and **execute** them (run actual queries, don't just describe).

---

## Routing Examples

**Clear match**: "comprehensive research report on breast cancer" → `Skill(skill="tooluniverse-disease-research", args="breast cancer")`

**Ambiguous**: "Tell me about aspirin" → AskUserQuestion: drug profile, safety, chemical data, or repurposing?

**No match**: "How can I find all tools related to proteomics?" → General strategies: run find_tools queries

**Domain + setup keyword**: "help me understand BRCA1 variants" → `Skill(skill="tooluniverse-variant-interpretation", args="BRCA1")`
