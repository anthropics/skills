# Human Protein Atlas Search Query API Reference

This document provides a comprehensive guide to constructing search queries for
the **Human Protein Atlas (HPA)**. The search engine allows users to filter the
HPA database based on protein expression, mRNA levels, subcellular localization,
and functional classifications.

---

## 1. Core Syntax Overview

The HPA search engine follows a standard key-value pair format. All queries are
**case-insensitive**.

**IMPORTANT:** Terms with spaces do **not** need to be enclosed in double
quotes (e.g. `protein_class:Transcription factors`), and adding quotes may
actually break the query. When a field has sub-categories, values for them are
separated by a semi-colon `;`. Multiple selections within a sub-category are
separated by a comma `,`.

* **Field Search**: `field:value`
  * Example: `chromosome:12`
* **Field with Subfields**: `field:subvalue1;subvalue2`
  * Example: `tissue_category_rna:Brain;Tissue enriched`
* **Multiple selections**: `field:subval1;sel1,sel2`
  * Example: `tissue_category_rna:Any;Tissue enriched,Group enriched`
* **Boolean AND**: `term1 AND term2`
  * Example: `protein_class:Enzymes AND chromosome:X`
* **Boolean OR**: `term1 OR term2`
  * Example: `tissue_category_rna:Any;Tissue enriched OR tissue_category_rna:Any;Tissue enhanced`
* **Boolean NOT**: `term1 NOT term2`
  * Example: `protein_class:Enzymes NOT chromosome:1`
* **Grouping**: `( ... )`
  * Example: `(tissue_category_rna:Any;Tissue enriched OR tissue_category_rna:Any;Group enriched) AND chromosome:1`

---

## 2. Specificity Classifications

The HPA categorizes gene expression based on RNA-seq data across tissues
(General Atlas), brain regions (Brain Atlas) and single cell types (Single Cell
Atlas). These categories are built out of two dropdowns in the UI: the
region/tissue to filter on, and the specificity category.

### RNA Tissue Specificity (`tissue_category_rna`)
Filters based on the general tissue distribution across the entire human body.
Format: `tissue_category_rna:<Tissue Name>;<Specificity Category>`

* **Specificity Categories**:
  * **`Tissue enriched`**: Genes with mRNA levels at least 4-fold higher in a
    single tissue compared to all others.
  * **`Group enriched`**: Genes with mRNA levels at least 4-fold higher in a
    group of 2-5 tissues compared to all others.
  * **`Tissue enhanced`**: Genes with mRNA levels at least 4-fold higher in a
    tissue compared to the *average* of all others.
  * **`Low tissue specificity`**: Low tissue specificity; detected in many
    tissues.
  * **`Not detected`**: Not detected in tissues.

*Example*: `tissue_category_rna:Liver;Tissue enriched`
*Example*: `tissue_category_rna:Any;Tissue enriched,Group enriched`

### RNA Brain Region Specificity (`brain_category_rna`)
Filters based on distribution across different brain structures.
Format: `brain_category_rna:<Brain Region>;<Specificity Category>`

* **Specificity Categories**:
  * **`Region enriched`**: Genes with mRNA levels at least 4-fold higher in one
    brain region compared to all others.
  * **`Group enriched`**: mRNA levels at least 4-fold higher in 2-5 brain
    regions.
  * **`Region enhanced`**: mRNA levels at least 4-fold higher in a brain region
    compared to the average of others.

*Example*: `brain_category_rna:Amygdala;Region enriched,Group enriched`

> **Pro-Tip:** If you are specifically looking for proteins that are *unique* to
> the brain compared to the rest of the body, combine `tissue_category_rna` and
> `brain_category_rna` fields.

---

## 3. Commonly Used Query Fields

Below is a reference of the most frequently used fields for filtering the
database.

* **`gene_name`**: Search by the official HGNC symbol.
  * Examples: `gene_name:APOE`, `gene_name:TP53`
* **`chromosome`**: Filter by the genomic location.
  * Examples: `1`, `2`, ..., `X`, `Y`, `MT`
* **`protein_class`**: Functional classification of the protein.
  * Examples: `Enzymes`, `Transcription factors`, `FDA approved drug targets`
* **`subcell_location`**: Main localization based on ICC staining.
  * Examples: `Nucleoplasm`, `Mitochondria`, `Cytosol`
* **`predicted_location`**: Filter for secreted or intracellular logic.
  * Examples: `Predicted secreted proteins`, `Predicted membrane proteins`
* **`cancer_category_rna`**: Expression in specific cancers.
  * Example: `cancer_category_rna:Breast cancer;Cancer enriched`
* **`ihc_ab_validation`**: The validation level of the IHC antibody data.
  * Examples: `Supported`, `Approved`, `Enhanced - Independent`

---

## 4. Constructing Complex Queries

### Scenario A: Finding Specific Brain Markers
To find genes that are **Enriched** in a specific brain region (e.g.,
Hypothalamus) and localized to the **Vesicles** (for secretory/synaptic paths):
`brain_category_rna:Hypothalamus;Region enriched AND subcell_location:Vesicles`

### Scenario B: Finding Elevated Genes in a Region
To find genes that show an elevated protein expression level in the amygdala
compared to other regions of the human brain:
```
brain_category_rna:Amygdala;Region enriched,Group enriched,Region enhanced
AND sort_by:Tissue specific score
```

### Scenario C: Filtering for Validated Enzymes on Chromosome 1
To find Enzymes with Approved reliability (high-quality IHC data) located on
Chromosome 1:
`protein_class:Enzymes AND chromosome:1 AND ihc_ab_validation:Approved`

### Scenario D: Identifying Tissue-Specific Transcription Factors
To find Transcription factors that are either Tissue Enriched or Group Enriched
across any tissue:
```
protein_class:Transcription factors
AND tissue_category_rna:Any;Tissue enriched,Group enriched
```

---

Note on Data Versions: The HPA is updated periodically. The specificity
categories remain consistent, but the underlying RNA-seq datasets (e.g., HPA vs.
GTEx) may yield slightly different results if you specify the data source.
