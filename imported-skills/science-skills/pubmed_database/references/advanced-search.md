# PubMed Advanced Search Reference

This guide provides a comprehensive reference for advanced PubMed querying,
specifically for scientific research, high-precision filtering, and niche
metadata analysis.

## 1. Complete Field Qualifier Reference (Search Tags)

*   **[sh]**, MeSH Subheadings: Limits a MeSH term to a specific aspect. E.g.,
    `"Parkinson disease/genetics"[sh]`. Common: `/therapy`, `/toxicity`,
    `/drug effects`.
*   **[majr]**, MeSH Major Topic: Limits results to citations where the MeSH
    term is the **primary focus** of the article.
*   **[crdt]**, Create Date: The date the record was first added to PubMed. Best
    for finding "what's new" in the database.
*   **[edat]**, Entry Date: Used for sorting by "Most Recent." Set to
    publication date for older papers newly added.
*   **[sb]**, Subset: Pre-built high-quality filters. E.g., `systematic[sb]`,
    `"free full text"[sb]`, `cancer[sb]`.
*   **[nm]**, Supplementary Concept: For specific chemicals, drugs, or rare
    substances not yet in MeSH (formerly Substance Name).
*   **[ad]**, Affiliation: Search for authors at specific institutions, cities,
    or countries. E.g., `Stanford[ad]`.
*   **[auid]**, Author Identifier: Search by unique identifiers like ORCID.
    E.g., `0000-0002-1234-5678[auid]`.
*   **[la]**, Language: Restrict results by language. E.g., `eng[la]`.
*   **[pt]**, Publication Type: Filter by study design: `Meta-Analysis`,
    `Systematic Review`, `Randomized Controlled Trial`.
*   **[tw]**, Text Word: Includes Title, Abstract, MeSH, Subheadings, and other
    indexing fields. Very broad.
*   **[ta]**, Journal: Search by NLM Title Abbreviation or ISSN. E.g.,
    `Nature[ta]`.

## 2. Advanced Syntax & Logic

### Proximity Searching

Finds terms within a specific distance of each other. Available in `[ti]`,
`[tiab]`, and `[ad]`.

**Format:** `"term1 term2"[field:~N]`

**Example:** `"gut microbiome"[tiab:~2]` finds "gut" and "microbiome" with up
to 2 words between them.

### Boolean Nesting

PubMed processes logic from left to right. Use parentheses to control the order
of operations.

**Example:**

`(Parkinson OR "Dopamine deficiency") AND (Microbiome OR "Gut Flora")`

### Truncation

Use `*` at the end of a word to search for all terms that begin with that root.

**Example:** `patholog*` finds pathology, pathologist, pathological.

**Note:** Truncation turns off **Automatic Term Mapping (ATM)**.

## 3. Specialized Research Strategies

### Evidence-Based Medicine (EBM) Filters

To find the highest quality clinical evidence, append these filters:

-   **Systematic Reviews:** `AND systematic[sb]`
-   **Clinical Trials:** `AND "Clinical Trial"[pt]`
-   **Meta-Analyses:** `AND "Meta-Analysis"[pt]`

### The "Expert Query" Construction

For maximum coverage and precision, combine MeSH terms with Title/Abstract
keywords:

```
("Parkinson Disease"[mesh] OR "Parkinson's"[tiab])
    AND ("Gastrointestinal Microbiome"[mesh] OR "gut microbiome"[tiab:~2])
```

### Tracking Literature Updates

To find only the papers added to the database since your last visit (e.g., March
1st):

-   `Parkinson[tiab] AND 2026/03/01:2026/03/13[crdt]`

## 4. Troubleshooting & Nuances

-   **ATM (Automatic Term Mapping):** If you search `Parkinson`, PubMed
    automatically adds `"Parkinson Disease"[mesh]`. If you use quotes
    (`"Parkinson"`) or truncation (`Parkinson*`), ATM is disabled.
-   **Interchangeable Tags:** `[dp]` and `[pdat]` are identical. `[ta]` and
    `[journal]` are identical.
-   **Language Bias:** PubMed is predominantly English-language. Use `eng[la]`
    if the agent must perform text analysis on the results.
